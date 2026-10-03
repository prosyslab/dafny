using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractCallableSelector {
  public static Method SelectMethod(Program program, ContractEntry entry, bool requireConcreteReceiver = true) {
    var matches = program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members)
      .Where(member => member.FullDafnyName == entry.Symbol || member.FullName == entry.Symbol).ToList();
    if (matches.Count != 1) {
      throw new ArgumentException($"Expected one resolved callable named '{entry.Symbol}', found {matches.Count}.");
    }
    var method = matches[0] switch {
      Method selected => selected,
      Function function => DescribeFunction(program, function),
      _ => throw new NotSupportedException("The selected declaration is not a method or function.")
    };
    if (method.IsGhost || method.EnclosingClass.TypeArgs.Count != 0 || entry.InputMode != ContractInputMode.Unit) {
      throw new NotSupportedException("This execution slice requires a non-ghost unit callable in a concrete class.");
    }
    if (method.TypeArgs.Count != (entry.TypeArguments?.Count ?? 0)) {
      throw new ArgumentException("Explicit type arguments must exactly match the callable's type parameters.");
    }
    if (method.TypeArgs.Count > 0) {
      var resolver = new ModuleResolver(new ProgramResolver(program), program.Options) {
        moduleInfo = program.ModuleSigs[method.EnclosingClass.EnclosingModuleDefinition]
      };
      var arguments = entry.TypeArguments!.Select(text => {
        var reporter = new BatchErrorReporter(program.Options);
        var type = ProgramParser.ParseType(text, method.Origin.Uri, reporter);
        if (reporter.ErrorCount != 0) {
          throw new ArgumentException("Invalid explicit Dafny type argument: " + text);
        }
        resolver.ResolveType(method.Origin, type, (ICodeContext)method,
          ResolveTypeOptionEnum.DontInfer, null);
        if (resolver.Reporter.ErrorCount != 0) {
          throw new ArgumentException("Unresolved explicit Dafny type argument: " + text);
        }
        if (!ContractHarnessBuilder.SupportedType(type)) {
          throw new NotSupportedException("Unsupported explicit callable type argument: " + text);
        }
        return type;
      }).ToList();
      var characteristics = new BatchErrorReporter(program.Options);
      TypeCharacteristicChecker.CheckInstantiation(method, arguments, characteristics);
      if (characteristics.ErrorCount != 0) {
        throw new ArgumentException(string.Join("\n", characteristics.AllMessages.Select(message => message.Message)));
      }
      method = ContractConcreteMethod.Create(method, (MethodOrFunction)matches[0], arguments);
    }
    if (method.IsStatic && entry.Receiver != null || requireConcreteReceiver && !method.IsStatic && entry.Receiver?.Kind != ContractValueKind.Reference) {
      throw new ArgumentException("Instance entries require an explicit heap reference receiver; static entries do not take a receiver.");
    }
    return method;
  }

  public static string FunctionResultName(Program program, Function function) =>
    function.Result?.Name ?? ContractBodyNames.Family(program, "contractResult");

  internal static Method DescribeFunction(Program program, Function function, string? resultFamily = null) {
    var resultName = function.Result?.Name ?? resultFamily ?? FunctionResultName(program, function);
    var result = function.Result ?? new Formal(function.Origin, resultName, function.ResultType, false, false, null);
    var contractCloner = new FunctionDescriptorCloner(function, result, true);
    var bodyCloner = new FunctionDescriptorCloner(function, result, false);
    var body = function.ByMethodBody != null ? bodyCloner.CloneBlockStmt(function.ByMethodBody) :
      function.Body == null ? null : new BlockStmt(function.Body.Origin, [
        new SingleAssignStmt(function.Body.Origin, Expression.CreateIdentExpr(result), new ExprRhs(bodyCloner.CloneExpr(function.Body))),
        new ReturnStmt(function.Body.Origin, null)
      ]);
    var descriptor = new Method(function.Origin, function.NameNode, function.Attributes, function.HasStaticKeyword,
      function.IsGhost, function.TypeArgs, function.Ins, function.Req,
      function.Ens.Select(clause => new AttributedExpression(contractCloner.CloneExpr(clause.E))).ToList(),
      function.Reads, function.Decreases, [result], new Specification<FrameExpression>([], null), body, null) {
      EnclosingClass = function.EnclosingClass,
      FunctionFromWhichThisIsByMethodDecl = function
    };
    descriptor.InheritVisibility(function);
    return descriptor;
  }

  private sealed class FunctionDescriptorCloner(Function function, Formal result, bool replaceResultCalls)
    : Cloner(cloneResolvedFields: true) {
    public override Expression CloneExpr(Expression expression) {
      // A by-method call statement keeps its unresolved (untyped) method-call syntax beside the resolved CallStmt.
      if (expression == null || !expression.WasResolved()) {
        return base.CloneExpr(expression!);
      }
      if (expression.Resolved is IdentifierExpr identifier &&
          (identifier.Var == function.Result || function.ByMethodDecl?.Outs.Any(output => output == identifier.Var) == true)) {
        return Expression.CreateIdentExpr(result);
      }
      if (replaceResultCalls && expression.Resolved is FunctionCallExpr call && call.Function == function &&
          (function.IsStatic || call.Receiver.Resolved is ThisExpr) &&
          call.Args.Count == function.Ins.Count && call.Args.Select((argument, index) =>
            argument.Resolved is IdentifierExpr argumentIdentifier && argumentIdentifier.Var == function.Ins[index]).All(matches => matches)) {
        return Expression.CreateIdentExpr(result);
      }
      return base.CloneExpr(expression);
    }
  }
}

/// <summary>A detached concrete view; compilation still executes OriginalCallable.</summary>
public sealed class ContractConcreteMethod : Method {
  public MethodOrFunction OriginalCallable { get; }

  private ContractConcreteMethod(Cloner cloner, Method descriptor, MethodOrFunction original)
    : base(cloner, descriptor) {
    TypeArgs = [];
    EnclosingClass = descriptor.EnclosingClass;
    FunctionFromWhichThisIsByMethodDecl = descriptor.FunctionFromWhichThisIsByMethodDecl;
    OriginalCallable = original;
    InheritVisibility(original);
  }

  internal static ContractConcreteMethod Create(Method descriptor, MethodOrFunction original,
    IReadOnlyList<Microsoft.Dafny.Type> arguments) {
    var substitution = descriptor.TypeArgs.Zip(arguments).ToDictionary(pair => pair.First, pair => pair.Second);
    var cloner = new ConcreteCloner(substitution);
    // Contracts precede formal declarations in the native Method copy constructor.
    foreach (var formal in descriptor.Ins.Concat(descriptor.Outs)) {
      cloner.CloneFormal(formal, false);
    }
    return new ContractConcreteMethod(cloner, descriptor, original);
  }

  private sealed class ConcreteCloner(Dictionary<TypeParameter, Microsoft.Dafny.Type> substitution)
    : Cloner(cloneResolvedFields: true) {
    public override Microsoft.Dafny.Type CloneType(Microsoft.Dafny.Type type) =>
      type == null ? null! : type.Subst(substitution);

    public override Expression CloneExpr(Expression expression) {
      if (expression == null) {
        return null!;
      }
      var clone = base.CloneExpr(expression);
      return new Substituter(null, [], substitution).Substitute(clone);
    }
  }
}
