#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

public record DefinitionAnalysisResult(
  string Name,
  string FullName,
  string Kind,
  string EnclosingName,
  int Line,
  int Column,
  int Start,
  int? BodyStart,
  int End,
  string SourcePath,
  bool Ghost,
  bool HasByMethod,
  bool HasLoop,
  bool WorldRelated,
  string DeclarationKind,
  bool HasAxiomAttribute,
  bool HasExternAttribute,
  bool HasVerifyFalseAttribute,
  bool HasAssumeStatement,
  bool HasVarDeclaration,
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
  IReadOnlyList<string> Returns,
  IReadOnlyList<string> ReturnNames,
  IReadOnlyList<string> Requires,
  IReadOnlyList<string> Ensures,
  IReadOnlyList<string> Modifies,
  IReadOnlyList<string> SourceModules,
  IReadOnlyList<string> IncludedFiles,
  IReadOnlyList<string> LocalIncludedModules,
  IReadOnlyList<string> ImportedModules,
  IReadOnlyList<DefinitionAnalysisInclude> LocalIncludes,
  bool Recursive,
  IReadOnlyList<string> RecursiveGroup,
  IReadOnlyList<string> Callees,
  IReadOnlyList<string> CallSequence,
  IReadOnlyList<string> CallNames,
  IReadOnlyList<string> DirectPostconditionCallees,
  IReadOnlyList<DefinitionReference> References,
  IReadOnlyList<string> Dependencies
);

public record DefinitionReference(
  string TargetFullName,
  string TargetModule,
  string TargetKind,
  bool IsPattern,
  int Start,
  int End
);

public record DefinitionAnalysisInclude(
  string SourcePath,
  string TargetPath,
  int Start,
  int End
);

public static class DefinitionAnalysis {
  public static IReadOnlyList<DefinitionAnalysisResult> Analyze(Program program) {
    var sourceFacts = SourceFacts.For(program);
    var allDeclarations = SourceDefinitions(program, spansOnly: false, includeIncludes: true);
    var declarations = allDeclarations
      .Where(declaration => !declaration.Declaration.Origin.FromIncludeDirective(program))
      .ToList();
    var callableDeclarations = allDeclarations
      .Where(declaration => declaration.BodyKind is
        DefinitionBodyKind.Function or
        DefinitionBodyKind.FunctionByMethod or
        DefinitionBodyKind.Method)
      .ToList();
    var callTargetIndex = CallTargetIndex.For(callableDeclarations);
    var callFacts = callableDeclarations.ToDictionary(
      declaration => declaration,
      declaration => CalledDefinitions(declaration, callTargetIndex));
    var graph = callFacts.ToDictionary(
      item => item.Key,
      item => item.Value.UniqueCallees);
    var declarationNodes = allDeclarations
      .Where(declaration => declaration.BodyKind != DefinitionBodyKind.FunctionByMethod)
      .ToDictionary(declaration => declaration.Declaration);
    var resolvedDeclarationFacts = ResolvedDeclarationFacts.For(declarations, declarationNodes);
    var recursionFacts = AnalyzeRecursion(graph);

    var results = declarations
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        sourceFacts,
        recursionFacts,
        graph,
        callFacts,
        declarationNodes,
        resolvedDeclarationFacts))
      .ToList();
    return results;
  }

  public static IReadOnlyList<DefinitionAnalysisResult> AnalyzeSpans(Program program) {
    var sourceFacts = SourceFacts.For(program);
    var results = RootSourceDefinitions(program, spansOnly: true)
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultForSpans(declaration, sourceFacts))
      .ToList();
    return results;
  }

  private static DefinitionAnalysisResult ResultFor(
    DefinitionNode declaration,
    SourceFacts sourceFacts,
    RecursionFacts recursionFacts,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph,
    IReadOnlyDictionary<DefinitionNode, CallFacts> callFacts,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    ResolvedDeclarationFacts resolvedDeclarationFacts) {
    return CreateResult(
      declaration,
      sourceFacts,
      recursionFacts.RecursiveDeclarations.Contains(declaration),
      recursionFacts.GroupNames.TryGetValue(declaration, out var groupNames)
        ? groupNames
        : Array.Empty<string>(),
      graph.TryGetValue(declaration, out var callees)
        ? callees.Select(item => item.ReportFullName).OrderBy(name => name, StringComparer.Ordinal).ToList()
        : Array.Empty<string>(),
      callFacts.TryGetValue(declaration, out var calls)
        ? calls.Sequence.Select(item => item.ReportFullName).ToList()
        : Array.Empty<string>(),
      resolvedDeclarationFacts.DirectPostconditionCalleesFor(declaration.Declaration),
      resolvedDeclarationFacts.ReferencesFor(declaration.Declaration),
      DependenciesFor(declaration, graph, declarationNodes));
  }

  private static DefinitionAnalysisResult ResultForSpans(
    DefinitionNode declaration,
    SourceFacts sourceFacts) {
    return CreateResult(
      declaration,
      sourceFacts,
      false,
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<DefinitionReference>(),
      Array.Empty<string>());
  }

  private static DefinitionAnalysisResult CreateResult(
    DefinitionNode declaration,
    SourceFacts sourceFacts,
    bool recursive,
    IReadOnlyList<string> recursiveGroup,
    IReadOnlyList<string> callees,
    IReadOnlyList<string> callSequence,
    IReadOnlyList<string> directPostconditionCallees,
    IReadOnlyList<DefinitionReference> references,
    IReadOnlyList<string> dependencies) {
    return new DefinitionAnalysisResult(
      declaration.Name,
      declaration.ReportFullName,
      declaration.Kind,
      declaration.EnclosingName,
      declaration.Line,
      declaration.Column,
      declaration.Start,
      declaration.BodyStart,
      declaration.End,
      declaration.SourcePath,
      declaration.Ghost,
      declaration.HasByMethod,
      declaration.HasLoop,
      declaration.WorldRelated,
      declaration.DeclarationKind,
      declaration.HasAxiomAttribute,
      declaration.HasExternAttribute,
      declaration.HasVerifyFalseAttribute,
      declaration.HasAssumeStatement,
      declaration.HasVarDeclaration,
      declaration.BodyShape,
      declaration.HasBroadExitRangeDisjunct,
      declaration.TypeParameters,
      declaration.TypeParameterNames,
      declaration.Parameters,
      declaration.ParameterNames,
      declaration.Returns,
      declaration.ReturnNames,
      declaration.Requires,
      declaration.Ensures,
      declaration.Modifies,
      sourceFacts.SourceModules,
      sourceFacts.IncludedFiles,
      sourceFacts.LocalIncludedModules,
      sourceFacts.ImportedModules,
      sourceFacts.LocalIncludes,
      recursive,
      recursiveGroup,
      callees,
      callSequence,
      declaration.CallNames,
      directPostconditionCallees,
      references,
      dependencies);
  }

  private sealed class ResolvedDeclarationFacts {
    private readonly IReadOnlyDictionary<INode, IReadOnlyList<DefinitionReference>> references;
    private readonly IReadOnlyDictionary<INode, IReadOnlyList<string>> directPostconditionCallees;

    private ResolvedDeclarationFacts(
      IReadOnlyDictionary<INode, IReadOnlyList<DefinitionReference>> references,
      IReadOnlyDictionary<INode, IReadOnlyList<string>> directPostconditionCallees) {
      this.references = references;
      this.directPostconditionCallees = directPostconditionCallees;
    }

    public static ResolvedDeclarationFacts For(
      IReadOnlyList<DefinitionNode> declarations,
      IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
      var uniqueDeclarations = declarations
        .Where(declaration => declaration.BodyKind != DefinitionBodyKind.FunctionByMethod)
        .ToList();
      return new ResolvedDeclarationFacts(
        uniqueDeclarations.ToDictionary(
          declaration => declaration.Declaration,
          declaration => (IReadOnlyList<DefinitionReference>)DefinitionAnalysis.ReferencesFor(
            declaration,
            declarationNodes)),
        uniqueDeclarations.ToDictionary(
          declaration => declaration.Declaration,
          declaration => (IReadOnlyList<string>)DefinitionAnalysis.DirectPostconditionCalleesFor(
            declaration,
            declarationNodes)));
    }

    public IReadOnlyList<DefinitionReference> ReferencesFor(INode declaration) {
      return references[declaration];
    }

    public IReadOnlyList<string> DirectPostconditionCalleesFor(INode declaration) {
      return directPostconditionCallees[declaration];
    }
  }

  private static List<DefinitionReference> ReferencesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    var references = new List<DefinitionReference>();
    ((Node)declaration.Declaration).Visit(node => {
      if (node is not IHasReferences hasReferences) {
        return true;
      }
      foreach (var reference in hasReferences.GetReferences()) {
        var result = ReferenceFor(
          reference,
          declarationNodes,
          node is MatchCase or IdPattern);
        if (result != null && result.Start >= declaration.Start && result.End <= declaration.End) {
          references.Add(result);
        }
      }
      return true;
    });
    return references
      .Distinct()
      .OrderBy(reference => reference.Start)
      .ThenBy(reference => reference.End)
      .ThenBy(reference => reference.TargetFullName, StringComparer.Ordinal)
      .ToList();
  }

  private static DefinitionReference? ReferenceFor(
    Reference reference,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    bool isPattern) {
    var start = reference.Referer.StartToken.pos;
    var end = reference.Referer.EndToken.pos + reference.Referer.EndToken.val.Length;
    if (declarationNodes.TryGetValue(reference.Referred, out var target)) {
      var suffix = $".{target.Name}";
      var targetModule = target.ReportFullName.EndsWith(suffix, StringComparison.Ordinal)
        ? target.ReportFullName[..^suffix.Length]
        : target.EnclosingName;
      return new DefinitionReference(
        target.ReportFullName,
        targetModule,
        target.Kind,
        isPattern,
        start,
        end);
    }
    if (reference.Referred is DatatypeCtor { EnclosingDatatype: { } datatype } constructor) {
      return new DefinitionReference(
        $"{datatype.FullDafnyName}.{constructor.Name}",
        datatype.EnclosingModuleDefinition.FullDafnyName,
        "constructor",
        isPattern,
        start,
        end);
    }
    return null;
  }

  private static List<string> DirectPostconditionCalleesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    if (declaration.Declaration is not MethodOrFunction methodOrFunction) {
      return [];
    }
    return methodOrFunction.Ens
      .Select(ensures => UnwrapExpression(ensures.E).Resolved)
      .OfType<FunctionCallExpr>()
      .Where(call => call.Function != null && declarationNodes.ContainsKey(call.Function))
      .Select(call => declarationNodes[call.Function].ReportFullName)
      .ToList();
  }

  private static List<string> DependenciesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    var dependencies = graph.TryGetValue(declaration, out var callees)
      ? callees.Where(node => node.BodyKind != DefinitionBodyKind.FunctionByMethod).ToHashSet()
      : new HashSet<DefinitionNode>();
    foreach (var type in declaration.Types) {
      CollectTypeDependencies(type, declarationNodes, dependencies);
    }
    return dependencies
      .Where(node => node != declaration)
      .Select(node => node.ReportFullName)
      .Distinct()
      .OrderBy(name => name, StringComparer.Ordinal)
      .ToList();
  }

  private static void CollectTypeDependencies(
    Type type,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    ISet<DefinitionNode> dependencies) {
    if (type is UserDefinedType { ResolvedClass: { } resolvedClass } &&
        declarationNodes.TryGetValue(resolvedClass, out var dependency)) {
      dependencies.Add(dependency);
    }
    foreach (var typeArgument in type.TypeArgs) {
      CollectTypeDependencies(typeArgument, declarationNodes, dependencies);
    }
  }

  internal static string SourcePath(INode declaration) {
    var filename = declaration.StartToken.ActualFilename;
    return filename == null ? "" : Path.GetFullPath(filename);
  }

  private static List<DefinitionNode> RootSourceDefinitions(Program program, bool spansOnly) {
    return SourceDefinitions(program, spansOnly, includeIncludes: false);
  }

  private static List<DefinitionNode> SourceDefinitions(
    Program program,
    bool spansOnly,
    bool includeIncludes) {
    var declarations = new List<DefinitionNode>();
    var modules = spansOnly ? ParsedModules(program) : program.Modules();
    foreach (var moduleDefinition in modules) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        var topLevelFromInclude = topLevelDecl.Origin.FromIncludeDirective(program);
        if (topLevelDecl is DatatypeDecl datatypeDecl && (includeIncludes || !topLevelFromInclude)) {
          var purpose = NodePurpose(spansOnly, topLevelFromInclude);
          declarations.Add(DefinitionNode.ForDatatype(datatypeDecl, moduleDefinition.Name, purpose));
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var member in topLevelDeclWithMembers.Members.OrderBy(member => member.Origin.pos)) {
          if (AutoGeneratedOrigin.Is(member.Origin)) {
            continue;
          }
          var memberFromInclude = member.Origin.FromIncludeDirective(program);
          if (!includeIncludes && memberFromInclude) {
            continue;
          }

          var purpose = NodePurpose(spansOnly, memberFromInclude);
          if (member is Function function) {
            declarations.Add(DefinitionNode.ForFunction(function, moduleDefinition.Name, purpose));
            if (!spansOnly && function.ByMethodBody != null) {
              declarations.Add(DefinitionNode.ForFunctionByMethod(function, moduleDefinition.Name, purpose));
            }
          } else if (member is MethodOrConstructor method && method is not Method { IsByMethod: true }) {
            declarations.Add(DefinitionNode.ForMethod(method, moduleDefinition.Name, purpose));
          } else if (member is ConstantField constant && constant.EnclosingClass is DefaultClassDecl) {
            declarations.Add(DefinitionNode.ForConstant(constant, moduleDefinition.Name, purpose));
          }
        }
      }
    }

    return declarations;

    static DefinitionNodePurpose NodePurpose(bool spansOnly, bool fromInclude) {
      if (spansOnly) {
        return DefinitionNodePurpose.Spans;
      }
      return fromInclude ? DefinitionNodePurpose.ResolvedInclude : DefinitionNodePurpose.ResolvedRoot;
    }
  }

  internal static IEnumerable<ModuleDefinition> ParsedModules(Program program) {
    var seen = new HashSet<ModuleDefinition>();
    foreach (var module in Visit(program.DefaultModuleDef)) {
      yield return module;
    }

    IEnumerable<ModuleDefinition> Visit(ModuleDefinition module) {
      if (!seen.Add(module)) {
        yield break;
      }
      yield return module;
      foreach (var nested in module.TopLevelDecls.OfType<LiteralModuleDecl>()) {
        foreach (var nestedModule in Visit(nested.ModuleDef)) {
          yield return nestedModule;
        }
      }
    }
  }

  private sealed record CallTargetIndex(
    IReadOnlyDictionary<Function, DefinitionNode> FunctionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> ByMethodNodes,
    IReadOnlyDictionary<MethodOrConstructor, DefinitionNode> MethodNodes
  ) {
    public static CallTargetIndex For(IReadOnlyList<DefinitionNode> declarations) {
      var functionNodes = new Dictionary<Function, DefinitionNode>();
      var byMethodNodes = new Dictionary<Function, DefinitionNode>();
      var methodNodes = new Dictionary<MethodOrConstructor, DefinitionNode>();
      foreach (var declaration in declarations) {
        switch (declaration.BodyKind) {
          case DefinitionBodyKind.Function:
            functionNodes.Add((Function)declaration.Declaration, declaration);
            break;
          case DefinitionBodyKind.FunctionByMethod:
            byMethodNodes.Add((Function)declaration.Declaration, declaration);
            break;
          case DefinitionBodyKind.Method:
            methodNodes.Add((MethodOrConstructor)declaration.Declaration, declaration);
            break;
          default:
            throw new InvalidOperationException($"Unexpected callable body kind: {declaration.BodyKind}");
        }
      }
      return new CallTargetIndex(functionNodes, byMethodNodes, methodNodes);
    }
  }

  private sealed record CallFacts(
    IReadOnlyList<DefinitionNode> Sequence,
    HashSet<DefinitionNode> UniqueCallees
  );

  private static CallFacts CalledDefinitions(
    DefinitionNode declaration,
    CallTargetIndex callTargetIndex) {
    var sequence = new List<DefinitionNode>();
    var uniqueCallees = new HashSet<DefinitionNode>();

    foreach (var expression in declaration.SpecificationExpressions) {
      CollectExpressionCalls(
        expression,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        sequence,
        uniqueCallees);
    }

    if (declaration.ExpressionBody != null) {
      CollectExpressionCalls(
        declaration.ExpressionBody,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        sequence,
        uniqueCallees);
    }

    if (declaration.StatementBody != null) {
      CollectStatementCalls(
        declaration.StatementBody,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        callTargetIndex.MethodNodes,
        sequence,
        uniqueCallees);
    }

    return new CallFacts(sequence, uniqueCallees);
  }

  private static void CollectExpressionCalls(
    Expression expression,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    List<DefinitionNode> sequence,
    HashSet<DefinitionNode> uniqueCallees) {
    if (expression is FunctionCallExpr { Function: { } function } functionCall) {
      var nodes = functionCall.IsByMethodCall ? byMethodNodes : functionNodes;
      if (nodes.TryGetValue(function, out var target)) {
        sequence.Add(target);
        uniqueCallees.Add(target);
      }
    }

    foreach (var subExpression in expression.SubExpressions) {
      CollectExpressionCalls(subExpression, functionNodes, byMethodNodes, sequence, uniqueCallees);
    }
  }

  private static void CollectStatementCalls(
    Statement statement,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    IReadOnlyDictionary<MethodOrConstructor, DefinitionNode> methodNodes,
    List<DefinitionNode> sequence,
    HashSet<DefinitionNode> uniqueCallees) {
    if (statement is CallStmt callStmt && methodNodes.TryGetValue(callStmt.Method, out var methodTarget)) {
      sequence.Add(methodTarget);
      uniqueCallees.Add(methodTarget);
    }

    foreach (var expression in statement.SubExpressions) {
      CollectExpressionCalls(expression, functionNodes, byMethodNodes, sequence, uniqueCallees);
    }

    foreach (var subStatement in statement.SubStatements) {
      CollectStatementCalls(subStatement, functionNodes, byMethodNodes, methodNodes, sequence, uniqueCallees);
    }
  }

  internal static bool ContainsLoop(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is LoopStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsLoop);
  }

  internal static bool ContainsAssume(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is AssumeStmt or ExpectStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsAssume);
  }

  internal static bool ContainsVarDeclaration(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is VarDeclStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsVarDeclaration);
  }

  internal static string BodyShape(Expression? expression) {
    if (expression is SeqDisplayExpr { Elements.Count: 0 }) {
      return "empty-seq";
    }
    if (expression is LiteralExpr { Value: bool boolValue }) {
      return boolValue ? "true" : "false";
    }
    if (expression is LiteralExpr { Value: BigInteger integerValue } && integerValue == BigInteger.Zero) {
      return "zero";
    }
    if (expression is StringLiteralExpr { Value: string stringValue } && stringValue.Length == 0) {
      return "empty-string";
    }
    return "";
  }

  internal static bool ContainsBroadExitRangeDisjunct(Expression? expression) {
    if (expression == null) {
      return false;
    }
    if (IsBroadExitRangeDisjunct(expression)) {
      return true;
    }
    return expression.SubExpressions.Any(ContainsBroadExitRangeDisjunct);
  }

  internal static bool IsBroadExitRangeDisjunct(Expression expression) {
    expression = UnwrapExpression(expression);
    return IsExitRange(expression) ||
           expression is BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr &&
           (IsExitRange(binaryExpr.E0) || IsExitRange(binaryExpr.E1));
  }

  internal static bool StatementContainsBroadExitRangeDisjunct(Statement? statement) {
    if (statement == null) {
      return false;
    }
    return statement.SubExpressions.Any(ContainsBroadExitRangeDisjunct) ||
           statement.SubStatements.Any(StatementContainsBroadExitRangeDisjunct);
  }

  private static bool IsExitRange(Expression expression) {
    expression = UnwrapExpression(expression);
    if (expression is ChainingExpression chainingExpression) {
      for (var index = 0; index + 2 < chainingExpression.Operators.Count; index += 1) {
        if (chainingExpression.Operators[index] == BinaryExpr.Opcode.Eq &&
            chainingExpression.Operators[index + 1] == BinaryExpr.Opcode.Or &&
            chainingExpression.Operators[index + 2] == BinaryExpr.Opcode.Eq &&
            ((IsExitEquals(chainingExpression.Operands[index], chainingExpression.Operands[index + 1], 0) &&
              IsExitEquals(chainingExpression.Operands[index + 2], chainingExpression.Operands[index + 3], 1)) ||
             (IsExitEquals(chainingExpression.Operands[index], chainingExpression.Operands[index + 1], 1) &&
              IsExitEquals(chainingExpression.Operands[index + 2], chainingExpression.Operands[index + 3], 0)))) {
          return true;
        }
      }
      return IsExitRange(chainingExpression.E);
    }
    return expression is BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr &&
           ((IsExitEquals(binaryExpr.E0, 0) && IsExitEquals(binaryExpr.E1, 1)) ||
            (IsExitEquals(binaryExpr.E0, 1) && IsExitEquals(binaryExpr.E1, 0)));
  }

  private static bool IsExitEquals(Expression expression, int value) {
    expression = UnwrapExpression(expression);
    if (expression is ChainingExpression { Operators.Count: 1 } chainingExpression &&
        chainingExpression.Operators[0] == BinaryExpr.Opcode.Eq) {
      return (IsExitIdentifier(chainingExpression.Operands[0]) &&
              IsIntegerLiteral(chainingExpression.Operands[1], value)) ||
             (IsExitIdentifier(chainingExpression.Operands[1]) &&
              IsIntegerLiteral(chainingExpression.Operands[0], value));
    }
    if (expression is not BinaryExpr { Op: BinaryExpr.Opcode.Eq } binaryExpr) {
      return false;
    }
    return (IsExitIdentifier(binaryExpr.E0) && IsIntegerLiteral(binaryExpr.E1, value)) ||
           (IsExitIdentifier(binaryExpr.E1) && IsIntegerLiteral(binaryExpr.E0, value));
  }

  private static bool IsExitEquals(Expression left, Expression right, int value) {
    return (IsExitIdentifier(left) && IsIntegerLiteral(right, value)) ||
           (IsExitIdentifier(right) && IsIntegerLiteral(left, value));
  }

  private static bool IsExitIdentifier(Expression expression) {
    expression = UnwrapExpression(expression);
    return expression is IdentifierExpr { Name: "exit" } or NameSegment { Name: "exit" };
  }

  private static bool IsIntegerLiteral(Expression expression, int value) {
    expression = UnwrapExpression(expression);
    return expression is LiteralExpr { Value: BigInteger integerValue } &&
           integerValue == new BigInteger(value);
  }

  internal static Expression UnwrapExpression(Expression expression) {
    while (expression is ParensExpression parensExpression) {
      expression = parensExpression.E;
    }
    return expression;
  }

  internal static bool WorldRelated(MethodOrFunction declaration) {
    return declaration is Function { WhatKind: "predicate" } &&
           declaration.EntireRange.PrintOriginal().Contains("World");
  }

  private sealed record RecursionFacts(
    IReadOnlySet<DefinitionNode> RecursiveDeclarations,
    IReadOnlyDictionary<DefinitionNode, IReadOnlyList<string>> GroupNames
  );

  private static RecursionFacts AnalyzeRecursion(
    Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var recursiveDeclarations = new HashSet<DefinitionNode>();
    var groupNames = new Dictionary<DefinitionNode, IReadOnlyList<string>>();
    foreach (var component in StronglyConnectedComponents(graph)) {
      var first = component.First();
      if (component.Count == 1 && !graph[first].Contains(first)) {
        continue;
      }

      var names = component
        .Select(item => item.ReportFullName)
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToArray();
      foreach (var item in component) {
        recursiveDeclarations.Add(item);
        groupNames.Add(item, names);
      }
    }

    return new RecursionFacts(recursiveDeclarations, groupNames);
  }

  private static List<HashSet<DefinitionNode>> StronglyConnectedComponents(
    Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var index = 0;
    var stack = new Stack<DefinitionNode>();
    var onStack = new HashSet<DefinitionNode>();
    var indexes = new Dictionary<DefinitionNode, int>();
    var lowlinks = new Dictionary<DefinitionNode, int>();
    var components = new List<HashSet<DefinitionNode>>();

    foreach (var node in graph.Keys) {
      if (!indexes.ContainsKey(node)) {
        Visit(node);
      }
    }

    return components;

    void Visit(DefinitionNode node) {
      indexes[node] = index;
      lowlinks[node] = index;
      index += 1;
      stack.Push(node);
      onStack.Add(node);

      foreach (var target in graph[node]) {
        if (!indexes.ContainsKey(target)) {
          Visit(target);
          lowlinks[node] = System.Math.Min(lowlinks[node], lowlinks[target]);
        } else if (onStack.Contains(target)) {
          lowlinks[node] = System.Math.Min(lowlinks[node], indexes[target]);
        }
      }

      if (lowlinks[node] != indexes[node]) {
        return;
      }

      var component = new HashSet<DefinitionNode>();
      while (true) {
        var item = stack.Pop();
        onStack.Remove(item);
        component.Add(item);
        if (ReferenceEquals(item, node)) {
          break;
        }
      }

      components.Add(component);
    }
  }
}

internal sealed record SourceFacts(
  IReadOnlyList<string> SourceModules,
  IReadOnlyList<string> IncludedFiles,
  IReadOnlyList<string> LocalIncludedModules,
  IReadOnlyList<string> ImportedModules,
  IReadOnlyList<DefinitionAnalysisInclude> LocalIncludes
) {
  public static SourceFacts For(Program program) {
    var rootUris = program.Compilation.RootSourceUris.ToHashSet();
    var parsedModules = DefinitionAnalysis.ParsedModules(program).ToList();
    var rootModules = parsedModules
      .Where(module => !module.IsDefaultModule && !module.Origin.FromIncludeDirective(program))
      .ToList();

    var rootIncludes = program.Compilation.Includes
      .Where(include => rootUris.Contains(include.IncluderFilename))
      .ToList();

    return new SourceFacts(
      rootModules.Select(module => module.Name).Distinct().OrderBy(name => name, StringComparer.Ordinal).ToList(),
      rootIncludes.Select(include => Path.GetFileName(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      rootIncludes.Where(IsSameDirectoryDafnyInclude)
        .Select(include => Path.GetFileNameWithoutExtension(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      parsedModules
        .Where(module => !module.Origin.FromIncludeDirective(program))
        .SelectMany(module => ImportedModuleNames(program, module))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      rootIncludes
        .Where(include => Path.GetExtension(include.IncludedFilename.LocalPath) == ".dfy")
        .Select(include => new DefinitionAnalysisInclude(
          Path.GetFullPath(include.IncluderFilename.LocalPath),
          Path.GetFullPath(include.IncludedFilename.LocalPath),
          include.StartToken.pos,
          include.EndToken.pos + include.EndToken.val.Length))
        .OrderBy(include => include.SourcePath)
        .ThenBy(include => include.Start)
        .ToList());
  }

  private static bool IsSameDirectoryDafnyInclude(Include include) {
    if (Path.GetExtension(include.IncludedFilename.LocalPath) != ".dfy") {
      return false;
    }
    return Path.GetDirectoryName(include.IncluderFilename.LocalPath) ==
           Path.GetDirectoryName(include.IncludedFilename.LocalPath);
  }

  private static IEnumerable<string> ImportedModuleNames(Program program, ModuleDefinition module) {
    foreach (var moduleDecl in module.TopLevelDecls.OfType<ModuleDecl>()) {
      if (moduleDecl.Origin.FromIncludeDirective(program)) {
        continue;
      }

      foreach (var importedName in ImportedModuleNames(moduleDecl)) {
        if (importedName.Length > 0) {
          yield return importedName;
        }
      }
    }
  }

  private static IEnumerable<string> ImportedModuleNames(ModuleDecl moduleDecl) {
    if (moduleDecl is AliasModuleDecl alias) {
      foreach (var name in ModuleQualifiedNames(alias.TargetQId)) {
        yield return name;
      }
      if (alias.Signature?.ModuleDef != null) {
        yield return alias.Signature.ModuleDef.Name;
      }
    } else if (moduleDecl is AbstractModuleDecl abstractModule) {
      foreach (var name in ModuleQualifiedNames(abstractModule.QId)) {
        yield return name;
      }
      if (abstractModule.OriginalSignature?.ModuleDef != null) {
        yield return abstractModule.OriginalSignature.ModuleDef.Name;
      }
    }
  }

  private static IEnumerable<string> ModuleQualifiedNames(ModuleQualifiedId qualifiedId) {
    yield return qualifiedId.ToString();
    yield return qualifiedId.Path.Last().Value;
  }
}

internal enum DefinitionBodyKind {
  Function,
  FunctionByMethod,
  Method,
  Datatype,
  Constant
}

internal enum DefinitionNodePurpose {
  ResolvedRoot,
  ResolvedInclude,
  Spans
}

internal sealed record DefinitionReportFacts(
  int Line,
  int Column,
  int Start,
  int? BodyStart,
  int End,
  string SourcePath,
  bool Ghost,
  bool HasByMethod,
  bool HasLoop,
  bool WorldRelated,
  string DeclarationKind,
  bool HasAxiomAttribute,
  bool HasExternAttribute,
  bool HasVerifyFalseAttribute,
  bool HasAssumeStatement,
  bool HasVarDeclaration,
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
  IReadOnlyList<string> Returns,
  IReadOnlyList<string> ReturnNames,
  IReadOnlyList<string> Requires,
  IReadOnlyList<string> Ensures,
  IReadOnlyList<string> Modifies,
  IReadOnlyList<string> CallNames,
  IReadOnlyList<Type> Types
);

internal sealed class DefinitionNode(
  INode declaration,
  DefinitionBodyKind bodyKind,
  string name,
  string reportFullName,
  string kind,
  string enclosingName,
  IReadOnlyList<Expression> specificationExpressions,
  Expression? expressionBody,
  Statement? statementBody,
  DefinitionReportFacts? reportFacts
) {
  public INode Declaration { get; } = declaration;
  public DefinitionBodyKind BodyKind { get; } = bodyKind;
  public string Name { get; } = name;
  public string ReportFullName { get; } = reportFullName;
  public string Kind { get; } = kind;
  public string EnclosingName { get; } = enclosingName;
  public IReadOnlyList<Expression> SpecificationExpressions { get; } = specificationExpressions;
  public Expression? ExpressionBody { get; } = expressionBody;
  public Statement? StatementBody { get; } = statementBody;
  public DefinitionReportFacts? ReportFacts { get; } = reportFacts;

  public int Line => ReportFacts!.Line;
  public int Column => ReportFacts!.Column;
  public int Start => ReportFacts!.Start;
  public int? BodyStart => ReportFacts!.BodyStart;
  public int End => ReportFacts!.End;
  public string SourcePath => ReportFacts!.SourcePath;
  public bool Ghost => ReportFacts!.Ghost;
  public bool HasByMethod => ReportFacts!.HasByMethod;
  public bool HasLoop => ReportFacts!.HasLoop;
  public bool WorldRelated => ReportFacts!.WorldRelated;
  public string DeclarationKind => ReportFacts!.DeclarationKind;
  public bool HasAxiomAttribute => ReportFacts!.HasAxiomAttribute;
  public bool HasExternAttribute => ReportFacts!.HasExternAttribute;
  public bool HasVerifyFalseAttribute => ReportFacts!.HasVerifyFalseAttribute;
  public bool HasAssumeStatement => ReportFacts!.HasAssumeStatement;
  public bool HasVarDeclaration => ReportFacts!.HasVarDeclaration;
  public string BodyShape => ReportFacts!.BodyShape;
  public bool HasBroadExitRangeDisjunct => ReportFacts!.HasBroadExitRangeDisjunct;
  public IReadOnlyList<string> TypeParameters => ReportFacts!.TypeParameters;
  public IReadOnlyList<string> TypeParameterNames => ReportFacts!.TypeParameterNames;
  public IReadOnlyList<string> Parameters => ReportFacts!.Parameters;
  public IReadOnlyList<string> ParameterNames => ReportFacts!.ParameterNames;
  public IReadOnlyList<string> Returns => ReportFacts!.Returns;
  public IReadOnlyList<string> ReturnNames => ReportFacts!.ReturnNames;
  public IReadOnlyList<string> Requires => ReportFacts!.Requires;
  public IReadOnlyList<string> Ensures => ReportFacts!.Ensures;
  public IReadOnlyList<string> Modifies => ReportFacts!.Modifies;
  public IReadOnlyList<string> CallNames => ReportFacts!.CallNames;
  public IReadOnlyList<Type> Types => ReportFacts!.Types;

  public static DefinitionNode ForFunction(
    Function function,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    var specificationExpressions = SpecificationExpressionsFor(function);
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeExpressionBody(function.Body);
      reportFacts = new DefinitionReportFacts(
        function.Origin.line,
        function.Origin.col,
        function.StartToken.pos,
        BodyStartOffset(function),
        EndOffset(function),
        DefinitionAnalysis.SourcePath(function),
        function.IsGhost,
        function.ByMethodBody != null,
        false,
        DefinitionAnalysis.WorldRelated(function),
        function.WhatKind,
        function.HasAxiomAttribute,
        function.HasExternAttribute,
        function.HasVerifyFalseAttribute,
        false,
        false,
        DefinitionAnalysis.BodyShape(function.Body),
        specificationExpressions.Any(DefinitionAnalysis.ContainsBroadExitRangeDisjunct) ||
          bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(function.TypeArgs),
        TypeParameterNameTexts(function.TypeArgs),
        ParameterTexts(function),
        ParameterNameTexts(function),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. function.Ins.Select(formal => formal.Type), function.ResultType]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      function,
      DefinitionBodyKind.Function,
      function.Name,
      FullName(function, enclosingName),
      function.WhatKind,
      enclosingName,
      purpose == DefinitionNodePurpose.Spans ? Array.Empty<Expression>() : specificationExpressions,
      purpose == DefinitionNodePurpose.Spans ? null : function.Body,
      null,
      reportFacts);
  }

  public static DefinitionNode ForFunctionByMethod(
    Function function,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeStatementBody(function.ByMethodBody);
      reportFacts = new DefinitionReportFacts(
        function.Origin.line,
        function.Origin.col,
        function.StartToken.pos,
        function.ByMethodBody?.StartToken.pos,
        EndOffset(function),
        DefinitionAnalysis.SourcePath(function),
        function.IsGhost,
        true,
        bodyAnalysis.HasLoop,
        false,
        "by-method",
        function.HasAxiomAttribute,
        function.HasExternAttribute,
        function.HasVerifyFalseAttribute,
        bodyAnalysis.HasAssumeStatement,
        bodyAnalysis.HasVarDeclaration,
        "",
        bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(function.TypeArgs),
        TypeParameterNameTexts(function.TypeArgs),
        ParameterTexts(function),
        ParameterNameTexts(function),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. function.Ins.Select(formal => formal.Type), function.ResultType]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      function,
      DefinitionBodyKind.FunctionByMethod,
      function.Name,
      FullName(function, enclosingName) + "#by-method",
      "function-by-method",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      purpose == DefinitionNodePurpose.Spans ? null : function.ByMethodBody,
      reportFacts);
  }

  public static DefinitionNode ForMethod(
    MethodOrConstructor method,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    var specificationExpressions = SpecificationExpressionsFor(method);
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeStatementBody(method.Body);
      reportFacts = new DefinitionReportFacts(
        method.Origin.line,
        method.Origin.col,
        method.StartToken.pos,
        BodyStartOffset(method),
        EndOffset(method),
        DefinitionAnalysis.SourcePath(method),
        method.IsGhost,
        false,
        bodyAnalysis.HasLoop,
        false,
        method.WhatKind,
        method.HasAxiomAttribute,
        method.HasExternAttribute,
        method.HasVerifyFalseAttribute,
        bodyAnalysis.HasAssumeStatement,
        bodyAnalysis.HasVarDeclaration,
        "",
        specificationExpressions.Any(DefinitionAnalysis.ContainsBroadExitRangeDisjunct) ||
          bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(method.TypeArgs),
        TypeParameterNameTexts(method.TypeArgs),
        ParameterTexts(method),
        ParameterNameTexts(method),
        method.Outs.Select(formal => $"{formal.Name}: {formal.Type}").ToList(),
        method.Outs.Select(formal => formal.Name).ToList(),
        method.Req.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        method.Ens.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        method.Mod?.Expressions?.Select(item => item.EntireRange.PrintOriginal()).ToList() ?? [],
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. method.Ins.Select(formal => formal.Type), .. method.Outs.Select(formal => formal.Type)]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      method,
      DefinitionBodyKind.Method,
      method.Name,
      FullName(method, enclosingName),
      method is Constructor ? "constructor" : "method",
      enclosingName,
      purpose == DefinitionNodePurpose.Spans ? Array.Empty<Expression>() : specificationExpressions,
      null,
      purpose == DefinitionNodePurpose.Spans ? null : method.Body,
      reportFacts);
  }

  public static DefinitionNode ForDatatype(
    DatatypeDecl datatype,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      reportFacts = new DefinitionReportFacts(
        datatype.Origin.line,
        datatype.Origin.col,
        datatype.StartToken.pos,
        null,
        EndOffset(datatype),
        DefinitionAnalysis.SourcePath(datatype),
        false,
        false,
        false,
        false,
        "datatype",
        datatype.HasAxiomAttribute,
        datatype.HasExternAttribute,
        datatype.HasVerifyFalseAttribute,
        false,
        false,
        "",
        false,
        TypeParameterTexts(datatype.TypeArgs),
        TypeParameterNameTexts(datatype.TypeArgs),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. datatype.Ctors.SelectMany(constructor => constructor.Formals).Select(formal => formal.Type)]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      datatype,
      DefinitionBodyKind.Datatype,
      datatype.Name,
      FullName(datatype, enclosingName),
      "datatype",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      null,
      reportFacts);
  }

  public static DefinitionNode ForConstant(
    ConstantField constant,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeExpressionBody(constant.Rhs);
      reportFacts = new DefinitionReportFacts(
        constant.Origin.line,
        constant.Origin.col,
        constant.StartToken.pos,
        null,
        EndOffset(constant),
        DefinitionAnalysis.SourcePath(constant),
        constant.IsGhost,
        false,
        false,
        false,
        constant.WhatKind,
        constant.HasAxiomAttribute,
        constant.HasExternAttribute,
        constant.HasVerifyFalseAttribute,
        false,
        false,
        DefinitionAnalysis.BodyShape(constant.Rhs),
        bodyAnalysis.HasBroadExitRangeDisjunct,
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot ? [constant.Type] : Array.Empty<Type>());
    }
    return new DefinitionNode(
      constant,
      DefinitionBodyKind.Constant,
      constant.Name,
      FullName(constant, enclosingName),
      "constant",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      null,
      reportFacts);
  }

  private static List<Expression> SpecificationExpressionsFor(MethodOrFunction declaration) {
    var expressions = new List<Expression>();
    expressions.AddRange(declaration.Req.Select(item => item.E));
    expressions.AddRange(declaration.Ens.Select(item => item.E));
    if (declaration.Decreases.Expressions != null) {
      expressions.AddRange(declaration.Decreases.Expressions);
    }
    return expressions;
  }

  private static List<string> ParameterTexts(MethodOrFunction declaration) {
    return declaration.Ins
      .Select(formal => $"{formal.Name}: {formal.Type}")
      .ToList();
  }

  private static List<string> ParameterNameTexts(MethodOrFunction declaration) {
    return declaration.Ins
      .Select(formal => formal.Name)
      .ToList();
  }

  private static List<string> TypeParameterTexts(List<TypeParameter> typeParameters) {
    return typeParameters
      .Select(typeParameter => typeParameter.EntireRange.PrintOriginal())
      .ToList();
  }

  private static List<string> TypeParameterNameTexts(List<TypeParameter> typeParameters) {
    return typeParameters
      .Select(typeParameter => typeParameter.Name)
      .ToList();
  }

  private sealed record ExpressionBodyAnalysis(
    bool HasBroadExitRangeDisjunct,
    IReadOnlyList<string> CallNames
  );

  private sealed record StatementBodyAnalysis(
    bool HasLoop,
    bool HasAssumeStatement,
    bool HasVarDeclaration,
    bool HasBroadExitRangeDisjunct,
    IReadOnlyList<string> CallNames
  );

  private static ExpressionBodyAnalysis AnalyzeExpressionBody(Expression? expression) {
    var names = new List<string>();
    var hasBroadExitRangeDisjunct = false;
    if (expression != null) {
      VisitExpression(expression);
    }
    return new ExpressionBodyAnalysis(hasBroadExitRangeDisjunct, names);

    void VisitExpression(Expression current) {
      if (DefinitionAnalysis.IsBroadExitRangeDisjunct(current)) {
        hasBroadExitRangeDisjunct = true;
      }
      if (current is ApplySuffix applySuffix) {
        var name = SyntacticExpressionName(applySuffix.Lhs);
        if (name.Length > 0) {
          names.Add(name);
        }
      }
      foreach (var subExpression in current.SubExpressions) {
        VisitExpression(subExpression);
      }
    }
  }

  private static StatementBodyAnalysis AnalyzeStatementBody(Statement? statement) {
    var hasLoop = false;
    var hasAssumeStatement = false;
    var hasVarDeclaration = false;
    var hasBroadExitRangeDisjunct = false;
    if (statement == null) {
      return new StatementBodyAnalysis(false, false, false, false, []);
    }

    VisitStatement(statement);
    var names = new List<string>();
    CollectStatementCallNames(statement, names);
    return new StatementBodyAnalysis(
      hasLoop,
      hasAssumeStatement,
      hasVarDeclaration,
      hasBroadExitRangeDisjunct,
      names);

    void VisitStatement(Statement current) {
      hasLoop |= current is LoopStmt;
      hasAssumeStatement |= current is AssumeStmt or ExpectStmt;
      hasVarDeclaration |= current is VarDeclStmt;
      foreach (var expression in current.SubExpressions) {
        VisitExpression(expression);
      }
      foreach (var subStatement in current.SubStatements) {
        VisitStatement(subStatement);
      }
    }

    void VisitExpression(Expression current) {
      if (DefinitionAnalysis.IsBroadExitRangeDisjunct(current)) {
        hasBroadExitRangeDisjunct = true;
      }
      foreach (var subExpression in current.SubExpressions) {
        VisitExpression(subExpression);
      }
    }
  }

  private static void CollectStatementCallNames(Statement statement, List<string> names) {
    foreach (var expression in statement.PreResolveSubExpressions) {
      CollectExpressionCallNames(expression, names);
    }
    foreach (var subStatement in statement.PreResolveSubStatements) {
      CollectStatementCallNames(subStatement, names);
    }
  }

  private static void CollectExpressionCallNames(Expression expression, List<string> names) {
    if (expression is ApplySuffix applySuffix) {
      var name = SyntacticExpressionName(applySuffix.Lhs);
      if (name.Length > 0) {
        names.Add(name);
      }
    }
    foreach (var subExpression in expression.SubExpressions) {
      CollectExpressionCallNames(subExpression, names);
    }
  }

  private static string SyntacticExpressionName(Expression expression) {
    expression = DefinitionAnalysis.UnwrapExpression(expression);
    return expression switch {
      NameSegment nameSegment => nameSegment.Name,
      ExprDotName exprDotName => JoinName(SyntacticExpressionName(exprDotName.Lhs), exprDotName.SuffixName),
      MemberSelectExpr memberSelectExpr => JoinName(SyntacticExpressionName(memberSelectExpr.Obj), memberSelectExpr.MemberName),
      FunctionCallExpr functionCallExpr => JoinName(SyntacticExpressionName(functionCallExpr.Receiver), functionCallExpr.Name),
      _ => ""
    };
  }

  private static string JoinName(string prefix, string suffix) {
    return prefix.Length == 0 ? suffix : $"{prefix}.{suffix}";
  }

  private static int? BodyStartOffset(Declaration declaration) {
    return declaration.BodyStartTok == Token.NoToken ? null : declaration.BodyStartTok.pos;
  }

  private static string FullName(MemberDecl member, string enclosingName) {
    if (member.EnclosingClass != null) {
      return member.FullDafnyName;
    }
    return enclosingName.Length == 0 ? member.Name : $"{enclosingName}.{member.Name}";
  }

  private static string FullName(TopLevelDecl declaration, string enclosingName) {
    if (declaration.EnclosingModuleDefinition != null) {
      return declaration.FullDafnyName;
    }
    return enclosingName.Length == 0 ? declaration.Name : $"{enclosingName}.{declaration.Name}";
  }

  private static int EndOffset(INode node) {
    return node.EndToken.pos + node.EndToken.val.Length;
  }

}
