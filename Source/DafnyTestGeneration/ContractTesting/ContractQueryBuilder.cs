using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractQueryBuilder {
  public const string QueryName = "ContractDiagnosticQuery";
  public const string TargetMarker = "contract_query_target";
  public static string Name(ContractPreparedProgram prepared) => ContractBodyNames.Family(prepared.Program, QueryName);

  public static string Build(ContractPreparedProgram prepared, ContractTestRequest request,
    ContractQueryKind kind, IReadOnlyDictionary<string, ContractValue>? outputs = null, bool negate = false,
    IReadOnlyDictionary<string, ContractValue>? observations = null, IReadOnlyList<string>? choiceConstraints = null) {
    var method = prepared.Method;
    var formals = method.Ins.Concat(outputs == null ? [] : method.Outs).ToList();
    var parameterParts = formals.Select(formal => formal.Name + ": " + formal.Type).ToList();
    if (!method.IsStatic) {
      parameterParts.Add(prepared.ReceiverName + ": " + method.EnclosingClass.Name);
    }
    if (!string.IsNullOrEmpty(prepared.Heap?.QueryParameters)) {
      parameterParts.Add(prepared.Heap.QueryParameters);
    }
    var parameters = string.Join(", ", parameterParts);
    var bindings = method.Ins.Select(formal => formal.Name + " == " + ContractHarnessBuilder.InputExpression(prepared, request, formal.Name)).ToList();
    if (!method.IsStatic) {
      bindings.Add(prepared.ReceiverName + " == " + prepared.Heap!.ReferenceExpression(request.Entry.Receiver!.Value!));
    }
    bindings.AddRange(prepared.Heap?.InitialConstraints ?? []);
    bindings.AddRange(choiceConstraints ?? []);
    if (outputs != null) {
      bindings.AddRange(method.Outs.Select(formal => formal.Name + " == " +
        (prepared.Heap != null
          ? prepared.Heap.ValueExpression(outputs[formal.Name], formal.Type)
          : ContractModelCodec.ToDafny(outputs[formal.Name], method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName))));
    }
    var precondition = Conjunction(method.Req.Select(clause => RenderExpression(prepared, clause.E)));
    var postcondition = Conjunction(method.Ens.Select(clause => RenderExpression(prepared, clause.E)));
    var assertion = kind switch {
      ContractQueryKind.PremiseConsistency => "false",
      ContractQueryKind.EntryPrecondition or ContractQueryKind.CallPrecondition => precondition,
      _ => postcondition
    };
    if (negate) {
      assertion = "!(" + assertion + ")";
    }
    // The property under test occurs only in the assertion. In particular, no call to the
    // selected method introduces its ensures as an assumption into this diagnostic query.
    var assignments = observations != null ? prepared.Heap?.QueryAssignments(observations) : "";
    return ContractHarnessBuilder.Insert(prepared, $"\nmethod {Name(prepared)}({parameters})\n" +
      string.Join("\n", bindings.Select(binding => "requires " + binding)) + "\n" +
      (outputs != null ? "requires " + precondition + "\n" : "") + prepared.Heap?.QueryModifies + "\n" +
      $"{{ {assignments}\nassert {{:error \"{TargetMarker}\"}} {assertion}; }}\n");
  }

  public static string RenderExpression(ContractPreparedProgram prepared, Expression expression) {
    var method = prepared.Method;
    Expression? receiver = method.IsStatic ? null : new IdentifierExpr(method.Origin, prepared.ReceiverName) {
      Type = UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)
    };
    return Printer.ExprToString(prepared.Program.Options,
      new QuerySubstituter(receiver).Substitute(expression));
  }

  private sealed class QuerySubstituter(Expression? receiver) : Substituter(receiver!, [], []) {
    public override Expression Substitute(Expression expression) {
      if (expression is StaticReceiverExpr staticReceiver) {
        return new StaticReceiverExpr(expression.Origin, expression.Type, false) { Type = staticReceiver.Type };
      }
      return base.Substitute(expression);
    }
  }

  private static string Conjunction(IEnumerable<string> expressions) {
    var clauses = expressions.Select(expression => "(" + expression + ")").ToList();
    return clauses.Count == 0 ? "true" : string.Join(" && ", clauses);
  }
}
