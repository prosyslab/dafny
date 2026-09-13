using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Extracts input goals while retaining unprojected original specification expressions.</summary>
public sealed class ContractScenarioExtractor(Program program, Method method, int maxGoals = 64, Expression? receiverExpression = null) {
  private readonly List<ContractScenario> scenarios = [];

  public IReadOnlyList<ContractScenario> Extract() {
    foreach (var clause in method.Ens) {
      Visit(clause.E, "true", true);
    }
    return scenarios;
  }

  private void Add(Expression expression, string? condition, ContractScenarioProjection projection, string reason) {
    if (scenarios.Count < maxGoals) {
      scenarios.Add(new("spec" + scenarios.Count, expression, condition, projection, reason));
    }
  }

  private void Visit(Expression original, string prefix, bool positive) {
    var expression = original.Resolved;
    if (expression is ITEExpr conditional && !conditional.IsBindingGuard && InputOnly(conditional.Test)) {
      var thenPrefixes = GuardCases(conditional.Test, true).Select(guard => And(prefix, guard)).Take(maxGoals).ToList();
      var elsePrefixes = GuardCases(conditional.Test, false).Select(guard => And(prefix, guard)).Take(maxGoals).ToList();
      foreach (var branchPrefix in thenPrefixes) {
        Add(original, branchPrefix, ContractScenarioProjection.Exact, "Input-dependent then branch with exact short-circuit conditions.");
      }
      foreach (var branchPrefix in elsePrefixes) {
        Add(original, branchPrefix, ContractScenarioProjection.Exact, "Input-dependent else branch with exact short-circuit conditions and prior negations.");
      }
      foreach (var branchPrefix in thenPrefixes) { Visit(conditional.Thn, branchPrefix, positive); }
      foreach (var branchPrefix in elsePrefixes) { Visit(conditional.Els, branchPrefix, positive); }
      return;
    }
    if (positive && expression is BinaryExpr binary && binary.Op == BinaryExpr.Opcode.And) {
      Visit(binary.E0, prefix, true);
      Visit(binary.E1, prefix, true);
      return;
    }
    if (positive && expression is BinaryExpr disjunction && disjunction.Op == BinaryExpr.Opcode.Or) {
      foreach (var term in new[] { disjunction.E0, disjunction.E1 }) {
        if (InputOnly(term)) {
          Add(term, And(prefix, Initial(term)), ContractScenarioProjection.Necessary,
            "Overlapping disjunct goal; failure of this term does not decide the full specification.");
        } else {
          Visit(term, prefix, true);
        }
      }
      return;
    }
    if (positive && InputOnly(expression)) {
      Add(original, And(prefix, Initial(expression)), ContractScenarioProjection.Necessary,
        "Necessary input constraint for this positive specification fragment.");
      return;
    }
    Add(original, null, ContractScenarioProjection.Residual,
      "Output/current-heap dependence, binder context or negative polarity requires the original residual relation.");
  }

  private IEnumerable<string> GuardCases(Expression original, bool value) {
    var expression = original.Resolved;
    if (expression is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } negation) {
      return GuardCases(negation.E, !value);
    }
    if (expression is BinaryExpr binary && binary.Op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or or BinaryExpr.Opcode.Imp) {
      IEnumerable<string> Both(bool left, bool right) => GuardCases(binary.E0, left)
        .SelectMany(first => GuardCases(binary.E1, right).Select(second => And(first, second))).Take(maxGoals);
      // Preserve short-circuit definedness: a right operand is constrained only where it is evaluated.
      return binary.Op switch {
        BinaryExpr.Opcode.And => value ? Both(true, true) : GuardCases(binary.E0, false).Concat(Both(true, false)).Take(maxGoals),
        BinaryExpr.Opcode.Or => value ? GuardCases(binary.E0, true).Concat(Both(false, true)).Take(maxGoals) : Both(false, false),
        _ => value ? GuardCases(binary.E0, false).Concat(Both(true, true)).Take(maxGoals) : Both(true, false)
      };
    }
    var text = Initial(expression);
    return [value ? text : "!(" + text + ")"];
  }

  private bool InputOnly(Expression expression) {
    var variables = new HashSet<IVariable>();
    var heap = false;
    var oldHeap = false;
    DafnyType receiver = null!;
    var labels = new HashSet<Label>();
    FreeVariablesUtil.ComputeFreeVariables(program.Options, expression, variables, ref heap,
      ref oldHeap, labels, ref receiver, false);
    return !heap && labels.Count == 0 && (receiver == null || receiverExpression != null) && variables.All(variable => method.Ins.Any(formal => formal == variable));
  }

  private string Initial(Expression expression) => Printer.ExprToString(program.Options,
    new Substituter(receiverExpression!, [], []).Substitute(new InitialHeapCloner().CloneExpr(expression)));
  private static string And(string first, string second) => "(" + first + ") && (" + second + ")";
  private sealed class InitialHeapCloner : Cloner {
    public InitialHeapCloner() : base(cloneResolvedFields: true) { }
    public override Expression CloneExpr(Expression expression) => expression == null ? null! : expression.Resolved is OldExpr { AtLabel: null } old
      ? CloneExpr(old.Expr) : base.CloneExpr(expression);
  }
}
