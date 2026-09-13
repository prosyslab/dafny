#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>
/// Audits the boundary between executable state and Dafny's logical heap before a
/// diagnostic body is compiled.  The runtime bridge observes only compiled fields;
/// silently dropping a ghost field write would therefore make the later Q check
/// unsound.
/// </summary>
internal static class ContractLogicalEffectAnalyzer {
  internal static void EnsureExecutableHeapEffectsSupported(IEnumerable<MethodOrFunction> reachable) {
    ArgumentNullException.ThrowIfNull(reachable);
    foreach (var callable in reachable.Where(callable => !callable.IsGhost && !HasExternAttribute(callable))) {
      var body = callable switch {
        Method method => method.Body,
        Function function => function.ByMethodBody,
        _ => null
      };
      if (body == null) {
        continue;
      }

      foreach (var statement in body.Descendants().OfType<Statement>()) {
        foreach (var lhs in AssignedExpressions(statement)) {
          if (FindGhostHeapField(lhs) is { } field) {
            throw new NotSupportedException(
              $"Internal implementation '{callable.FullDafnyName}' writes tracked ghost heap field " +
              $"'{field.EnclosingClass.FullDafnyName}.{field.Name}' at {field.Origin.line}:{field.Origin.col}; " +
              "logical heap effects are unsupported for runtime contract execution.");
          }
        }
      }
    }
  }

  private static IEnumerable<Expression> AssignedExpressions(Statement statement) {
    switch (statement) {
      case SingleAssignStmt single:
        yield return single.Lhs;
        break;
      case CallStmt call:
        foreach (var lhs in call.Lhs) {
          yield return lhs;
        }
        break;
    }
  }

  private static Field? FindGhostHeapField(Expression expression) {
    var resolved = expression.Resolved ?? expression;
    return resolved switch {
      MemberSelectExpr member when member.Member is Field field && field.IsGhost => field,
      MemberSelectExpr member => FindGhostHeapField(member.Obj),
      SeqSelectExpr select => FindGhostHeapField(select.Seq),
      MultiSelectExpr select => FindGhostHeapField(select.Array),
      _ => null
    };
  }

  private static bool HasExternAttribute(MethodOrFunction callable) =>
    Attributes.Contains(callable.Attributes, "extern");
}
