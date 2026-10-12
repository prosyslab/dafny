#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Identifies original declared contracts without importing detached diagnostic expressions.</summary>
public static class ContractRuntimeClauseDependencies {
  /// <summary>Returns a unique source-bound original requires/ensures expression, or no supported mapping.</summary>
  public static Expression? OriginalExpression(Program original, IReadOnlyList<ContractSource> sources,
    ContractRuntimeClause clause) {
    if (clause.TypeConstraint || clause.OriginalSourceSetHash != ContractRuntimeTypeEvidence.SourceSetHash(sources)) {
      return null;
    }
    var owners = ContractRuntimeObligationTransformer.Members(original).OfType<MethodOrFunction>()
      .Where(owner => owner.FullDafnyName == clause.Owner.FullDafnyName && owner.Origin.Uri == clause.Owner.Origin.Uri).ToList();
    if (owners.Count != 1) { return null; }
    var owner = owners[0];
    var source = sources.SingleOrDefault(candidate => candidate.Path == clause.Obligation.Path &&
      ContractSourceSnapshot.UriFor(candidate.Path) == owner.Origin.Uri);
    if (source == null || source.Sha256 != clause.OriginalSourceHash ||
        ContractHarnessBuilder.Hash(source.Content) != source.Sha256) { return null; }
    IEnumerable<Expression> candidates = clause.Obligation.Kind switch {
      ContractRuntimeObligationKind.EntryPrecondition or ContractRuntimeObligationKind.CallPrecondition => owner.Req.Select(item => item.E),
      ContractRuntimeObligationKind.Postcondition or ContractRuntimeObligationKind.CalleePostcondition => owner.Ens.Select(item => item.E),
      ContractRuntimeObligationKind.Assertion when owner is Method method =>
        ContractRuntimeObligationTransformer.ExecutableAssertions(method).Select(assertion => assertion.Expr),
      _ => []
    };
    var bytes = Encoding.UTF8.GetBytes(source.Content);
    var matches = candidates.Where(expression =>
      expression.Origin.Uri == owner.Origin.Uri && expression.Origin.line == clause.Obligation.Line &&
      expression.Origin.col == clause.Obligation.Column && MatchesText(expression)).ToList();
    return matches.Count == 1 ? matches[0] : null;

    bool MatchesText(Expression expression) {
      var range = expression.EntireRange;
      var start = range.StartToken.pos;
      return start >= 0 && range.Length >= 0 && start <= bytes.Length - range.Length &&
        Encoding.UTF8.GetString(bytes, start, range.Length) == clause.Obligation.Clause;
    }
  }
}
