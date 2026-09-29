#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Removes abstract-global assumptions from proof premises to prevent circular inhabitance proofs.</summary>
internal static class ContractGlobalAssumptions {
  internal static string RemoveAbstractConstantAxioms(Microsoft.Dafny.Program source, Program translated) {
    var names = ContractRuntimeHeapChecking.StaticConstants(source).Where(field => field.Rhs == null)
      .Select(field => field.FullSanitizedName).ToHashSet(StringComparer.Ordinal);
    var functions = translated.TopLevelDeclarations.OfType<Function>().Where(function => names.Contains(function.Name)).ToHashSet();
    var removed = translated.TopLevelDeclarations.OfType<Axiom>().Where(axiom => {
      var visitor = new References(functions);
      visitor.VisitExpr(axiom.Expr);
      return visitor.Found;
    }).ToHashSet();
    translated.RemoveTopLevelDeclarations(declaration => declaration is Axiom axiom && removed.Contains(axiom));
    foreach (var function in translated.TopLevelDeclarations.OfType<Function>()) {
      if (function.DefinitionAxiom != null && removed.Contains(function.DefinitionAxiom)) {
        function.DefinitionAxiom = null;
      }
      foreach (var axiom in function.OtherDefinitionAxioms.Where(removed.Contains).ToList()) {
        function.OtherDefinitionAxioms.Remove(axiom);
      }
    }
    foreach (var constant in translated.TopLevelDeclarations.OfType<Constant>()) {
      foreach (var axiom in constant.DefinitionAxioms.Where(removed.Contains).ToList()) {
        constant.DefinitionAxioms.Remove(axiom);
      }
    }
    return "Abstract-global proof assumptions removed: " + removed.Count + "; symbols: " +
      string.Join(", ", functions.Select(function => function.Name).OrderBy(name => name, StringComparer.Ordinal)) +
      "; axiom ids: " + string.Join(", ", removed.Select(axiom => axiom.UniqueId).OrderBy(id => id)) + ".";
  }

  private sealed class References(HashSet<Function> functions) : StandardVisitor {
    internal bool Found { get; private set; }

    public override Expr VisitNAryExpr(NAryExpr node) {
      if (node.Fun is FunctionCall call && functions.Contains(call.Func)) { Found = true; }
      return base.VisitNAryExpr(node);
    }
  }
}
