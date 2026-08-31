// The analysis should report only the explicit source while preserving resolved calls and import alias facts.
// RUN: %baredafny definition-analysis --include-source-facts --standard-libraries "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// RUN: %OutputCheck --file-to-check "%t" "%S/Inputs/definitionAnalysisTargets.not.check"

include "Inputs/definitionAnalysisIncluded.dfy"

module DefinitionAnalysisTarget {
  import Included = DefinitionAnalysisIncluded
  import Seq = Std.Collections.Seq
  import Std.Math

  function Target(xs: seq<int>): int
    requires |xs| > 0
  {
    Included.External(Seq.First(xs))
  }
}

// CHECK-L: "fullName": "DefinitionAnalysisTarget.Target",
// CHECK-L: "DefinitionAnalysisIncluded.External",
// CHECK-L: "Std.Collections.Seq.First"
// CHECK-L: "name": "DefinitionAnalysisTarget",
// CHECK-L: "alias": "Seq",
// CHECK-NEXT-L: "resolvedTarget": "Std.Collections.Seq",
// CHECK-NEXT-L: "hasAlias": true,
// CHECK: "resolvedTargetSourcePath": ".*DafnyStandardLibraries.dfy",
// CHECK-L: "alias": "Math",
// CHECK-NEXT-L: "resolvedTarget": "Std.Math",
// CHECK-NEXT-L: "hasAlias": false,
// CHECK: "resolvedTargetSourcePath": ".*DafnyStandardLibraries.dfy",
