// The analysis should treat standard input as a target without serializing injected standard-library declarations.
// RUN: %baredafny definition-analysis --standard-libraries --stdin < "%S/Inputs/definitionAnalysisStdinInput.dfy" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"

// CHECK-NOT: DafnyStandardLibraries
// CHECK-L: "fullName": "DefinitionAnalysisStdin.Input",
// CHECK-NOT: DafnyStandardLibraries
