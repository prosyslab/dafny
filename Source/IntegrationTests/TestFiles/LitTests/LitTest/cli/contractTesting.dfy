// The diagnostic executes an unverified body and returns a structured counterexample.
// RUN: %baredafny test-contracts "%S/Inputs/contractTesting.request.json" > "%t"
// RUN: %baredafny test-contracts "%S/Inputs/contractTesting.frameRestore.request.json" >> "%t"
// RUN: %baredafny test-contracts "%S/Inputs/contractTesting.classAssertion.request.json" >> "%t"
// RUN: %baredafny test-contracts "%S/Inputs/contractTesting.functionPrecondition.request.json" >> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: "status":"counterexample".*"violation":"postcondition"
// CHECK: "status":"counterexample".*"violation":"frame"
// CHECK: "status":"counterexample".*"violation":"body_assertion"
// CHECK: "status":"counterexample".*"violation":"call_precondition"

method Selected(x: int) returns (r: int)
  ensures r == x
{
  r := x + 1;
}
