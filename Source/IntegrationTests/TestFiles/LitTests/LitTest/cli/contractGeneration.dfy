// Input generation follows the actual arithmetic of an uncontracted helper.
// RUN: %baredafny test-contracts "%S/Inputs/contractGeneration.request.json" --generate > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: "status":"passed".*"kind":"integer","value":"8".*"goalId":"body0","goalKind":"implementation_path"

method Transform(x: int) returns (t: int) {
  t := 2 * x + 1;
}

method Entry(x: int) returns (r: int)
  ensures r >= 0
{
  var t := Transform(x);
  r := if t == 17 then -1 else 0;
}
