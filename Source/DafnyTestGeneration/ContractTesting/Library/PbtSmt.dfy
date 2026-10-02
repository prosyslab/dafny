// Smt role (sends requests to the parent process, which answers them with SMT through .rpc request/response files).
// Declarations of DafnyPbtSmt.Oracle, inserted into every source module for the legacy fixed-input harness.
class {:extern "DafnyPbtSmt", "Oracle"} PbtSmt {
  // Legacy harness. Smt role: starts collecting the arguments of a precondition request for callee name.
  static method {:extern "DafnyPbtSmt.Oracle", "Begin"} Begin(name: string)
  // Legacy harness. Smt role: adds one encoded argument (name, value interpreted by the base64 shape token) to the request started by Begin.
  static method {:extern "DafnyPbtSmt.Oracle", "Input"} Input<T>(name: string, value: T, shape: string)
  // Legacy harness. Smt role: sends the "precondition" request for the arguments collected since Begin and blocks until the parent answers; throws if it does not answer "realized".
  static method {:extern "DafnyPbtSmt.Oracle", "End"} End()
  // Legacy harness. Smt role: sends a "precondition" request for callee name with JSON arguments and blocks for the answer; returns true once answered.
  static function {:extern "DafnyPbtSmt.Oracle", "CheckPrecondition"} CheckPrecondition(name: string, arguments: string): bool
  // Legacy harness. Smt role: asks the parent for a model of callee name with JSON arguments and returns the answer as JSON; when pure, an identical call on an identical heap reuses the earlier answer.
  static function {:extern "DafnyPbtSmt.Oracle", "Realize"} Realize(name: string, arguments: string, pure: bool): string
  // Legacy harness. Smt role: decodes the output named outputName from a Realize answer into a value of type T.
  static function {:extern "DafnyPbtSmt.Oracle", "Output"} Output<T>(realization: string, outputName: string): T
  // Legacy harness. Smt role: Realize followed by Output; returns the SMT-chosen value of type T for a function result.
  static function {:extern "DafnyPbtSmt.Oracle", "Choose"} Choose<T>(name: string, arguments: string, outputName: string, pure: bool): T
  // Legacy harness. Smt role: counts calls to the target symbol; on call number invocation sends "entry_start" and returns a nonzero token, otherwise returns 0.
  static function {:extern "DafnyPbtSmt.Oracle", "StartTarget"} StartTarget(symbol: string, arguments: string, invocation: int): int
  // Legacy harness. Smt role: for a nonzero token sends "entry_end" with the JSON outputs and ends the process with exit code 0; a zero token does nothing.
  static method {:extern "DafnyPbtSmt.Oracle", "EndTarget"} EndTarget(token: int, outputs: string)
  // Legacy harness. Smt role: EndTarget for a function target whose single output outputName is value (encoded by shape); returns value.
  static function {:extern "DafnyPbtSmt.Oracle", "EndTargetValue"} EndTargetValue<T>(token: int, outputName: string, value: T, shape: string): T
}
