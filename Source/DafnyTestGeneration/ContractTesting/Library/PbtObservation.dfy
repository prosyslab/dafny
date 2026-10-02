// Runtime role (local observation and value encoding; never contacts the parent process).
// Declarations of DafnyPbtRuntime.Observation, inserted into every source module for the legacy fixed-input harness.
class {:extern "DafnyPbtRuntime", "Observation"} PbtObservation {
  // Legacy harness. Runtime role: appends one observation record {name, value encoded by shape} for a named output after the call returns.
  static method {:extern "DafnyPbtRuntime.Observation", "Capture"} Capture<T>(name: string, value: T, shape: string)
  // Legacy harness. Runtime role: registers a heap object under the stable reference id name (type typeName), with its initial logical (ghost) fields given as base64 JSON.
  static method {:extern "DafnyPbtRuntime.Observation", "Register"} Register<T>(name: string, typeName: string, value: T, logicalBase64: string)
  // Legacy harness. Runtime role: appends one record per field/array element of every registered heap object, prefixed by phase ("initial" or "final").
  static method {:extern "DafnyPbtRuntime.Observation", "Snapshot"} Snapshot(phase: string)
  // Legacy harness. Runtime role: records a failed diagnostic-body assertion, then throws to abort the body.
  static method {:extern "DafnyPbtRuntime.Observation", "AssertionFailed"} AssertionFailed()
  // Legacy harness. Runtime role: pushes the modifies frame of method name; frame is a JSON array of reference values the method may write.
  static method {:extern "DafnyPbtRuntime.Observation", "EnterFrame"} EnterFrame(name: string, frame: string)
  // Legacy harness. Runtime role: pops the innermost modifies frame pushed by EnterFrame.
  static method {:extern "DafnyPbtRuntime.Observation", "ExitFrame"} ExitFrame()
  // Legacy harness. Runtime role: records a field write to receiver and throws if receiver is not in the observed heap; records a frame violation if receiver is outside an active frame (only the first violation of the process is recorded); returns receiver unchanged.
  static function {:extern "DafnyPbtRuntime.Observation", "Write"} Write<T>(receiver: T, field: string): T
  // Legacy harness. Runtime role: records the boolean value of one branch condition (symbol, source position, line, column) and returns value unchanged.
  static function {:extern "DafnyPbtRuntime.Observation", "Trace"} Trace(symbol: string, position: int, line: int, column: int, value: bool): bool
  // Legacy harness. Runtime role: placed after a precondition check that always returns true; throws if it is ever executed.
  static function {:extern "DafnyPbtRuntime.Observation", "Unreachable"} Unreachable<T>(): T
  // Legacy harness. Runtime role: returns the JSON encoding of value, interpreted by the base64 shape token, for use as a request argument.
  static function {:extern "DafnyPbtRuntime.Observation", "Serialize"} Serialize<T>(value: T, shape: string): string
}
