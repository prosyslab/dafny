// Runtime role: local checks, observation records and value encoding for generated runtime-check instrumentation.
// These calls are inserted by the transformer, never written by a generator author; none contacts the parent process.
module {:extern "DafnyPbtRuntime"} PbtRuntime {
  // Static API of DafnyPbtRuntime.Checks; records JSON lines to the file named by --pbt-out.
  class {:extern "DafnyPbtRuntime", "Checks"} PbtChecks {
    // Generated runtime-check instrumentation. Runtime role: records one executed contract check (id, iteration, verdict, named values as JSON fragments) and returns passed; on a failed "call_precondition:" check it first records complete, then ends the sample process with exit code 0.
    static function {:extern} Check(id: string, iteration: int, passed: bool, values: seq<string>): bool
    // Generated runtime-check instrumentation. Runtime role: marks the start of one actual contract evaluation for profiling; returns true.
    static function {:extern} BeginCheck(): bool
    // Generated runtime-check instrumentation. Runtime role: marks the end of that evaluation for profiling; returns passed unchanged.
    static function {:extern} Evaluated(passed: bool): bool
    // Generated runtime-check instrumentation. Runtime role: returns true, or throws when a callee implementation was reached outside its precondition (passed is false).
    static function {:extern} Require(passed: bool): bool
    // Generated runtime-check instrumentation. Runtime role: returns true, or throws when obligation evaluation called a function outside its precondition (passed is false).
    static function {:extern} RequireInSpec(passed: bool): bool
    // Generated runtime-check instrumentation. Runtime role: recursion guard; returns true if (id, values) was not already being checked and marks it pending, false if it is already pending.
    static function {:extern} EnterContract<T>(id: string, values: T): bool
    // Generated runtime-check instrumentation. Runtime role: clears the pending mark set by EnterContract for (id, values); returns true if it was pending.
    static function {:extern} ExitContract<T>(id: string, values: T): bool
    // Generated runtime-check instrumentation. Runtime role: records a check whose verdict is not decided at runtime (id, iteration, named values); returns true.
    static function {:extern} Checkpoint(id: string, iteration: int, values: seq<string>): bool
    // Generated runtime-check instrumentation. Runtime role: returns the JSON encoding of value, interpreted by the base64 shape token (Observation.Serialize).
    static function {:extern "DafnyPbtRuntime.Observation", "Serialize"} Serialize<T>(value: T, shape: string): string
    // Generated runtime-check instrumentation. Runtime role: returns the JSON fragment "name":encoded for value under shape (plus extra runtime-field pairs for arrays and heap objects when RuntimeReferences is on), to pass as an element of Check/Checkpoint values (Observation.SerializeNamed).
    static function {:extern "DafnyPbtRuntime.Observation", "SerializeNamed"} SerializeNamed<T>(name: string, value: T, shape: string): string
    // Generated runtime-check instrumentation. Runtime role: substitutes concrete shape tokens (arguments) for the type parameters of a base64 shape token and returns the resulting token.
    static function {:extern "DafnyPbtRuntime.Observation", "InstantiateShape"} InstantiateShape(shape: string, arguments: seq<string>): string
    // Generated runtime-check instrumentation. Runtime role: remembers the current source location (for runtime_error records); returns true.
    static function {:extern} Location(location: string): bool
    // Generated runtime-check instrumentation. Runtime role: records one generated input (name, JSON value text).
    static method {:extern} Input(name: string, value: string)
    // Generated runtime-check instrumentation. Runtime role: records every member of a JSON object of generated inputs as one input record.
    static method {:extern} InputValues(values: string)
    // Generated runtime-check instrumentation. Runtime role: records a heap capture for phase ("entry" or "return") with outputs as JSON and the current observed heap.
    static method {:extern} CaptureHeap(phase: string, outputs: string)
    // Generated runtime-check instrumentation. Runtime role: records the heap on entry to a nested call (scope = callee name, inputs as JSON) and returns the new invocation number.
    static method {:extern} BeginCall(scope: string, inputs: string) returns (invocation: int)
    // Generated runtime-check instrumentation. Runtime role: records the heap on return from invocation of scope with outputs as JSON; throws if it is not the innermost call.
    static method {:extern} EndCall(scope: string, invocation: int, outputs: string)
    // Generated runtime-check instrumentation. Runtime role: pops invocation from the call stack; throws if it is not the innermost call.
    static method {:extern} LeaveCall(invocation: int)
    // Generated runtime-check instrumentation. Runtime role: records that the generator produced inputs.
    static method {:extern} Generated()
    // Generated runtime-check instrumentation. Runtime role: records that the entry call is about to execute.
    static method {:extern} Executed()
    // Generated runtime-check instrumentation. Runtime role: records that the sample finished and flushes the profile.
    static method {:extern} Complete()
    // Generated runtime-check instrumentation. Runtime role: records that the sample is rejected (entry precondition failed) and ends the process with exit code 0.
    static method {:extern} Stop()
    // Generated runtime-check instrumentation. Runtime role: throws; marks a statement that is unreachable by a failing assert false in the scaffold.
    static method {:extern} Unreachable()
    // Generated runtime-check instrumentation. Runtime role: throws; replaces a body that must never execute in the diagnostic program.
    static method {:extern} UnreachableBody()
    // Generated runtime-check instrumentation. Runtime role: throws; replaces an expression or field value that must never be evaluated.
    static function {:extern} UnreachableValue<T>(): T
  }
}
// Generator author API (model-facing): deterministic random stream for writing Generate(r).
// The stream depends only on --pbt-seed and --pbt-ordinal, so a sample is reproducible.
module {:extern "DafnyPbtRandom"} PbtRandom {
  // A seeded random source; obtain it with New(). Each draw except Size advances the stream.
  class {:extern "DafnyPbtRandom", "Source"} Source {
    // Returns an integer drawn from the stream in lo..hi inclusive.
    method {:extern} {:axiom} Int(lo: int, hi: int) returns (v: int) requires lo <= hi ensures lo <= v <= hi
    // Returns a natural number drawn from the stream in 0..bound inclusive.
    method {:extern} {:axiom} Nat(bound: nat) returns (v: nat) ensures v <= bound
    // Returns true or false drawn from the stream.
    method {:extern} Bool() returns (b: bool)
    // Returns a Unicode scalar character drawn from the stream in lo..hi inclusive, excluding surrogate code points.
    method {:extern} {:axiom} Char(lo: char, hi: char) returns (c: char) requires lo <= hi ensures lo <= c <= hi
    // Returns an index drawn from the stream in 0..n-1; requires n > 0.
    method {:extern} {:axiom} Index(n: nat) returns (i: nat) requires n > 0 ensures i < n
    // Returns a suggested collection size: 2 + ordinal / 4 (rounded down) capped at 32, so later samples get larger sizes; it does not advance the stream.
    method {:extern} {:axiom} Size() returns (s: nat) ensures 2 <= s <= 32
  }
  // Creates the random source; reads --pbt-seed and --pbt-ordinal from the process command line.
  method {:extern "DafnyPbtRandom.Source", "New"} {:axiom} New() returns (r: Source)
}
