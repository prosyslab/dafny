// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

datatype Observation = Observation(entry: int)
datatype Choice = Some(count: nat) | None
datatype Pair = Pair(left: Choice, right: Choice)

class Constants {
  const Values := seq(2, i => i + 1)
}

method Main() {
  var length, lengthOnly := LengthOnly();
  expect length == 3 && lengthOnly == [1, 2, 3];
  print lengthOnly, "\n";

  var value, bodyOnly := BodyOnly();
  expect value == 7 && bodyOnly == [7, 8, 9];
  print bodyOnly, "\n";

  var observations, entries := Project();
  expect observations == [Observation(4), Observation(7)] && entries == [5, 8];
  print entries, "\n";

  var updated, original := SelfAssignment();
  expect updated == [5, 8] && original == [4, 7];
  print updated, " ", original, "\n";

  var start, nested := Nested();
  expect start == 20 && nested == [[20, 21], [21, 22]];
  print nested, "\n";

  var fromLet, offset := LetBody();
  expect offset == 10 && fromLet == [10, 11, 12];
  print fromLet, "\n";

  var i, shadowed := IndexShadowing();
  expect i == 100 && shadowed == [1, 2];
  print shadowed, " ", i, "\n";

  var count, fromFunction := FunctionInitializer();
  expect count == 2 && fromFunction == [3, 4];
  print fromFunction, "\n";

  var fromManyInputs := ManyInputs(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
  expect fromManyInputs == [153];
  print fromManyInputs, "\n";

  var a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s, fromManyOutputs := ManyOutputs();
  expect [a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s] ==
         [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
  expect fromManyOutputs == [153];
  print fromManyOutputs, "\n";

  var outputValue, outputTrips := OutputLoop();
  expect outputValue == 2 && outputTrips == 2;
  print "output-loop:", outputValue, ":", outputTrips, "\n";

  var localValue := LocalLoop();
  expect localValue == 2;
  print "local-loop:", localValue, "\n";

  outputValue, outputTrips := OutputLetLoop();
  expect outputValue == 2 && outputTrips == 2;
  print "output-let-loop:", outputValue, ":", outputTrips, "\n";

  localValue := LocalLetLoop();
  expect localValue == 2;
  print "local-let-loop:", localValue, "\n";

  outputValue, outputTrips := OutputMatchLoop();
  expect outputValue == 2 && outputTrips == 2;
  print "output-match-loop:", outputValue, ":", outputTrips, "\n";

  localValue := LocalMatchLoop();
  expect localValue == 2;
  print "local-match-loop:", localValue, "\n";

  fromManyInputs := ManyInputsInLet(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
  expect fromManyInputs == [153];
  print fromManyInputs, "\n";

  a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s, fromManyOutputs := ManyOutputsInMatch();
  expect [a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s] ==
         [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17];
  expect fromManyOutputs == [153];
  print fromManyOutputs, "\n";

  var conditional, divisor := Conditional(false);
  expect conditional == [42] && divisor == 0;
  print conditional, "\n";

  var current, actions := Deferred();
  expect current == 9 && |actions| == 1 && actions[0]() == 4;
  print current, " ", actions[0](), "\n";

  var genericOriginal, genericProjection := GenericProjection([6, 9]);
  expect genericOriginal == [6, 9] && genericProjection == [6, 9];
  print genericProjection, "\n";

  var empty, zero := ZeroLength();
  expect empty == [] && zero == 0;
  print empty, "\n";

  var updatedBase, simultaneous := Simultaneous();
  expect updatedBase == 5 && simultaneous == [11, 12];
  print updatedBase, " ", simultaneous, "\n";

  expect FunctionValues(5) == [5, 6];
  print FunctionValues(5), "\n";
  var constants := new Constants;
  expect constants.Values == [1, 2];
  print constants.Values, "\n";
}

// Capture an output parameter used only as the sequence length.
method LengthOnly() returns (length: nat, values: seq<int>)
  ensures length == 3 && values == [1, 2, 3]
{
  length := 3;
  values := seq(length, i => i + 1);
}

// Capture an output parameter used only in the initializer body.
method BodyOnly() returns (value: int, values: seq<int>)
  ensures value == 7 && values == [7, 8, 9]
{
  value := 7;
  values := seq(3, i => value + i);
}

// Project a datatype sequence output used in both length and initializer.
method Project() returns (observations: seq<Observation>, entries: seq<int>)
  ensures observations == [Observation(4), Observation(7)] && entries == [5, 8]
{
  observations := [Observation(4), Observation(7)];
  entries := seq(|observations|,
  j requires 0 <= j < |observations| => observations[j].entry + 1);
}

// Read the previous output value while assigning its replacement.
method SelfAssignment() returns (values: seq<int>, original: seq<int>)
  ensures values == [5, 8] && original == [4, 7]
{
  values := [4, 7];
  original := values;
  values := seq(|values|,
  i requires 0 <= i < |values| => values[i] + 1);
}

// Retain the outer index while nested constructors capture an output parameter.
method Nested() returns (start: int, values: seq<seq<int>>)
  ensures start == 20 && values == [[20, 21], [21, 22]]
{
  start := 20;
  values := seq(2, i => seq(2, j => start + i + j));
  assert values[0] == [20, 21];
  assert values[1] == [21, 22];
}

// Capture an output parameter inside a constructor in a let-expression body.
method LetBody() returns (values: seq<int>, offset: int)
  ensures offset == 10 && values == [10, 11, 12]
{
  offset := 10;
  values := var count := 3; seq(count, i => offset + i);
}

// Keep the bound index distinct from an output parameter with the same name.
method IndexShadowing() returns (i: int, values: seq<int>)
  ensures i == 100 && values == [1, 2]
{
  i := 100;
  values := seq(2, i => i + 1);
}

// Preserve construction with a function initializer instead of a literal lambda.
method FunctionInitializer() returns (count: nat, values: seq<int>)
  ensures count == 2 && values == [3, 4]
{
  count := 2;
  var initialize := i => i + 3;
  values := seq(count, initialize);
}

// Preserve construction with more ordinary inputs than a C# Func can accept.
method ManyInputs(a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int,
                  j: int, k: int, l: int, m: int, n: int, p: int, q: int, r: int, s: int)
  returns (values: seq<int>)
  ensures values == [a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s]
{
  values := seq(1, _ => a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s);
}

// Capture more output parameters than a C# Func can accept.
method ManyOutputs() returns (a: int, b: int, c: int, d: int, e: int, f: int, g: int,
                              h: int, j: int, k: int, l: int, m: int, n: int, p: int, q: int, r: int, s: int, values: seq<int>)
  ensures [a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s] ==
          [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  ensures values == [153]
{
  a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s :=
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17;
  values := seq(1, _ => a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s);
}

// Refresh captured output parameters on every direct loop-guard evaluation.
method OutputLoop() returns (value: int, trips: int)
  ensures value == 2 && trips == 2
{
  value, trips := 0, 0;
  while trips < 3 && seq(1, _ => value)[0] < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
}

// Preserve expression-time reads of an ordinary local in a direct loop guard.
method LocalLoop() returns (result: int)
  ensures result == 2
{
  var value, trips := 0, 0;
  while trips < 3 && seq(1, _ => value)[0] < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
  result := value;
}

// Capture outputs before a let introduces an enclosing lambda in the loop guard.
method OutputLetLoop() returns (value: int, trips: int)
  ensures value == 2 && trips == 2
{
  value, trips := 0, 0;
  while trips < 3 && (var count := 1; seq(count, _ => value))[0] < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
}

// Preserve current local values under a let-wrapped constructor in the loop guard.
method LocalLetLoop() returns (result: int)
  ensures result == 2
{
  var value, trips := 0, 0;
  while trips < 3 && (var count := 1; seq(count, _ => value))[0] < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
  result := value;
}

// Capture outputs before nested pattern matching introduces a loop-guard lambda.
method OutputMatchLoop() returns (value: int, trips: int)
  ensures value == 2 && trips == 2
{
  value, trips := 0, 0;
  while trips < 3 &&
    (match Pair(Some(1), None)
    case Pair(Some(count), _) => if count > 0 then seq(count, _ => value)[0] else -1
    case _ => -1) < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
}

// Preserve current local values under nested pattern matching in the loop guard.
method LocalMatchLoop() returns (result: int)
  ensures result == 2
{
  var value, trips := 0, 0;
  while trips < 3 &&
    (match Pair(Some(1), None)
    case Pair(Some(count), _) => if count > 0 then seq(count, _ => value)[0] else -1
    case _ => -1) < 2
    invariant value == trips && 0 <= trips <= 2
    decreases 2 - trips
  {
    value, trips := value + 1, trips + 1;
  }
  result := value;
}

// Capture more than sixteen inputs before an enclosing let-expression lambda.
method ManyInputsInLet(a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int,
                       j: int, k: int, l: int, m: int, n: int, p: int, q: int, r: int, s: int)
  returns (values: seq<int>)
  ensures values == [a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s]
{
  values := var count := 1;
            seq(count, _ => a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s);
}

// Capture more than sixteen outputs before an enclosing nested-match lambda.
method ManyOutputsInMatch() returns (a: int, b: int, c: int, d: int, e: int, f: int, g: int,
                                     h: int, j: int, k: int, l: int, m: int, n: int, p: int, q: int, r: int, s: int, values: seq<int>)
  ensures [a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s] ==
          [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  ensures values == [153]
{
  a, b, c, d, e, f, g, h, j, k, l, m, n, p, q, r, s :=
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17;
  values := match Pair(Some(1), None)
    case Pair(Some(count), _) =>
      seq(count, _ => a + b + c + d + e + f + g + h + j + k + l + m + n + p + q + r + s)
    case _ => [];
}

// Keep skipped initializer computations inside their conditional and short-circuit branches.
method Conditional(enabled: bool) returns (values: seq<int>, divisor: int)
  requires !enabled
  ensures values == [42] && divisor == 0
{
  divisor := 0;
  var unused := enabled && seq(1, _ => 10 / divisor)[0] == 0;
  expect !unused;
  values := if enabled then seq(1, _ => 10 / divisor) else [42];
}

// Preserve the captured value when an element is a lambda invoked after reassignment.
method Deferred() returns (value: int, actions: seq<() -> int>)
  ensures value == 9 && |actions| == 1 && actions[0]() == 4
{
  value := 4;
  actions := seq(1, _ => () => value);
  value := 9;
}

// Preserve generic sequence element types when capturing an output parameter.
method GenericProjection<T(==)>(items: seq<T>) returns (observations: seq<T>, results: seq<T>)
  ensures observations == items && results == items
{
  observations := items;
  results := seq(|observations|,
  i requires 0 <= i < |observations| => observations[i]);
}

// Avoid evaluating an initializer whose constructor has zero elements.
method ZeroLength() returns (values: seq<int>, divisor: int)
  ensures values == [] && divisor == 0
{
  divisor := 0;
  values := seq(0, i requires 0 <= i < 0 => 10 / divisor);
}

// Read old values while evaluating simultaneous output assignments.
method Simultaneous() returns (base: int, values: seq<int>)
  ensures base == 5 && values == [11, 12]
{
  base, values := 4, [7, 8];
  base, values := 5, seq(|values|, i requires 0 <= i < |values| => base + values[i]);
}

// Preserve construction in an ordinary function body.
function FunctionValues(value: int): seq<int> {
  seq(2, i => value + i)
}
