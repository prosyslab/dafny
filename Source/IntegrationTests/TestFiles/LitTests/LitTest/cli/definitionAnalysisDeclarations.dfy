// Authored declaration families must survive resolved and parse-only inventory without synthetic duplicates.
// RUN: %baredafny definition-analysis --allow-warnings --suppress-warnings --include-source-facts --include-semantic-facts "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// RUN: %baredafny definition-analysis --spans-only "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"

module Coverage {
  type Alias<T> = seq<T>
  type Positive = x: int | x >= 0 witness 0
  newtype Counter = x: int | x >= 0 witness 0
  type Opaque
  datatype Value = Empty | Full(value: Alias<int>)
  codatatype Stream = More(value: int, rest: Stream)
  trait Base extends object { var inherited: int }
  class Box extends Base {
    var first: int, second: int
    const Limit: int := 10
    constructor() { first := 0; second := 0; inherited := 0; }
    ghost predicate Valid() reads this { first <= Limit }
  }
  iterator Numbers() yields (value: int) { value := 0; yield; }
  least predicate Minimum(n: nat) { n == 0 }
  greatest predicate Maximum(n: nat) { n == 0 }
  export Public reveals Alias
}

module Outer.Inner {
  type Item = int
}

// CHECK-L: "fullName": "Coverage.Alias",
// CHECK-NEXT-L: "kind": "type synonym",
// CHECK-L: "fullName": "Coverage.Positive",
// CHECK-NEXT-L: "kind": "subset type",
// CHECK-L: "fullName": "Coverage.Counter",
// CHECK-NEXT-L: "kind": "newtype",
// CHECK-L: "fullName": "Coverage.Opaque",
// CHECK-NEXT-L: "kind": "abstract type",
// CHECK-L: "fullName": "Coverage.Value",
// CHECK-NEXT-L: "kind": "datatype",
// CHECK-L: "fullName": "Coverage.Stream",
// CHECK-NEXT-L: "kind": "datatype",
// CHECK-L: "fullName": "Coverage.Base",
// CHECK-NEXT-L: "kind": "trait",
// CHECK-L: "fullName": "Coverage.Base.inherited",
// CHECK-NEXT-L: "kind": "field",
// CHECK-L: "fullName": "Coverage.Box",
// CHECK-NEXT-L: "kind": "class",
// CHECK-L: "fullName": "Coverage.Box.first",
// CHECK-NEXT-L: "kind": "field",
// CHECK-L: "fullName": "Coverage.Box.second",
// CHECK-NEXT-L: "kind": "field",
// CHECK-L: "fullName": "Coverage.Box.Limit",
// CHECK-NEXT-L: "kind": "constant",
// CHECK-L: "fullName": "Coverage.Box._ctor",
// CHECK-NEXT-L: "kind": "constructor",
// CHECK-L: "fullName": "Coverage.Box.Valid",
// CHECK-NEXT-L: "kind": "predicate",
// CHECK-L: "fullName": "Coverage.Numbers",
// CHECK-NEXT-L: "kind": "iterator",
// CHECK-L: "fullName": "Coverage.Minimum",
// CHECK-NEXT-L: "kind": "least predicate",
// CHECK-L: "fullName": "Coverage.Maximum",
// CHECK-NEXT-L: "kind": "greatest predicate",
// CHECK-L: "fullName": "Coverage.Public",
// CHECK-NEXT-L: "kind": "export",
// CHECK-L: "fullName": "Outer.Inner.Item",
// CHECK-NEXT-L: "kind": "type synonym",
