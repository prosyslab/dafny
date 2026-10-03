// Diagnostic construction of recursive, nested and class-only heap shapes. Bucket = Size() - 2.

// == source FixedList ==
// No frame: buckets 0 and 1 make the last addend 0 and 1 for the sum clause; bucket 2 checks the unchanged node.
module Client {
  class Node {
    var value: int
    var next: Node?
    ghost var repr: set<object>
    ghost predicate Valid() reads this, repr decreases repr {
      this in repr && (next != null ==> next in repr && next.repr <= repr && this !in next.repr && next.Valid())
    }
    constructor Init() requires false {}
  }
  ghost function Sum(n: Node): int reads n.repr requires n.Valid() decreases n.repr {
    n.value + (if n.next == null then 0 else Sum(n.next))
  }
  twostate predicate Same(n: Node) reads n { n.value == old(n.value) }
  method Goal(tag: int, head: Node) returns (s: int) requires head.Valid()
    ensures tag <= 1 ==> s == Sum(head)
    ensures tag == 2 ==> Same(head)
  {
    s := 0;
    var cur: Node? := head;
    while cur != null
      invariant cur == null || (cur.Valid() && cur.repr <= head.repr)
      invariant s + (if cur == null then 0 else Sum(cur)) == Sum(head)
      decreases if cur == null then {} else cur.repr
    {
      s := s + cur.value + (if cur.next == null then (if tag == 1 then 1 else 0) else 0);
      cur := cur.next;
    }
  }
}
// == generator FixedList ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Node", "Client.Node.value", "Client.Node.next", "Client.Node.repr"}
  Generate(r: PbtRandom.Source) returns (tag: int, head: Node) {
  var size := r.Size();
  tag := size - 2;
  var tail := new Node.ContractDiagnosticCreate(2, null, {});
  tail.repr := {tail};
  head := new Node.ContractDiagnosticCreate(1, tail, {});
  head.repr := {head} + tail.repr;
}

// == source MutatedList ==
module Client {
  class Node {
    var value: int
    var next: Node?
    ghost var repr: set<object>
    ghost predicate Valid() reads this, repr decreases repr {
      this in repr && (next != null ==> next in repr && next.repr <= repr && this !in next.repr && next.Valid())
    }
    constructor Init() requires false {}
  }
  ghost function Sum(n: Node): int reads n.repr requires n.Valid() decreases n.repr {
    n.value + (if n.next == null then 0 else Sum(n.next))
  }
  twostate predicate Same(n: Node) reads n { n.value == old(n.value) }
  method Goal(head: Node) returns (s: int) requires head.Valid() ensures Same(head) modifies head {
    s := 0;
    var cur: Node? := head;
    while cur != null
      invariant cur == null || (cur.Valid() && cur.repr <= head.repr)
      invariant s + (if cur == null then 0 else Sum(cur)) == Sum(head)
      decreases if cur == null then {} else cur.repr
    {
      s := s + cur.value + (if cur.next == null then 0 else 0);
      cur := cur.next;
    }
    head.value := head.value + 1;
  }
}
// == generator MutatedList ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Node", "Client.Node.value", "Client.Node.next", "Client.Node.repr"}
  Generate(r: PbtRandom.Source) returns (head: Node) {
  var tail := new Node.ContractDiagnosticCreate(2, null, {});
  tail.repr := {tail};
  head := new Node.ContractDiagnosticCreate(1, tail, {});
  head.repr := {head} + tail.repr;
}

// == source NestedPaths ==
// Bucket 0 adds 0 (holds), bucket 1 adds 1 (violates).
module Store {
  datatype Level = Low | High(n: int)
  class Box { ghost var value: Level constructor Init() requires false {} }
  class Note { ghost var text: seq<char> constructor Init() requires false {} }
}
module Client {
  import Store
  class Pair {
    ghost const left: Store.Box
    ghost const right: Store.Box
    ghost const note: Store.Note
    constructor Init() requires false {}
  }
  method Goal(tag: int, p: Pair, x: int) returns (y: int) ensures p.left.value == p.right.value ==> y == x {
    y := x + (if tag == 1 then 1 else 0);
  }
}
// == generator NestedPaths ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Pair", "Client.Pair.left.value", "Client.Pair.right.value"}
  Generate(r: PbtRandom.Source) returns (tag: int, p: Pair, x: int) {
  var size := r.Size();
  tag := size - 2;
  p := new Pair.ContractDiagnosticCreate(Store.High(2), Store.High(2));
  x := 3;
}

// == source ClassOnly ==
module Client {
  class Inner { ghost var hidden: int constructor Init() requires false {} }
  class Outer { var inner: Inner constructor Init() requires false {} }
  method Goal(o: Outer) ensures false {}
}
// == generator ClassOnly ==
method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Outer"}
  Generate(r: PbtRandom.Source) returns (o: Outer) {
  o := new Outer.ContractDiagnosticCreate();
}
