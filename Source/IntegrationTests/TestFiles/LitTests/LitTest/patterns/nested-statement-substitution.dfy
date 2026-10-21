// RUN: %verify --cores 1 --isolate-assertions --boogie /randomSeed:42 --filter-symbol NestedProof. "%s"
// RUN: %exits-with 4 %verify --cores 1 --isolate-assertions --boogie /randomSeed:42 --filter-symbol NestedProofRejectsFalse. "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Tree = Leaf(value: int) | Node(left: Tree, right: Tree)

function NestedProof(tree: Tree, expected: int): int
  requires tree == Leaf(expected) || tree == Node(Leaf(expected), Leaf(0))
{
  var outer := expected;
  forall current <- {tree} {:trigger current.Leaf?}
    ensures current == tree
  {
    match current
    case Leaf(outer) =>
      assert outer == expected;
    case Node(Leaf(outer), _) =>
      assert outer == expected;
    case _ =>
      assert false;
  }
  outer
}

function NestedProofRejectsFalse(tree: Tree): bool
{
  forall current <- {tree} {:trigger current.Leaf?}
    ensures current == tree
  {
    match current
    case Leaf(value) =>
      assert value != value;
    case _ =>
      assert true;
  }
  true
}
