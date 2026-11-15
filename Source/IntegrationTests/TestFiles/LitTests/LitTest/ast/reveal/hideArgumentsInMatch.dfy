// RUN: ! %verify --isolate-assertions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Hide and reveal arguments are never resolved. Match flattening clones them with the
// resolved case body; the statements must still resolve and keep their effect.

datatype Mode = Plain | Conditional | Indexed

type Small = k: int | 0 <= k < 10

predicate P(s: seq<int>) { |s| >= 0 }

predicate Holds<T>(f: T -> bool) { true }

function F(x: int): int { x }

opaque function G(x: int): int { x }

method Hidden(m: Mode, x: seq<int>, y: seq<int>, n: int) {
  match m {
    case Plain => {
      hide P(x + y);
      assert P(x); // error: P is hidden
    }
    case Conditional => {
      hide P(if n < 0 then x else y);
      assert P(y); // error: P is hidden
    }
    case Indexed => {
      hide F(-n), P(x[..0]);
      assert F(n) == n; // error: F is hidden
    }
  }
}

// Arguments that name user-defined types.
method Typed(m: Mode, x: seq<int>, n: int) {
  match m {
    case Plain => {
      hide P(if m is Mode then x else []), F(n as Small);
      assert P(x); // error: P is hidden
    }
    case Conditional => {
      hide Holds((z: Mode) => z == m);
      assert Holds((z: Mode) => z == m); // error: Holds is hidden
    }
    case Indexed => {
      hide F(var k: Small := 0; k), Holds((z: Small) => exists w: Mode :: w == m);
      assert F(n) == n; // error: F is hidden
    }
  }
}

// Without isolated assertions, a reveal in one branch also cancels a hide in the other
// branches of the method, so the reveals get their own method.
method Revealed(m: Mode, x: seq<int>, y: seq<int>, n: int) {
  match m {
    case Plain => {
      hide P(x + y);
      reveal P(x + y);
      assert P(x);
    }
    case Conditional => {
      reveal G(n as Small);
      assert G(n) == n;
    }
    case _ => {
    }
  }
}
