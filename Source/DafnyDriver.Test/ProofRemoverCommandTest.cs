using Microsoft.Dafny;

namespace DafnyDriver.Test;

public class ProofRemoverCommandTest {
  [Fact]
  public void StripsSpecClausesAndPrunesUnusedDeclarations() {
    var source = """
module M {
  function Used(): int {
    Helper()
  }

  function Helper(): int {
    1
  }

  function Unused(): int {
    2
  }

  method Run()
    ensures Used() == 1
    decreases *
  {
    var text := "ensures stays in strings";
    var value := Used();
  }
}
""";

    var result = DafnyProofRemover.Preprocess(source);

    Assert.DoesNotContain("ensures Used", result);
    Assert.DoesNotContain("decreases *", result);
    Assert.Contains("\"ensures stays in strings\"", result);
    Assert.Contains("function Used", result);
    Assert.Contains("function Helper", result);
    Assert.DoesNotContain("function Unused", result);
    Assert.Contains("method Run", result);
  }

  [Fact]
  public void PreservesMethodBodyAfterMultilineClauseRemoval() {
    var source = """
module M {
  method Apply(x: int, y: int)
    ensures
      forall p | p in [x, y] ::
        p == x ||
        p == y
    decreases *
  {
    assert x == x;
  }
}
""";

    var result = DafnyProofRemover.Preprocess(source);

    Assert.DoesNotContain("ensures", result);
    Assert.DoesNotContain("p == y", result);
    Assert.Contains("assert x == x;", result);
    Assert.Contains("method Apply", result);
  }
}
