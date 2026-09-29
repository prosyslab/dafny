#nullable enable
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyDriver.Test.ContractRuntimeHeapTests;

namespace DafnyDriver.Test;

public class ContractRuntimeHeapConstructionTests {
  private const string RecursiveList = """
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
      method Goal(head: Node) returns (s: int) requires head.Valid() SPEC {
        s := 0;
        var cur: Node? := head;
        while cur != null
          invariant cur == null || (cur.Valid() && cur.repr <= head.repr)
          invariant s + (if cur == null then 0 else Sum(cur)) == Sum(head)
          decreases if cur == null then {} else cur.repr
        {
          s := s + cur.value + LAST;
          cur := cur.next;
        }
        MUTATE
      }
    }
    """;

  private const string ListGenerator = """
    method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Node", "Client.Node.value", "Client.Node.next", "Client.Node.repr"}
      Generate(r: PbtRandom.Source) returns (head: Node) {
      var tail := new Node.ContractDiagnosticCreate(2, null, {});
      tail.repr := {tail};
      head := new Node.ContractDiagnosticCreate(1, tail, {});
      head.repr := {head} + tail.repr;
    }
    """;

  private static string List(string spec, int last = 0, bool mutate = false) => RecursiveList
    .Replace("SPEC", spec + (mutate ? " modifies head" : ""))
    .Replace("LAST", "(if cur.next == null then " + last + " else 0)")
    .Replace("MUTATE", mutate ? "head.value := head.value + 1;" : "");

  // A recursive list whose ghost representation set has type set<object> is valid captured state.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task ObjectRepresentationSetDecidesRecursiveList(int last, bool violation) {
    var result = await Run(List("ensures s == Sum(head)", last), ListGenerator, maxQueries: 16);
    Assert.True(result.Status == (violation ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.NoViolationFound),
      Detail(result));
    Assert.Equal(1, result.Population.Valid);
  }

  // A node whose representation set contains itself still supports a fixed-heap postcondition query.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task CyclicRepresentationSupportsFixedHeapPostcondition(bool mutate) {
    var result = await Run(List("ensures Same(head)", mutate: mutate), ListGenerator, maxQueries: 16);
    Assert.True(result.Status == (mutate ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.NoViolationFound),
      Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Contains(result.Obligations, obligation =>
      obligation.Kind == ContractRuntimeObligationKind.Postcondition && obligation.Evaluations.ClosedSmt == 1);
  }

  private const string Nested = """
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
      method Goal(p: Pair, x: int) returns (y: int) ensures p.left.value == p.right.value ==> y == x {
        y := x + INCREMENT;
      }
    }
    """;

  // Leaf paths allocate imported inner objects in one generated constructor; the unmentioned one gets a default object.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task NestedPathsAllocateInnerObjects(int increment, bool violation) {
    const string generator = """
      method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Pair", "Client.Pair.left.value", "Client.Pair.right.value"}
        Generate(r: PbtRandom.Source) returns (p: Pair, x: int) {
        p := new Pair.ContractDiagnosticCreate(Store.High(2), Store.High(2));
        x := 3;
      }
      """;
    var result = await Run(Nested.Replace("INCREMENT", increment.ToString()), generator);
    Assert.True(result.Status == (violation ? ContractRuntimeStatus.ViolationFound : ContractRuntimeStatus.NoViolationFound),
      Detail(result));
    Assert.Equal(1, result.Population.Valid);
  }

  // A class-only annotation allocates an unmentioned non-null runtime object field instead of rejecting it.
  [Fact]
  public async Task ClassOnlyAnnotationAllocatesRuntimeObjectField() {
    const string source = """
      module Client {
        class Inner { ghost var hidden: int constructor Init() requires false {} }
        class Outer { var inner: Inner constructor Init() requires false {} }
        method Goal(o: Outer) ensures false {}
      }
      """;
    const string generator = """
      method {:pbt_generator "Client.Goal"} {:pbt_heap_constructor "Client.Outer"}
        Generate(r: PbtRandom.Source) returns (o: Outer) {
        o := new Outer.ContractDiagnosticCreate();
      }
      """;
    var result = await Run(source, generator);
    Assert.True(result.Status == ContractRuntimeStatus.ViolationFound, Detail(result));
    Assert.Equal(1, result.Population.Valid);
    Assert.Single(result.Violations.Where(violation => violation.Kind == ContractRuntimeObligationKind.Postcondition));
  }
}
