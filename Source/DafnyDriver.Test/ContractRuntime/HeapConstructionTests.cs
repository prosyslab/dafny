#nullable enable
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Xunit;
using static DafnyTestGeneration.ContractTesting.ContractRuntimeObligationKind;

namespace DafnyDriver.Test.ContractRuntime;

/// <summary>Diagnostic construction of recursive, nested and class-only heap shapes.</summary>
public class HeapConstructionTests : IClassFixture<HeapConstructionTests.Fixture> {
  private const string File = "HeapConstruction";

  private static CampaignSpec Heap(string section) =>
    CampaignSpec.Fixture(File, section, "Client.Goal") with { ClosedQueryTimeout = 3000 };

  private static readonly CampaignSpec FixedList = Heap("FixedList").Buckets(3);
  private static readonly CampaignSpec MutatedList = Heap("MutatedList");
  private static readonly CampaignSpec NestedPaths = Heap("NestedPaths").Buckets(2);
  private static readonly CampaignSpec ClassOnly = Heap("ClassOnly");

  public sealed class Fixture : CampaignFixture {
    protected override IEnumerable<CampaignSpec> Campaigns() => [FixedList, MutatedList, NestedPaths, ClassOnly];
  }

  public HeapConstructionTests(Fixture fixture) { }

  // A recursive list whose ghost representation set has type set<object> is valid captured state.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task ObjectRepresentationSetDecidesRecursiveList(int bucket, bool violation) {
    var run = await Campaign.RunAsync(FixedList);
    Assert.Equal(FixedList.SampleCount, run.Population.Valid);
    Assert.True(run.Obligation("s == Sum(head)", Postcondition).Evaluations.Unchecked == 0, run.Detail());
    if (violation) {
      run.AssertViolated(bucket, "s == Sum(head)", Postcondition);
    } else {
      Assert.Empty(run.Violations(bucket));
    }
  }

  // A node whose representation set contains itself still supports a fixed-heap postcondition query, unchanged or mutated.
  [Theory]
  [InlineData(false)]
  [InlineData(true)]
  public async Task CyclicRepresentationSupportsFixedHeapPostcondition(bool mutate) {
    var run = await Campaign.RunAsync(mutate ? MutatedList : FixedList);
    var obligation = run.Obligation("Same(head)", Postcondition);
    if (mutate) {
      Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
      Assert.Equal(1, run.Population.Valid);
      Assert.Equal(1, obligation.Evaluations.ClosedSmt);
    } else {
      Assert.Empty(run.Violations(2));
      Assert.Equal(FixedList.SampleCount, obligation.Evaluations.ClosedSmt);
    }
  }

  // Leaf paths allocate imported inner objects in one generated constructor; the unmentioned one gets a default object.
  [Theory]
  [InlineData(0, false)]
  [InlineData(1, true)]
  public async Task NestedPathsAllocateInnerObjects(int bucket, bool violation) {
    var run = await Campaign.RunAsync(NestedPaths);
    Assert.Equal(NestedPaths.SampleCount, run.Population.Valid);
    if (violation) {
      run.AssertViolated(bucket, "y == x", Postcondition);
    } else {
      Assert.Empty(run.Violations(bucket));
    }
  }

  // A class-only annotation allocates an unmentioned non-null runtime object field instead of rejecting it.
  [Fact]
  public async Task ClassOnlyAnnotationAllocatesRuntimeObjectField() {
    var run = await Campaign.RunAsync(ClassOnly);
    Assert.True(run.Result.Status == ContractRuntimeStatus.ViolationFound, run.Detail());
    Assert.Equal(1, run.Population.Valid);
    Assert.Single(run.Result.Violations.Where(violation => violation.Kind == Postcondition));
  }
}
