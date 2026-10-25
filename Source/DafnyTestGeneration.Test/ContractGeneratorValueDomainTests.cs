#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;
using SolverOutcome = Microsoft.Boogie.SolverOutcome;

namespace DafnyTestGeneration.Test;

// Boundary trace: these tests reuse ContractGeneratorProofTests' bounded source strings, embedded RNG resource,
// dictionary-backed parser and resolver, and pure coverage accounting. They reach no solver, file write, temporary
// directory, subprocess, synchronization, generated runtime compilation or deferred disk cleanup.
public sealed class ContractGeneratorValueDomainTests {
  // An empty target premise leaves authored generator obligations and positive native correctness coverage intact.
  [Fact]
  public async Task EmptyRequirementsRetainGeneratorProofObligations() {
    const string source = """
      module M {
        import PbtRandom
        type Positive = value: int | value > 0 witness 1
        newtype Count = value: int | value >= 0 witness 0
        method Goal(x: Positive, count: Count) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: Positive, count: Count)
          ensures x == 1 && count == 0
        { x := 1; count := 0; }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);
    var (build, program) = await ContractGeneratorProofTests.DirectProof(fixture);
    var generator = ContractGeneratorProofTests.Method(program, "Generate");

    Assert.Single(generator.Ens);
    Assert.Equal("x == 1 && count == 0", Printer.ExprToString(fixture.Options, generator.Ens[0].E));
    var scopes = ContractGeneratorProof.ProofScopes(program, build.Sources,
      ContractGeneratorProofTests.Method(program, "Goal"), generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource());
    var requiredChecks = scopes.SelectMany(scope => scope.RequiredNativeChecks).ToHashSet(StringComparer.Ordinal);
    Assert.Contains("M.Positive (well-formedness)", requiredChecks);
    Assert.Contains("M.Count (well-formedness)", requiredChecks);
    Assert.Contains("M.Generate (correctness)", requiredChecks);
  }

  // Finite collections recursively preserve supported nested value types in strengthened postconditions.
  [Fact]
  public async Task FiniteCollectionsSupportNestedValues() {
    const string source = """
      module M {
        import PbtRandom
        datatype Box<T> = Box(value: T)
        method Goal(xs: set<seq<int>>, bags: multiset<Box<seq<char>>>, table: map<seq<int>, set<Box<int>>>)
          requires xs == {}
          requires bags == multiset{}
          requires table == map[]
        {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
            returns (xs: set<seq<int>>, bags: multiset<Box<seq<char>>>, table: map<seq<int>, set<Box<int>>>) {
          xs := {};
          bags := multiset{};
          table := map[];
        }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.All(fixture.Goal.Ins, formal =>
      Assert.True(ContractGeneratorProof.SupportedValueType(formal.Type, new HashSet<string>())));
    var (_, program) = await ContractGeneratorProofTests.DirectProof(fixture);
    Assert.Equal(3, ContractGeneratorProofTests.Method(program, "Generate").Ens.Count);
  }

  // Direct and pure-function value projections retain their resolved datatype, tuple and finite-map identities.
  [Fact]
  public async Task ImmutableValueProjectionsSupportStrengthening() {
    const string source = """
      module M {
        import PbtRandom
        datatype Record = Record(value: int)
        predicate More(tuple: (int, bool), table: map<int, int>) {
          tuple.0 >= 0 && tuple.1 && table.Values == table.Values && table.Items == table.Items
        }
        method Goal(record: Record, tuple: (int, bool), table: map<int, int>)
          requires record.Record? && record.value >= 0 && table.Keys == table.Keys
          requires More(tuple, table)
        {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source)
            returns (record: Record, tuple: (int, bool), table: map<int, int>) {
          record := Record(0);
          tuple := (0, true);
          table := map[];
        }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);
    var (_, program) = await ContractGeneratorProofTests.DirectProof(fixture);
    var generator = ContractGeneratorProofTests.Method(program, "Generate");
    var directMembers = generator.Ens.SelectMany(ensure => ensure.E.DescendantsAndSelf)
      .OfType<MemberSelectExpr>().Select(select => select.Member).ToList();
    var predicate = Assert.Single(program.Descendants().OfType<Function>().Where(function => function.Name == "More"));
    var transitiveMembers = predicate.Body!.DescendantsAndSelf.OfType<MemberSelectExpr>()
      .Select(select => select.Member).ToList();

    Assert.Contains(directMembers, member => member is DatatypeDiscriminator);
    Assert.Contains(directMembers, member => member is DatatypeDestructor);
    Assert.Contains(directMembers, member => member is SpecialField { SpecialId: SpecialField.ID.Keys });
    Assert.Contains(transitiveMembers, member => member is DatatypeDestructor);
    Assert.Contains(transitiveMembers, member => member is SpecialField { SpecialId: SpecialField.ID.Values });
    Assert.Contains(transitiveMembers, member => member is SpecialField { SpecialId: SpecialField.ID.Items });
  }

  // A finite-map subset keeps its refinement well-formedness check while exposing immutable map projections.
  [Fact]
  public async Task FiniteMapSubsetSupportsValueProjections() {
    const string source = """
      module M {
        import PbtRandom
        type SmallMap = table: map<int, int> | |table| <= 2 witness map[]
        method Goal(table: SmallMap)
          requires table.Keys == table.Keys && table.Values == table.Values && table.Items == table.Items
        {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (table: SmallMap) {
          table := map[];
        }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);
    var (build, program) = await ContractGeneratorProofTests.DirectProof(fixture);
    var generator = ContractGeneratorProofTests.Method(program, "Generate");
    var projectionIds = Assert.Single(generator.Ens).E.DescendantsAndSelf.OfType<MemberSelectExpr>()
      .Select(select => select.Member).OfType<SpecialField>().Select(field => field.SpecialId).ToHashSet();
    var scopes = ContractGeneratorProof.ProofScopes(program, build.Sources,
      ContractGeneratorProofTests.Method(program, "Goal"), generator,
      ContractGeneratorProof.ExtractPinnedPbtRandomSource());

    Assert.Contains(SpecialField.ID.Keys, projectionIds);
    Assert.Contains(SpecialField.ID.Values, projectionIds);
    Assert.Contains(SpecialField.ID.Items, projectionIds);
    Assert.Contains("M.SmallMap (well-formedness)", scopes.SelectMany(scope => scope.RequiredNativeChecks));
  }

  // A reference nested beneath otherwise finite value containers remains outside the proof input domain.
  [Fact]
  public async Task NestedReferencesRemainUnsupported() {
    const string source = """
      module M {
        import PbtRandom
        class Cell { var value: int }
        datatype Box = Box(cell: Cell)
        method Goal(values: set<Box>) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (values: set<Box>) {}
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportedSelectedGoal(fixture.Program, fixture.Goal, fixture.Generator,
      out var failure));
    Assert.Contains("outside the supported", failure, StringComparison.Ordinal);
  }

  // Projecting a reference from a static immutable datatype still falls outside the value-only requirement scope.
  [Fact]
  public async Task DatatypeProjectionCannotHideAReference() {
    const string source = """
      module M {
        import PbtRandom
        class Cell { var value: int }
        datatype Box = Box(cell: Cell?)
        class Constants { static const boxed: Box := Box(null) }
        method Goal(x: int) requires Constants.boxed.cell == null {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportsRequiredPostconditions(fixture.Program, fixture.Goal,
      fixture.Generator, out var failure));
    Assert.Contains("mutable heap fields", failure, StringComparison.Ordinal);
  }

  // A finite map projection cannot hide a reference-valued range behind a static immutable constant.
  [Fact]
  public async Task MapProjectionCannotHideAReference() {
    const string source = """
      module M {
        import PbtRandom
        class Cell { var value: int }
        class Constants { static const cells: map<int, Cell?> := map[] }
        method Goal(x: int) requires Constants.cells.Keys == {} {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportsRequiredPostconditions(fixture.Program, fixture.Goal,
      fixture.Generator, out var failure));
    Assert.Contains("mutable heap fields", failure, StringComparison.Ordinal);
  }

  // Infinite set and map inputs remain outside the finite runtime value domain.
  [Theory]
  [InlineData("iset<int>")]
  [InlineData("imap<int, int>")]
  public async Task InfiniteCollectionsRemainUnsupported(string type) {
    var source = $$"""
      module M {
        import PbtRandom
        method Goal(value: {{type}}) {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (value: {{type}}) {}
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportedSelectedGoal(fixture.Program, fixture.Goal, fixture.Generator,
      out var failure));
    Assert.Contains("outside the supported", failure, StringComparison.Ordinal);
  }

  // A direct mutable-field read remains rejected even when the selected input itself is scalar.
  [Fact]
  public async Task DirectHeapReadRemainsUnsupported() {
    const string source = """
      module M {
        import PbtRandom
        class Cell { var value: int }
        const cell: Cell?
        method Goal(x: int) requires cell == null || cell.value >= 0 {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportsRequiredPostconditions(fixture.Program, fixture.Goal,
      fixture.Generator, out var failure));
    Assert.Contains("mutable heap fields", failure, StringComparison.Ordinal);
  }

  // A mutable-field read reached through a requirement function remains rejected as transitive heap state.
  [Fact]
  public async Task TransitiveHeapReadRemainsUnsupported() {
    const string source = """
      module M {
        import PbtRandom
        class Cell { var value: int }
        const cell: Cell?
        function Read(): int reads cell { if cell == null then 0 else cell.value }
        method Goal(x: int) requires Read() >= 0 {}
        method {:pbt_generator "M.Goal"} Generate(r: PbtRandom.Source) returns (x: int) { x := 0; }
      }
      """;
    var fixture = await ContractGeneratorProofTests.Prepare(source);

    Assert.False(ContractGeneratorProof.SupportsRequiredPostconditions(fixture.Program, fixture.Goal,
      fixture.Generator, out var failure));
    Assert.Contains("requirement functions", failure, StringComparison.Ordinal);
  }

  // Valid helper coverage cannot replace the required positive generator correctness implementation result.
  [Fact]
  public void MissingGeneratorImplementationCoverageRemainsIncomplete() {
    const string generatorCheck = "M.Generate (correctness)";
    const string helperCheck = "M.Helper (well-formedness)";
    var required = new HashSet<string>([generatorCheck, helperCheck], StringComparer.Ordinal);
    var helperPart = new ContractGeneratorVerificationPart(helperCheck, 0);
    var coverage = ContractGeneratorVerification.Account(required, [helperPart],
      new Dictionary<ContractGeneratorVerificationPart, SolverOutcome> { [helperPart] = SolverOutcome.Valid },
      generatorCheck);

    Assert.False(coverage.Complete);
    Assert.False(ContractGeneratorProof.AcceptCoverage(coverage));
  }
}
