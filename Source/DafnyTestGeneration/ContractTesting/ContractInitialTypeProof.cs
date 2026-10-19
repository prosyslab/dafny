#nullable enable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Owns one original initial-state preparation and its exact source verification scope.</summary>
public sealed class ContractInitialTypePreparation {
  public ContractRuntimeHeapCheck Initial { get; }
  public ContractSpecificationScope Scope { get; }
  internal ContractSpecificationChecker Specifications { get; }

  internal ContractInitialTypePreparation(ContractRuntimeHeapCheck initial, ContractSpecificationScope scope,
    ContractSpecificationChecker specifications) {
    Initial = initial;
    Scope = scope;
    Specifications = specifications;
  }

  internal bool Matches(ContractSpecificationChecker specifications) =>
    ReferenceEquals(Specifications, specifications) && Initial.IsOriginalInitial &&
    specifications.IsBoundTo(Initial.Prepared.Program, Initial.Request.Sources, Initial.TrustedSources);
}

/// <summary>A source-bound plan for proving exact heap carriers by native construction or compiled membership.</summary>
public sealed class ContractInitialTypeProof {
  public ContractRuntimeHeapCheck Initial { get; }
  public IReadOnlyList<string> RuntimeChecks { get; }
  public bool RequiresNativeProof => Values.Count != 0;
  public bool Observed { get; }
  public int HostMembershipChecks { get; }
  public ContractGlobalInhabitationCertificate? IndependentGlobals { get; }
  internal IReadOnlyList<(ContractValue Value, Type Type)> Values { get; }

  private ContractInitialTypeProof(ContractRuntimeHeapCheck initial, IReadOnlyList<(ContractValue Value, Type Type)> values,
    IReadOnlyList<string> runtimeChecks, int hostMembershipChecks,
    ContractGlobalInhabitationCertificate? independentGlobals, bool observed = false) {
    Initial = initial;
    Values = values;
    RuntimeChecks = runtimeChecks;
    Observed = observed;
    HostMembershipChecks = hostMembershipChecks;
    IndependentGlobals = independentGlobals;
  }

  /// <summary>Collects all original type and function WD obligations for heap fields, root inputs and the receiver.</summary>
  public static ContractSpecificationScope RequiredScope(Program program, ContractRuntimeCampaignRequest campaign,
    IReadOnlyList<ContractHeapObject> heap, ContractSpecificationChecker specifications) {
    var method = ContractCallableSelector.SelectMethod(program, campaign.Entry, requireConcreteReceiver: false, allowLemmaContract: true);
    return RequiredScope(program, method, heap, specifications);
  }

  private static ContractSpecificationScope RequiredScope(Program program, Method method,
    IReadOnlyList<ContractHeapObject> heap, ContractSpecificationChecker specifications) {
    var types = ContractRuntimeHeapChecking.InitialTypes(program, heap).Concat(method.Ins.Select(formal => formal.Type));
    if (!method.IsStatic) { types = types.Append(UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)); }
    var scope = ConstructionScope(program, types, specifications);
    return method is Lemma && scope.ContainsDeclaration(method)
      ? specifications.UnsupportedScope("target_lemma_dependency") : scope;
  }

  /// <summary>Binds an attested initial preparation to its exact scope without repeating source preparation.</summary>
  public static ContractInitialTypePreparation Prepare(ContractRuntimeHeapCheck initial, ContractSpecificationChecker specifications) {
    if (!initial.IsOriginalInitial || !specifications.IsBoundTo(initial.Prepared.Program, initial.Request.Sources,
          initial.TrustedSources)) {
      throw new System.ArgumentException("Initial preparation is not bound to this original request and specification checker.", nameof(initial));
    }
    return new(initial, RequiredScope(initial.Prepared.Program, initial.Prepared.Method, initial.Request.Heap ?? [], specifications), specifications);
  }

  /// <summary>Plans one bound state after its owned original scope is certified, retaining all exact membership checks.</summary>
  public static ContractInitialTypeProof? TryPrepare(ContractInitialTypePreparation preparation,
    ContractSpecificationChecker specifications, ContractRuntimeTypeEvidence? runtimeEvidence = null) {
    if (!preparation.Matches(specifications) || !specifications.Accept(preparation.Scope)) { return null; }
    return Plan(preparation.Initial, specifications, runtimeEvidence);
  }

  /// <summary>Collects original WD obligations for final heap fields and every declared entry output.</summary>
  public static ContractSpecificationScope RequiredObservedScope(Program program, ContractRuntimeHeapCheck check,
    ContractSpecificationChecker specifications) => ConstructionScope(program,
    ContractRuntimeHeapChecking.InitialTypes(program, check.FinalHeap ?? [])
      .Concat(check.Prepared.Method.Outs.Select(formal => formal.Type)), specifications);

  private static ContractSpecificationScope ConstructionScope(Program program, IEnumerable<Type> types,
    ContractSpecificationChecker specifications) {
    var unsupported = ContractRuntimeHeapChecking.DatatypeMemberConstants(program);
    if (unsupported.Count != 0) {
      return specifications.UnsupportedScope("Unsupported global datatype member constants: " +
        string.Join(", ", unsupported.Select(field => field.FullDafnyName)));
    }
    var globals = ContractRuntimeHeapChecking.StaticConstants(program);
    // Native static constants impose unconditional type/allocation axioms, even
    // without a reference in the tested clause. Defined constants also impose RHS equations.
    return specifications.Scope([], types.Concat(globals.Select(field => field.Type)), globals.Where(field => field.Rhs != null));
  }

  internal static ContractSpecificationScope RequiredGlobalScope(Program program, ContractSpecificationChecker specifications) =>
    ConstructionScope(program, [], specifications);

  /// <summary>Plans final carriers; the caller must also establish a constructive initial state and original P.</summary>
  public static ContractInitialTypeProof? TryPrepareObserved(Program program, ContractRuntimeHeapCheck check,
    ContractSpecificationChecker specifications, ContractRuntimeTypeEvidence? runtimeEvidence = null) {
    if (!specifications.IsBoundTo(program, check.Request.Sources, check.TrustedSources) ||
        check.FinalHeap == null || check.FrameViolation != null ||
        !specifications.Accept(RequiredObservedScope(program, check, specifications)) ||
        HasUnsupportedCarrierShape(check.Prepared)) { return null; }
    var outputs = check.Prepared.Method.Outs.Select(formal => (check.Outputs[formal.Name], formal.Type)).ToList();
    return PlanCarriers(program, check, check.FinalHeap, outputs, specifications, runtimeEvidence, observed: true);
  }

  /// <summary>Plans only states whose remaining requirements compose from checked references, inhabited omissions and pure carriers.</summary>
  public static ContractInitialTypeProof? TryPrepare(Program program, ContractRuntimeCampaignRequest campaign,
    IReadOnlyDictionary<string, ContractValue> inputs, IReadOnlyList<ContractHeapObject> heap,
    ContractSpecificationChecker specifications, ContractRuntimeTypeEvidence? runtimeEvidence = null) {
    if (!specifications.IsBoundTo(program, campaign.Sources, campaign.TrustedSources) ||
        !specifications.Accept(RequiredScope(program, campaign, heap, specifications))) { return null; }
    var initial = ContractRuntimeHeapChecking.PrepareInitial(program, campaign, inputs, heap, specifications);
    return Plan(initial, specifications, runtimeEvidence);
  }

  private static ContractInitialTypeProof? Plan(ContractRuntimeHeapCheck initial, ContractSpecificationChecker specifications,
    ContractRuntimeTypeEvidence? runtimeEvidence) {
    if (HasUnsupportedCarrierShape(initial.Prepared)) { return null; }
    var method = initial.Prepared.Method;
    var rootInputs = method.Ins.Select(formal => (initial.Request.Inputs[formal.Name], formal.Type)).ToList();
    if (!method.IsStatic) {
      if (initial.Request.Entry.Receiver is not { Kind: ContractValueKind.Reference } receiver) { return null; }
      rootInputs.Add((receiver, UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)));
    }
    return PlanCarriers(initial.Prepared.Program, initial, initial.Request.Heap ?? [], rootInputs, specifications,
      runtimeEvidence, observed: false);
  }

  // Generic entries and defined readonly heap fields need obligations this carrier plan does not model.
  private static bool HasUnsupportedCarrierShape(ContractPreparedProgram prepared) =>
    prepared.Method.TypeArgs.Count != 0 || prepared.Method.EnclosingClass.TypeArgs.Count != 0 ||
    prepared.Heap?.Slots.Any(slot => slot.Fields.Concat(slot.OmittedGhostFields)
      .OfType<ConstantField>().Any(field => field.Rhs != null)) == true;

  // Every pure carrier is covered by a matching compiled check or left for one native construction proof.
  private static ContractInitialTypeProof? PlanCarriers(Program program, ContractRuntimeHeapCheck check,
    IReadOnlyList<ContractHeapObject> heap, IReadOnlyList<(ContractValue Value, Type Type)> roots,
    ContractSpecificationChecker specifications, ContractRuntimeTypeEvidence? runtimeEvidence, bool observed) {
    if (runtimeEvidence?.IsBoundTo(program, check.Request.Sources) != true) { runtimeEvidence = null; }
    var values = new List<(ContractValue Value, Type Type)>();
    var runtimeChecks = new HashSet<string>();
    var hostChecks = 0;
    var covered = ContractRuntimeHeapChecking.PlanInitialTypes(program, heap, specifications, roots, Plan, () => hostChecks++);
    var globals = specifications.IndependentGlobals(program, check.Request.Sources);
    if (globals == null && !ContractRuntimeHeapChecking.AbstractGlobalsInhabited(program, heap, specifications)) { return null; }
    return covered == true
      ? new(check, values, runtimeChecks.OrderBy(id => id, System.StringComparer.Ordinal).ToList(), hostChecks, globals, observed)
      : null;

    bool Plan(ContractValue value, Type type) {
      if (!IsPure(type, [])) { return false; }
      if (runtimeEvidence?.Match(value, type) is { } runtimeCheck) {
        runtimeChecks.Add(runtimeCheck);
      } else {
        values.Add((value, type));
      }
      return true;
    }
  }

  /// <summary>Builds a zero-input query whose native assignment checks establish every candidate carrier.</summary>
  public string BuildQuery() => ContractQueryBuilder.BuildInitialTypeProof(Initial.Prepared, Values);

  internal static bool IsPure(Type type, HashSet<TopLevelDecl> active) {
    type = type.NormalizeExpandKeepConstraints();
    if (type.IsRefType || type.IsArrowType || type is TypeProxy ||
        type.TypeArgs.Any(argument => !IsPure(argument, new HashSet<TopLevelDecl>(active)))) { return false; }
    if (type is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } appliedSubset) {
      return active.Add(subset) && IsPure(subset.RhsWithArgument(appliedSubset.TypeArgs), active);
    }
    if (type is UserDefinedType { ResolvedClass: NewtypeDecl newtype } appliedNewtype) {
      return active.Add(newtype) && IsPure(newtype.ConcreteBaseType(appliedNewtype.TypeArgs), active);
    }
    if (type is CollectionType or MapType || type.IsBoolType || type.IsCharType || type.IsIntegerType ||
        type.IsRealType || type.IsBitVectorType) { return true; }
    if (type is not UserDefinedType { ResolvedClass: IndDatatypeDecl datatype } applied) { return false; }
    if (datatype.Members.OfType<ConstantField>().Any()) { return false; }
    if (!active.Add(datatype)) { return true; }
    var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, applied.TypeArgs);
    return datatype.Ctors.All(constructor => !constructor.IsGhost && constructor.Formals.All(formal =>
      !formal.IsGhost && IsPure(formal.Type.Subst(substitution), new HashSet<TopLevelDecl>(active))));
  }
}
