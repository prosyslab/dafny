#nullable enable

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text.Json;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Original-source query inputs and validated observations for a completed heap sample.</summary>
public sealed record ContractRuntimeHeapCheck(ContractPreparedProgram Prepared, ContractTestRequest Request,
  IReadOnlyDictionary<string, ContractValue> Outputs, IReadOnlyDictionary<string, ContractValue> Observations,
  IReadOnlyDictionary<string, ContractValue> Evidence, string? FrameViolation,
  IReadOnlyList<string>? InitialTypeConstraints = null, IReadOnlyList<ContractHeapObject>? FinalHeap = null) {
  internal ContractPreparedProgram? OriginalInitialPreparation { get; init; }
  internal string? OriginalInitialRequestHash { get; init; }
  internal IReadOnlyList<ContractDependency>? TrustedSources { get; init; }
  internal string RequestHash() => ContractHarnessBuilder.Hash(JsonSerializer.Serialize(new { Request, TrustedSources }, ContractJson.Options));
  internal bool IsOriginalInitial => ReferenceEquals(Prepared, OriginalInitialPreparation) && OriginalInitialRequestHash == RequestHash();
}

/// <summary>Validates captured runtime heaps before they can become fixed-state contract queries.</summary>
public static class ContractRuntimeHeapChecking {
  /// <summary>Matches one returned invocation in an ordered prefix, rejecting malformed or crossed call boundaries.</summary>
  public static (JsonElement Entry, JsonElement Return)? MatchCallCaptures(IReadOnlyList<JsonElement> prefix,
    string scope, int invocation) {
    var active = new Stack<(string Scope, int Invocation)>();
    var seen = new HashSet<int>();
    JsonElement entry = default;
    JsonElement returned = default;
    foreach (var record in prefix) {
      if (Text(record, "kind") != "heap_capture") { continue; }
      var phase = Text(record, "phase");
      if (phase is not ("call_entry" or "call_return")) { continue; }
      var actualScope = Text(record, "scope");
      if (actualScope == null || !record.TryGetProperty("invocation", out var encoded) ||
          encoded.ValueKind != JsonValueKind.Number || !encoded.TryGetInt32(out var actualInvocation) || actualInvocation <= 0 ||
          !record.TryGetProperty("heap", out var heap) || heap.ValueKind != JsonValueKind.Array ||
          !record.TryGetProperty(phase == "call_entry" ? "inputs" : "outputs", out var values) || values.ValueKind != JsonValueKind.Object) {
        return null;
      }
      if (phase == "call_entry") {
        if (!seen.Add(actualInvocation)) { return null; }
        active.Push((actualScope, actualInvocation));
        if (actualInvocation == invocation) {
          if (actualScope != scope) { return null; }
          entry = record;
        }
      } else {
        if (!active.TryPop(out var opened) || opened != (actualScope, actualInvocation)) { return null; }
        if (actualInvocation == invocation) {
          if (actualScope != scope) { return null; }
          returned = record;
        }
      }
    }
    return entry.ValueKind != JsonValueKind.Undefined && returned.ValueKind != JsonValueKind.Undefined
      ? (entry, returned) : null;

    static string? Text(JsonElement value, string property) => value.ValueKind == JsonValueKind.Object &&
      value.TryGetProperty(property, out var field) && field.ValueKind == JsonValueKind.String ? field.GetString() : null;
  }

  internal static IReadOnlyList<ConstantField> StaticConstants(Program program) =>
    ContractRuntimeObligationTransformer.Members(program).OfType<ConstantField>()
      .Where(field => field.IsStatic && field.EnclosingClass.EnclosingModuleDefinition != program.SystemModuleManager.SystemModule).ToList();

  internal static IReadOnlyList<ConstantField> DatatypeMemberConstants(Program program) =>
    ContractRuntimeObligationTransformer.Members(program).OfType<ConstantField>()
      .Where(field => field.EnclosingClass is DatatypeDecl &&
        field.EnclosingClass.EnclosingModuleDefinition != program.SystemModuleManager.SystemModule).ToList();

  // Runtime captures name a class by its Dafny or compiled full name.
  private static ClassDecl? CapturedClass(IReadOnlyList<ClassDecl> classes, ContractHeapObject item) =>
    classes.SingleOrDefault(candidate => candidate.FullDafnyName == item.Type || candidate.FullName == item.Type);

  private static ClassDecl RequireCapturedClass(IReadOnlyList<ClassDecl> classes, ContractHeapObject item) =>
    CapturedClass(classes, item) ?? throw new NotSupportedException("Unknown captured class: " + item.Type);

  private static bool IndependentGlobalInhabitants(Program program) => StaticConstants(program).All(field =>
    field.Rhs == null && HasStructuralInhabitant(program, field.Type, [], [], null, freshReferences: true));

  // These witnesses are conditional on the complete captured-heap construction.
  // Its native proofs exclude abstract-global axioms, preventing circular admission.
  internal static bool AbstractGlobalsInhabited(Program program, IReadOnlyList<ContractHeapObject> heap,
    ContractSpecificationChecker specifications) => GlobalsInhabited(program, heap, specifications, independent: false);

  internal static bool IndependentCertifiedGlobalsInhabited(Program program, ContractSpecificationChecker specifications) =>
    GlobalsInhabited(program, [], specifications, independent: true);

  private static bool GlobalsInhabited(Program program, IReadOnlyList<ContractHeapObject> heap,
    ContractSpecificationChecker specifications, bool independent) {
    var classes = ContractHeapFactory.ClassDeclarations(program);
    var arrays = ContractHeapFactory.ResolvedArrayTypes(program);
    var witnesses = new List<Microsoft.Dafny.Type>();
    foreach (var item in heap) {
      if (item.Elements != null || item.Dimensions != null) {
        if (arrays.TryGetValue(item.Type, out var array) && array.NormalizeExpand() is UserDefinedType reference) {
          witnesses.Add(UserDefinedType.CreateNonNullTypeIfReferenceType(reference));
        }
      } else {
        var declaration = CapturedClass(classes, item);
        if (declaration != null && declaration.TypeArgs.Count == 0) {
          witnesses.Add(UserDefinedType.CreateNonNullType(UserDefinedType.FromTopLevelDecl(declaration.Origin, declaration)));
        }
      }
    }
    // Only bodyless globals may use independently certified leaf witnesses. Their
    // axioms were removed from every native certificate proof. Defined globals
    // retain the closed structural gate, preventing their own RHS/type axioms from
    // making the native witness proof vacuous.
    return StaticConstants(program).All(field =>
      HasStructuralInhabitant(program, field.Type, witnesses, [],
        independent && field.Rhs == null ? specifications : null, freshReferences: independent) &&
      (field.Rhs == null || ClosedConstantValue(field.Rhs, field.Type, [])));

    bool ClosedConstantValue(Expression expression, Microsoft.Dafny.Type expected, HashSet<ConstantField> active) {
      expression = expression.Resolved;
      expected = expected.NormalizeExpandKeepConstraints();
      if (expression is MemberSelectExpr { Member: ConstantField { IsStatic: true, Rhs: { } rhs } field }) {
        return active.Add(field) && field.Type.Equals(expected, keepConstraints: true) &&
          ClosedConstantValue(rhs, expected, active);
      }
      if (expected is UserDefinedType { ResolvedClass: SubsetTypeDecl subset }) {
        return subset == program.SystemModuleManager.NatDecl &&
          ContractExpressionReducer.TryFoldTotalIntegerArithmetic(expression, out var integer) && integer >= 0;
      }
      if (expected is UserDefinedType { ResolvedClass: NewtypeDecl }) { return false; }
      if (expected.IsIntegerType &&
          ContractExpressionReducer.TryFoldTotalIntegerArithmetic(expression, out _)) {
        return true;
      }
      if (expression is ConversionExpr conversion && conversion.E.Resolved is LiteralExpr { Value: BigInteger integerValue }) {
        return expected.IsBitVectorType && conversion.ToType.Equals(expected, keepConstraints: true) &&
          integerValue >= 0 && integerValue < (BigInteger.One << expected.AsBitVectorType.Width);
      }
      if (expression is LiteralExpr literal) {
        return literal.Value switch {
          BigInteger integer => expected.IsIntegerType || expected.IsRealType ||
            expected.IsBitVectorType && integer >= 0 && integer < (BigInteger.One << expected.AsBitVectorType.Width),
          bool => expected.IsBoolType,
          null => expected.IsRefType,
          _ => false
        };
      }
      if (expression is DatatypeValue { Ctor: { } constructor } value &&
          expected is UserDefinedType { ResolvedClass: IndDatatypeDecl datatype } applied &&
          constructor.EnclosingDatatype == datatype && constructor.Formals.Count == value.Arguments.Count) {
        var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, applied.TypeArgs);
        return constructor.Formals.Select((formal, index) => ClosedConstantValue(value.Arguments[index],
          formal.Type.Subst(substitution), new HashSet<ConstantField>(active))).All(valid => valid);
      }
      if (expression is DisplayExpression display && expected.AsCollectionType is { } collection &&
          expression.Type.NormalizeExpand().GetType() == expected.NormalizeExpand().GetType()) {
        return display.Elements.All(item => ClosedConstantValue(item, collection.Arg, new HashSet<ConstantField>(active)));
      }
      if (expression is MapDisplayExpr map && expected.AsMapType is { } mapType && map.Finite == mapType.Finite) {
        return map.Elements.All(item => ClosedConstantValue(item.A, mapType.Domain, new HashSet<ConstantField>(active)) &&
          ClosedConstantValue(item.B, mapType.Range, new HashSet<ConstantField>(active)));
      }
      return false;
    }
  }

  /// <summary>Checks concrete field types, returning null only for constraints requiring an original-source query.</summary>
  public static bool? CheckInitialTypes(Program originalProgram, IReadOnlyList<ContractHeapObject> initial,
    ContractSpecificationChecker? specifications = null) {
    var result = CheckInitialTypesCore(originalProgram, initial, specifications, [], null);
    // Primitive heap carriers alone do not establish consistency of unconditional
    // global type/allocation/equality axioms. Route those states through the full
    // construction certificate (or original SAT fallback), including empty heaps.
    return result == true && (DatatypeMemberConstants(originalProgram).Count != 0 ||
      !IndependentGlobalInhabitants(originalProgram)) ? null : result;
  }

  internal static bool? PlanInitialTypes(Program originalProgram, IReadOnlyList<ContractHeapObject> initial,
    ContractSpecificationChecker specifications, IReadOnlyList<(ContractValue Value, Microsoft.Dafny.Type Type)> inputs,
    Func<ContractValue, Microsoft.Dafny.Type, bool> planValue, System.Action? hostCheck = null) =>
    CheckInitialTypesCore(originalProgram, initial, specifications, inputs, planValue, hostCheck);

  /// <summary>Checks concrete pure inputs without inventing a runtime campaign or an initial-heap attestation.</summary>
  internal static bool? CheckPureInputs(Program program,
    IReadOnlyList<(ContractValue Value, Microsoft.Dafny.Type Type)> inputs) =>
    CheckInitialTypesCore(program, [], null, inputs, null);

  private static bool? CheckInitialTypesCore(Program originalProgram, IReadOnlyList<ContractHeapObject> initial,
    ContractSpecificationChecker? specifications, IReadOnlyList<(ContractValue Value, Microsoft.Dafny.Type Type)> inputs,
    Func<ContractValue, Microsoft.Dafny.Type, bool>? planValue, System.Action? hostCheck = null) {
    if (initial.Count == 0 && inputs.Count == 0) { return true; }
    var objects = ObjectsById(initial);
    var classes = ContractHeapFactory.ClassDeclarations(originalProgram);
    var arrays = ContractHeapFactory.ResolvedArrayTypes(originalProgram);
    var witnesses = CapturedTypeWitnesses(originalProgram, initial);
    var result = (bool?)true;
    foreach (var item in initial) {
      if (item.Elements != null || item.Dimensions != null) {
        if (item.Dimensions is not { Count: 1 } || item.Elements == null ||
            item.Dimensions[0] != item.Elements.Count || item.Fields.Count != 0 ||
            !arrays.TryGetValue(item.Type, out var arrayType)) { return false; }
        foreach (var value in item.Elements) { result = And(result, Check(value, arrayType.NormalizeExpand().TypeArgs[0])); }
      } else {
        var declaration = RequireCapturedClass(classes, item);
        var (fields, omitted) = ContractHeapFactory.ValidateFields(declaration, item);
        if (fields.Concat(omitted).OfType<ConstantField>().Any(field => field.Rhs != null)) {
          // Field membership does not establish the readonly defining equations.
          // Initial admission must check RHS WD/dependencies and full consistency.
          result = And(result, null);
        }
        foreach (var field in fields) { result = And(result, Check(item.Fields[field.Name], field.Type)); }
        foreach (var field in omitted) {
          if (HasStructuralInhabitant(originalProgram, field.Type, witnesses, [], specifications)) { continue; }
          if (planValue != null) {
            // Constructive admission needs an affirmative inhabitant for every
            // omission; the legacy unknown-type query policy is not a witness.
            result = And(result, null);
            continue;
          }
          if (OmittedNeedsQuery(originalProgram, field.Type, [], specifications)) { result = And(result, null); }
        }
      }
    }
    foreach (var (value, type) in inputs) { result = And(result, Check(value, type)); }
    return result;

    static bool? And(bool? left, bool? right) => left == false || right == false ? false : left == null || right == null ? null : true;
    bool? Check(ContractValue value, Microsoft.Dafny.Type type) {
      ContractModelCodec.Validate(value);
      return CheckWithPlan(value, type, true);
    }

    bool? CheckWithPlan(ContractValue value, Microsoft.Dafny.Type type, bool allowPlan) {
      if (allowPlan && planValue != null) {
        var concrete = CheckWithPlan(value, type, false);
        if (concrete != null) { hostCheck?.Invoke(); return concrete; }
        // Only unknown exact membership needs runtime evidence or a future native
        // proof. Decisive host membership (including false) cannot be replaced.
        if (planValue(value, type)) { return true; }
      }
      type = type.NormalizeExpandKeepConstraints();
      if (type is UserDefinedType { ResolvedClass: NonNullTypeDecl nonNull } reference) {
        return value.Kind == ContractValueKind.Null ? false : CheckWithPlan(value, nonNull.RhsWithArgument(reference.TypeArgs), allowPlan);
      }
      if (type is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } refined) {
        CheckConstraintDependencies(originalProgram, subset.Constraint, specifications);
        var baseResult = CheckWithPlan(value, subset.RhsWithArgument(refined.TypeArgs), allowPlan);
        return And(baseResult, subset == originalProgram.SystemModuleManager.NatDecl
          ? value.Kind == ContractValueKind.Integer && BigInteger.Parse(value.Value!, CultureInfo.InvariantCulture) >= 0
          : null);
      }
      if (type is UserDefinedType { ResolvedClass: NewtypeDecl newtype } refinedNewtype) {
        if (newtype.Constraint != null) { CheckConstraintDependencies(originalProgram, newtype.Constraint, specifications); }
        return And(CheckWithPlan(value, newtype.ConcreteBaseType(refinedNewtype.TypeArgs), allowPlan), newtype.Var == null ? true : null);
      }
      if (!ContractHeapFactory.ValueMatchesType(value, type)) { return false; }
      if (type.IsRefType) {
        if (value.Kind == ContractValueKind.Null) { return true; }
        if (!objects.TryGetValue(value.Value!, out var target)) { return false; }
        // Every captured object, including an array, inhabits the built-in object trait.
        if (type.IsObjectQ) { return true; }
        if (type.IsArrayType) { return target.Type == ContractHeapFactory.ArrayTypeName(type); }
        // Concrete observations originate from compiled typed fields; reject mismatched declared classes.
        var expected = (type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
        return expected is ClassDecl actual && (target.Type == actual.FullDafnyName || target.Type == actual.FullName)
          ? true : expected is ClassDecl ? false : null;
      }
      if (type is UserDefinedType { ResolvedClass: DatatypeDecl datatype } instantiated) {
        if (datatype.Members.OfType<ConstantField>().Any()) { return null; }
        var constructor = datatype.Ctors.SingleOrDefault(candidate => ContractHeapFactory.NamesConstructor(value.Constructor, datatype, candidate));
        if (constructor == null || value.Fields == null ||
            !constructor.Formals.Select(formal => formal.Name).ToHashSet().SetEquals(value.Fields.Keys)) { return false; }
        if (datatype is CoDatatypeDecl || constructor.IsGhost || constructor.Formals.Any(formal => formal.IsGhost)) { return null; }
        var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, instantiated.TypeArgs);
        return constructor.Formals.Aggregate((bool?)true, (valid, formal) =>
          And(valid, CheckWithPlan(value.Fields[formal.Name], formal.Type.Subst(substitution), allowPlan)));
      }
      if (type.AsMapType is { } map) {
        return value.Entries!.Aggregate((bool?)true, (valid, entry) =>
          And(valid, And(CheckWithPlan(entry.Key, map.Domain, allowPlan), CheckWithPlan(entry.Value, map.Range, allowPlan))));
      }
      if (type.AsCollectionType is { } collection) {
        return value.Items!.Aggregate((bool?)true, (valid, item) => And(valid, CheckWithPlan(item, collection.Arg, allowPlan)));
      }
      return true;
    }
  }

  /// <summary>Returns the declared types whose constraints govern every captured or omitted initial field.</summary>
  public static IReadOnlyList<Microsoft.Dafny.Type> InitialTypes(Program program, IReadOnlyList<ContractHeapObject> initial) {
    var classes = ContractHeapFactory.ClassDeclarations(program);
    var arrays = ContractHeapFactory.ResolvedArrayTypes(program);
    var result = new List<Microsoft.Dafny.Type>();
    foreach (var item in initial) {
      if (item.Elements != null || item.Dimensions != null) {
        if (arrays.TryGetValue(item.Type, out var array)) { result.Add(array); }
      } else {
        var declaration = RequireCapturedClass(classes, item);
        var (fields, omitted) = ContractHeapFactory.ValidateFields(declaration, item);
        result.AddRange(fields.Concat(omitted).Select(field => field.Type));
      }
    }
    return result;
  }

  private static void CheckConstraintDependencies(Program originalProgram, Expression constraint, ContractSpecificationChecker? specifications) {
    var roots = ContractRuntimeObligationTransformer.FunctionReferences(constraint).ToList();
    if (roots.Count == 0) { return; }
    var unvalidated = ContractRuntimeObligationTransformer.ExecutionReachable(originalProgram, roots).OfType<Function>()
      .Where(function => (function.Req.Count > 0 || function.Ens.Count > 0 || function.ByMethodBody != null) &&
        specifications?.IsValidated(function) != true)
      .OrderBy(function => function.FullDafnyName, StringComparer.Ordinal).ToList();
    if (unvalidated.Count > 0) {
      throw new NotSupportedException("Initial heap type constraint has an unvalidated specification callee: " +
        string.Join(", ", unvalidated.Select(function => function.FullDafnyName +
          " (requires=" + function.Req.Count + ", ensures=" + function.Ens.Count +
          ", byMethod=" + (function.ByMethodBody != null) + ")")) + ".");
    }
  }

  // These are conditional witnesses, not declarations assumed inhabited: CheckInitialTypes checks every
  // corresponding captured value, and any residual constraint still requires the original initial SAT premise.
  private static IReadOnlyList<Microsoft.Dafny.Type> CapturedTypeWitnesses(Program program,
    IReadOnlyList<ContractHeapObject> initial) {
    var classes = ContractHeapFactory.ClassDeclarations(program);
    var result = new List<Microsoft.Dafny.Type>();
    foreach (var item in initial.Where(item => item.Elements == null && item.Dimensions == null)) {
      var declaration = RequireCapturedClass(classes, item);
      var (fields, _) = ContractHeapFactory.ValidateFields(declaration, item);
      result.AddRange(fields.Select(field => field.Type.NormalizeExpandKeepConstraints())
        .Where(type => type is UserDefinedType { ResolvedClass: SubsetTypeDecl or NewtypeDecl }));
    }
    return result;
  }

  private static bool HasStructuralInhabitant(Program program, Microsoft.Dafny.Type type,
    IReadOnlyList<Microsoft.Dafny.Type> witnesses, HashSet<TopLevelDecl> active, ContractSpecificationChecker? specifications,
    bool freshReferences = false) {
    type = type.NormalizeExpandKeepConstraints();
    if (freshReferences && type is UserDefinedType { ResolvedClass: NonNullTypeDecl nonNull }) {
      if (nonNull.Class is not ClassDecl declaration || declaration is ArrayClassDecl ||
          declaration.TypeArgs.Count != 0 || declaration.Traits.Count != 0 || declaration.InheritedMembers.Count != 0 ||
          !active.Add(declaration)) { return false; }
      // A finite logical heap can allocate one fresh object per acyclic field
      // edge. Constructors are not axioms restricting the set of possible heaps.
      var fields = declaration.Members.OfType<Field>().Where(field => !field.IsStatic).ToList();
      return fields.All(field =>
        field is ConstantField { Rhs: not null } initialized
          ? IsOwnBodylessConstantAlias(declaration, fields, initialized)
          : HasStructuralInhabitant(program, field.Type, witnesses,
            new HashSet<TopLevelDecl>(active), specifications, freshReferences: true));
    }
    // A constant pure lambda inhabits every built-in arrow flavor if its codomain has an inhabitant.
    if (type.IsBuiltinArrowType) {
      return (!freshReferences || specifications != null) && HasStructuralInhabitant(program, type.TypeArgs.Last(),
        witnesses, active, specifications, freshReferences);
    }
    if (type is UserDefinedType { ResolvedClass: SubsetTypeDecl subset }) {
      return subset == program.SystemModuleManager.NatDecl ||
        specifications?.IsValidated(subset) == true && subset.WitnessKind != SubsetTypeDecl.WKind.OptOut ||
        witnesses.Any(witness => witness.Equals(type, keepConstraints: true));
    }
    if (type is UserDefinedType { ResolvedClass: NewtypeDecl newtype }) {
      return specifications?.IsValidated(newtype) == true && newtype.WitnessKind != SubsetTypeDecl.WKind.OptOut || witnesses.Any(witness => witness.Equals(type, keepConstraints: true));
    }
    // Non-null reference refinements were handled above; null inhabits nullable references.
    if (type.IsRefType) { return true; }
    // Empty collections exist even when their element/key/value types are empty.
    if (type is CollectionType or MapType) { return true; }
    if (type.IsBoolType || type.IsCharType || type.IsIntegerType || type.IsRealType || type.IsBitVectorType) {
      return true;
    }
    if (type is not UserDefinedType { ResolvedClass: DatatypeDecl datatype } applied ||
        datatype is CoDatatypeDecl || datatype.Members.OfType<ConstantField>().Any() || !active.Add(datatype)) { return false; }
    var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, applied.TypeArgs);
    // One constructor is enough. A cycle is unknown; another constructor can still supply a finite value.
    return datatype.Ctors.Any(constructor => constructor.Formals.All(formal =>
      HasStructuralInhabitant(program, formal.Type.Subst(substitution), witnesses, new HashSet<TopLevelDecl>(active), specifications, freshReferences)));
  }

  private static bool IsOwnBodylessConstantAlias(ClassDecl declaration, IReadOnlyCollection<Field> fields,
    ConstantField alias) {
    if (alias.IsStatic || !ReferenceEquals(alias.EnclosingClass, declaration) ||
        alias.Rhs?.Resolved is not MemberSelectExpr {
          AtLabel: null,
          Obj: var receiver,
          Member: ConstantField target
        } selection || receiver.Resolved is not ThisExpr || receiver.Resolved is ImplicitThisExprConstructorCall ||
        ReferenceEquals(alias, target) || target.IsStatic || target.Rhs != null ||
        !ReferenceEquals(target.EnclosingClass, declaration) || !fields.Contains(target)) {
      return false;
    }
    return alias.Type.Equals(selection.Type, keepConstraints: true) &&
      alias.Type.Equals(target.Type, keepConstraints: true) &&
      selection.Type.Equals(target.Type, keepConstraints: true);
  }

  private static bool OmittedNeedsQuery(Program originalProgram, Microsoft.Dafny.Type type, HashSet<TopLevelDecl> seen,
    ContractSpecificationChecker? specifications) {
    type = type.NormalizeExpandKeepConstraints();
    // Ordinary arrow restrictions have inhabitants; user refinements around them still require checking.
    if (type.IsBuiltinArrowType) {
      var constrained = type.TypeArgs.Select(argument => OmittedNeedsQuery(originalProgram, argument, seen, specifications)).ToList().Any(needsQuery => needsQuery);
      if (constrained) { throw new NotSupportedException("Omitted arrow fields with refined components require unsupported inhabitance validation."); }
      return false;
    }
    if (type is UserDefinedType { ResolvedClass: NonNullTypeDecl nonNull } reference) {
      return OmittedNeedsQuery(originalProgram, nonNull.RhsWithArgument(reference.TypeArgs), seen, specifications);
    }
    if (type is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } refined) {
      CheckConstraintDependencies(originalProgram, subset.Constraint, specifications);
      var nestedNeedsQuery = OmittedNeedsQuery(originalProgram, subset.RhsWithArgument(refined.TypeArgs), seen, specifications);
      if (nestedNeedsQuery) { throw new NotSupportedException("Omitted nested refined fields require unsupported inhabitance validation."); }
      return subset != originalProgram.SystemModuleManager.NatDecl;
    }
    if (type is UserDefinedType { ResolvedClass: NewtypeDecl newtype } refinedNewtype) {
      if (newtype.Constraint != null) { CheckConstraintDependencies(originalProgram, newtype.Constraint, specifications); }
      var nestedNeedsQuery = OmittedNeedsQuery(originalProgram, newtype.ConcreteBaseType(refinedNewtype.TypeArgs), seen, specifications);
      if (nestedNeedsQuery) { throw new NotSupportedException("Omitted nested refined fields require unsupported inhabitance validation."); }
      return newtype.Var != null;
    }
    var argumentNeedsQuery = type.TypeArgs.Select(argument => OmittedNeedsQuery(originalProgram, argument, seen, specifications)).ToList().Any(needsQuery => needsQuery);
    if (type is not UserDefinedType { ResolvedClass: { } declaration }) { return argumentNeedsQuery; }
    if (!seen.Add(declaration)) { return true; }
    var dependent = declaration switch {
      DatatypeDecl datatype => datatype.Ctors.SelectMany(constructor => constructor.Formals).Select(formal => formal.Type),
      ClassLikeDecl classLike => classLike.Members.OfType<Field>().Select(field => field.Type),
      _ => Enumerable.Empty<Microsoft.Dafny.Type>()
    };
    var dependentNeedsQuery = dependent.Select(nested => OmittedNeedsQuery(originalProgram, nested, new HashSet<TopLevelDecl>(seen), specifications)).ToList().Any(needsQuery => needsQuery);
    if (argumentNeedsQuery || dependentNeedsQuery) { throw new NotSupportedException("Omitted structured fields with refined components require unsupported inhabitance validation."); }
    return false;
  }

  /// <summary>Builds an original typed initial-state request without requiring a final heap or return values.</summary>
  public static ContractRuntimeHeapCheck PrepareInitial(Program originalProgram, ContractRuntimeCampaignRequest campaign,
    IReadOnlyDictionary<string, ContractValue> inputs, IReadOnlyList<ContractHeapObject> initial,
    ContractSpecificationChecker? specifications = null) {
    if (specifications != null && !specifications.IsBoundTo(originalProgram, campaign.Sources, campaign.TrustedSources)) {
      throw new ArgumentException("Campaign trust context is not bound to the supplied specification checker.", nameof(specifications));
    }
    var method = ContractCallableSelector.SelectMethod(originalProgram, campaign.Entry, requireConcreteReceiver: false, allowLemmaContract: true);
    var entry = CapturedEntry(method, campaign, inputs);
    var request = new ContractTestRequest(ContractJson.SchemaVersion, campaign.Sources, entry,
      SelectFormals(method.Ins, inputs, "input"), initial, campaign.Dependencies, campaign.ClosedQueryTimeoutMilliseconds);
    ContractHarnessBuilder.ValidateRequest(request);
    var prepared = ContractHarnessBuilder.PrepareInitial(originalProgram, request);
    var constraints = new List<string>();
    var edits = new List<ContractSourceEdit>();
    var index = 0;
    var prefix = ContractBodyNames.Family(originalProgram, "ContractOmittedTypeInhabited");
    var witnesses = CapturedTypeWitnesses(originalProgram, initial);
    foreach (var slot in prepared.Heap?.Slots ?? []) {
      foreach (var field in slot.OmittedGhostFields) {
        if (HasStructuralInhabitant(originalProgram, field.Type, witnesses, [], specifications)) { continue; }
        if (!OmittedNeedsQuery(originalProgram, field.Type, [], specifications)) { continue; }
        var name = prefix + index++;
        // Keep the declared type in its original class/module scope, including aliases and type arguments.
        edits.Add(new(slot.Class.Origin.Uri, slot.Class.EndToken.pos,
          "\nstatic ghost predicate " + name + "() { exists value: " + field.Type + " :: true }\n"));
        constraints.Add(slot.SourceTypeName + "." + name + "()");
      }
    }
    if (prepared.Heap != null) { prepared = prepared with { Heap = prepared.Heap.WithAdditionalSourceEdits(edits) }; }
    var result = new ContractRuntimeHeapCheck(prepared, request, new Dictionary<string, ContractValue>(), new Dictionary<string, ContractValue>(),
      new Dictionary<string, ContractValue>(), null, constraints);
    var bound = result with {
      OriginalInitialPreparation = prepared,
      TrustedSources = CopyTrustedSources(campaign.TrustedSources)
    };
    return bound with { OriginalInitialRequestHash = bound.RequestHash() };
  }

  /// <summary>Prepares an original-contract query without assuming any tested postcondition.</summary>
  public static ContractRuntimeHeapCheck Prepare(Program originalProgram, ContractRuntimeCampaignRequest campaign,
    IReadOnlyDictionary<string, ContractValue> inputs, IReadOnlyList<ContractHeapObject> initial,
    IReadOnlyList<ContractHeapObject> final, IReadOnlyDictionary<string, ContractValue> outputs) {
    if (campaign.Entry.InputMode != ContractInputMode.Unit) {
      throw new NotSupportedException("Runtime heap queries require a captured unit-mode entry.");
    }
    var method = ContractCallableSelector.SelectMethod(originalProgram, campaign.Entry, requireConcreteReceiver: false);
    var entry = CapturedEntry(method, campaign, inputs);
    var actualInputs = SelectFormals(method.Ins, inputs, "input");
    var actualOutputs = SelectFormals(method.Outs, outputs, "output");
    var request = new ContractTestRequest(ContractJson.SchemaVersion, campaign.Sources, entry, actualInputs,
      initial, campaign.Dependencies, campaign.ClosedQueryTimeoutMilliseconds);
    ContractHarnessBuilder.ValidateRequest(request);
    ContractHarnessBuilder.ValidateRequest(request with { Heap = final });
    ValidateShape(initial, final);

    var prepared = ContractHarnessBuilder.PrepareObservedHeap(originalProgram, request);
    var observations = new Dictionary<string, ContractValue>(StringComparer.Ordinal);
    Capture(initial, true, observations);
    Capture(final, false, observations);
    string? frameViolation = null;
    if (prepared.Heap is { } heap) {
      var initialError = heap.ValidateInitialObservations(observations);
      if (initialError != null) {
        throw new ArgumentException(initialError, nameof(initial));
      }
      // This validates reference identities, cell types and immutable cells before solver use.
      heap.QueryAssignments(observations);
      foreach (var formal in method.Outs) {
        heap.ValueExpression(actualOutputs[formal.Name], formal.Type);
      }
      frameViolation = heap.CheckFrame(method, actualInputs, observations, entry.Receiver);
    }
    var evidence = new Dictionary<string, ContractValue>(observations, StringComparer.Ordinal);
    foreach (var output in actualOutputs) {
      evidence.Add(output.Key, output.Value);
    }
    return new ContractRuntimeHeapCheck(prepared, request, actualOutputs, observations, evidence, frameViolation,
      FinalHeap: final) { TrustedSources = CopyTrustedSources(campaign.TrustedSources) };
  }

  private static IReadOnlyList<ContractDependency>? CopyTrustedSources(IReadOnlyList<ContractDependency>? sources) =>
    sources?.ToArray();

  private static ContractEntry CapturedEntry(Method method, ContractRuntimeCampaignRequest campaign,
    IReadOnlyDictionary<string, ContractValue> inputs) => method.IsStatic ? campaign.Entry : campaign.Entry with {
      Receiver = inputs.TryGetValue(ContractRuntimeGeneratorSignature.Names(method).Receiver!, out var receiver) ? receiver :
        throw new ArgumentException("Missing captured entry receiver.", nameof(inputs))
    };

  private static Dictionary<string, ContractValue> SelectFormals(IEnumerable<Formal> formals,
    IReadOnlyDictionary<string, ContractValue> captured, string role) {
    var values = new Dictionary<string, ContractValue>(StringComparer.Ordinal);
    foreach (var formal in formals) {
      if (!captured.TryGetValue(formal.Name, out var value)) {
        throw new ArgumentException($"Missing captured {role} '{formal.Name}'.", nameof(captured));
      }
      ContractModelCodec.Validate(value);
      values.Add(formal.Name, value);
    }
    return values;
  }

  private static void ValidateShape(IReadOnlyList<ContractHeapObject> initial,
    IReadOnlyList<ContractHeapObject> final) {
    var before = ObjectsById(initial);
    var after = ObjectsById(final);
    if (!before.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(after.Keys)) {
      throw new NotSupportedException("Runtime heap queries do not support changed allocation topology.");
    }
    foreach (var (id, item) in before) {
      var observed = after[id];
      if (item.Type != observed.Type ||
          (item.Dimensions == null) != (observed.Dimensions == null) ||
          item.Dimensions != null && !item.Dimensions.SequenceEqual(observed.Dimensions!) ||
          (item.Elements == null) != (observed.Elements == null) ||
          item.Elements?.Count != observed.Elements?.Count ||
          !item.Fields.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(observed.Fields.Keys)) {
        throw new NotSupportedException($"Runtime heap object '{id}' changed type, dimensions or captured fields.");
      }
    }
  }

  private static Dictionary<string, ContractHeapObject> ObjectsById(IEnumerable<ContractHeapObject> heap) {
    var objects = new Dictionary<string, ContractHeapObject>(StringComparer.Ordinal);
    foreach (var item in heap) {
      if (!objects.TryAdd(item.Id, item)) {
        throw new ArgumentException($"Duplicate captured heap object id '{item.Id}'.", nameof(heap));
      }
    }
    return objects;
  }

  private static void Capture(IEnumerable<ContractHeapObject> heap, bool initial,
    IDictionary<string, ContractValue> observations) {
    foreach (var item in heap) {
      string Key(string field) => initial ? ContractHeapPlan.InitialObservationKey(item.Id, field) :
        ContractHeapPlan.FinalObservationKey(item.Id, field);
      if (item.Elements is { } elements) {
        observations.Add(Key("$length"), new ContractValue(ContractValueKind.Integer,
          elements.Count.ToString(CultureInfo.InvariantCulture)));
        for (var index = 0; index < elements.Count; index++) {
          observations.Add(Key("[" + index + "]"), elements[index]);
        }
      } else {
        foreach (var (field, value) in item.Fields) {
          observations.Add(Key(field), value);
        }
      }
    }
  }
}
