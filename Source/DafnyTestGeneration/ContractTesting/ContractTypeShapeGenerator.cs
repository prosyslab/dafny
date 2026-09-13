using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

internal sealed record ContractRefinementObligation(string Value, string TypeName, string ConstraintSha256,
  ContractReductionResult? Reduction) {
  public string Canonical => TypeName + "\n" + Value + "\n" + ConstraintSha256;
  public string Sha256 => ContractHarnessBuilder.Hash(Canonical);
}
internal sealed record ContractRefinementCandidate(string Value, string TypeName, string BaseTypeName,
  string DeclarationName, IReadOnlyList<string> TypeArgumentNames, string ConstraintSha256) {
  public string Canonical => TypeName + "\n" + Value + "\n" + ConstraintSha256;
}
internal sealed record ContractRefinementReductionCacheEntry(string Canonical, ContractReductionResult Reduction);

internal sealed record ContractShapeValue(DafnyType Type, string? Leaf = null,
  IReadOnlyList<ContractShapeValue>? Items = null, string? Constructor = null,
  IReadOnlyDictionary<string, ContractShapeValue>? Fields = null,
  IReadOnlyList<(ContractShapeValue Key, ContractShapeValue Value)>? MapEntries = null,
  ContractValueKind? CollectionKind = null,
  string? ReferenceId = null, bool IsNull = false, string? ReferenceExpression = null) {
  public string Expression => IsNull ? "null" : ReferenceId != null ? ReferenceExpression! : Leaf ??
    (Items != null ? CollectionKind switch {
      ContractValueKind.Set => "{" + string.Join(", ", Items.Select(item => item.Expression)) + "}",
      ContractValueKind.Multiset => "multiset{" + string.Join(", ", Items.Select(item => item.Expression)) + "}",
      _ => "[" + string.Join(", ", Items.Select(item => item.Expression)) + "]"
    } :
      MapEntries != null ? "map[" + string.Join(", ", MapEntries.Select(entry =>
        entry.Key.Expression + " := " + entry.Value.Expression)) + "]" :
      Constructor + "(" + string.Join(", ", Fields!.Select(field => field.Key + " := " + field.Value.Expression)) + ")");
  public IEnumerable<(string Name, DafnyType Type)> Leaves => IsNull || ReferenceId != null ? [] : Leaf != null ? [(Leaf, Type)] :
    (Items ?? (MapEntries != null ? MapEntries.SelectMany(entry => new[] { entry.Key, entry.Value }).ToList() :
      Fields!.Values.ToList())).SelectMany(item => item.Leaves);
  public bool HasRefinement => IsRefined(Type) ||
    (Items ?? []).Any(item => item.HasRefinement) ||
    (Fields?.Values ?? []).Any(item => item.HasRefinement) ||
    (MapEntries ?? []).Any(entry => entry.Key.HasRefinement || entry.Value.HasRefinement);
  public IEnumerable<string> ValidityConstraints => IsNull || ReferenceId != null || Leaf != null ? [] :
    (Items ?? (MapEntries != null ? MapEntries.SelectMany(entry => new[] { entry.Key, entry.Value }).ToList() :
      Fields!.Values.ToList())).SelectMany(item => item.ValidityConstraints).Concat(MapEntries == null ? [] :
      MapEntries.SelectMany((entry, index) => MapEntries.Take(index).Select(prior =>
        entry.Key.Expression + " != " + prior.Key.Expression))).Concat(CollectionKind == ContractValueKind.Set ?
      Items!.SelectMany((item, index) => Items!.Take(index).Select(prior =>
        item.Expression + " != " + prior.Expression)) : []);
  public ContractValue Materialize(IReadOnlyDictionary<string, ContractValue> values) => IsNull ? new(ContractValueKind.Null) :
    ReferenceId != null ? new(ContractValueKind.Reference, "object" + ReferenceId) : Leaf != null ? values[Leaf] :
    Items != null ? new(CollectionKind ?? ContractValueKind.Sequence,
      Items: Items.Select(item => item.Materialize(values)).ToList()) :
    MapEntries != null ? new(ContractValueKind.Map, Entries: MapEntries.Select(entry =>
      new ContractMapEntry(entry.Key.Materialize(values), entry.Value.Materialize(values))).ToList()) :
    new(ContractValueKind.Datatype, Constructor: Constructor,
      Fields: Fields!.ToDictionary(field => field.Key, field => field.Value.Materialize(values)));
  public IEnumerable<string> ConcreteBindings(ContractValue value, string module) {
    if (Leaf != null) {
      yield return Leaf + " == " + ContractModelCodec.ToDafny(value, module);
      yield break;
    }
    if (Items != null) {
      foreach (var binding in Items.Zip(value.Items!, (shape, item) => shape.ConcreteBindings(item, module))
                 .SelectMany(bindings => bindings)) {
        yield return binding;
      }
      yield break;
    }
    if (MapEntries != null) {
      foreach (var binding in MapEntries.Zip(value.Entries!, (shape, entry) =>
                   shape.Key.ConcreteBindings(entry.Key, module)
                     .Concat(shape.Value.ConcreteBindings(entry.Value, module)))
                 .SelectMany(bindings => bindings)) {
        yield return binding;
      }
      yield break;
    }
    if (Fields != null) {
      foreach (var binding in Fields.SelectMany(field =>
                 field.Value.ConcreteBindings(value.Fields![field.Key], module))) {
        yield return binding;
      }
    }
  }

  internal static bool IsRefined(DafnyType type) => type.AsSubsetType != null ||
    type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: SubsetTypeDecl or NewtypeDecl };
}
internal sealed record ContractReferenceShape(ClassDecl Class, DafnyType? ElementType = null) {
  public string Name => ElementType == null ? Class.FullDafnyName : "array<" + ElementType + ">";
}
internal sealed record ContractShapeHeapObject(string Id, ClassDecl Class, IReadOnlyDictionary<string, ContractShapeValue> Fields,
  DafnyType? ElementType = null, IReadOnlyList<ContractShapeValue>? Elements = null, string ObjectPrefix = "contractObject") {
  public string VariableName => ObjectPrefix + Id;
  public string TypeName => ElementType == null ? Class.FullDafnyName : "array<" + ElementType + ">";
}
internal sealed record ContractInputShape(IReadOnlyDictionary<string, ContractShapeValue> Inputs,
  IReadOnlyList<ContractShapeHeapObject>? Objects = null, string? ReceiverName = null) {
  public IReadOnlyList<(string Name, DafnyType Type)> Leaves => Inputs.Values.SelectMany(value => value.Leaves)
    .Concat((Objects ?? []).SelectMany(item => item.Fields.Values.Concat(item.Elements ?? []).SelectMany(value => value.Leaves))).ToList();
  public IEnumerable<string> ObjectParameters(Program program, Method method) => (Objects ?? []).Select(item => item.VariableName + ": " +
    (item.ElementType == null ? ContractHeapFactory.SourceTypeName(program, method, item.Class) : item.TypeName));
  public IReadOnlyList<string> Constraints {
    get {
      var result = Inputs.SelectMany(input => input.Value.ValidityConstraints)
        .Concat(Inputs.Select(input => input.Key + " == " + input.Value.Expression)).ToList();
      foreach (var item in Objects ?? []) {
        result.AddRange(item.Fields.Values.Concat(item.Elements ?? []).SelectMany(value => value.ValidityConstraints));
        result.AddRange(item.Fields.Select(field => item.VariableName + "." + field.Key + " == " + field.Value.Expression));
        if (item.Elements != null) {
          result.Add(item.VariableName + ".Length == " + item.Elements.Count);
          result.AddRange(item.Elements.Select((element, index) => item.VariableName + "[" + index + "] == " + element.Expression));
        }
        result.AddRange((Objects ?? []).Where(other => other.Id != item.Id && other.TypeName == item.TypeName)
          .Select(other => item.VariableName + " != " + other.VariableName));
      }
      return result;
    }
  }
  public string HeapLayout => string.Join(";", (Objects ?? []).Select(item => item.Id + ":" + item.TypeName + ":" + item.Elements?.Count));
  public bool HasRefinement => Inputs.Values.Any(value => value.HasRefinement) ||
    (Objects ?? []).Any(item => item.Fields.Values.Any(value => value.HasRefinement) ||
      (item.Elements ?? []).Any(value => value.HasRefinement));
  public IReadOnlyDictionary<string, ContractValue> Materialize(IReadOnlyDictionary<string, ContractValue> values) =>
    Inputs.ToDictionary(input => input.Key, input => input.Value.Materialize(values));
  public IReadOnlyList<ContractHeapObject> MaterializeHeap(IReadOnlyDictionary<string, ContractValue> values) =>
    (Objects ?? []).Select(item => new ContractHeapObject("object" + item.Id, item.TypeName,
      item.Fields.ToDictionary(field => field.Key, field => field.Value.Materialize(values)),
      item.Elements == null ? null : [item.Elements.Count], item.Elements?.Select(element => element.Materialize(values)).ToList())).ToList();
  public IReadOnlyList<string> ConcreteBindings(IReadOnlyDictionary<string, ContractValue> inputs,
    IReadOnlyList<ContractHeapObject> heap, string module) {
    var result = Inputs.SelectMany(input => input.Value.ConcreteBindings(inputs[input.Key], module)).ToList();
    foreach (var item in Objects ?? []) {
      var concrete = heap.Single(value => value.Id == "object" + item.Id);
      result.AddRange(item.Fields.SelectMany(field =>
        field.Value.ConcreteBindings(concrete.Fields[field.Key], module)));
      if (item.Elements != null) {
        result.AddRange(item.Elements.Zip(concrete.Elements!, (shape, value) =>
          shape.ConcreteBindings(value, module)).SelectMany(bindings => bindings));
      }
    }
    return result;
  }
  public async Task<IReadOnlyList<ContractRefinementObligation>?> RefinementObligationsAsync(
    IReadOnlyDictionary<string, ContractValue> inputs, IReadOnlyList<ContractHeapObject> heap,
    ContractPreparedProgram prepared, IReadOnlyDictionary<string, string> verifiedRefinements,
    IDictionary<string, ContractRefinementReductionCacheEntry> reductionCache,
    CancellationToken cancellationToken) {
    var candidates = new List<ContractRefinementCandidate>();
    var safe = true;
    foreach (var input in Inputs) {
      CollectRefinements(input.Value, inputs[input.Key], prepared, candidates, ref safe);
    }
    foreach (var item in Objects ?? []) {
      var concrete = heap.Single(value => value.Id == "object" + item.Id);
      foreach (var field in item.Fields) {
        CollectRefinements(field.Value, concrete.Fields[field.Key], prepared, candidates, ref safe);
      }
      if (item.Elements != null) {
        foreach (var (shape, value) in item.Elements.Zip(concrete.Elements!)) {
          CollectRefinements(shape, value, prepared, candidates, ref safe);
        }
      }
    }
    if (!safe) {
      return null;
    }
    candidates = candidates.GroupBy(candidate => candidate.Canonical, StringComparer.Ordinal)
      .Select(group => group.First()).ToList();
    if (candidates.Count == 0) {
      return [];
    }

    var obligations = candidates.Select(candidate => new ContractRefinementObligation(
      candidate.Value, candidate.TypeName, candidate.ConstraintSha256, null)).ToList();
    for (var index = 0; index < obligations.Count; index++) {
      var obligation = obligations[index];
      if (reductionCache.TryGetValue(obligation.Sha256, out var cachedReduction)) {
        if (cachedReduction.Canonical != obligation.Canonical) {
          return null;
        }
        obligations[index] = obligation with { Reduction = cachedReduction.Reduction };
      }
    }
    var pending = candidates.Select((candidate, index) => (Candidate: candidate, Index: index))
      .Where(item => !verifiedRefinements.TryGetValue(obligations[item.Index].Sha256, out var cached) ||
                     cached != obligations[item.Index].Canonical)
      .Where(item => obligations[item.Index].Reduction == null).ToList();
    if (pending.Count == 0) {
      return obligations;
    }

    var carrierPrefix = ContractBodyNames.Family(prepared.Program, "contractRefinementCarrier");
    var typeArgumentPrefix = ContractBodyNames.Family(prepared.Program, "contractRefinementTypeArgument");
    var declarations = string.Join("\n", pending.Select(item =>
      "function " + carrierPrefix + item.Index + "(" + string.Join(", ",
        item.Candidate.TypeArgumentNames.Select((typeArgument, argumentIndex) =>
          typeArgumentPrefix + item.Index + "_" + argumentIndex + ": " + typeArgument)) + "): " +
      item.Candidate.BaseTypeName + " { " + item.Candidate.Value + " }"));
    var diagnosticContent = ContractHarnessBuilder.Insert(prepared, "\n" + declarations + "\n");
    var diagnosticSources = ContractSourceSnapshot.Replace(prepared.SourceSnapshots,
      prepared.Source.Path, diagnosticContent);
    var diagnosticOptions = new DafnyOptions(prepared.Program.Options, useNullWriters: true) {
      Compile = false
    };
    var reporter = new BatchErrorReporter(diagnosticOptions);
    var diagnosticProgram = await ContractSourceSnapshot.ParseAsync(reporter, diagnosticSources,
      cancellationToken);
    if (reporter.ErrorCount != 0) {
      return null;
    }

    var functions = diagnosticProgram.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(declaration => declaration.Members)
      .OfType<Function>().Where(function => pending.Any(item => function.Name == carrierPrefix + item.Index))
      .ToList();
    foreach (var item in pending) {
      var matching = functions.Where(function => function.Name == carrierPrefix + item.Index).ToList();
      if (matching.Count != 1 || matching[0].Body == null ||
          !TryReduceCarrier(matching[0], item.Candidate, diagnosticProgram, out var reduction)) {
        return null;
      }
      obligations[item.Index] = obligations[item.Index] with { Reduction = reduction };
      reductionCache.Add(obligations[item.Index].Sha256,
        new(obligations[item.Index].Canonical, reduction));
    }
    return obligations;
  }

  private static void CollectRefinements(ContractShapeValue shape, ContractValue value,
    ContractPreparedProgram prepared,
    ICollection<ContractRefinementCandidate> candidates, ref bool safe) {
    if (ContractShapeValue.IsRefined(shape.Type)) {
      if (ContainsReference(value)) {
        safe = false;
      } else {
        var typeName = shape.Type.ToString().Replace(" ", "", StringComparison.Ordinal);
        if (!ContractPatternCodec.IsTypeName(typeName)) {
          safe = false;
        } else {
          try {
            var expression = ContractModelCodec.ToDafny(value,
              prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
            if (!TryCarrierTypes(shape.Type, prepared, out var baseTypeName, out var declarationName,
                  out var typeArgumentNames, out var constraintSha256)) {
              safe = false;
            } else if (baseTypeName != null) {
              candidates.Add(new(expression, typeName, baseTypeName, declarationName!, typeArgumentNames!,
                constraintSha256!));
            }
          } catch (ArgumentException) {
            safe = false;
          }
        }
      }
    }
    if (shape.Items != null) {
      foreach (var (nested, nestedValue) in shape.Items.Zip(value.Items!)) {
        CollectRefinements(nested, nestedValue, prepared, candidates, ref safe);
      }
    }
    if (shape.MapEntries != null) {
      foreach (var (entry, concrete) in shape.MapEntries.Zip(value.Entries!)) {
        CollectRefinements(entry.Key, concrete.Key, prepared, candidates, ref safe);
        CollectRefinements(entry.Value, concrete.Value, prepared, candidates, ref safe);
      }
    }
    if (shape.Fields != null) {
      foreach (var field in shape.Fields) {
        CollectRefinements(field.Value, value.Fields![field.Key], prepared, candidates, ref safe);
      }
    }
  }

  private static bool TryCarrierTypes(DafnyType type, ContractPreparedProgram prepared,
    out string? baseTypeName, out string? declarationName,
    out IReadOnlyList<string>? typeArgumentNames, out string? constraintSha256) {
    var applied = type.NormalizeExpandKeepConstraints() as UserDefinedType ??
                  type.NormalizeExpand(true) as UserDefinedType;
    if (applied?.ResolvedClass is not RedirectingTypeDecl declaration) {
      baseTypeName = null;
      declarationName = null;
      typeArgumentNames = null;
      constraintSha256 = null;
      return false;
    }
    if (declaration.Var == null || declaration.Constraint == null) {
      baseTypeName = null;
      declarationName = null;
      typeArgumentNames = null;
      constraintSha256 = null;
      return true;
    }
    var typeParameters = applied.ResolvedClass switch {
      SubsetTypeDecl subset => subset.TypeArgs,
      NewtypeDecl newtype => newtype.TypeArgs,
      _ => null
    };
    if (typeParameters == null || typeParameters.Count != applied.TypeArgs.Count) {
      baseTypeName = null;
      declarationName = null;
      typeArgumentNames = null;
      constraintSha256 = null;
      return false;
    }
    var baseType = applied.ResolvedClass switch {
      SubsetTypeDecl subset => subset.RhsWithArgument(applied.TypeArgs).NormalizeExpand(false),
      NewtypeDecl newtype => newtype.ConcreteBaseType(applied.TypeArgs).NormalizeExpand(false),
      _ => null
    };
    if (baseType == null) {
      baseTypeName = null;
      declarationName = null;
      typeArgumentNames = null;
      constraintSha256 = null;
      return false;
    }
    if (!TryErasedTypeName(baseType, out baseTypeName)) {
      declarationName = null;
      typeArgumentNames = null;
      constraintSha256 = null;
      return false;
    }
    var arguments = new List<string>();
    foreach (var typeArgument in applied.TypeArgs) {
      var name = typeArgument.ToString().Replace(" ", "", StringComparison.Ordinal);
      if (!ContractPatternCodec.IsTypeName(name)) {
        declarationName = null;
        typeArgumentNames = null;
        constraintSha256 = null;
        return false;
      }
      arguments.Add(name);
    }
    declarationName = declaration.FullDafnyName;
    typeArgumentNames = arguments;
    constraintSha256 = ContractHarnessBuilder.Hash(declaration.FullDafnyName + "\n" +
      Printer.ExprToString(prepared.Program.Options, declaration.Constraint));
    return true;
  }

  private static bool TryErasedTypeName(DafnyType type, out string name) {
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: SubsetTypeDecl subset
    } subsetType) {
      return TryErasedTypeName(subset.RhsWithArgument(subsetType.TypeArgs), out name);
    }
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: NewtypeDecl newtype
    } newtypeType) {
      return TryErasedTypeName(newtype.ConcreteBaseType(newtypeType.TypeArgs), out name);
    }
    if (type.AsSeqType is { } sequence && TryErasedTypeName(sequence.Arg, out var elementName)) {
      name = "seq<" + elementName + ">";
      return true;
    }
    if (type.AsSetType is { } set && TryErasedTypeName(set.Arg, out var setElementName)) {
      name = (set.Finite ? "set<" : "iset<") + setElementName + ">";
      return true;
    }
    if (type.AsMultiSetType is { } multiset && TryErasedTypeName(multiset.Arg, out var multisetElementName)) {
      name = "multiset<" + multisetElementName + ">";
      return true;
    }
    if (type.AsMapType is { } map && TryErasedTypeName(map.Domain, out var domainName) &&
        TryErasedTypeName(map.Range, out var rangeName)) {
      name = (map.Finite ? "map<" : "imap<") + domainName + "," + rangeName + ">";
      return true;
    }
    if (type is UserDefinedType userDefined && userDefined.ResolvedClass is DatatypeDecl datatype) {
      var typeArguments = new List<string>();
      foreach (var typeArgument in userDefined.TypeArgs) {
        if (!TryErasedTypeName(typeArgument, out var typeArgumentName)) {
          name = "";
          return false;
        }
        typeArguments.Add(typeArgumentName);
      }
      name = datatype.FullDafnyName + (typeArguments.Count == 0 ? "" :
        "<" + string.Join(",", typeArguments) + ">");
      return ContractPatternCodec.IsTypeName(name);
    }
    name = type.NormalizeExpand().ToString().Replace(" ", "", StringComparison.Ordinal);
    return ContractPatternCodec.IsTypeName(name);
  }

  private static bool TryReduceCarrier(Function carrier, ContractRefinementCandidate candidate,
    Program diagnosticProgram,
    out ContractReductionResult reduction) {
    reduction = null!;
    var declarations = diagnosticProgram.RawModules().SelectMany(module => module.TopLevelDecls)
      .Concat(diagnosticProgram.SystemModuleManager.SystemModule.SourceDecls)
      .OfType<RedirectingTypeDecl>().Where(declaration => declaration.FullDafnyName == candidate.DeclarationName)
      .Distinct().ToList();
    if (declarations.Count != 1 || declarations[0].Var == null || declarations[0].Constraint == null ||
        carrier.Body == null) {
      return false;
    }
    var declaration = declarations[0];
    var typeParameters = declaration switch {
      SubsetTypeDecl subset => subset.TypeArgs,
      NewtypeDecl newtype => newtype.TypeArgs,
      _ => null
    };
    if (typeParameters == null || typeParameters.Count != carrier.Ins.Count) {
      return false;
    }
    var typeMap = TypeParameter.SubstitutionMap(typeParameters,
      carrier.Ins.Select(formal => formal.Type).ToList());
    var constraint = new Substituter(null, new Dictionary<IVariable, Expression>(), typeMap,
      null, diagnosticProgram.SystemModuleManager).Substitute(declaration.Constraint);
    var reducer = new ContractExpressionReducer(diagnosticProgram.Options,
      carrier.EnclosingClass.EnclosingModuleDefinition, diagnosticProgram.SystemModuleManager);
    reduction = reducer.Reduce(constraint, new Dictionary<IVariable, Expression> {
      [declaration.Var] = carrier.Body
    });
    return true;
  }

  private static bool ContainsReference(ContractValue value) => value.Kind == ContractValueKind.Reference ||
    (value.Items ?? []).Any(ContainsReference) || (value.Fields?.Values ?? []).Any(ContainsReference) ||
    (value.Entries ?? []).Any(entry => ContainsReference(entry.Key) || ContainsReference(entry.Value));
  public string ConcreteExpression(ContractValue value, string module) => value.Kind switch {
    ContractValueKind.Reference => (Objects ?? []).Any(item => "object" + item.Id == value.Value)
      ? (Objects ?? []).Single(item => "object" + item.Id == value.Value).VariableName : throw new ArgumentException("Candidate references a heap slot outside this input shape."),
    ContractValueKind.Sequence => "[" + string.Join(", ", value.Items!.Select(item => ConcreteExpression(item, module))) + "]",
    ContractValueKind.Set => "{" + string.Join(", ", value.Items!.Select(item => ConcreteExpression(item, module))) + "}",
    ContractValueKind.Multiset => "multiset{" + string.Join(", ", value.Items!.Select(item => ConcreteExpression(item, module))) + "}",
    ContractValueKind.Map => "map[" + string.Join(", ", value.Entries!.Select(entry =>
      ConcreteExpression(entry.Key, module) + " := " + ConcreteExpression(entry.Value, module))) + "]",
    ContractValueKind.Datatype => ContractModelCodec.LocalName(value.Constructor!, module) + "(" +
      string.Join(", ", value.Fields!.Select(field => field.Key + " := " + ConcreteExpression(field.Value, module))) + ")",
    _ => ContractModelCodec.ToDafny(value, module)
  };
}

/// <summary>Builds finite structural alternatives with symbolic primitive leaves, never global type axioms.</summary>
public sealed class ContractTypeShapeGenerator(ContractGenerationBounds bounds) {
  private int leaf;
  private string leafPrefix = "contractLeaf";
  private string objectPrefix = "contractObject";

  internal IReadOnlyList<ContractInputShape> Generate(Program program, Method method, string? receiverName = null) {
    leafPrefix = ContractBodyNames.Family(program, "contractLeaf");
    objectPrefix = ContractBodyNames.Family(program, "contractObject");
    var formals = method.Ins.ToList();
    if (receiverName != null) {
      formals.Add(new Formal(method.Origin, receiverName,
        UserDefinedType.FromTopLevelDecl(method.Origin, ((ClassLikeDecl)method.EnclosingClass).NonNullTypeDecl!), true, false, null));
    }
    var classes = new Dictionary<string, ContractReferenceShape>(StringComparer.Ordinal);
    foreach (var formal in formals) {
      CollectClasses(formal.Type, classes);
    }
    var result = new List<ContractInputShape>();
    for (var size = 0; size <= (classes.Count == 0 ? 0 : bounds.MaxHeapObjects); size++) {
      foreach (var layout in ClassLayouts(classes.Values.ToList(), size)) {
        foreach (var objects in HeapFields(layout)) {
          result.AddRange(InputShapes(formals, objects, receiverName));
          if (result.Count >= bounds.MaxGoals) {
            return result.Take(bounds.MaxGoals).ToList();
          }
        }
      }
    }
    return result;
  }

  internal ContractInputShape FromConcrete(Program program, Method method,
    IReadOnlyDictionary<string, ContractValue> inputs, ContractHeapPlan? heap) {
    leaf = 0;
    leafPrefix = ContractBodyNames.Family(program, "contractLeaf");
    objectPrefix = ContractBodyNames.Family(program, "contractObject");
    if (!method.Ins.Select(formal => formal.Name).ToHashSet(StringComparer.Ordinal).SetEquals(inputs.Keys)) {
      throw new ArgumentException("Concrete pattern input names do not match the selected declaration's formals.");
    }
    var objects = (heap?.Slots ?? []).Select(slot => new ContractShapeHeapObject(
      ShapeObjectId(slot.Object.Id), slot.Class, new Dictionary<string, ContractShapeValue>(),
      slot.ElementType, slot.IsArray ? [] : null, objectPrefix)).ToList();
    for (var index = 0; index < (heap?.Slots.Count ?? 0); index++) {
      var slot = heap!.Slots[index];
      objects[index] = slot.IsArray
        ? objects[index] with {
          Elements = slot.Cells.Select(cell => ConcreteValue(cell.InitialValue, cell.Type, objects)).ToList()
        }
        : objects[index] with {
          Fields = slot.Cells.ToDictionary(cell => cell.Name,
            cell => ConcreteValue(cell.InitialValue, cell.Type, objects), StringComparer.Ordinal)
        };
    }
    return new(method.Ins.ToDictionary(formal => formal.Name,
      formal => ConcreteValue(inputs[formal.Name], formal.Type, objects), StringComparer.Ordinal), objects);
  }

  private ContractShapeValue ConcreteValue(ContractValue value, DafnyType expected,
    IReadOnlyList<ContractShapeHeapObject> objects) {
    if (value.Kind == ContractValueKind.Reference) {
      var item = objects.SingleOrDefault(candidate => "object" + candidate.Id == value.Value) ??
                 throw new ArgumentException("Concrete pattern reference does not name a resolved heap object.");
      var declaration = ReferenceClass(expected);
      var expectedElement = expected.AsArrayType == null ? null : expected.NormalizeExpand().TypeArgs[0];
      if (declaration != item.Class || (expectedElement != null && !expectedElement.Equals(item.ElementType))) {
        throw new ArgumentException("Concrete pattern reference has an incompatible resolved heap type.");
      }
      return new(expected, ReferenceId: item.Id, ReferenceExpression: item.VariableName);
    }
    if (value.Kind == ContractValueKind.Null) {
      if (!expected.IsRefType || expected.IsNonNullRefType) {
        throw new ArgumentException("Concrete pattern null does not match its resolved type.");
      }
      return new(expected, IsNull: true);
    }
    if (TryRefinedBaseType(expected, out var baseType)) {
      var refined = ConcreteValue(value, baseType, objects);
      return refined with { Type = expected };
    }
    if ((expected.IsIntegerType && value.Kind == ContractValueKind.Integer) ||
        (expected.IsBoolType && value.Kind == ContractValueKind.Boolean) ||
        (expected.IsCharType && value.Kind == ContractValueKind.Character) ||
        (expected.AsBitVectorType is { } bitvector && value.Kind == ContractValueKind.Bitvector &&
         value.Width == bitvector.Width)) {
      return new(expected, leafPrefix + leaf++);
    }
    if (expected.AsSeqType is { } sequence && value.Kind == ContractValueKind.Sequence) {
      return new(expected, Items: value.Items!.Select(item => ConcreteValue(item, sequence.Arg, objects)).ToList());
    }
    if (expected.AsSetType is { Finite: true } set && value.Kind == ContractValueKind.Set) {
      return new(expected, Items: value.Items!.Select(item => ConcreteValue(item, set.Arg, objects)).ToList(),
        CollectionKind: ContractValueKind.Set);
    }
    if (expected.AsMultiSetType is { } multiset && value.Kind == ContractValueKind.Multiset) {
      return new(expected, Items: value.Items!.Select(item => ConcreteValue(item, multiset.Arg, objects)).ToList(),
        CollectionKind: ContractValueKind.Multiset);
    }
    if (expected.AsMapType is { Finite: true } map && value.Kind == ContractValueKind.Map) {
      return new(expected, MapEntries: value.Entries!.Select(entry =>
        (ConcreteValue(entry.Key, map.Domain, objects), ConcreteValue(entry.Value, map.Range, objects))).ToList());
    }
    if (expected.AsDatatype is { } datatype && value.Kind == ContractValueKind.Datatype) {
      var constructor = datatype.Ctors.SingleOrDefault(candidate => value.Constructor == candidate.FullName ||
        value.Constructor == datatype.Name + "." + candidate.Name ||
        value.Constructor == datatype.FullDafnyName + "." + candidate.Name || value.Constructor == candidate.Name);
      if (constructor == null || !constructor.Formals.Select(formal => formal.Name)
            .ToHashSet(StringComparer.Ordinal).SetEquals(value.Fields!.Keys)) {
        throw new ArgumentException("Concrete pattern datatype does not match its resolved constructor.");
      }
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, expected.TypeArgs);
      return new(expected, Constructor: datatype.Name + "." + constructor.Name,
        Fields: constructor.Formals.ToDictionary(formal => formal.Name,
          formal => ConcreteValue(value.Fields[formal.Name], formal.Type.Subst(substitution), objects),
          StringComparer.Ordinal));
    }
    throw new ArgumentException("Concrete pattern value does not match resolved Dafny type '" + expected + "'.");
  }

  private static string ShapeObjectId(string id) {
    if (!id.StartsWith("object", StringComparison.Ordinal) || id.Length == "object".Length) {
      throw new ArgumentException("Normalized concrete pattern heap ids must use the objectN form.");
    }
    return id["object".Length..];
  }

  private static bool TryRefinedBaseType(DafnyType type, out DafnyType baseType) {
    var constrained = type.NormalizeExpandKeepConstraints();
    if (constrained is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } subsetType) {
      baseType = subset.RhsWithArgument(subsetType.TypeArgs);
      return true;
    }
    if (constrained is UserDefinedType { ResolvedClass: NewtypeDecl newtype } newtypeType) {
      baseType = newtype.ConcreteBaseType(newtypeType.TypeArgs);
      return true;
    }
    baseType = null!;
    return false;
  }

  private IEnumerable<ContractInputShape> InputShapes(IReadOnlyList<Formal> formals, IReadOnlyList<ContractShapeHeapObject> objects, string? receiverName) {
    var alternatives = new List<Dictionary<string, ContractShapeValue>> { new() };
    foreach (var formal in formals) {
      var values = Shapes(formal.Type, bounds.MaxDatatypeDepth, objects).ToList();
      alternatives = alternatives.SelectMany(prior => values.Select(value =>
        new Dictionary<string, ContractShapeValue>(prior) { [formal.Name] = value })).Take(bounds.MaxGoals).ToList();
    }
    return alternatives.Select(inputs => new ContractInputShape(inputs, objects, receiverName)).ToList();
  }

  private IEnumerable<ContractShapeValue> Shapes(DafnyType type, int depth, IReadOnlyList<ContractShapeHeapObject> objects) {
    if (ReferenceClass(type) is { } reference) {
      if (!type.IsNonNullRefType) { yield return new(type, IsNull: true); }
      foreach (var item in objects.Where(item => item.Class == reference &&
        (!type.IsArrayType || item.ElementType!.Equals(type.NormalizeExpand().TypeArgs[0])))) {
        yield return new(type, ReferenceId: item.Id, ReferenceExpression: item.VariableName);
      }
      yield break;
    }
    if (type.IsIntegerType || type.IsBoolType || type.IsCharType || type.IsBitVectorType ||
        type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: SubsetTypeDecl or NewtypeDecl }) {
      yield return new(type, leafPrefix + leaf++);
      yield break;
    }
    if (type.AsSeqType is { } sequence) {
      for (var length = 0; length <= bounds.MaxSequenceLength; length++) {
        var alternatives = Product(Enumerable.Repeat(sequence.Arg, length), depth, objects);
        foreach (var values in alternatives) {
          yield return new(type, Items: values);
        }
      }
      yield break;
    }
    if (type.AsSetType is { } set) {
      if (!set.Finite) {
        throw new NotSupportedException("Automatic input shape is unsupported for type " + type + ".");
      }
      for (var size = 0; size <= bounds.MaxSequenceLength; size++) {
        foreach (var values in Product(Enumerable.Repeat(set.Arg, size), depth, objects)) {
          yield return new(type, Items: values, CollectionKind: ContractValueKind.Set);
        }
      }
      yield break;
    }
    if (type.AsMultiSetType is { } multiset) {
      for (var size = 0; size <= bounds.MaxSequenceLength; size++) {
        foreach (var values in Product(Enumerable.Repeat(multiset.Arg, size), depth, objects)) {
          yield return new(type, Items: values, CollectionKind: ContractValueKind.Multiset);
        }
      }
      yield break;
    }
    if (type.AsMapType is { } map) {
      if (!map.Finite) {
        throw new NotSupportedException("Automatic input shape is unsupported for type " + type + ".");
      }
      for (var count = 0; count <= bounds.MaxSequenceLength; count++) {
        var componentTypes = Enumerable.Range(0, count)
          .SelectMany(_ => new[] { map.Domain, map.Range });
        foreach (var values in Product(componentTypes, depth, objects)) {
          yield return new(type, MapEntries: Enumerable.Range(0, count).Select(index =>
            (values[index * 2], values[index * 2 + 1])).ToList());
        }
      }
      yield break;
    }
    if (type.AsDatatype is { } datatype) {
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, type.TypeArgs);
      foreach (var constructor in datatype.Ctors) {
        if (constructor.Formals.Any(formal => formal.IsGhost) || (depth == 0 && constructor.Formals.Count > 0)) {
          continue;
        }
        foreach (var values in Product(constructor.Formals.Select(formal => formal.Type.Subst(substitution)), depth - 1, objects)) {
          yield return new(type, Constructor: datatype.Name + "." + constructor.Name,
            Fields: constructor.Formals.Select((formal, index) => (formal.Name, values[index]))
              .ToDictionary(pair => pair.Name, pair => pair.Item2));
        }
      }
      yield break;
    }
    throw new NotSupportedException("Automatic input shape is unsupported for type " + type + ".");
  }

  private IReadOnlyList<IReadOnlyList<ContractShapeValue>> Product(IEnumerable<DafnyType> types, int depth,
    IReadOnlyList<ContractShapeHeapObject> objects) {
    var alternatives = new List<IReadOnlyList<ContractShapeValue>> { new List<ContractShapeValue>() };
    foreach (var type in types) {
      var values = Shapes(type, depth, objects).Take(bounds.MaxGoals).ToList();
      alternatives = alternatives.SelectMany(prior => values.Select(value =>
        (IReadOnlyList<ContractShapeValue>)prior.Append(value).ToList())).Take(bounds.MaxGoals).ToList();
    }
    return alternatives;
  }

  private static ClassDecl? ReferenceClass(DafnyType type) => type.NormalizeExpand() is UserDefinedType user ? user.ResolvedClass switch {
    NonNullTypeDecl { Class: ClassDecl nonNull } => nonNull,
    ClassDecl nullable => nullable,
    _ => null
  } : null;

  private static void CollectClasses(DafnyType type, Dictionary<string, ContractReferenceShape> classes,
    HashSet<DatatypeDecl>? visited = null) {
    visited ??= [];
    if (type.AsDatatype is { } datatype && visited.Add(datatype)) {
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, type.TypeArgs);
      foreach (var formal in datatype.Ctors.SelectMany(constructor => constructor.Formals)) {
        CollectClasses(formal.Type.Subst(substitution), classes, visited);
      }
    }
    if (type.AsArrayType is { } array) {
      if (array.Dims != 1) { throw new NotSupportedException("Automatic array shapes support one dimension."); }
      var element = type.NormalizeExpand().TypeArgs[0];
      var reference = new ContractReferenceShape(array, element);
      if (classes.TryAdd(reference.Name, reference)) { CollectClasses(element, classes, visited); }
      return;
    }
    if (ReferenceClass(type) is { } declaration && classes.TryAdd(declaration.FullDafnyName, new(declaration))) {
      foreach (var field in declaration.Members.OfType<Field>()
                 .Where(field => field.Origin.line > 0 && !field.IsStatic)) {
        CollectClasses(field.Type, classes, visited);
      }
    }
    foreach (var argument in type.TypeArgs) { CollectClasses(argument, classes, visited); }
  }

  private IEnumerable<IReadOnlyList<ContractReferenceShape>> ClassLayouts(IReadOnlyList<ContractReferenceShape> classes, int count) {
    if (count == 0) { yield return []; yield break; }
    foreach (var prior in ClassLayouts(classes, count - 1)) {
      foreach (var declaration in classes) { yield return prior.Append(declaration).ToList(); }
    }
  }

  private IEnumerable<IReadOnlyList<ContractShapeHeapObject>> HeapFields(IReadOnlyList<ContractReferenceShape> layout) {
    var alternatives = new List<IReadOnlyList<ContractShapeHeapObject>> { new List<ContractShapeHeapObject>() };
    foreach (var reference in layout) {
      var next = new List<IReadOnlyList<ContractShapeHeapObject>>();
      foreach (var prior in alternatives) {
        if (reference.ElementType != null) {
          for (var length = 0; length <= bounds.MaxSequenceLength; length++) {
            foreach (var values in Product(Enumerable.Repeat(reference.ElementType, length), bounds.MaxDatatypeDepth, prior)) {
              next.Add(prior.Append(new ContractShapeHeapObject(prior.Count.ToString(), reference.Class,
                new Dictionary<string, ContractShapeValue>(), reference.ElementType, values, objectPrefix)).ToList());
              if (next.Count >= bounds.MaxGoals) { break; }
            }
            if (next.Count >= bounds.MaxGoals) { break; }
          }
        } else {
          var fields = reference.Class.Members.OfType<Field>()
            .Where(field => field.Origin.line > 0 && !field.IsStatic).ToList();
          foreach (var values in Product(fields.Select(field => field.Type), bounds.MaxDatatypeDepth, prior)) {
            next.Add(prior.Append(new ContractShapeHeapObject(prior.Count.ToString(), reference.Class,
              fields.Select((field, index) => (field.Name, values[index])).ToDictionary(pair => pair.Name, pair => pair.Item2), ObjectPrefix: objectPrefix)).ToList());
            if (next.Count >= bounds.MaxGoals) { break; }
          }
        }
        if (next.Count >= bounds.MaxGoals) { break; }
      }
      alternatives = next;
    }
    return alternatives;
  }
}
