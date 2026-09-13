using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Checks data-only pattern nodes against the selected declaration's resolved Dafny types.</summary>
internal static class ContractPatternCompiler {
  internal const string ExecutorBaselineId = "__executor_baseline";

  internal static ContractPatternCampaign AddExecutorBaseline(Method method,
    ContractPatternCampaign campaign, ContractGenerationBounds bounds, out string? baselineId) {
    baselineId = null;
    var inputs = new Dictionary<string, ContractInputPattern>(StringComparer.Ordinal);
    foreach (var formal in method.Ins) {
      if (!TryCreateBaseline(formal.Type, bounds, 0, new HashSet<DatatypeDecl>(), out var pattern)) {
        return campaign;
      }
      inputs.Add(formal.Name, pattern);
    }
    if (inputs.Count == 0) {
      return campaign;
    }
    var id = ExecutorBaselineId;
    for (var suffix = 1; campaign.Patterns.Any(pattern => pattern.Id == id); suffix++) {
      id = ExecutorBaselineId + "-" + suffix;
    }
    baselineId = id;
    return campaign with {
      Patterns = new[] { new ContractCompleteInputPattern(id, 1, inputs) }.Concat(campaign.Patterns).ToArray()
    };
  }

  internal static void Validate(Method method, ContractPatternCampaign campaign, ContractGenerationBounds bounds) {
    ContractPatternCodec.Validate(campaign);
    var formalNames = method.Ins.Select(formal => formal.Name).ToHashSet(StringComparer.Ordinal);
    foreach (var complete in campaign.Patterns) {
      if (!formalNames.SetEquals(complete.Inputs.Keys)) {
        throw new ArgumentException("Pattern '" + complete.Id +
          "' input names must exactly match the selected declaration's formals.");
      }
      if ((complete.Heap?.Count ?? 0) > bounds.MaxHeapObjects) {
        throw new ArgumentException("Pattern '" + complete.Id + "' exceeds maxHeapObjects.");
      }
      var bindings = new Dictionary<string, DafnyType>(StringComparer.Ordinal);
      var pendingReuses = new List<(string Name, DafnyType Type)>();
      foreach (var formal in method.Ins) {
        Validate(complete.Inputs[formal.Name], formal.Type, bindings, pendingReuses, bounds);
      }
      foreach (var reuse in pendingReuses) {
        if (!bindings.TryGetValue(reuse.Name, out var bound) || !bound.Equals(reuse.Type)) {
          throw new ArgumentException("Input-pattern binding '" + reuse.Name +
            "' is unavailable or has a different resolved Dafny type.");
        }
      }
    }
  }

  private static void Validate(ContractInputPattern pattern, DafnyType expected,
    IDictionary<string, DafnyType> bindings, IList<(string Name, DafnyType Type)> pendingReuses,
    ContractGenerationBounds bounds) {
    if (TryRefinedBaseType(expected, out var baseType)) {
      Validate(pattern, baseType, bindings, pendingReuses, bounds);
      return;
    }
    switch (pattern.Kind) {
      case ContractInputPatternKind.Literal:
        ValidateValue(pattern.Value!, expected);
        return;
      case ContractInputPatternKind.OneOf:
        foreach (var choice in pattern.Choices!) {
          Validate(choice.Pattern, expected, bindings, pendingReuses, bounds);
        }
        return;
      case ContractInputPatternKind.Boolean:
        Require(expected.IsBoolType, expected, pattern.Kind);
        return;
      case ContractInputPatternKind.IntegerRange:
        Require(expected.IsIntegerType, expected, pattern.Kind);
        return;
      case ContractInputPatternKind.BitvectorRange:
        Require(expected.AsBitVectorType?.Width == pattern.Width, expected, pattern.Kind);
        return;
      case ContractInputPatternKind.Character:
        Require(expected.IsCharType, expected, pattern.Kind);
        return;
      case ContractInputPatternKind.String:
        Require(expected.AsSeqType?.Arg.IsCharType == true, expected, pattern.Kind);
        if (pattern.MaxLength > bounds.MaxSequenceLength) {
          throw new ArgumentException("String pattern exceeds maxSequenceLength.");
        }
        return;
      case ContractInputPatternKind.Sequence:
        if (expected.AsSeqType is not { } sequence) {
          Require(false, expected, pattern.Kind);
          return;
        }
        if (pattern.MaxLength > bounds.MaxSequenceLength) {
          throw new ArgumentException("Sequence pattern exceeds maxSequenceLength.");
        }
        Validate(pattern.Element!, sequence.Arg, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Set:
        if (expected.AsSetType is not { Finite: true } set) {
          Require(false, expected, pattern.Kind);
          return;
        }
        if (pattern.MaxSize > bounds.MaxSequenceLength) {
          throw new ArgumentException("Set pattern exceeds the finite collection bound maxSequenceLength.");
        }
        Validate(pattern.Element!, set.Arg, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Multiset:
        if (expected.AsMultiSetType is not { } multiset) {
          Require(false, expected, pattern.Kind);
          return;
        }
        if (pattern.MaxSize > bounds.MaxSequenceLength) {
          throw new ArgumentException("Multiset pattern exceeds the finite collection bound maxSequenceLength.");
        }
        Validate(pattern.Element!, multiset.Arg, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Map:
        if (expected.AsMapType is not { Finite: true } map) {
          Require(false, expected, pattern.Kind);
          return;
        }
        if (pattern.MaxEntries > bounds.MaxSequenceLength) {
          throw new ArgumentException("Map pattern exceeds the finite collection bound maxSequenceLength.");
        }
        Validate(pattern.KeyPattern!, map.Domain, bindings, pendingReuses, bounds);
        Validate(pattern.ValuePattern!, map.Range, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Datatype:
        ValidateDatatype(pattern, expected, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Null:
        Require(expected.IsRefType && !expected.IsNonNullRefType, expected, pattern.Kind);
        return;
      case ContractInputPatternKind.Reference:
        ValidateReference(pattern, expected, bindings, pendingReuses, bounds);
        return;
      case ContractInputPatternKind.Bind:
        if (bindings.ContainsKey(pattern.Name!)) {
          throw new ArgumentException("Duplicate input-pattern binding '" + pattern.Name + "'.");
        }
        Validate(pattern.Pattern!, expected, bindings, pendingReuses, bounds);
        bindings.Add(pattern.Name!, expected);
        return;
      case ContractInputPatternKind.Reuse:
        pendingReuses.Add((pattern.Name!, expected));
        return;
      default:
        throw new ArgumentOutOfRangeException(nameof(pattern.Kind));
    }
  }

  private static bool TryCreateBaseline(DafnyType expected, ContractGenerationBounds bounds,
    int depth, ISet<DatatypeDecl> activeDatatypes, out ContractInputPattern pattern) {
    if (TryRefinedBaseType(expected, out var baseType)) {
      return TryCreateBaseline(baseType, bounds, depth, activeDatatypes, out pattern);
    }
    if (expected.IsBoolType) {
      pattern = new(ContractInputPatternKind.Boolean);
      return true;
    }
    if (expected.IsIntegerType) {
      pattern = new(ContractInputPatternKind.IntegerRange, MinValue: "-1", MaxValue: "1",
        BoundaryValues: ["-1", "0", "1"]);
      return true;
    }
    if (expected.AsBitVectorType is { } bitvector) {
      var maximum = BigInteger.Min(new BigInteger(3), (BigInteger.One << bitvector.Width) - BigInteger.One);
      pattern = new(ContractInputPatternKind.BitvectorRange, MinValue: "0",
        MaxValue: maximum.ToString(), BoundaryValues: ["0", maximum.ToString()], Width: bitvector.Width);
      return true;
    }
    if (expected.IsCharType) {
      pattern = new(ContractInputPatternKind.Character, Alphabet: "a0");
      return true;
    }
    if (expected.AsSeqType is { } sequence) {
      var maximum = Math.Min(2, bounds.MaxSequenceLength);
      if (sequence.Arg.IsCharType) {
        pattern = new(ContractInputPatternKind.String, Alphabet: "a0", MinLength: 0,
          MaxLength: maximum);
        return true;
      }
      if (TryCreateBaseline(sequence.Arg, bounds, depth + 1, activeDatatypes, out var element)) {
        pattern = new(ContractInputPatternKind.Sequence, MinLength: 0, MaxLength: maximum,
          Element: element);
        return true;
      }
    }
    if (expected.AsMapType is { Finite: true } map &&
        TryCreateBaseline(map.Domain, bounds, depth + 1, activeDatatypes, out var key) &&
        TryCreateBaseline(map.Range, bounds, depth + 1, activeDatatypes, out var value)) {
      pattern = new(ContractInputPatternKind.Map, MinEntries: 0, MaxEntries: 0,
        KeyPattern: key, ValuePattern: value);
      return true;
    }
    if (expected.AsSetType is { Finite: true } set &&
        TryCreateBaseline(set.Arg, bounds, depth + 1, activeDatatypes, out var setElement)) {
      pattern = new(ContractInputPatternKind.Set, MinSize: 0, MaxSize: 0, Element: setElement);
      return true;
    }
    if (expected.AsMultiSetType is { } multiset &&
        TryCreateBaseline(multiset.Arg, bounds, depth + 1, activeDatatypes, out var multisetElement)) {
      pattern = new(ContractInputPatternKind.Multiset, MinSize: 0, MaxSize: 0, Element: multisetElement);
      return true;
    }
    if (expected.AsDatatype is { } datatype && depth < bounds.MaxDatatypeDepth &&
        activeDatatypes.Add(datatype)) {
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, expected.TypeArgs);
      foreach (var constructor in datatype.Ctors) {
        var fields = new Dictionary<string, ContractInputPattern>(StringComparer.Ordinal);
        var complete = true;
        foreach (var formal in constructor.Formals) {
          if (!TryCreateBaseline(formal.Type.Subst(substitution), bounds, depth + 1,
                activeDatatypes, out var field)) {
            complete = false;
            break;
          }
          fields.Add(formal.Name, field);
        }
        if (complete) {
          activeDatatypes.Remove(datatype);
          pattern = new(ContractInputPatternKind.Datatype,
            Constructor: datatype.Name + "." + constructor.Name,
            Fields: fields);
          return true;
        }
      }
      activeDatatypes.Remove(datatype);
    }
    if (expected.IsRefType && !expected.IsNonNullRefType) {
      pattern = new(ContractInputPatternKind.Null);
      return true;
    }
    pattern = null!;
    return false;
  }

  private static void ValidateDatatype(ContractInputPattern pattern, DafnyType expected,
    IDictionary<string, DafnyType> bindings, IList<(string Name, DafnyType Type)> pendingReuses,
    ContractGenerationBounds bounds) {
    var datatype = expected.AsDatatype ?? throw Mismatch(expected, pattern.Kind);
    var constructor = datatype.Ctors.SingleOrDefault(candidate => pattern.Constructor == candidate.FullName ||
      pattern.Constructor == datatype.Name + "." + candidate.Name ||
      pattern.Constructor == datatype.FullDafnyName + "." + candidate.Name || pattern.Constructor == candidate.Name);
    if (constructor == null || !constructor.Formals.Select(formal => formal.Name)
          .ToHashSet(StringComparer.Ordinal).SetEquals(pattern.Fields!.Keys)) {
      throw new ArgumentException("Datatype pattern constructor and fields do not match resolved type '" + expected + "'.");
    }
    var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, expected.TypeArgs);
    foreach (var formal in constructor.Formals) {
      Validate(pattern.Fields[formal.Name], formal.Type.Subst(substitution), bindings, pendingReuses, bounds);
    }
  }

  private static void ValidateReference(ContractInputPattern pattern, DafnyType expected,
    IDictionary<string, DafnyType> bindings, IList<(string Name, DafnyType Type)> pendingReuses,
    ContractGenerationBounds bounds) {
    var declaration = ReferenceClass(expected) ?? throw Mismatch(expected, pattern.Kind);
    if (pattern.Type != declaration.Name && pattern.Type != declaration.FullName &&
        pattern.Type != declaration.FullDafnyName) {
      throw new ArgumentException("Reference pattern type '" + pattern.Type +
        "' does not match resolved type '" + expected + "'.");
    }
    var fields = declaration.Members.OfType<Field>()
      .Where(field => field.Origin.line > 0 && !field.IsStatic).ToList();
    if (!fields.Select(field => field.Name).ToHashSet(StringComparer.Ordinal).SetEquals(pattern.Fields!.Keys)) {
      throw new ArgumentException("Reference pattern fields must exactly match class '" + declaration.FullDafnyName + "'.");
    }
    foreach (var field in fields) {
      Validate(pattern.Fields[field.Name], field.Type, bindings, pendingReuses, bounds);
    }
  }

  private static void ValidateValue(ContractValue value, DafnyType expected) {
    if (TryRefinedBaseType(expected, out var baseType)) {
      ValidateValue(value, baseType);
      return;
    }
    switch (value.Kind) {
      case ContractValueKind.Integer:
        Require(expected.IsIntegerType, expected, ContractInputPatternKind.Literal);
        return;
      case ContractValueKind.Bitvector:
        Require(expected.AsBitVectorType?.Width == value.Width, expected, ContractInputPatternKind.Literal);
        return;
      case ContractValueKind.Boolean:
        Require(expected.IsBoolType, expected, ContractInputPatternKind.Literal);
        return;
      case ContractValueKind.Character:
        Require(expected.IsCharType, expected, ContractInputPatternKind.Literal);
        return;
      case ContractValueKind.Sequence:
        if (expected.AsSeqType is not { } sequence) {
          throw Mismatch(expected, ContractInputPatternKind.Literal);
        }
        foreach (var item in value.Items!) {
          ValidateValue(item, sequence.Arg);
        }
        return;
      case ContractValueKind.Set:
        if (expected.AsSetType is not { Finite: true } set) {
          throw Mismatch(expected, ContractInputPatternKind.Literal);
        }
        foreach (var item in value.Items!) {
          ValidateValue(item, set.Arg);
        }
        return;
      case ContractValueKind.Multiset:
        if (expected.AsMultiSetType is not { } multiset) {
          throw Mismatch(expected, ContractInputPatternKind.Literal);
        }
        foreach (var item in value.Items!) {
          ValidateValue(item, multiset.Arg);
        }
        return;
      case ContractValueKind.Map:
        if (expected.AsMapType is not { Finite: true } map) {
          throw Mismatch(expected, ContractInputPatternKind.Literal);
        }
        foreach (var entry in value.Entries!) {
          ValidateValue(entry.Key, map.Domain);
          ValidateValue(entry.Value, map.Range);
        }
        return;
      case ContractValueKind.Datatype:
        var datatypePattern = new ContractInputPattern(ContractInputPatternKind.Datatype,
          Constructor: value.Constructor, Fields: value.Fields!.ToDictionary(field => field.Key,
            field => new ContractInputPattern(ContractInputPatternKind.Literal, Value: field.Value)));
        ValidateDatatype(datatypePattern, expected, new Dictionary<string, DafnyType>(),
          new List<(string Name, DafnyType Type)>(), new());
        return;
      case ContractValueKind.Reference:
        Require(expected.IsRefType, expected, ContractInputPatternKind.Literal);
        return;
      case ContractValueKind.Null:
        Require(expected.IsRefType && !expected.IsNonNullRefType, expected, ContractInputPatternKind.Literal);
        return;
      default:
        throw new ArgumentOutOfRangeException(nameof(value.Kind));
    }
  }

  private static ClassDecl? ReferenceClass(DafnyType type) => type.NormalizeExpand() is UserDefinedType user ?
    user.ResolvedClass switch {
      NonNullTypeDecl { Class: ClassDecl nonNull } => nonNull,
      ClassDecl nullable => nullable,
      _ => null
    } : null;

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

  private static void Require(bool condition, DafnyType expected, ContractInputPatternKind kind) {
    if (!condition) {
      throw Mismatch(expected, kind);
    }
  }

  private static ArgumentException Mismatch(DafnyType expected, ContractInputPatternKind kind) =>
    new("Pattern kind '" + kind + "' does not produce resolved Dafny type '" + expected + "'.");
}
