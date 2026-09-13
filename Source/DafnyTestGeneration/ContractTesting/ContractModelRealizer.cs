using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

public enum ContractRealizationStatus {
  Realized, CallPreconditionViolation, InconsistentContract, Unsupported, Inconclusive, Timeout, Error
}

public sealed record ContractRealizationResult(ContractRealizationStatus Status,
  IReadOnlyDictionary<string, ContractValue>? Outputs, IReadOnlyList<ContractQueryResult> Queries,
  string Reason, bool TypeFrameOnly = false, bool ExactUnboundedContradiction = false,
  bool ModelCompleted = false, IReadOnlyList<ContractHeapObject>? PostHeap = null);

/// <summary>Realizes an absent callable's relation using Dafny's existing Boogie model path.</summary>
public static partial class ContractModelRealizer {
  // Returned values are candidates. Callers must check the entire original relation
  // after materialization, including any primitive witnesses supplied for omitted slots.
  public static bool TryExtractModelValues(string diagnostics, DafnyOptions options,
    IReadOnlyList<(string Name, DafnyType Type)> variables,
    out IReadOnlyDictionary<string, ContractValue> values, out bool completedModel) =>
    TryExtractOutputs(diagnostics, options, variables.Select(variable =>
      new OutputFormal(variable.Name, variable.Type)).ToList(), out values, out completedModel);

  public static async Task<ContractRealizationResult> CheckPreconditionAsync(ContractPreparedProgram prepared,
    ContractTestRequest request, string childSymbol, IReadOnlyDictionary<string, ContractValue> inputs,
    CancellationToken cancellationToken, IReadOnlyList<ContractAbstractChoice>? priorChoices = null) {
    var callables = prepared.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<MethodOrFunction>()
      .Where(member => member.FullDafnyName == childSymbol || member.FullName == childSymbol).ToList();
    if (callables.Count != 1) {
      return new(ContractRealizationStatus.Error, null, [], "The call symbol does not identify one declaration.");
    }
    var child = callables[0];
    if (child.TypeArgs.Count > 0) {
      if (!prepared.ConcreteCalls.TryGetValue(child.FullDafnyName, out var concrete)) {
        return new(ContractRealizationStatus.Unsupported, null, [], "No resolved concrete type evidence exists for this call.");
      }
      child = concrete;
    }
    if (!child.IsStatic || child.TypeArgs.Count != 0 || request.Heap?.Count > 0 ||
        child.Ins.Any(formal => formal.IsGhost || !ContractHarnessBuilder.SupportedType(formal.Type))) {
      return new(ContractRealizationStatus.Unsupported, null, [],
        "This call precondition query requires static, monomorphic, observable inputs without heap state.");
    }
    if (!child.Ins.Select(formal => formal.Name).ToHashSet().SetEquals(inputs.Keys)) {
      return new(ContractRealizationStatus.Error, null, [], "Call input names do not match its formals.");
    }
    var precondition = Conjunction(child.Req.Select(clause => Printer.ExprToString(prepared.Program.Options, clause.E)));
    var choices = PureChoiceConstraints(prepared, priorChoices ?? [], child.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
    var queries = new List<ContractQueryResult>();
    async Task<ContractQueryResult> Check(string assertion, ContractQueryKind kind) {
      var source = QuerySource(prepared, child, inputs, [], assertion, precondition, "true",
        false, false, null, choices, bindFunctionResult: false);
      var result = await ContractSolver.CheckAsync(source, kind, prepared.Program.Options, cancellationToken,
        queryName: ContractQueryBuilder.Name(prepared), sourceSnapshots: prepared.SourceSnapshots,
        sourcePath: ContractSourceSnapshot.Find(prepared.SourceSnapshots, child.Origin.Uri).Path);
      queries.Add(result);
      return result;
    }
    ContractRealizationResult Unresolved(ContractQueryResult query) => new(
      query.Outcome switch {
        ContractQueryOutcome.Timeout => ContractRealizationStatus.Timeout,
        ContractQueryOutcome.Error => ContractRealizationStatus.Error,
        _ => ContractRealizationStatus.Inconclusive
      }, null, queries, "The original call precondition or its input premise could not be decided.");
    var premise = await Check("false", ContractQueryKind.PremiseConsistency);
    if (premise.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(premise);
    }
    var pre = await Check(precondition, ContractQueryKind.CallPrecondition);
    if (pre.Outcome == ContractQueryOutcome.Unsat) {
      return new(ContractRealizationStatus.Realized, null, queries,
        "The actual call inputs satisfy P; no body or output was modeled.");
    }
    if (pre.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(pre);
    }
    var opposite = await Check("!(" + precondition + ")", ContractQueryKind.CallPrecondition);
    return opposite.Outcome == ContractQueryOutcome.Unsat
      ? new(ContractRealizationStatus.CallPreconditionViolation, null, queries,
        "The actual call inputs violate the original precondition before body execution.")
      : Unresolved(opposite);
  }

  public static async Task<ContractRealizationResult> RealizeAsync(ContractPreparedProgram prepared,
    ContractTestRequest request, string childSymbol, IReadOnlyDictionary<string, ContractValue> inputs,
    CancellationToken cancellationToken, IReadOnlyList<ContractAbstractChoice>? priorChoices = null,
    IReadOnlyDictionary<string, ContractValue>? replayOutputs = null,
    IReadOnlyList<ContractHeapObject>? currentHeap = null,
    IReadOnlyList<ContractHeapObject>? replayHeap = null, ContractValue? receiver = null) {
    var callables = prepared.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<MethodOrFunction>()
      .Where(member => member.FullDafnyName == childSymbol || member.FullName == childSymbol).ToList();
    if (callables.Count != 1) {
      return new(ContractRealizationStatus.Error, null, [], "The child symbol does not identify one declaration.");
    }
    var child = callables[0];
    if ((child is Method { Body: not null } or Function { Body: not null }) &&
        !Attributes.Contains(child.Attributes, "extern")) {
      return new(ContractRealizationStatus.Error, null, [], "An existing body must execute, not use a contract model.");
    }
    if (child.TypeArgs.Count > 0) {
      if (!prepared.ConcreteCalls.TryGetValue(child.FullDafnyName, out var concrete)) {
        return new(ContractRealizationStatus.Unsupported, null, [], "No resolved concrete type evidence exists for this absent call.");
      }
      child = concrete;
    }
    if (currentHeap?.Count > 0 || request.Heap?.Count > 0 || receiver != null) {
      return await RealizeHeapAsync(prepared, request, child, inputs, cancellationToken, priorChoices,
        replayOutputs, currentHeap, replayHeap, receiver);
    }
    if (!child.IsStatic || child.TypeArgs.Count != 0 ||
        child is Method method && (method.Mod.Expressions?.Count > 0 || method.Reads.Expressions?.Count > 0) ||
        child is Function function && function.Reads.Expressions?.Count > 0 || request.Heap?.Count > 0) {
      return new(ContractRealizationStatus.Unsupported, null, [],
        "This realization slice supports static, monomorphic, heap-independent absent declarations.");
    }
    if (!child.Ins.Select(formal => formal.Name).ToHashSet().SetEquals(inputs.Keys)) {
      return new(ContractRealizationStatus.Error, null, [], "Child input names do not match its formals.");
    }

    var outputs = OutputFormals(child, prepared.Program);
    if (child.Ins.Any(formal => !ContractHarnessBuilder.SupportedType(formal.Type)) ||
        outputs.Any(formal => !ContractHarnessBuilder.SupportedType(formal.Type))) {
      return new(ContractRealizationStatus.Unsupported, null, [], "The child has unsupported model value types.");
    }
    var precondition = Conjunction(child.Req.Select(clause => Printer.ExprToString(prepared.Program.Options, clause.E)));
    var postcondition = Conjunction(child.Ens.Select(clause => Printer.ExprToString(prepared.Program.Options, clause.E)));
    var queries = new List<ContractQueryResult>();
    var choiceConstraints = PureChoiceConstraints(prepared, priorChoices ?? [],
      child.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);
    async Task<ContractQueryResult> Check(string assertion, bool includePostcondition = false,
      IReadOnlyDictionary<string, ContractValue>? observed = null, bool captureModel = false,
      bool includePrecondition = false, ContractQueryKind kind = ContractQueryKind.ContractRealization) {
      var source = QuerySource(prepared, child, inputs, outputs, assertion, precondition,
        postcondition, includePrecondition, includePostcondition, observed, choiceConstraints);
      var result = await ContractSolver.CheckAsync(source, kind, prepared.Program.Options,
        cancellationToken, captureModel, ContractQueryBuilder.Name(prepared), prepared.SourceSnapshots,
        ContractSourceSnapshot.Find(prepared.SourceSnapshots, child.Origin.Uri).Path);
      queries.Add(result);
      return result;
    }
    ContractRealizationResult Unresolved(ContractQueryResult query, string reason) => new(
      query.Outcome switch {
        ContractQueryOutcome.Timeout => ContractRealizationStatus.Timeout,
        ContractQueryOutcome.Error => ContractRealizationStatus.Error,
        _ => ContractRealizationStatus.Inconclusive
      }, null, queries, reason, child.Ens.Count == 0);

    var premise = await Check("false", kind: ContractQueryKind.PremiseConsistency);
    if (premise.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(premise, "The input/type/definition premise was not established satisfiable.");
    }
    var pre = await Check(precondition, kind: ContractQueryKind.CallPrecondition);
    if (pre.Outcome != ContractQueryOutcome.Unsat) {
      if (pre.Outcome == ContractQueryOutcome.Sat) {
        var opposite = await Check("!(" + precondition + ")", kind: ContractQueryKind.CallPrecondition);
        if (opposite.Outcome == ContractQueryOutcome.Unsat) {
          return new(ContractRealizationStatus.CallPreconditionViolation, null, queries,
            "The actual call inputs violate the original precondition.");
        }
        return Unresolved(opposite, "The call precondition is not determined by the fixed inputs.");
      }
      return Unresolved(pre, "The original call precondition could not be decided.");
    }

    IReadOnlyDictionary<string, ContractValue> values;
    var completedModel = false;
    if (replayOutputs != null) {
      if (!outputs.Select(formal => formal.Name).ToHashSet().SetEquals(replayOutputs.Keys)) {
        return new(ContractRealizationStatus.Error, null, queries, "Replay outputs do not match the original declaration.");
      }
      values = replayOutputs;
    } else {
      var realization = await Check("false", includePostcondition: true, captureModel: true,
        includePrecondition: true);
      if (realization.Outcome == ContractQueryOutcome.Unsat) {
        return new(ContractRealizationStatus.InconsistentContract, null, queries,
          "No output satisfies the original contract at these valid inputs; no generation bounds were added.",
          ExactUnboundedContradiction: true);
      }
      if (realization.Outcome != ContractQueryOutcome.Sat) {
        return Unresolved(realization, "The original output relation could not be solved.");
      }
      if (!TryExtractOutputs(realization.Diagnostics, prepared.Program.Options, outputs, out values,
            out completedModel)) {
        return new(ContractRealizationStatus.Inconclusive, null, queries,
          "The solver model does not expose a complete concrete output state; no defaults were substituted.",
          child.Ens.Count == 0);
      }
    }
    // The recheck deliberately removes the child's ensures from the assumptions.
    var concretePremise = await Check("false", observed: values, includePrecondition: true,
      kind: ContractQueryKind.PremiseConsistency);
    if (concretePremise.Outcome != ContractQueryOutcome.Sat) {
      return Unresolved(concretePremise, "The materialized output premise is not satisfiable.");
    }
    var recheck = await Check(postcondition, observed: values, includePrecondition: true);
    if (recheck.Outcome != ContractQueryOutcome.Unsat) {
      return Unresolved(recheck, "The materialized outputs did not establish the original relation.");
    }
    return new(ContractRealizationStatus.Realized, values, queries,
      completedModel
        ? "Missing primitive model values were completed with type witnesses and the entire original relation was rechecked."
        : "One contract model was materialized and rechecked; this is not an implementation test or proof.",
      child.Ens.Count == 0, ModelCompleted: completedModel);
  }

  private sealed record OutputFormal(string Name, DafnyType Type);

  // Purity comes from the resolved declaration, never from an untrusted runtime flag.
  // Equalities persist across calls and are also used by the caller's original Q query.
  public static IReadOnlyList<string> PureChoiceConstraints(ContractPreparedProgram prepared,
    IReadOnlyList<ContractAbstractChoice> choices, string? moduleName = null) {
    moduleName ??= prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName;
    var functions = prepared.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members).OfType<Function>()
      .Where(function => (function.Body == null || Attributes.Contains(function.Attributes, "extern")) && function.IsStatic &&
                         function.Reads.Expressions?.Count is null or 0).ToList();
    var constraints = new List<string>();
    foreach (var choice in choices.Where(choice => choice.Status == ContractRealizationStatus.Realized)) {
      var function = functions.SingleOrDefault(function => function.FullDafnyName == choice.Symbol ||
                                                          function.FullName == choice.Symbol);
      if (function == null) {
        continue;
      }
      var typeArguments = "";
      if (function.TypeArgs.Count > 0) {
        if (!prepared.ConcreteCalls.TryGetValue(function.FullDafnyName, out var concrete) ||
            !(choice.TypeArguments ?? []).SequenceEqual(concrete.ConcreteTypeArguments.Select(type => type.ToString()))) {
          throw new ArgumentException("A prior generic pure choice lacks matching concrete call-site type evidence.", nameof(choices));
        }
        typeArguments = "<" + string.Join(", ", concrete.ConcreteTypeArguments) + ">";
      }
      var resultName = ContractCallableSelector.FunctionResultName(prepared.Program, function);
      if (!function.Ins.Select(formal => formal.Name).ToHashSet().SetEquals(choice.Inputs.Keys) ||
          choice.Outputs == null || !choice.Outputs.TryGetValue(resultName, out var value)) {
        throw new ArgumentException("A prior pure choice does not match its resolved declaration.", nameof(choices));
      }
      var symbol = function.FullDafnyName;
      if (symbol.StartsWith(moduleName + ".", StringComparison.Ordinal)) {
        symbol = symbol[(moduleName.Length + 1)..];
      }
      constraints.Add(symbol + typeArguments + "(" + string.Join(", ", function.Ins.Select(formal =>
        ContractModelCodec.ToDafny(choice.Inputs[formal.Name], moduleName))) + ") == " +
        ContractModelCodec.ToDafny(value, moduleName));
    }
    return constraints;
  }

  private static List<OutputFormal> OutputFormals(MethodOrFunction child, Program program) => child switch {
    Method method => method.Outs.Select(formal => new OutputFormal(formal.Name, formal.Type)).ToList(),
    Function function => [new OutputFormal(ContractCallableSelector.FunctionResultName(program, function), function.ResultType)],
    _ => throw new ArgumentException("Expected a method or function.", nameof(child))
  };

  private static string QuerySource(ContractPreparedProgram prepared, MethodOrFunction child,
    IReadOnlyDictionary<string, ContractValue> inputs, IReadOnlyList<OutputFormal> outputs,
    string assertion, string precondition, string postcondition, bool includePrecondition,
    bool includePostcondition, IReadOnlyDictionary<string, ContractValue>? observed,
    IReadOnlyList<string> choiceConstraints, bool bindFunctionResult = true) {
    var parameters = child.Ins.Select(formal => formal.Name + ": " + formal.Type)
      .Concat(outputs.Select(formal => formal.Name + ": " + formal.Type));
    var moduleName = child.EnclosingClass.EnclosingModuleDefinition.FullDafnyName;
    var assumptions = child.Ins.Select(formal => formal.Name + " == " + ContractModelCodec.ToDafny(inputs[formal.Name], moduleName)).ToList();
    assumptions.AddRange(choiceConstraints);
    if (observed != null) {
      assumptions.AddRange(outputs.Select(formal => formal.Name + " == " + ContractModelCodec.ToDafny(observed[formal.Name], moduleName)));
    }
    if (includePrecondition) {
      assumptions.Add(precondition);
    }
    if (includePostcondition) {
      assumptions.Add(postcondition);
    }
    var function = child as Function ?? (child as ContractConcreteMethod)?.OriginalCallable as Function;
    if (bindFunctionResult && function != null && (includePostcondition || child is Function { Result: null })) {
      var typeArguments = child is ContractConcreteMethod concrete ? "<" + string.Join(", ", concrete.ConcreteTypeArguments) + ">" : "";
      assumptions.Add(outputs[0].Name + " == " + child.Name + typeArguments + "(" + string.Join(", ", child.Ins.Select(formal => formal.Name)) + ")");
    }
    var declaration = $"\nghost method {ContractQueryBuilder.Name(prepared)}({string.Join(", ", parameters)})\n" +
      string.Join("\n", assumptions.Select(assumption => "requires " + assumption)) +
      $"\n{{ assert {{:error \"{ContractQueryBuilder.TargetMarker}\"}} {assertion}; }}\n";
    return ContractSourceSnapshot.Find(prepared.SourceSnapshots, child.Origin.Uri).Content.Insert(child.StartToken.pos, declaration);
  }

  private static string Conjunction(IEnumerable<string> expressions) {
    var parts = expressions.Select(expression => "(" + expression + ")").ToList();
    return parts.Count == 0 ? "true" : string.Join(" && ", parts);
  }

  private static bool TryExtractOutputs(string diagnostics, DafnyOptions options,
    IReadOnlyList<OutputFormal> outputs, out IReadOnlyDictionary<string, ContractValue> values,
    out bool completedModel) {
    values = new Dictionary<string, ContractValue>();
    completedModel = false;
    if (outputs.Count == 0) {
      return true;
    }
    if (!diagnostics.Contains("*** MODEL", StringComparison.Ordinal) ||
        !diagnostics.Contains("*** END_MODEL", StringComparison.Ordinal)) {
      return false;
    }
    var model = DafnyModel.ExtractModel(options, diagnostics);
    foreach (var state in model.States.AsEnumerable().Reverse()) {
      var result = new Dictionary<string, ContractValue>();
      foreach (var output in outputs) {
        var candidates = state.KnownVariableNames.Where(pair => pair.Value.Contains(output.Name)).Select(pair => pair.Key).ToList();
        if (candidates.Count != 1 || !TryValue(candidates[0], output.Type, options, out var concrete)) {
          break;
        }
        result.Add(output.Name, concrete);
      }
      if (result.Count == outputs.Count) {
        values = result;
        return true;
      }
    }
    // A model may omit an irrelevant output entirely. Completion creates a candidate,
    // never an accepted output: RealizeAsync still checks its satisfiable premise and Q
    // without assuming Q. Prefer fully decoded states above before considering witnesses.
    foreach (var state in model.States.AsEnumerable().Reverse()) {
      var result = new Dictionary<string, ContractValue>();
      foreach (var output in outputs) {
        var candidates = state.KnownVariableNames.Where(pair => pair.Value.Contains(output.Name)).Select(pair => pair.Key).ToList();
        if (candidates.Count == 1 && TryValue(candidates[0], output.Type, options, out var concrete)) {
          result.Add(output.Name, concrete);
        } else if (candidates.Count <= 1 && TryPrimitiveWitness(output.Type, out var witness)) {
          result.Add(output.Name, witness);
        } else {
          break;
        }
      }
      if (result.Count == outputs.Count) {
        values = result;
        completedModel = true;
        return true;
      }
    }
    return false;
  }

  private static bool TryPrimitiveWitness(DafnyType type, out ContractValue witness) {
    witness = type.NormalizeToAncestorType() switch {
      IntType => new(ContractValueKind.Integer, "0"),
      BitvectorType bitvector => new(ContractValueKind.Bitvector, "0", Width: bitvector.Width),
      BoolType => new(ContractValueKind.Boolean, "false"),
      CharType => new(ContractValueKind.Character, "\0"),
      SeqType => new(ContractValueKind.Sequence, Items: []),
      SetType { Finite: true } => new(ContractValueKind.Set, Items: []),
      MultiSetType => new(ContractValueKind.Multiset, Items: []),
      MapType { Finite: true } => new(ContractValueKind.Map, Entries: []),
      _ => null!
    };
    return witness != null;
  }

  private static bool TryValue(PartialValue value, DafnyType expectedType, DafnyOptions options,
    out ContractValue concrete, int depth = 0) {
    concrete = null!;
    if (depth > 64) {
      return false;
    }
    if (expectedType.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: SubsetTypeDecl subset
    } subsetType) {
      return TryValue(value, subset.RhsWithArgument(subsetType.TypeArgs), options, out concrete, depth + 1);
    }
    if (expectedType.NormalizeExpandKeepConstraints() is UserDefinedType {
      ResolvedClass: NewtypeDecl newtype
    } newtypeType) {
      return TryValue(value, newtype.ConcreteBaseType(newtypeType.TypeArgs), options, out concrete, depth + 1);
    }
    // Expansion exposes the model's own constraints without assigning arbitrary primitive values.
    _ = value.GetRelatedValues().ToList();
    // Collection expansion creates related length/index values lazily. Their literal
    // constraints must be expanded before Cardinality() and the sequence indexer read them.
    foreach (var cardinality in value.Constraints.OfType<CardinalityConstraint>().ToList()) {
      _ = cardinality.DefinedValue.GetRelatedValues().ToList();
    }
    foreach (var selection in value.Constraints.OfType<SeqSelectExprConstraint>().ToList()) {
      _ = selection.Index.GetRelatedValues().ToList();
    }
    var literal = value.Constraints.OfType<LiteralExprConstraint>().Select(constraint => constraint.LiteralExpr).FirstOrDefault();
    if (expectedType.AsBitVectorType is { } bitvector &&
        literal is LiteralExpr { Value: BigInteger bitvectorValue } && bitvectorValue >= 0 &&
        bitvectorValue < BigInteger.One << bitvector.Width) {
      concrete = new(ContractValueKind.Bitvector, bitvectorValue.ToString(CultureInfo.InvariantCulture),
        Width: bitvector.Width);
      return true;
    }
    switch (literal) {
      case NegationExpression { E: LiteralExpr { Value: BigInteger magnitude } }:
        concrete = new(ContractValueKind.Integer, (-magnitude).ToString(CultureInfo.InvariantCulture));
        return true;
      case CharLiteralExpr { Value: string encodedCharacter }: {
          var points = Util.UnescapedCharacters(options, encodedCharacter, false).ToList();
          if (points.Count != 1) {
            return false;
          }
          concrete = new(ContractValueKind.Character, char.ConvertFromUtf32(points[0]));
          return true;
        }
      case LiteralExpr { Value: BigInteger integer }:
        concrete = new(ContractValueKind.Integer, integer.ToString(CultureInfo.InvariantCulture));
        return true;
      case LiteralExpr { Value: bool boolean }:
        concrete = new(ContractValueKind.Boolean, boolean ? "true" : "false");
        return true;
    }
    if (expectedType.AsSeqType is { } sequence && value.Cardinality() is >= 0 and <= 1024 and var length) {
      var items = new List<ContractValue>();
      for (var index = 0; index < length; index++) {
        if (value[index] is not { } item || !TryValue(item, sequence.Arg, options, out var converted, depth + 1)) {
          return false;
        }
        items.Add(converted);
      }
      concrete = new(ContractValueKind.Sequence, Items: items);
      return true;
    }
    if (expectedType.AsSetType is { Finite: true } set) {
      var items = new List<ContractValue>();
      foreach (var element in value.Constraints.OfType<ContainmentConstraint>()
                 .Where(constraint => constraint.IsIn && Equals(constraint.Set, value))
                 .Select(constraint => constraint.Element)) {
        _ = element.GetRelatedValues().ToList();
        if (!TryValue(element, set.Arg, options, out var converted, depth + 1)) {
          return false;
        }
        if (!items.Any(item => ContractModelCodec.ValuesEqual(item, converted))) {
          items.Add(converted);
        }
      }
      concrete = new(ContractValueKind.Set, Items: items);
      return true;
    }
    if (expectedType.AsMultiSetType is { } multiset) {
      var items = new List<ContractValue>();
      foreach (var element in value.MultiSetElements()) {
        _ = element.GetRelatedValues().ToList();
        if (!TryValue(element, multiset.Arg, options, out var converted, depth + 1)) {
          return false;
        }
        items.Add(converted);
      }
      if (items.Count == 0 && value.Cardinality() != 0) {
        return false;
      }
      concrete = new(ContractValueKind.Multiset, Items: items);
      return true;
    }
    if (expectedType.AsMapType is { Finite: true } map) {
      var entries = new List<ContractMapEntry>();
      foreach (var mapping in value.Mappings()) {
        _ = mapping.Key.GetRelatedValues().ToList();
        _ = mapping.Value.GetRelatedValues().ToList();
        if (!TryValue(mapping.Key, map.Domain, options, out var key, depth + 1) ||
            !TryValue(mapping.Value, map.Range, options, out var mapped, depth + 1)) {
          return false;
        }
        entries.Add(new(key, mapped));
      }
      if (ContractModelCodec.HasDuplicateMapKeys(entries)) {
        return false;
      }
      concrete = new(ContractValueKind.Map, Entries: entries);
      return true;
    }
    if (expectedType.NormalizeExpand() is UserDefinedType { ResolvedClass: IndDatatypeDecl datatype } userType) {
      var constructor = datatype.Ctors.SingleOrDefault(candidate => candidate.Name == value.DatatypeConstructorName());
      if (constructor == null || constructor.Formals.Any(formal => formal.IsGhost)) {
        return false;
      }
      var modelFields = value.Fields();
      var unnamedFields = value.UnnamedDestructors().ToList();
      var typeArguments = datatype.TypeArgs.Zip(userType.TypeArgs).ToDictionary(pair => pair.First, pair => pair.Second);
      var fields = new Dictionary<string, ContractValue>();
      for (var index = 0; index < constructor.Formals.Count; index++) {
        var formal = constructor.Formals[index];
        PartialValue field;
        if (modelFields.TryGetValue(formal.Name, out var named)) {
          field = named;
        } else if (modelFields.Count == 0 && unnamedFields.Count == constructor.Formals.Count) {
          field = unnamedFields[index];
        } else {
          return false;
        }
        if (!TryValue(field, formal.Type.Subst(typeArguments), options, out var converted, depth + 1)) {
          return false;
        }
        fields.Add(formal.Name, converted);
      }
      concrete = new(ContractValueKind.Datatype, Constructor: datatype.FullDafnyName + "." + constructor.Name,
        Fields: fields);
      return true;
    }
    return false;
  }
}
