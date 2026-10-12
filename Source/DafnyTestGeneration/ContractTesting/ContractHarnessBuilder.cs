using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractPreparedProgram(Program Program, Method Method, ContractSource Source,
  ContractSourceLocation Location, ContractHeapPlan? Heap = null, MethodOrFunction? OriginalCallable = null,
  IReadOnlyList<ContractSource>? Sources = null) {
  public IReadOnlyList<ContractSource> SourceSnapshots => Sources ?? [Source];
  public IReadOnlyList<ContractSource> DiagnosticSourceSnapshots =>
    ContractSourceSnapshot.ApplyEdits(SourceSnapshots, Heap?.QuerySourceEdits ?? []);
  public MethodOrFunction Callable => OriginalCallable ?? Method;
  public string ReceiverName => ContractBodyNames.Family(Program, "contractReceiver");
}

public static class ContractHarnessBuilder {
  private enum PreparationMode { InitialState, ObservedHeap }

  public static string Hash(string content) => Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(content))).ToLowerInvariant();

  public static void ValidateRequest(ContractTestRequest request) {
    if (request.SchemaVersion != ContractJson.SchemaVersion || request.Sources == null || request.Sources.Count == 0 ||
        request.Entry == null || string.IsNullOrWhiteSpace(request.Entry.Symbol) || request.Inputs == null ||
        request.TimeoutMilliseconds <= 0) {
      throw new ArgumentException("Invalid contract request version, sources, entry, inputs or deadline.");
    }
    foreach (var source in request.Sources) {
      if (source == null || string.IsNullOrWhiteSpace(source.Path) || source.Content == null || Hash(source.Content) != source.Sha256) {
        throw new ArgumentException("Source snapshot hash mismatch or missing path/content.");
      }
    }
    if (request.Sources.Select(source => ContractSourceSnapshot.UriFor(source.Path)).Distinct().Count() != request.Sources.Count) {
      throw new ArgumentException("Source snapshot paths must be unique.");
    }
    foreach (var value in request.Inputs.Values) {
      ContractModelCodec.Validate(value);
    }
    if (request.Entry.Receiver != null) {
      ContractModelCodec.Validate(request.Entry.Receiver);
    }
    if (request.Entry.TypeArguments?.Any(string.IsNullOrWhiteSpace) == true) {
      throw new ArgumentException("Explicit type arguments must contain Dafny type syntax.");
    }
    if (request.Entry.InputMode != ContractInputMode.Unit || request.Entry.ReachableFrom != null ||
        request.Entry.ReachableReceiver != null || request.Entry.ReachableInvocation != 0) {
      throw new ArgumentException("Reachable entry capture is not supported; entries must use unit mode without reachability fields.");
    }
    foreach (var item in request.Heap ?? []) {
      if (item == null || string.IsNullOrWhiteSpace(item.Id) || string.IsNullOrWhiteSpace(item.Type) || item.Fields == null) {
        throw new ArgumentException("Heap objects require an id, a resolved type name and a fields object.");
      }
      foreach (var value in item.Fields.Values) {
        ContractModelCodec.Validate(value);
      }
      ValidateArray(item);
    }
    foreach (var dependency in request.Dependencies ?? []) {
      if (dependency == null || string.IsNullOrWhiteSpace(dependency.Path) || string.IsNullOrWhiteSpace(dependency.Sha256)) {
        throw new ArgumentException("Dependencies require a path and content hash.");
      }
    }

    static void ValidateArray(ContractHeapObject item) {
      if (item.Dimensions != null || item.Elements != null) {
        if (item.Dimensions?.Count != 1 || item.Dimensions[0] < 0 || item.Elements == null ||
            item.Elements.Count != item.Dimensions[0] || item.Fields.Count != 0) {
          throw new ArgumentException("Array heap objects require one nonnegative dimension, exact elements and no fields.");
        }
        foreach (var value in item.Elements) {
          ContractModelCodec.Validate(value);
        }
      }
    }
  }

  public static ContractPreparedProgram PrepareInitial(Program program, ContractTestRequest request) =>
    Prepare(program, request, PreparationMode.InitialState);

  public static ContractPreparedProgram PrepareObservedHeap(Program program, ContractTestRequest request) =>
    Prepare(program, request, PreparationMode.ObservedHeap);

  private static ContractPreparedProgram Prepare(Program program, ContractTestRequest request, PreparationMode mode) {
    var method = ContractCallableSelector.SelectMethod(program, request.Entry, allowLemmaContract: mode == PreparationMode.InitialState);
    if (!method.Ins.Select(input => input.Name).ToHashSet().SetEquals(request.Inputs.Keys)) {
      throw new ArgumentException("Input names must exactly match the selected declaration's formals.");
    }
    ValidateSignature(method, mode);
    var source = ContractSourceSnapshot.Find(request.Sources, method.Origin.Uri);
    var heap = request.Heap?.Count > 0 ? ContractHeapFactory.PrepareFixedState(program, request) : null;
    if (!method.IsStatic && (heap == null || request.Heap!.SingleOrDefault(item => item.Id == request.Entry.Receiver!.Value)?.Type != method.EnclosingClass.FullDafnyName)) {
      throw new ArgumentException("The receiver must name a heap object of the selected callable's concrete class.");
    }
    return new ContractPreparedProgram(program, method, source,
      new ContractSourceLocation(source.Path, method.Origin.line, method.Origin.col, method.FullDafnyName, source.Sha256), heap,
      method is ContractConcreteMethod concrete ? concrete.OriginalCallable :
        method.FunctionFromWhichThisIsByMethodDecl ?? (MethodOrFunction)method, Sources: request.Sources);
  }

  private static void ValidateSignature(Method method, PreparationMode mode) {
    var inputUnsupported = method.Ins.Any(formal => !SupportedType(formal.Type) && !formal.Type.IsRefType);
    var outputUnsupported = mode != PreparationMode.InitialState && method.Outs.Any(formal =>
      formal.IsGhost || !SupportedType(formal.Type) && !formal.Type.IsRefType);
    if (inputUnsupported || outputUnsupported ||
        mode != PreparationMode.InitialState && method.FunctionFromWhichThisIsByMethodDecl == null && method.Reads.Expressions?.Count > 0) {
      throw new NotSupportedException("Unsupported ghost, type or heap-dependent entry signature.");
    }
  }

  public static bool SupportedType(Microsoft.Dafny.Type type) {
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } subsetType) {
      return SupportedType(subset.RhsWithArgument(subsetType.TypeArgs));
    }
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: NewtypeDecl newtype } newtypeType) {
      return SupportedType(newtype.ConcreteBaseType(newtypeType.TypeArgs));
    }
    return type.IsIntegerType || type.IsBoolType || type.IsCharType || type.IsDatatype ||
      type.IsBitVectorType ||
      type.AsSeqType is { } sequence && SupportedType(sequence.Arg) ||
      type.AsSetType is { Finite: true } set && SupportedType(set.Arg) ||
      type.AsMultiSetType is { } multiset && SupportedType(multiset.Arg) ||
      type.AsMapType is { Finite: true } map && SupportedType(map.Domain) && SupportedType(map.Range);
  }

  public static string Insert(ContractPreparedProgram prepared, string declaration) {
    var edits = (prepared.Heap?.QuerySourceEdits ?? []).Append(new ContractSourceEdit(
      ContractSourceSnapshot.UriFor(prepared.Source.Path), InsertionPosition(prepared), declaration)).ToList();
    return ContractSourceSnapshot.Find(ContractSourceSnapshot.ApplyEdits(prepared.SourceSnapshots, edits),
      ContractSourceSnapshot.UriFor(prepared.Source.Path)).Content;
  }

  private static int InsertionPosition(ContractPreparedProgram prepared) => prepared.Method.EnclosingClass is DefaultClassDecl
    ? prepared.Method.StartToken.pos : prepared.Method.EnclosingClass.StartToken.pos;

  public static string InputExpression(ContractPreparedProgram prepared, ContractTestRequest request, string name) =>
    prepared.Heap != null
      ? prepared.Heap.ValueExpression(request.Inputs[name], prepared.Method.Ins.Single(formal => formal.Name == name).Type)
      : ContractModelCodec.ToDafny(request.Inputs[name], prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);

  internal static HashSet<ICallable> ReachableCallables(Program program, MethodOrFunction entry) {
    var edges = program.RawModules().SelectMany(module => module.CallGraph.GetVertices().Concat(module.InterModuleCallGraph.GetVertices()))
      .GroupBy(vertex => vertex.N).ToDictionary(group => group.Key, group => group.SelectMany(vertex => vertex.Successors).Select(vertex => vertex.N).Distinct().ToList());
    var reachable = new HashSet<ICallable>();
    var pending = new Stack<ICallable>();
    pending.Push((ICallable)entry);
    while (pending.TryPop(out var callable)) {
      if (!reachable.Add(callable)) {
        continue;
      }
      if (callable is Function { ByMethodDecl: { } byMethod }) {
        pending.Push(byMethod);
      }
      foreach (var target in edges.GetValueOrDefault(callable) ?? []) {
        pending.Push(target);
      }
    }
    return reachable;
  }
}
