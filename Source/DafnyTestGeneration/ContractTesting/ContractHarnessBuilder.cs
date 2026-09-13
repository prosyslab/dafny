using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractPreparedProgram(Program Program, Method Method, ContractSource Source,
  ContractSourceLocation Location, ContractHeapPlan? Heap = null, MethodOrFunction? OriginalCallable = null,
  Method? ReachableTarget = null, IReadOnlyList<ContractSource>? Sources = null) {
  public IReadOnlyList<ContractSource> SourceSnapshots => Sources ?? [Source];
  public MethodOrFunction Callable => OriginalCallable ?? Method;
  public IReadOnlyList<Microsoft.Dafny.Type> ConcreteTypeArguments =>
    Method is ContractConcreteMethod concrete ? concrete.ConcreteTypeArguments : [];
  public IReadOnlyDictionary<TypeParameter, Microsoft.Dafny.Type> TypeSubstitution =>
    Method is ContractConcreteMethod concrete ? concrete.TypeSubstitution : new Dictionary<TypeParameter, Microsoft.Dafny.Type>();
  public IReadOnlyDictionary<string, ContractConcreteMethod> ConcreteCalls => ContractCallableSelector.ConcreteCalls(this);
  public string ReceiverName => ContractBodyNames.Family(Program, "contractReceiver");
}

public static class ContractHarnessBuilder {
  public const string MainName = "ContractDiagnosticMain";
  public const string BridgeName = "ContractDiagnosticBridge";
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
    if (request.Entry.ReachableReceiver != null) {
      ContractModelCodec.Validate(request.Entry.ReachableReceiver);
    }
    if (request.Entry.InputMode == ContractInputMode.EntryReachable
          ? string.IsNullOrWhiteSpace(request.Entry.ReachableFrom) || request.Entry.Receiver != null || request.Entry.ReachableInvocation < 0
          : request.Entry.ReachableFrom != null || request.Entry.ReachableReceiver != null || request.Entry.ReachableInvocation != 0) {
      throw new ArgumentException("Reachable mode requires an outer symbol, no unit receiver and a nonnegative invocation; unit mode does not accept reachability fields.");
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
    foreach (var choice in request.ReplayChoices ?? []) {
      if (choice == null || string.IsNullOrWhiteSpace(choice.Symbol) || choice.Inputs == null || choice.Outputs == null ||
          choice.Status != ContractRealizationStatus.Realized || choice.TypeArguments?.Any(string.IsNullOrWhiteSpace) == true) {
        throw new ArgumentException("Replay choices require a realized symbol, inputs and outputs.");
      }
      foreach (var value in choice.Inputs.Values.Concat(choice.Outputs.Values)) {
        ContractModelCodec.Validate(value);
      }
      if (choice.Receiver != null) {
        ContractModelCodec.Validate(choice.Receiver);
      }
      foreach (var item in (choice.PreHeap ?? []).Concat(choice.PostHeap ?? [])) {
        if (item == null || string.IsNullOrWhiteSpace(item.Id) || string.IsNullOrWhiteSpace(item.Type) || item.Fields == null) {
          throw new ArgumentException("Replay heap objects require an id, a type and fields.");
        }
        foreach (var value in item.Fields.Values) {
          ContractModelCodec.Validate(value);
        }
        ValidateArray(item);
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

  public static ContractPreparedProgram Prepare(Program program, ContractTestRequest request) {
    if (request.Entry.InputMode == ContractInputMode.EntryReachable) {
      var target = ContractCallableSelector.SelectMethod(program,
        new ContractEntry(request.Entry.Symbol, request.Entry.TypeArguments), requireConcreteReceiver: false);
      if (target is ContractConcreteMethod) {
        throw new NotSupportedException("Reachable generic invocation capture requires concrete type evidence from each outer call site.");
      }
      ValidateSignature(target);
      if (Attributes.Contains(target.Attributes, "extern")) {
        throw new NotSupportedException("Reachable external entry capture requires call-site return instrumentation.");
      }
      return Prepare(program, ExecutionRequest(request)) with { ReachableTarget = target };
    }
    var method = ContractCallableSelector.SelectMethod(program, request.Entry);
    if (!method.Ins.Select(input => input.Name).ToHashSet().SetEquals(request.Inputs.Keys)) {
      throw new ArgumentException("Input names must exactly match the selected declaration's formals.");
    }
    ValidateSignature(method);
    var source = ContractSourceSnapshot.Find(request.Sources, method.Origin.Uri);
    var heap = request.Heap?.Count > 0 ? ContractHeapFactory.Prepare(program, request) : null;
    if (!method.IsStatic && (heap == null || request.Heap!.SingleOrDefault(item => item.Id == request.Entry.Receiver!.Value)?.Type != method.EnclosingClass.FullDafnyName)) {
      throw new ArgumentException("The receiver must name a heap object of the selected callable's concrete class.");
    }
    return new ContractPreparedProgram(program, method, source,
      new ContractSourceLocation(source.Path, method.Origin.line, method.Origin.col, method.FullDafnyName, source.Sha256), heap,
      method is ContractConcreteMethod concrete ? concrete.OriginalCallable :
        method.FunctionFromWhichThisIsByMethodDecl ?? (MethodOrFunction)method, Sources: request.Sources);
  }

  public static ContractTestRequest ExecutionRequest(ContractTestRequest request) =>
    request.Entry.InputMode == ContractInputMode.EntryReachable
      ? request with { Entry = new ContractEntry(request.Entry.ReachableFrom!, Receiver: request.Entry.ReachableReceiver) }
      : request;

  private static void ValidateSignature(Method method) {
    if (method.Ins.Concat(method.Outs).Any(formal => formal.IsGhost || !SupportedType(formal.Type) && !formal.Type.IsRefType) ||
        method.FunctionFromWhichThisIsByMethodDecl == null && method.Reads.Expressions?.Count > 0) {
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

  public static string RuntimeSource(ContractPreparedProgram prepared, ContractTestRequest request) =>
    RuntimeSourceForFile(prepared, request, prepared.Source);

  public static IReadOnlyList<ContractSource> RuntimeSources(ContractPreparedProgram prepared, ContractTestRequest request) =>
    request.Sources.Select(snapshot => {
      var content = RuntimeSourceForFile(prepared, request, snapshot);
      return snapshot with { Content = content, Sha256 = Hash(content) };
    }).ToList();

  private static string RuntimeSourceForFile(ContractPreparedProgram prepared, ContractTestRequest request, ContractSource sourceSnapshot) {
    var requestedInvocation = request.Entry.ReachableInvocation;
    request = ExecutionRequest(request);
    if (prepared.Program.RawModules().SelectMany(module => module.TopLevelDecls)
        .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members)
        .Any(member => member.Name is MainName or BridgeName)) {
      throw new ArgumentException("Source declares a reserved diagnostic harness name.");
    }
    var arguments = string.Join(", ", prepared.Method.Ins.Select(formal => InputExpression(prepared, request, formal.Name)));
    var outputs = prepared.Method.Outs.Select((_, index) => ContractBodyNames.Family(prepared.Program, "contractOutput") + index).ToList();
    var invocationPrefix = ContractBodyNames.Family(prepared.Program, "contractInvocation");
    var returnPrefix = ContractBodyNames.Family(prepared.Program, "contractReturn");
    var modelName = ContractBodyNames.Family(prepared.Program, "contractModel");
    var target = !prepared.Method.IsStatic ? prepared.Heap!.ReferenceExpression(request.Entry.Receiver!.Value!) + "." :
      prepared.Method.EnclosingClass is DefaultClassDecl ? "" : prepared.Method.EnclosingClass.Name + ".";
    var typeArguments = prepared.ConcreteTypeArguments.Count == 0 ? "" :
      "<" + string.Join(", ", prepared.ConcreteTypeArguments) + ">";
    var call = (outputs.Count == 0 ? "" : "var " + string.Join(", ", outputs) + " := ") + target + prepared.Method.Name + typeArguments + "(" + arguments + ");";
    var captures = string.Join("\n", prepared.Method.Outs.Select((formal, index) =>
      $"{BridgeName}.Capture(\"{formal.Name}\", {outputs[index]}, {TypeShapeLiteral(formal.Type)});"));
    var bridgeDeclaration = $"\nclass {{:extern \"DafnyContractRuntime\", \"ContractDiagnosticBridge\"}} {BridgeName} {{\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Capture\"} Capture<T>(name: string, value: T, shape: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Register\"} Register<T>(name: string, typeName: string, value: T, logicalBase64: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Snapshot\"} Snapshot(phase: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Begin\"} Begin(name: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Input\"} Input<T>(name: string, value: T, shape: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"End\"} End()\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"AssertionFailed\"} AssertionFailed()\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"EnterFrame\"} EnterFrame(name: string, frame: string)\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"ExitFrame\"} ExitFrame()\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Write\"} Write<T>(receiver: T, field: string): T\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"CheckPrecondition\"} CheckPrecondition(name: string, arguments: string): bool\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Trace\"} Trace(symbol: string, position: int, line: int, column: int, value: bool): bool\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Unreachable\"} Unreachable<T>(): T\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Serialize\"} Serialize<T>(value: T, shape: string): string\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Realize\"} Realize(name: string, arguments: string, pure: bool): string\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Output\"} Output<T>(realization: string, outputName: string): T\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"Choose\"} Choose<T>(name: string, arguments: string, outputName: string, pure: bool): T\n}\n";
    bridgeDeclaration = bridgeDeclaration[..^2] +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"StartTarget\"} StartTarget(symbol: string, arguments: string, invocation: int): int\n" +
      "static method {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"EndTarget\"} EndTarget(token: int, outputs: string)\n" +
      "static function {:extern \"DafnyContractRuntime.ContractDiagnosticBridge\", \"EndTargetValue\"} EndTargetValue<T>(token: int, outputName: string, value: T, shape: string): T\n}\n";
    var declarations =
      $"method {MainName}() {{\n{prepared.Heap?.AllocationStatements}\n" +
      string.Join("\n", (request.Heap ?? []).Select(item => $"{BridgeName}.Register(\"{item.Id}\", \"{item.Type}\", {prepared.Heap!.ReferenceExpression(item.Id)}, \"{prepared.Heap.LogicalFieldsBase64(item.Id)}\");")) +
      $"\n{BridgeName}.Snapshot(\"initial\");\n{call}\n{BridgeName}.Snapshot(\"final\");\n{captures}\n}}\n";
    var sourceUri = ContractSourceSnapshot.UriFor(sourceSnapshot.Path);
    var edits = new List<(int Position, string Text)>();
    if (sourceUri == prepared.Method.Origin.Uri) {
      edits.Add((InsertionPosition(prepared), declarations));
    }
    var replacements = new List<(int Position, int Length, string Text)>();
    var directReplacements = new List<(int Position, int Length, string Text)>();
    var returnWrappers = new Dictionary<int, (string Prefix, string Suffix)>();
    var functionWrappers = new List<(int Position, int Length, string Prefix, string Suffix)>();
    var instrumentedWrites = new HashSet<(int Start, int End)>();
    var tracedGuards = new HashSet<(string Symbol, int Start, int End)>();
    var reachable = ReachableCallables(prepared);
    // The runtime bridge can observe compiled fields only.  Audit reachable
    // implementation bodies before applying instrumentation so a ghost heap
    // write cannot disappear and leave Q checked against a fabricated state.
    ContractLogicalEffectAnalyzer.EnsureExecutableHeapEffectsSupported(
      reachable.OfType<MethodOrFunction>());
    var concreteCalls = prepared.ConcreteCalls;
    var sourceUris = request.Sources.Select(snapshot => ContractSourceSnapshot.UriFor(snapshot.Path)).ToHashSet();
    var allSourceMembers = prepared.Program.RawModules().SelectMany(module => module.TopLevelDecls)
      .OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members)
      .Where(member => sourceUris.Contains(member.Origin.Uri) && member.Origin.line > 0)
      .SelectMany(member => member is Function { ByMethodDecl: { } byMethod } ? new MemberDecl[] { member, byMethod } : [member]).ToList();
    var sourceMembers = allSourceMembers.Where(member => member.Origin.Uri == sourceUri).ToList();
    foreach (var firstMember in allSourceMembers.GroupBy(member => member.EnclosingClass.EnclosingModuleDefinition).Select(group => group.First())
               .Where(member => member.Origin.Uri == sourceUri)) {
      edits.Add((firstMember.EnclosingClass is DefaultClassDecl ? firstMember.StartToken.pos : firstMember.EnclosingClass.StartToken.pos,
        bridgeDeclaration));
    }
    if (reachable.OfType<MethodOrFunction>().Any(callable => callable.Origin.line > 0 && !allSourceMembers.Contains(callable))) {
      throw new NotSupportedException("A reachable body is outside the immutable source snapshot.");
    }
    if (prepared.Heap != null) {
      edits.AddRange(prepared.Heap.SourceEdits.Where(edit => edit.SourceUri == sourceUri)
        .Select(edit => (edit.Position, edit.Text)));
    }
    foreach (var member in sourceMembers) {
      if (member is Method { FunctionFromWhichThisIsByMethodDecl: { } originalFunction } &&
          Attributes.Contains(originalFunction.Attributes, "extern")) {
        continue;
      }
      if (member is Method method && !method.IsGhost) {
        var isExternal = Attributes.Contains(method.Attributes, "extern");
        var isTarget = prepared.ReachableTarget == method || prepared.ReachableTarget?.FunctionFromWhichThisIsByMethodDecl?.ByMethodDecl == method;
        var invocationName = invocationPrefix + method.StartToken.pos;
        var methodEntry = "";
        var methodExit = "";
        var targetStart = isTarget ? $"var {invocationName} := {BridgeName}.StartTarget(\"{prepared.ReachableTarget!.FullDafnyName}\", {SerializedInputs(method.Ins, !method.IsStatic)}, {requestedInvocation});\n" : "";
        string TargetEnd(IEnumerable<string> values) => isTarget
          ? $"{BridgeName}.EndTarget({invocationName}, {SerializedValues(prepared.ReachableTarget!.Outs.Zip(values,
            (output, expression) => (output.Name, expression, output.Type)))});\n" : "";
        if (!reachable.Contains(method) && (isExternal || method.Body != null)) {
          continue;
        }
        if (isExternal) {
          RemoveExternAttribute(method);
        }
        if (method.Body != null && !isExternal) {
          if (method.Body.Descendants().Any(node => node is AllocateClass or AllocateArray)) {
            throw new NotSupportedException("Dynamic allocation and constructor frame tracking is not implemented at " + method.FullDafnyName);
          }
          foreach (var statement in method.Body.Descendants().OfType<Statement>()) {
            if (statement is AssumeStmt) {
              throw new NotSupportedException("Explicit assume requires trust tracking at " + method.FullDafnyName);
            }
            if (statement is AssertStmt assertion) {
              if (ExpressionTester.UsesSpecFeatures(assertion.Expr)) {
                throw new NotSupportedException("Ghost body assertion observation is not implemented at " + method.FullDafnyName);
              }
              edits.Add((assertion.StartToken.pos, "if !(" + Printer.ExprToString(prepared.Program.Options, assertion.Expr) +
                $") {{ {BridgeName}.AssertionFailed(); }}\n"));
            }
            if (!statement.IsGhost) {
              if (statement is IfStmt { IsBindingGuard: false, Guard: { } condition }) {
                Trace(condition, method.FullDafnyName);
              } else if (statement is WhileStmt { Guard: { } loopCondition }) {
                Trace(loopCondition, method.FullDafnyName);
              }
              if (statement is TryRecoverStatement or ModifyStmt or AssignOrReturnStmt) {
                throw new NotSupportedException("Frame scope recovery for this statement is not implemented at " + method.FullDafnyName);
              }
              IEnumerable<Expression> lhs = statement switch {
                AssignStatement assignment => assignment.Lhss,
                SingleAssignStmt assignment => [assignment.Lhs],
                CallStmt callStatement => callStatement.Lhs,
                _ => []
              };
              foreach (var assignmentTarget in lhs) {
                if (assignmentTarget.Resolved is SeqSelectExpr { SelectOne: true } arrayElement && arrayElement.Seq.Type.IsArrayType) {
                  var arrayRange = arrayElement.Seq.EntireRange;
                  var arrayStart = arrayRange.StartToken.pos;
                  var arrayEnd = arrayStart + arrayRange.Length;
                  if (instrumentedWrites.Add((arrayStart, arrayEnd))) {
                    edits.Add((arrayStart, BridgeName + ".Write(("));
                    edits.Add((arrayEnd, "), \"element\")"));
                  }
                  continue;
                }
                if (assignmentTarget.Resolved is not MemberSelectExpr { Member: Field field } selected || field.IsGhost) {
                  continue;
                }
                var range = selected.Obj.EntireRange;
                var start = range.StartToken.pos;
                var end = start + range.Length;
                if (selected.Obj is ImplicitThisExpr) {
                  var position = assignmentTarget.EntireRange.StartToken.pos;
                  if (instrumentedWrites.Add((position, position))) {
                    edits.Add((position, $"{BridgeName}.Write(this, \"{field.Name}\")."));
                  }
                  continue;
                }
                if (start < assignmentTarget.StartToken.pos || end > assignmentTarget.EndToken.pos) {
                  throw new NotSupportedException("The field write has no explicit receiver source range at " + method.FullDafnyName);
                }
                if (instrumentedWrites.Add((start, end))) {
                  edits.Add((start, BridgeName + ".Write(("));
                  edits.Add((end, $"), \"{field.Name}\")"));
                }
              }
              if (statement is ReturnStmt returned) {
                if (returned.Rhss?.Count > 0) {
                  var range = returned.EntireRange;
                  var text = prepared.Source.Content.Substring(range.StartToken.pos, range.Length);
                  if (!text.StartsWith("return", StringComparison.Ordinal) || !text.TrimEnd().EndsWith(';')) {
                    throw new NotSupportedException("The return has no complete source range at " + method.FullDafnyName);
                  }
                  if (method.Outs.Any(output => output.IsGhost)) {
                    throw new NotSupportedException("Mixed ghost return frame scope is not implemented at " + method.FullDafnyName);
                  }
                  var temporaries = method.Outs.Select((output, index) => (Name: returnPrefix + range.StartToken.pos + "_" + index, output.Type)).ToList();
                  returnWrappers.Add(range.StartToken.pos, (
                    "{ var " + string.Join(", ", temporaries.Select(output => output.Name + ": " + output.Type)) + " := ",
                    " " + TargetEnd(temporaries.Select(output => output.Name)) + $" {BridgeName}.ExitFrame(); return " + string.Join(", ", temporaries.Select(output => output.Name)) + "; }"));
                  replacements.Add((range.StartToken.pos, range.Length, ""));
                } else {
                  edits.Add((returned.StartToken.pos, TargetEnd(method.Outs.Select(output => output.Name)) + BridgeName + ".ExitFrame();\n"));
                }
              }
            }
          }
          foreach (var conditional in method.Body.Descendants().OfType<ITEExpr>().Where(expression => !expression.IsBindingGuard)) {
            Trace(conditional.Test, method.FullDafnyName);
          }
          {
            var frame = method.Mod.Expressions ?? [];
            if (frame.Any(expression => expression.FieldName != null || ExpressionTester.UsesSpecFeatures(expression.E))) {
              throw new NotSupportedException("Unsupported runtime frame expression at " + method.FullDafnyName);
            }
            var frameValues = frame.Select(expression => BridgeName + ".Serialize(" +
              Printer.ExprToString(prepared.Program.Options, expression.E) + ", " + OtherTypeShapeLiteral + ")").ToList();
            var frameJson = frameValues.Count == 0 ? "\"[]\"" : "\"[\" + " + string.Join(" + \",\" + ", frameValues) + " + \"]\"";
            methodEntry = $"\n{BridgeName}.EnterFrame(\"{method.FullDafnyName}\", {frameJson});\n";
            methodExit = "\n" + BridgeName + ".ExitFrame();\n";
          }
        }
        if (method.Body == null || isExternal) {
          if (method.Outs.Any(formal => !SupportedType(ConcreteType(method, formal.Type)))) {
            throw new NotSupportedException("Unsupported absent-body result type at " + method.FullDafnyName);
          }
          var returns = method.Outs.Select(formal => $"{formal.Name} := {BridgeName}.Output<{formal.Type}>({modelName}, \"{formal.Name}\");");
          var modelBody = " { " + targetStart +
            $"var {modelName} := {BridgeName}.Realize(\"{method.FullDafnyName}\", {SerializedInputs(method.Ins, !method.IsStatic)}, false); " +
            string.Join(" ", returns) + TargetEnd(method.Outs.Select(output => output.Name)) + " }\n";
          if (method.Body == null) {
            edits.Add((method.EndToken.pos + method.EndToken.val.Length, modelBody));
          } else {
            var range = method.Body.EntireRange;
            directReplacements.Add((range.StartToken.pos, range.Length, modelBody));
          }
        } else if (method.Body != null && method.Req.Count > 0 && !method.IsByMethod) {
          if (method.Ins.Any(formal => formal.IsGhost || !SupportedType(ConcreteType(method, formal.Type)) && !formal.Type.IsRefType)) {
            throw new NotSupportedException("Unsupported call precondition input at " + method.FullDafnyName);
          }
          var argumentsToCapture = (method.IsStatic ? "" : $"{BridgeName}.Input(\"$this\", this, {OtherTypeShapeLiteral});\n") + string.Join("\n", method.Ins.Select(formal =>
            $"{BridgeName}.Input(\"{formal.Name}\", {formal.Name}, {TypeShapeLiteral(formal.Type)});"));
          methodEntry = $"\n{BridgeName}.Begin(\"{method.FullDafnyName}\");\n{argumentsToCapture}\n{BridgeName}.End();\n" + methodEntry;
        }
        if (isTarget && method.Body != null && !isExternal) {
          methodEntry = "\n" + targetStart + methodEntry;
          if (method.Outs.All(output => !output.Name.StartsWith('#'))) {
            methodExit = "\n" + TargetEnd(method.Outs.Select(output => output.Name)) + methodExit;
          }
        }
        if (method.Body != null && !isExternal) {
          if (method.Body.StartToken.pos + 1 == method.Body.EndToken.pos) {
            edits.Add((method.Body.EndToken.pos, methodEntry + methodExit));
          } else {
            edits.Add((method.Body.StartToken.pos + 1, methodEntry));
            edits.Add((method.Body.EndToken.pos, methodExit));
          }
        }
      } else if (member is Function function && !function.IsGhost) {
        var isExternal = Attributes.Contains(function.Attributes, "extern");
        var isTarget = prepared.ReachableTarget?.FunctionFromWhichThisIsByMethodDecl == function && function.ByMethodBody == null;
        var invocationName = invocationPrefix + function.StartToken.pos;
        var targetPrefix = isTarget ? $"var {invocationName} := {BridgeName}.StartTarget(\"{function.FullDafnyName}\", {SerializedInputs(function.Ins, !function.IsStatic)}, {requestedInvocation}); " +
          $"{BridgeName}.EndTargetValue({invocationName}, \"{prepared.ReachableTarget!.Outs.Single().Name}\", (" : "";
        var targetSuffix = isTarget ? $"), {TypeShapeLiteral(prepared.ReachableTarget!.Outs.Single().Type)})" : "";
        if (!reachable.Contains(function) && (isExternal || function.Body != null)) {
          continue;
        }
        if (isExternal) {
          RemoveExternAttribute(function);
        }
        if (function.Body == null || isExternal) {
          var modelBody = " { " + targetPrefix +
            $"{BridgeName}.Choose<{function.ResultType}>(\"{function.FullDafnyName}\", {SerializedInputs(function.Ins, !function.IsStatic)}, \"{ContractCallableSelector.FunctionResultName(prepared.Program, function)}\", true)" +
            targetSuffix + " }\n";
          if (function.Body == null) {
            edits.Add((function.EndToken.pos + function.EndToken.val.Length, modelBody));
          } else {
            var start = function.BodyStartTok.pos;
            directReplacements.Add((start, function.EndToken.pos + function.EndToken.val.Length - start, modelBody));
          }
        } else if (function.Body != null && function.Req.Count > 0) {
          if (function.Ins.Any(formal => formal.IsGhost || !SupportedType(ConcreteType(function, formal.Type)) && !formal.Type.IsRefType)) {
            throw new NotSupportedException("Unsupported actual function precondition inputs at " + function.FullDafnyName);
          }
          if (function.ByMethodBody != null) {
            var inputs = (function.IsStatic ? "" : $"{BridgeName}.Input(\"$this\", this, {OtherTypeShapeLiteral});\n") + string.Join("\n", function.Ins.Select(formal =>
              $"{BridgeName}.Input(\"{formal.Name}\", {formal.Name}, {TypeShapeLiteral(formal.Type)});"));
            edits.Add((function.ByMethodBody.StartToken.pos + 1,
              $"\n{BridgeName}.Begin(\"{function.FullDafnyName}\");\n{inputs}\n{BridgeName}.End();\n"));
          } else {
            var range = function.Body.EntireRange;
            edits.Add((range.StartToken.pos, $"if {BridgeName}.CheckPrecondition(\"{function.FullDafnyName}\", {SerializedInputs(function.Ins, !function.IsStatic)}) then ("));
            edits.Add((range.StartToken.pos + range.Length, $") else {BridgeName}.Unreachable<{function.ResultType}>()"));
          }
        }
        if (function.Body != null && function.ByMethodBody == null && !isExternal) {
          if (isTarget) {
            var range = function.Body.EntireRange;
            functionWrappers.Add((range.StartToken.pos, range.Length, targetPrefix, targetSuffix));
          }
          foreach (var conditional in new[] { function.Body }.Concat(function.Body.Descendants().OfType<Expression>())
                     .OfType<ITEExpr>().Where(expression => !expression.IsBindingGuard)) {
            Trace(conditional.Test, function.FullDafnyName);
          }
        }
      }
    }
    var source = sourceSnapshot.Content;
    for (var index = 0; index < replacements.Count; index++) {
      var replacement = replacements[index];
      var original = source.Substring(replacement.Position, replacement.Length);
      var nested = edits.Where(edit => edit.Position > replacement.Position && edit.Position < replacement.Position + replacement.Length).ToList();
      foreach (var edit in nested.OrderByDescending(edit => edit.Position)) {
        original = original.Insert(edit.Position - replacement.Position, edit.Text);
        edits.Remove(edit);
      }
      var wrapper = returnWrappers[replacement.Position];
      replacements[index] = (replacement.Position, replacement.Length, wrapper.Prefix + original["return".Length..] + wrapper.Suffix);
    }
    foreach (var wrapper in functionWrappers) {
      var original = source.Substring(wrapper.Position, wrapper.Length);
      foreach (var edit in edits.Where(edit => edit.Position >= wrapper.Position && edit.Position <= wrapper.Position + wrapper.Length)
                 .OrderByDescending(edit => edit.Position).ToList()) {
        original = original.Insert(edit.Position - wrapper.Position, edit.Text);
        edits.Remove(edit);
      }
      replacements.Add((wrapper.Position, wrapper.Length, wrapper.Prefix + original + wrapper.Suffix));
    }
    foreach (var (position, length, text) in edits.Select(edit => (edit.Position, Length: 0, edit.Text)).Concat(replacements).Concat(directReplacements)
               .OrderByDescending(edit => edit.Position).ThenByDescending(edit => edit.Length)) {
      source = source.Remove(position, length).Insert(position, text);
    }
    return source;

    Microsoft.Dafny.Type ConcreteType(MethodOrFunction callable, Microsoft.Dafny.Type type) =>
      concreteCalls.TryGetValue((callable is Method { FunctionFromWhichThisIsByMethodDecl: { } function } ? function : callable).FullDafnyName,
        out var concrete) ? type.Subst(concrete.TypeSubstitution.ToDictionary(pair => pair.Key, pair => pair.Value)) : type;

    void Trace(Expression condition, string symbol) {
      if (ExpressionTester.UsesSpecFeatures(condition)) {
        return;
      }
      var range = condition.EntireRange;
      var token = range.StartToken;
      var end = token.pos + range.Length;
      if (tracedGuards.Add((symbol, token.pos, end))) {
        edits.Add((token.pos, $"{BridgeName}.Trace(\"{symbol}\", {token.pos}, {token.line}, {token.col}, ("));
        edits.Add((end, "))"));
      }
    }

    void RemoveExternAttribute(MemberDecl member) {
      if (Attributes.Find(member.Attributes, "extern") is not UserSuppliedAttributes attribute) {
        throw new NotSupportedException("The external declaration has no removable source attribute at " + member.FullDafnyName);
      }
      var start = attribute.OpenBrace.pos;
      directReplacements.Add((start, attribute.CloseBrace.pos + attribute.CloseBrace.val.Length - start, ""));
    }
  }

  public static string Insert(ContractPreparedProgram prepared, string declaration) =>
    prepared.Source.Content.Insert(InsertionPosition(prepared), declaration);

  private static int InsertionPosition(ContractPreparedProgram prepared) => prepared.Method.EnclosingClass is DefaultClassDecl
    ? prepared.Method.StartToken.pos : prepared.Method.EnclosingClass.StartToken.pos;

  public static string QualifiedDiagnosticName(ContractPreparedProgram prepared, string name) =>
    (prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName is { Length: > 0 } moduleName ? moduleName + "." : "") + name;

  public static string InputExpression(ContractPreparedProgram prepared, ContractTestRequest request, string name) =>
    prepared.Heap != null
      ? prepared.Heap.ValueExpression(request.Inputs[name], prepared.Method.Ins.Single(formal => formal.Name == name).Type)
      : ContractModelCodec.ToDafny(request.Inputs[name], prepared.Method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName);

  private static string SerializedInputs(IEnumerable<Formal> formals, bool receiver = false) {
    var parts = formals.Select(formal => "\"\\\"" + formal.Name + "\\\":\" + " + BridgeName + ".Serialize(" +
      formal.Name + ", " + TypeShapeLiteral(formal.Type) + ")").ToList();
    if (receiver) {
      parts.Add("\"\\\"$this\\\":\" + " + BridgeName + ".Serialize(this, " + OtherTypeShapeLiteral + ")");
    }
    return parts.Count == 0 ? "\"{}\"" : "\"{\" + " + string.Join(" + \",\" + ", parts) + " + \"}\"";
  }

  private static string SerializedValues(IEnumerable<(string Name, string Expression, Microsoft.Dafny.Type Type)> values) {
    var parts = values.Select(value => "\"\\\"" + value.Name + "\\\":\" + " + BridgeName + ".Serialize(" +
      value.Expression + ", " + TypeShapeLiteral(value.Type) + ")").ToList();
    return parts.Count == 0 ? "\"{}\"" : "\"{\" + " + string.Join(" + \",\" + ", parts) + " + \"}\"";
  }

  private const string OtherTypeShapeLiteral = "\"eyJraW5kIjoib3RoZXIifQ==\"";

  private static string TypeShapeLiteral(Microsoft.Dafny.Type type) =>
    "\"" + ContractStubRuntime.TypeShapeToken(type) + "\"";

  private static HashSet<ICallable> ReachableCallables(ContractPreparedProgram prepared) {
    var edges = prepared.Program.RawModules().SelectMany(module => module.CallGraph.GetVertices().Concat(module.InterModuleCallGraph.GetVertices()))
      .GroupBy(vertex => vertex.N).ToDictionary(group => group.Key, group => group.SelectMany(vertex => vertex.Successors).Select(vertex => vertex.N).Distinct().ToList());
    var reachable = new HashSet<ICallable>();
    var pending = new Stack<ICallable>();
    pending.Push((ICallable)prepared.Callable);
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
