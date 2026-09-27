#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Detached source snapshots with a mapping back to their supplied source locations.</summary>
public sealed record ContractRuntimePreparedSources(IReadOnlyList<ContractSource> Sources,
  ContractRuntimeSourceMap SourceMap);

/// <summary>Tracks UTF-8 token positions through draft replacements and generator insertions.</summary>
public sealed class ContractRuntimeSourceMap {
  internal sealed record Segment(int Start, int Length, ContractSource Original, int OriginalStart, bool Anchor);
  private readonly IReadOnlyDictionary<Uri, IReadOnlyList<Segment>> segments;

  internal ContractRuntimeSourceMap(IReadOnlyDictionary<Uri, IReadOnlyList<Segment>> segments) {
    this.segments = segments;
  }

  public ContractSourceLocation ResolveLocation(Uri uri, int byteOffset, string symbol = "") {
    if (!segments.TryGetValue(uri, out var candidates) || byteOffset < 0) {
      throw new ArgumentException("The diagnostic source position has no supplied origin.");
    }
    var segment = candidates.LastOrDefault(item => item.Start <= byteOffset && byteOffset <= item.Start + item.Length)
      ?? throw new ArgumentException("The diagnostic source position is outside its snapshot.");
    var offset = segment.OriginalStart + (segment.Anchor ? 0 : byteOffset - segment.Start);
    var prefix = Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(segment.Original.Content), 0, offset);
    var line = prefix.Count(character => character == '\n') + 1;
    var column = prefix[(prefix.LastIndexOf('\n') + 1)..].EnumerateRunes().Count() + 1;
    return new(segment.Original.Path, line, column, symbol, segment.Original.Sha256);
  }
}

/// <summary>Installs draft bodies without changing contracts, then adds a typed goal generator.</summary>
public static class ContractRuntimeSourcePreparation {
  private sealed record Edit(Uri Uri, int Start, int Length, string Text,
    ContractSource Original, int OriginalStart, bool Anchor = false);

  public static async Task<ContractRuntimePreparedSources> PrepareAsync(Program program,
    IReadOnlyList<ContractSource> sources, Method goal, IReadOnlyList<ContractRuntimeDraft> drafts,
    ContractSource generator, DafnyOptions options, CancellationToken cancellationToken) {
    var edits = new List<Edit>();
    var module = goal.EnclosingClass.EnclosingModuleDefinition;
    var source = ContractSourceSnapshot.Find(sources, goal.Origin.Uri);
    var modulePosition = module == program.DefaultModuleDef ? 0 : module.BodyStartTok.pos + 1;
    edits.Add(new(goal.Origin.Uri, modulePosition, 0, "\nimport PbtRandom\n", source, modulePosition, true));
    var moduleNames = new Dictionary<ModuleDefinition, HashSet<string>> { [module] = ModuleNames(module) };
    var names = moduleNames[module];
    var supplied = new HashSet<string>(StringComparer.Ordinal);
    foreach (var draft in drafts) {
      cancellationToken.ThrowIfCancellationRequested();
      if (!supplied.Add(draft.Symbol)) {
        throw new ArgumentException("Duplicate draft for " + draft.Symbol);
      }
      var targets = Members(program).OfType<MethodOrFunction>()
        .Where(member => member.FullDafnyName == draft.Symbol || member.FullName == draft.Symbol).ToList();
      if (targets.Count != 1) {
        throw new NotSupportedException("Draft target must identify one callable: " + draft.Symbol);
      }
      var target = targets[0];
      var snapshot = new ContractSource(draft.Path, draft.Content, draft.Sha256);
      var parsed = await ParseDeclarations(snapshot, options, cancellationToken);
      var declarations = Declarations(parsed).ToList();
      var marked = declarations.OfType<MethodOrFunction>()
        .Where(member => AttributeSymbol(member.Attributes, "pbt_draft") == draft.Symbol).ToList();
      if (marked.Count != 1) {
        throw new NotSupportedException("A draft must contain exactly one matching pbt_draft declaration: " + draft.Symbol);
      }
      var candidate = marked[0];
      ValidateSignature(target, candidate);
      var targetSource = ContractSourceSnapshot.Find(sources, target.Origin.Uri);
      if (!NeedsDraft(target)) {
        continue;
      }
      var targetModule = target.EnclosingClass.EnclosingModuleDefinition;
      if (!moduleNames.TryGetValue(targetModule, out var targetNames)) {
        targetNames = ModuleNames(targetModule);
        moduleNames.Add(targetModule, targetNames);
      }
      foreach (var helper in declarations.Where(declaration => declaration != candidate)) {
        AddHelper(helper, snapshot, targetModule, program, targetSource, targetNames, edits);
      }
      ReplaceBody(target, candidate, snapshot, targetSource, edits);
      RemoveAttributes(target.Attributes, targetSource, edits);
    }
    var parsedGenerator = await ParseDeclarations(generator, options, cancellationToken);
    var generatorDeclarations = Declarations(parsedGenerator).ToList();
    var generators = generatorDeclarations.OfType<Method>()
      .Where(method => AttributeSymbol(method.Attributes, "pbt_generator") == goal.FullDafnyName).ToList();
    if (generators.Count != 1) {
      throw new NotSupportedException("A generator must contain exactly one matching pbt_generator method.");
    }
    ValidateGenerator(goal, generators[0]);
    foreach (var declaration in generatorDeclarations) {
      AddHelper(declaration, generator, module, program, source, names, edits);
    }
    return Apply(sources, edits);
  }

  private static async Task<Program> ParseDeclarations(ContractSource source, DafnyOptions options,
    CancellationToken cancellationToken) {
    var reporter = new BatchErrorReporter(new DafnyOptions(options));
    var parsed = await ContractSourceSnapshot.ParseAsync(reporter, [source], cancellationToken, resolve: false);
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Invalid diagnostic declaration source: " +
        string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
    }
    return parsed;
  }

  private static IEnumerable<Node> Declarations(Program program) {
    foreach (var declaration in program.DefaultModuleDef.TopLevelDecls) {
      if (declaration is DefaultClassDecl defaultClass) {
        foreach (var member in defaultClass.Members) { yield return member; }
      } else {
        yield return declaration;
      }
    }
  }

  private static IEnumerable<MemberDecl> Members(Program program) => program.RawModules()
    .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>()
    .SelectMany(declaration => declaration.Members);

  private static HashSet<string> ModuleNames(ModuleDefinition module) => module.TopLevelDecls
    .Where(declaration => declaration is not DefaultClassDecl).Select(declaration => declaration.Name)
    .Concat(module.TopLevelDecls.OfType<DefaultClassDecl>().SelectMany(declaration => declaration.Members)
      .Select(member => member.Name)).ToHashSet(StringComparer.Ordinal);

  private static string? AttributeSymbol(Attributes? attributes, string name) {
    var matches = attributes.AsEnumerable().Where(attribute => attribute.Name == name).ToList();
    if (matches.Count == 0) { return null; }
    if (matches.Count != 1 || matches[0].Args is not [LiteralExpr { Value: string symbol }]) {
      throw new NotSupportedException("The " + name + " attribute requires one callable symbol string.");
    }
    return symbol;
  }

  private static bool SameFormals(IReadOnlyList<Formal> original, IReadOnlyList<Formal> draft) =>
    original.Count == draft.Count && original.Zip(draft).All(pair =>
      pair.First.Name == pair.Second.Name && pair.First.IsGhost == pair.Second.IsGhost &&
      pair.First.SafeSyntacticType.ToString() == pair.Second.SafeSyntacticType.ToString());

  private static void ValidateSignature(MethodOrFunction original, MethodOrFunction draft) {
    var valid = original.GetType() == draft.GetType() && original.Name == draft.Name &&
      original.IsGhost == draft.IsGhost && original.HasStaticKeyword == draft.HasStaticKeyword &&
      original.TypeArgs.Count == draft.TypeArgs.Count &&
      original.TypeArgs.Zip(draft.TypeArgs).All(pair => pair.First.Name == pair.Second.Name &&
        pair.First.Characteristics.Equals(pair.Second.Characteristics)) && SameFormals(original.Ins, draft.Ins);
    if (original is Method method && draft is Method candidate) {
      valid &= SameFormals(method.Outs, candidate.Outs) && candidate.Body != null;
    } else if (original is Function function && draft is Function candidateFunction) {
      valid &= function.ResultType.ToString() == candidateFunction.ResultType.ToString() && candidateFunction.Body != null;
    }
    if (!valid) {
      throw new NotSupportedException("Draft signature does not match the original callable: " + original.FullDafnyName);
    }
  }

  // A bodyless trait member is implemented by class overrides and dispatched at run time; it is never drafted.
  private static bool NeedsDraft(MethodOrFunction target) => !(target.EnclosingClass is TraitDecl && !target.IsStatic) && target switch {
    Method { Body: null } => true,
    Method { Body.Body: [AssertStmt { Expr.Resolved: LiteralExpr { Value: false } }] } => true,
    Function { Body: null } => true,
    _ => false
  };

  private static void ValidateGenerator(Method goal, Method generator) {
    var receiverCount = goal.IsStatic ? 0 : 1;
    if (generator.Name != "Generate" || generator.IsGhost || generator.Body == null ||
        generator.TypeArgs.Count != 0 || generator.Ins.Count != 1 || generator.Ins[0].Name != "r" ||
        generator.Ins[0].SafeSyntacticType.ToString() != "PbtRandom.Source" ||
        generator.Outs.Count != goal.Ins.Count + receiverCount) {
      throw new NotSupportedException("Generator signature does not match the current goal inputs.");
    }
    if (receiverCount != 0 && (generator.Outs[0].Name != "receiver" ||
        generator.Outs[0].SafeSyntacticType.ToString() != goal.EnclosingClass.Name)) {
      throw new NotSupportedException("Instance generators require a receiver of the original class type.");
    }
    foreach (var pair in goal.Ins.Zip(generator.Outs.Skip(receiverCount))) {
      if (pair.Second.IsGhost || pair.First.Name != pair.Second.Name ||
          pair.First.SafeSyntacticType.ToString() != pair.Second.SafeSyntacticType.ToString()) {
        throw new NotSupportedException("Generator outputs must match goal input names and types.");
      }
    }
  }

  private static void AddHelper(Node helper, ContractSource draft, ModuleDefinition module,
    Program program, ContractSource targetSource, HashSet<string> names, List<Edit> edits) {
    var name = helper switch {
      MethodOrFunction callable => callable.Name,
      DatatypeDecl datatype => datatype.Name,
      _ => throw new NotSupportedException("Diagnostic helpers must be callable or datatype declarations.")
    };
    if (!names.Add(name)) {
      throw new NotSupportedException("Diagnostic helper collides with a declaration: " + name);
    }
    var insertion = module == program.DefaultModuleDef ? 0 : module.BodyStartTok.pos + 1;
    var range = helper.EntireRange;
    var text = Slice(draft.Content, range.StartToken.pos, range.Length);
    edits.Add(new(ContractSourceSnapshot.UriFor(targetSource.Path), insertion, 0, "\n", targetSource, insertion, true));
    edits.Add(new(ContractSourceSnapshot.UriFor(targetSource.Path), insertion, 0, text, draft, range.StartToken.pos));
    edits.Add(new(ContractSourceSnapshot.UriFor(targetSource.Path), insertion, 0, "\n", targetSource, insertion, true));
  }

  private static void ReplaceBody(MethodOrFunction original, MethodOrFunction draft, ContractSource draftSource,
    ContractSource targetSource, List<Edit> edits) {
    var (oldBody, newBody) = (original, draft) switch {
      (Method method, Method candidate) => ((Node?)method.Body, (Node)candidate.Body!),
      (Function function, Function candidate) => (function.Body, (Node)candidate.Body!),
      _ => throw new NotSupportedException("Draft callable kinds differ.")
    };
    var bodyRange = newBody.EntireRange;
    var text = Slice(draftSource.Content, bodyRange.StartToken.pos, bodyRange.Length);
    var start = oldBody?.EntireRange.StartToken.pos ?? original.EndToken.pos + Encoding.UTF8.GetByteCount(original.EndToken.val);
    var length = oldBody?.EntireRange.Length ?? 0;
    if (original is Function && oldBody == null) {
      edits.Add(new(original.Origin.Uri, start, 0, " { ", targetSource, start, true));
      edits.Add(new(original.Origin.Uri, start, 0, text, draftSource, bodyRange.StartToken.pos));
      edits.Add(new(original.Origin.Uri, start, 0, " }", targetSource, start, true));
    } else {
      if (oldBody == null) {
        edits.Add(new(original.Origin.Uri, start, 0, "\n", targetSource, start, true));
      }
      edits.Add(new(original.Origin.Uri, start, length, text, draftSource, bodyRange.StartToken.pos));
    }
  }

  private static void RemoveAttributes(Attributes? attributes, ContractSource source, List<Edit> edits) {
    foreach (var attribute in attributes.AsEnumerable().OfType<UserSuppliedAttributes>()
               .Where(attribute => attribute.Name is "extern" or "axiom")) {
      edits.Add(new(attribute.OpenBrace.Uri, attribute.OpenBrace.pos,
        attribute.CloseBrace.pos + 1 - attribute.OpenBrace.pos, "", source, attribute.OpenBrace.pos, true));
    }
  }

  private static string Slice(string content, int start, int length) =>
    Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(content), start, length);

  private static ContractRuntimePreparedSources Apply(IReadOnlyList<ContractSource> sources, List<Edit> edits) {
    var allSegments = new Dictionary<Uri, IReadOnlyList<ContractRuntimeSourceMap.Segment>>();
    var prepared = new List<ContractSource>();
    foreach (var source in sources) {
      var bytes = Encoding.UTF8.GetBytes(source.Content);
      var uri = ContractSourceSnapshot.UriFor(source.Path);
      var cursor = 0;
      var output = new StringBuilder();
      var outputBytes = 0;
      var segments = new List<ContractRuntimeSourceMap.Segment>();
      foreach (var edit in edits.Where(edit => edit.Uri == uri).OrderBy(edit => edit.Start)) {
        if (edit.Start < cursor || edit.Start + edit.Length > bytes.Length) {
          throw new NotSupportedException("Overlapping or out-of-range diagnostic source edits.");
        }
        Append(Encoding.UTF8.GetString(bytes, cursor, edit.Start - cursor), source, cursor, false);
        Append(edit.Text, edit.Original, edit.OriginalStart, edit.Anchor);
        cursor = edit.Start + edit.Length;
      }
      Append(Encoding.UTF8.GetString(bytes, cursor, bytes.Length - cursor), source, cursor, false);
      allSegments.Add(uri, segments);
      var content = output.ToString();
      prepared.Add(source with { Content = content, Sha256 = ContractHarnessBuilder.Hash(content) });
      void Append(string text, ContractSource original, int originalStart, bool anchor) {
        var length = Encoding.UTF8.GetByteCount(text);
        if (length == 0) { return; }
        segments.Add(new(outputBytes, length, original, originalStart, anchor));
        output.Append(text);
        outputBytes += length;
      }
    }
    return new(prepared, new(allSegments));
  }
}
