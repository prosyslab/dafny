#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Prepares full-context diagnostic source views and extracts legacy runtime packets from them.</summary>
public static class ContractRuntimeSourceAuthoring {
  public const int SchemaVersion = 1;
  public const int MaximumRequestBytes = 64 * 1024 * 1024;
  private const int MaximumSourceCount = 4096;
  private const long MaximumSourceBytes = 64L * 1024 * 1024;
  private const string TodoPrefix = "PbtAuthoringTODO_";

  private sealed record Region(string Id, string Begin, string End, string Path);
  private sealed record RegionSpan(int Start, int End);
  private sealed record DraftLayout(ContractRuntimeDraft Packet, ContractRuntimeDraft Wrapped,
    string Symbol, string? Placeholder, Region Body, Region Helpers);
  private sealed record GeneratorLayout(ContractSource Packet, ContractSource Wrapped, string Symbol,
    string? Placeholder, Region Contracts, Region Body, Region Helpers);
  private sealed record Build(Program Program, Method Goal, IReadOnlyList<DraftLayout> Drafts,
    GeneratorLayout Generator, IReadOnlyList<ContractSource> View, ContractRuntimeAuthoringManifest Manifest);

  /// <summary>Runs one bounded in-memory prepare or extract operation.</summary>
  public static async Task<ContractRuntimeAuthoringResult> RunAsync(ContractRuntimeAuthoringRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    cancellationToken.ThrowIfCancellationRequested();
    ValidateRequest(request);
    cancellationToken.ThrowIfCancellationRequested();
    return request.Action switch {
      ContractRuntimeAuthoringAction.Prepare => await PrepareAsync(request, options, cancellationToken),
      ContractRuntimeAuthoringAction.Extract => await ExtractAsync(request, options, cancellationToken),
      _ => throw new ArgumentException("Unknown runtime authoring action.")
    };
  }

  private static async Task<ContractRuntimeAuthoringResult> PrepareAsync(ContractRuntimeAuthoringRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    if (request.AuthoredSources != null || request.Manifest != null) {
      throw new ArgumentException("Prepare does not accept authored sources or a prior manifest.");
    }
    var build = await BuildAsync(request, options, cancellationToken);
    return new(SchemaVersion, request.Action, ContractRuntimeAuthoringStatus.Ready,
      "Runtime authoring source view is ready.", build.View, build.Manifest);
  }

  private static async Task<ContractRuntimeAuthoringResult> ExtractAsync(ContractRuntimeAuthoringRequest request,
    DafnyOptions options, CancellationToken cancellationToken) {
    if (request.AuthoredSources == null || request.Manifest == null) {
      throw new ArgumentException("Extract requires authored sources and the prepare manifest.");
    }
    var build = await BuildAsync(request with {
      Action = ContractRuntimeAuthoringAction.Prepare,
      AuthoredSources = null,
      Manifest = null
    }, options, cancellationToken);
    if (!ManifestMatches(request.Manifest, build.Manifest)) {
      throw new ArgumentException("The runtime authoring manifest does not match the exact original source and packets.");
    }
    ContractSourceSnapshot.ValidateTrustedSources(request.AuthoredSources, null);
    var baseline = build.View.ToDictionary(source => source.Path, StringComparer.Ordinal);
    var authored = request.AuthoredSources.ToDictionary(source => source.Path, StringComparer.Ordinal);
    if (!baseline.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(authored.Keys)) {
      throw new ArgumentException("Authored source paths must exactly match the prepared source view.");
    }
    var regions = build.Drafts.SelectMany(layout => new[] { layout.Body, layout.Helpers })
      .Concat([build.Generator.Contracts, build.Generator.Body, build.Generator.Helpers]).ToArray();
    var authoredRegionText = new Dictionary<string, string>(StringComparer.Ordinal);
    foreach (var path in baseline.Keys) {
      cancellationToken.ThrowIfCancellationRequested();
      var expected = baseline[path].Content;
      var actual = authored[path].Content;
      var present = regions.Where(region => region.Path == path).ToArray();
      var expectedSpans = LocateRegions(expected, present, cancellationToken);
      var actualSpans = LocateRegions(actual, present, cancellationToken);
      if (Mask(expected, expectedSpans, cancellationToken) != Mask(actual, actualSpans, cancellationToken)) {
        throw new NotSupportedException("Authored source changed a signature, contract, source identity, or unrelated declaration: " + path);
      }
      foreach (var region in present) {
        var span = actualSpans[region];
        authoredRegionText.Add(region.Id, actual[span.Start..span.End]);
      }
    }

    var completed = new List<ContractRuntimeDraft>();
    var incomplete = new List<string>();
    foreach (var layout in build.Drafts) {
      cancellationToken.ThrowIfCancellationRequested();
      var body = authoredRegionText[layout.Body.Id];
      var helpers = authoredRegionText[layout.Helpers.Id];
      var content = ReplaceRegion(layout.Wrapped.Content, layout.Body, body);
      content = ReplaceRegion(content, layout.Helpers, helpers);
      content = RemoveMarkers(content, layout.Body, layout.Helpers).Trim() + "\n";
      if (layout.Placeholder != null && body.Contains(layout.Placeholder, StringComparison.Ordinal)) {
        incomplete.Add(layout.Symbol);
        continue;
      }
      completed.Add(new(layout.Symbol, layout.Packet.Path, content, ContractHarnessBuilder.Hash(content)));
    }
    var generatorContracts = authoredRegionText[build.Generator.Contracts.Id];
    var generatorBody = authoredRegionText[build.Generator.Body.Id];
    var generatorHelpers = authoredRegionText[build.Generator.Helpers.Id];
    var generatorContent = ReplaceRegion(build.Generator.Wrapped.Content, build.Generator.Contracts, generatorContracts);
    generatorContent = ReplaceRegion(generatorContent, build.Generator.Body, generatorBody);
    generatorContent = ReplaceRegion(generatorContent, build.Generator.Helpers, generatorHelpers);
    generatorContent = RemoveMarkers(generatorContent, build.Generator.Contracts,
      build.Generator.Body, build.Generator.Helpers).Trim() + "\n";
    ContractSource? generator = null;
    if (build.Generator.Placeholder != null &&
        generatorBody.Contains(build.Generator.Placeholder, StringComparison.Ordinal)) {
      incomplete.Add(build.Generator.Symbol);
    } else {
      generator = new(build.Generator.Packet.Path, generatorContent, ContractHarnessBuilder.Hash(generatorContent));
      await ValidateAuthoredGeneratorAsync(generator, build.Generator.Symbol, options, cancellationToken);
    }
    if (incomplete.Count != 0) {
      return new(SchemaVersion, request.Action, ContractRuntimeAuthoringStatus.Unsupported,
        "Unfilled runtime authoring templates: " + string.Join(", ", incomplete.Order(StringComparer.Ordinal)));
    }

    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(build.Program, request.Sources, build.Goal,
      completed, generator!, options, cancellationToken);
    if (!prepared.InstalledDraftSymbols.SetEquals(build.Manifest.DraftSymbols)) {
      throw new NotSupportedException("Extracted draft installation does not match the prepared authoring manifest.");
    }
    await ResolveExtractedAsync(options, prepared, cancellationToken);
    return new(SchemaVersion, request.Action, ContractRuntimeAuthoringStatus.Extracted,
      "Runtime authoring packets were extracted from the validated source view.",
      Drafts: completed, Generator: generator);
  }

  private static async Task<Build> BuildAsync(ContractRuntimeAuthoringRequest request, DafnyOptions options,
    CancellationToken cancellationToken) {
    ContractSourceSnapshot.ValidateTrustedSources(request.Sources, request.TrustedSources);
    var reporter = new BatchErrorReporter(options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, request.Sources, cancellationToken);
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Original runtime authoring sources do not resolve: " + Diagnostics(reporter));
    }
    var goal = ContractCallableSelector.SelectMethod(program, request.Entry,
      requireConcreteReceiver: false, allowLemmaContract: true);
    var membersBySymbol = ContractRuntimeSourcePreparation.Members(program).OfType<MethodOrFunction>()
      .ToDictionary(member => member.FullDafnyName, StringComparer.Ordinal);
    var drafts = (request.Drafts ?? []).ToList();
    var generatedDraftSymbols = new HashSet<string>(StringComparer.Ordinal);
    var indexed = ContractRuntimeSourcePreparation.IndexDrafts(program, drafts);
    if (indexed.Any(pair => pair.Value.Symbol != pair.Key)) {
      throw new NotSupportedException("Runtime authoring draft symbols must use exact canonical Dafny names.");
    }
    foreach (var requested in request.RequestedDraftSymbols ?? []) {
      cancellationToken.ThrowIfCancellationRequested();
      if (!membersBySymbol.TryGetValue(requested, out var target)) {
        throw new NotSupportedException("Requested draft target must identify one callable: " + requested);
      }
      if (!ContractRuntimeSourcePreparation.NeedsDraft(target) || indexed.ContainsKey(target.FullDafnyName)) {
        continue;
      }
      var packet = DraftTemplate(target, ContractSourceSnapshot.Find(request.Sources, target.Origin.Uri), request.Sources);
      drafts.Add(packet);
      generatedDraftSymbols.Add(target.FullDafnyName);
    }
    var generatedGenerator = request.Generator == null;
    var generator = request.Generator ?? await GeneratorTemplateAsync(program, goal, request.Entry,
      request.Sources, options, cancellationToken);
    var activeDrafts = new List<(ContractRuntimeDraft Draft, MethodOrFunction Target)>();
    foreach (var draft in drafts) {
      cancellationToken.ThrowIfCancellationRequested();
      var target = membersBySymbol[draft.Symbol];
      if (ContractRuntimeSourcePreparation.NeedsDraft(target)) { activeDrafts.Add((draft, target)); }
    }
    ValidatePacketPaths(request.Sources, drafts, generator, goal.FullDafnyName);

    var names = program.RawModules().ToDictionary(module => module,
      module => ContractRuntimeSourcePreparation.ModuleNames(module));
    var layouts = new List<DraftLayout>();
    foreach (var (suppliedDraft, target) in activeDrafts) {
      cancellationToken.ThrowIfCancellationRequested();
      var targetSource = ContractSourceSnapshot.Find(request.Sources, target.Origin.Uri);
      var draft = await CanonicalDraftAsync(suppliedDraft, target,
        targetSource, request.Sources, options, cancellationToken);
      var layout = await WrapDraftAsync(draft, target, names[target.EnclosingClass.EnclosingModuleDefinition],
        targetSource.Path, generatedDraftSymbols.Contains(target.FullDafnyName)
          ? TodoPrefix + Token("todo", target.FullDafnyName, SourceIdentity(request.Sources)) : null,
        options, cancellationToken);
      layouts.Add(layout);
    }
    var goalSource = ContractSourceSnapshot.Find(request.Sources, goal.Origin.Uri);
    var generatorLayout = await WrapGeneratorAsync(generator, goal, names[goal.EnclosingClass.EnclosingModuleDefinition],
      goalSource.Path, generatedGenerator
        ? TodoPrefix + Token("generator-todo", goal.FullDafnyName, SourceIdentity(request.Sources)) : null,
      options, cancellationToken);
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(program, request.Sources, goal,
      layouts.Select(layout => layout.Wrapped).ToArray(), generatorLayout.Wrapped, options, cancellationToken);
    var view = prepared.Sources.ToList();
    var runtimePath = FreshRuntimePath(view.Concat(layouts.Select(layout =>
      new ContractSource(layout.Packet.Path, layout.Packet.Content, layout.Packet.Sha256))).Append(generator));
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    view.Add(new(runtimePath, runtime, ContractHarnessBuilder.Hash(runtime)));
    ValidateSourceBudget(view, "Prepared runtime authoring sources");
    var runtimeDependency = new ContractDependency(runtimePath, ContractHarnessBuilder.Hash(runtime));
    var manifest = new ContractRuntimeAuthoringManifest(
      Dependencies(request.Sources), Dependencies(view),
      prepared.InstalledDraftSymbols.Order(StringComparer.Ordinal).ToArray(), goal.FullDafnyName,
      runtimeDependency);
    return new(program, goal, layouts, generatorLayout, view, manifest);
  }

  private static ContractRuntimeDraft DraftTemplate(MethodOrFunction target, ContractSource source,
    IReadOnlyList<ContractSource> sources) {
    var range = target.EntireRange;
    var declaration = Slice(source.Content, range.StartToken.pos, range.Length);
    var offset = range.StartToken.pos;
    var placeholder = TodoPrefix + Token("todo", target.FullDafnyName, SourceIdentity(sources));
    if (target is Method method) {
      declaration = method.Body == null
        ? declaration + "\n{ " + placeholder + "(); }"
        : ReplaceBytes(declaration, method.Body.EntireRange.StartToken.pos - offset,
          method.Body.EntireRange.Length, "{ " + placeholder + "(); }");
    } else if (target is Function function) {
      declaration = function.Body == null
        ? declaration + "\n{ " + placeholder + " }"
        : ReplaceBytes(declaration, function.Body.EntireRange.StartToken.pos - offset,
          function.Body.EntireRange.Length, placeholder);
    } else {
      throw new NotSupportedException("Runtime authoring drafts support methods and functions.");
    }
    var keyword = DeclarationKeyword(target);
    declaration = InsertBytes(declaration, keyword.pos + Encoding.UTF8.GetByteCount(keyword.val) - offset,
      " {:pbt_draft \"" + target.FullDafnyName + "\"}");
    var path = ".top-down-pbt/drafts/" + target.FullDafnyName + ".dfy";
    declaration = declaration.Trim() + "\n";
    return new(target.FullDafnyName, path, declaration, ContractHarnessBuilder.Hash(declaration));
  }

  private static async Task<ContractRuntimeDraft> CanonicalDraftAsync(ContractRuntimeDraft supplied,
    MethodOrFunction target, ContractSource originalSource, IReadOnlyList<ContractSource> originalSources,
    DafnyOptions options, CancellationToken cancellationToken) {
    var suppliedProgram = await ParsePacketAsync(new(supplied.Path, supplied.Content, supplied.Sha256),
      options, cancellationToken);
    var declarations = Declarations(suppliedProgram).ToList();
    var candidates = declarations.OfType<MethodOrFunction>()
      .Where(member => AttributeSymbol(member.Attributes, "pbt_draft") == supplied.Symbol).ToList();
    if (candidates.Count != 1) {
      throw new NotSupportedException("A draft must contain exactly one matching pbt_draft declaration: " + supplied.Symbol);
    }
    var candidate = candidates[0];
    var canonical = DraftTemplate(target, originalSource, originalSources);
    var canonicalProgram = await ParsePacketAsync(new(canonical.Path, canonical.Content, canonical.Sha256),
      options, cancellationToken);
    var canonicalCandidate = Declarations(canonicalProgram).OfType<MethodOrFunction>().Single();
    var suppliedBody = candidate switch {
      Method method when method.Body != null => (Node)method.Body,
      Function function when function.Body != null => function.Body,
      _ => throw new NotSupportedException("Draft authoring requires a syntactic candidate body.")
    };
    var canonicalBody = canonicalCandidate switch {
      Method method when method.Body != null => (Node)method.Body,
      Function function when function.Body != null => function.Body,
      _ => throw new InvalidOperationException("The native draft template did not contain a body.")
    };
    var content = ReplaceBytes(canonical.Content, canonicalBody.EntireRange.StartToken.pos,
      canonicalBody.EntireRange.Length, Slice(supplied.Content, suppliedBody.EntireRange.StartToken.pos,
        suppliedBody.EntireRange.Length));
    var helpers = new List<string>();
    foreach (var declaration in declarations.Where(declaration => declaration != candidate)) {
      cancellationToken.ThrowIfCancellationRequested();
      helpers.Add(Slice(supplied.Content, declaration.EntireRange.StartToken.pos, declaration.EntireRange.Length));
    }
    content = content.Trim() + "\n" + string.Join("\n", helpers) + "\n";
    return new(target.FullDafnyName, canonical.Path, content, ContractHarnessBuilder.Hash(content));
  }

  private static async Task<ContractSource> GeneratorTemplateAsync(Program program, Method goal,
    ContractEntry entry, IReadOnlyList<ContractSource> sources, DafnyOptions options,
    CancellationToken cancellationToken) {
    var placeholder = TodoPrefix + Token("generator-todo", goal.FullDafnyName, SourceIdentity(sources));
    var path = ".top-down-pbt/generators/" + goal.FullDafnyName + ".dfy";
    var signature = ContractRuntimeGeneratorSignature.Format(goal);
    var probeContent = signature + "\n{}\n";
    var probe = new ContractSource(path, probeContent, ContractHarnessBuilder.Hash(probeContent));
    var prepared = await ContractRuntimeSourcePreparation.PrepareAsync(program, sources, goal, [], probe,
      options, cancellationToken);
    var rawReporter = new BatchErrorReporter(new DafnyOptions(options));
    var raw = await ContractSourceSnapshot.ParseAsync(rawReporter, prepared.Sources, cancellationToken, resolve: false);
    if (rawReporter.ErrorCount != 0) {
      throw new NotSupportedException("Automatic generator contract preparation failed: " + Diagnostics(rawReporter));
    }
    var visible = ContractRuntimeObligationTransformer.MakeGeneratorVisible(raw, prepared.Sources,
      prepared.DiagnosticConstructors ?? new HashSet<string>());
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    var snapshots = visible.Append(new ContractSource(FreshRuntimePath(visible), runtime,
      ContractHarnessBuilder.Hash(runtime))).ToArray();
    var reporter = new BatchErrorReporter(new DafnyOptions(options));
    var resolved = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, cancellationToken,
      deferredGhostDiagnostics: new List<DafnyDiagnostic>());
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Automatic generator contract preparation failed: " + Diagnostics(reporter));
    }
    var resolvedGoal = ContractCallableSelector.SelectMethod(resolved,
      entry with { Symbol = goal.FullDafnyName }, requireConcreteReceiver: false, allowLemmaContract: true);
    var resolvedGenerator = ContractRuntimeGeneratorSignature.Select(resolved, resolvedGoal,
      prepared.GeneratorMethodName);
    var supportsPostconditions = ContractGeneratorProof.SupportsRequiredPostconditions(resolved, resolvedGoal,
      resolvedGenerator, out _);
    var postconditions = ContractGeneratorProof.RequiredPostconditions(resolved, resolvedGoal,
      resolvedGenerator, out var postconditionFailure, cancellationToken: cancellationToken);
    if (supportsPostconditions && postconditions == null) {
      throw new NotSupportedException(postconditionFailure ??
        "Automatic generator target-requirement rendering failed.");
    }
    postconditions ??= "\n";
    var content = signature + postconditions + "{ " + placeholder + "(); }\n";
    return new(path, content,
      ContractHarnessBuilder.Hash(content));
  }

  private static async Task<DraftLayout> WrapDraftAsync(ContractRuntimeDraft packet, MethodOrFunction target,
    HashSet<string> moduleNames, string targetPath, string? placeholder,
    DafnyOptions options, CancellationToken cancellationToken) {
    var parsed = await ParsePacketAsync(new(packet.Path, packet.Content, packet.Sha256), options, cancellationToken);
    var declarations = Declarations(parsed).ToList();
    var candidates = declarations.OfType<MethodOrFunction>()
      .Where(member => AttributeSymbol(member.Attributes, "pbt_draft") == packet.Symbol).ToList();
    if (candidates.Count != 1) {
      throw new NotSupportedException("A draft must contain exactly one matching pbt_draft declaration: " + packet.Symbol);
    }
    var candidate = candidates[0];
    var token = Token("draft", target.FullDafnyName, packet.Path + ":" + packet.Sha256);
    var body = new Region("draft-body:" + target.FullDafnyName,
      "/* pbt-authoring-" + token + "-body-begin */",
      "/* pbt-authoring-" + token + "-body-end */", targetPath);
    var beginName = Fresh(moduleNames, "PbtAuthoringBegin_" + token);
    var endName = Fresh(moduleNames, "PbtAuthoringEnd_" + token);
    var helper = new Region("draft-helpers:" + target.FullDafnyName,
      "datatype " + beginName + " = " + beginName,
      "datatype " + endName + " = " + endName, targetPath);
    var candidateText = Slice(packet.Content, candidate.EntireRange.StartToken.pos, candidate.EntireRange.Length);
    var bodyNode = candidate switch {
      Method method when method.Body != null => (Node)method.Body,
      Function function when function.Body != null => function.Body,
      _ => throw new NotSupportedException("Draft authoring requires a syntactic candidate body.")
    };
    var bodyStart = bodyNode.EntireRange.StartToken.pos - candidate.EntireRange.StartToken.pos;
    var bodyEnd = bodyStart + bodyNode.EntireRange.Length;
    if (candidate is Method) {
      bodyStart += Encoding.UTF8.GetByteCount(bodyNode.StartToken.val);
      bodyEnd -= Encoding.UTF8.GetByteCount(bodyNode.EndToken.val);
    }
    candidateText = InsertBytes(candidateText, bodyEnd, "\n" + body.End + "\n");
    candidateText = InsertBytes(candidateText, bodyStart, "\n" + body.Begin + "\n");
    var helpers = new List<string>();
    foreach (var declaration in declarations.Where(declaration => declaration != candidate)) {
      cancellationToken.ThrowIfCancellationRequested();
      helpers.Add(Slice(packet.Content, declaration.EntireRange.StartToken.pos,
        declaration.EntireRange.Length));
    }
    var content = candidateText + "\n" + helper.Begin + "\n" + string.Join("\n", helpers) +
      "\n" + helper.End + "\n";
    var wrapped = new ContractRuntimeDraft(packet.Symbol, packet.Path, content, ContractHarnessBuilder.Hash(content));
    return new(packet, wrapped, target.FullDafnyName, placeholder, body, helper);
  }

  private static async Task<GeneratorLayout> WrapGeneratorAsync(ContractSource packet, Method goal,
    HashSet<string> moduleNames, string targetPath, string? placeholder,
    DafnyOptions options, CancellationToken cancellationToken) {
    var parsed = await ParsePacketAsync(packet, options, cancellationToken);
    var declarations = Declarations(parsed).ToList();
    var generators = declarations.OfType<Method>()
      .Where(method => AttributeSymbol(method.Attributes, "pbt_generator") == goal.FullDafnyName).ToList();
    if (generators.Count != 1) {
      throw new NotSupportedException("A generator must contain exactly one matching pbt_generator method.");
    }
    var generator = generators[0];
    if (generator.Body == null || generator.Req.Count != 0 || generator.Reads.Expressions?.Count > 0 ||
        generator.Reads.Attributes != null || generator.Mod.Expressions?.Count > 0 || generator.Mod.Attributes != null ||
        generator.Decreases.Expressions?.Count > 0 || generator.Decreases.Attributes != null) {
      throw new NotSupportedException(
        "A runtime authoring generator requires a body and supports only ensures clauses.");
    }
    var token = Token("generator", goal.FullDafnyName, packet.Path + ":" + packet.Sha256);
    var contracts = new Region("generator-contracts:" + goal.FullDafnyName,
      "/* pbt-authoring-" + token + "-contracts-begin */",
      "/* pbt-authoring-" + token + "-contracts-end */", targetPath);
    var body = new Region("generator-body:" + goal.FullDafnyName,
      "/* pbt-authoring-" + token + "-body-begin */",
      "/* pbt-authoring-" + token + "-body-end */", targetPath);
    var beginName = Fresh(moduleNames, "PbtAuthoringBegin_" + token);
    var endName = Fresh(moduleNames, "PbtAuthoringEnd_" + token);
    var helpers = new Region("generator-helpers:" + goal.FullDafnyName,
      "datatype " + beginName + " = " + beginName,
      "datatype " + endName + " = " + endName, targetPath);
    var generatorText = Slice(packet.Content, generator.EntireRange.StartToken.pos, generator.EntireRange.Length);
    var bodyStart = generator.Body.EntireRange.StartToken.pos - generator.EntireRange.StartToken.pos +
      Encoding.UTF8.GetByteCount(generator.Body.StartToken.val);
    var bodyEnd = generator.Body.EntireRange.StartToken.pos - generator.EntireRange.StartToken.pos +
      generator.Body.EntireRange.Length - Encoding.UTF8.GetByteCount(generator.Body.EndToken.val);
    generatorText = InsertBytes(generatorText, bodyEnd, "\n" + body.End + "\n");
    generatorText = InsertBytes(generatorText, bodyStart, "\n" + body.Begin + "\n");
    var contractPosition = generator.Body.EntireRange.StartToken.pos - generator.EntireRange.StartToken.pos;
    generatorText = InsertBytes(generatorText, contractPosition,
      "\n" + contracts.Begin + "\n" + contracts.End + "\n");
    var helperTexts = new List<string>();
    foreach (var declaration in declarations.Where(declaration => declaration != generator)) {
      cancellationToken.ThrowIfCancellationRequested();
      helperTexts.Add(Slice(packet.Content, declaration.EntireRange.StartToken.pos,
        declaration.EntireRange.Length));
    }
    var content = generatorText + "\n" + helpers.Begin + "\n" + string.Join("\n", helperTexts) +
      "\n" + helpers.End + "\n";
    return new(packet, packet with { Content = content, Sha256 = ContractHarnessBuilder.Hash(content) },
      goal.FullDafnyName, placeholder, contracts, body, helpers);
  }

  private static async Task ValidateAuthoredGeneratorAsync(ContractSource packet, string goalSymbol,
    DafnyOptions options, CancellationToken cancellationToken) {
    var parsed = await ParsePacketAsync(packet, options, cancellationToken);
    var generators = Declarations(parsed).OfType<Method>()
      .Where(method => AttributeSymbol(method.Attributes, "pbt_generator") == goalSymbol).ToList();
    if (generators.Count != 1) {
      throw new NotSupportedException("The authored generator lost its exact target identity.");
    }
    var generator = generators[0];
    if (generator.Req.Count != 0 || generator.Reads.Expressions?.Count > 0 || generator.Reads.Attributes != null ||
        generator.Mod.Expressions?.Count > 0 || generator.Mod.Attributes != null ||
        generator.Decreases.Expressions?.Count > 0 || generator.Decreases.Attributes != null) {
      throw new NotSupportedException("The editable generator contract region accepts only additional ensures clauses.");
    }
  }

  private static async Task<Program> ParsePacketAsync(ContractSource packet, DafnyOptions options,
    CancellationToken cancellationToken) {
    var reporter = new BatchErrorReporter(new DafnyOptions(options));
    var program = await ContractSourceSnapshot.ParseAsync(reporter, [packet], cancellationToken, resolve: false);
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Invalid runtime authoring packet " + packet.Path + ": " + Diagnostics(reporter));
    }
    return program;
  }

  private static async Task ResolveExtractedAsync(DafnyOptions options,
    ContractRuntimePreparedSources prepared, CancellationToken cancellationToken) {
    var rawReporter = new BatchErrorReporter(new DafnyOptions(options));
    var raw = await ContractSourceSnapshot.ParseAsync(rawReporter, prepared.Sources, cancellationToken, resolve: false);
    if (rawReporter.ErrorCount != 0) {
      throw new NotSupportedException("Extracted runtime packets do not parse: " + Diagnostics(rawReporter));
    }
    var visible = ContractRuntimeObligationTransformer.MakeGeneratorVisible(raw, prepared.Sources,
      prepared.DiagnosticConstructors ?? new HashSet<string>());
    var runtime = ContractRuntimeInstrumentation.DafnySource;
    var runtimePath = FreshRuntimePath(visible);
    var snapshots = visible.Append(new ContractSource(runtimePath, runtime, ContractHarnessBuilder.Hash(runtime))).ToArray();
    var reporter = new BatchErrorReporter(new DafnyOptions(options));
    _ = await ContractSourceSnapshot.ParseAsync(reporter, snapshots, cancellationToken,
      deferredGhostDiagnostics: new List<DafnyDiagnostic>());
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Extracted runtime packets do not resolve: " + Diagnostics(reporter));
    }
  }

  private static string ReplaceRegion(string content, Region region, string replacement) {
    var begin = UniqueIndex(content, region.Begin) + region.Begin.Length;
    var end = content.IndexOf(region.End, begin, StringComparison.Ordinal);
    if (end < 0) { throw new NotSupportedException("Runtime authoring region is incomplete: " + region.Id); }
    return content[..begin] + replacement + content[end..];
  }

  private static IReadOnlyDictionary<Region, RegionSpan> LocateRegions(string content,
    IReadOnlyList<Region> regions, CancellationToken cancellationToken) {
    var markerOwners = new Dictionary<string, (Region Region, bool Begin)>(StringComparer.Ordinal);
    foreach (var region in regions) {
      markerOwners.Add(region.Begin, (region, true));
      markerOwners.Add(region.End, (region, false));
    }
    var occurrences = new Dictionary<(Region Region, bool Begin), (int Start, int End)>();
    var cursor = 0;
    while (cursor < content.Length) {
      cancellationToken.ThrowIfCancellationRequested();
      var candidate = content.AsSpan(cursor).IndexOfAny('/', 'd');
      if (candidate < 0) { break; }
      var start = cursor + candidate;
      var comment = content.AsSpan(start).StartsWith("/* pbt-authoring-", StringComparison.Ordinal);
      var datatype = content.AsSpan(start).StartsWith("datatype PbtAuthoring", StringComparison.Ordinal);
      if (!comment && !datatype) {
        cursor = start + 1;
        continue;
      }
      int end;
      if (comment) {
        var close = content.IndexOf("*/", start + 3, StringComparison.Ordinal);
        end = close < 0 ? start + "/* pbt-authoring-".Length : close + 2;
      } else {
        var newline = content.IndexOf('\n', start);
        end = newline < 0 ? content.Length : newline;
        if (end > start && content[end - 1] == '\r') { end--; }
      }
      var marker = content[start..end];
      if (markerOwners.TryGetValue(marker, out var owner) &&
          !occurrences.TryAdd(owner, (start, end))) {
        throw new NotSupportedException("Runtime authoring region marker is duplicated: " + owner.Region.Id);
      }
      cursor = Math.Max(end, start + 1);
    }
    var result = new Dictionary<Region, RegionSpan>();
    foreach (var region in regions) {
      cancellationToken.ThrowIfCancellationRequested();
      if (!occurrences.TryGetValue((region, true), out var begin) ||
          !occurrences.TryGetValue((region, false), out var end) || begin.End > end.Start) {
        throw new NotSupportedException("Runtime authoring region marker is missing or reordered: " + region.Id);
      }
      result.Add(region, new(begin.End, end.Start));
    }
    var ordered = result.OrderBy(pair => pair.Value.Start).ToArray();
    for (var index = 1; index < ordered.Length; index++) {
      if (ordered[index - 1].Value.End > ordered[index].Value.Start) {
        throw new NotSupportedException("Runtime authoring regions overlap.");
      }
    }
    return result;
  }

  private static string Mask(string content, IReadOnlyDictionary<Region, RegionSpan> spans,
    CancellationToken cancellationToken) {
    var output = new StringBuilder(content.Length);
    var cursor = 0;
    foreach (var pair in spans.OrderBy(pair => pair.Value.Start)) {
      cancellationToken.ThrowIfCancellationRequested();
      output.Append(content, cursor, pair.Value.Start - cursor);
      output.Append('<').Append(pair.Key.Id).Append('>');
      cursor = pair.Value.End;
    }
    output.Append(content, cursor, content.Length - cursor);
    return output.ToString();
  }

  private static string RemoveMarkers(string content, params Region[] regions) {
    foreach (var region in regions) {
      content = content.Replace(region.Begin, "", StringComparison.Ordinal)
        .Replace(region.End, "", StringComparison.Ordinal);
    }
    return content;
  }

  private static int UniqueIndex(string content, string marker) {
    var index = content.IndexOf(marker, StringComparison.Ordinal);
    if (index < 0 || content.IndexOf(marker, index + marker.Length, StringComparison.Ordinal) >= 0) {
      throw new NotSupportedException("Runtime authoring region marker is missing or duplicated.");
    }
    return index;
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

  private static string? AttributeSymbol(Attributes? attributes, string name) {
    var matches = attributes.AsEnumerable().Where(attribute => attribute.Name == name).ToList();
    if (matches.Count == 0) { return null; }
    if (matches.Count != 1 || matches[0].Args is not [LiteralExpr { Value: string symbol }]) {
      throw new NotSupportedException("The " + name + " attribute requires one callable symbol string.");
    }
    return symbol;
  }

  private static Token DeclarationKeyword(MethodOrFunction declaration) {
    var end = declaration.EndToken.pos + Encoding.UTF8.GetByteCount(declaration.EndToken.val);
    for (var token = declaration.StartToken; token != null && token.pos < end; token = token.Next) {
      if (token.val is "method" or "function" or "predicate" or "lemma") { return token; }
    }
    throw new NotSupportedException("Runtime authoring could not locate the callable declaration keyword.");
  }

  private static string Fresh(HashSet<string> names, string preferred) {
    while (!names.Add(preferred)) { preferred += "0"; }
    return preferred;
  }

  private static string Token(string kind, string symbol, string identity) =>
    ContractHarnessBuilder.Hash(kind + "\n" + symbol + "\n" + identity)[..20];

  private static string SourceIdentity(IReadOnlyList<ContractSource> sources) => string.Join("\n",
    sources.OrderBy(source => source.Path, StringComparer.Ordinal).Select(source => source.Path + ":" + source.Sha256));

  private static IReadOnlyList<ContractDependency> Dependencies(IReadOnlyList<ContractSource> sources) =>
    sources.Select(source => new ContractDependency(source.Path, source.Sha256)).ToArray();

  private static bool ManifestMatches(ContractRuntimeAuthoringManifest supplied,
    ContractRuntimeAuthoringManifest expected) => supplied.GeneratorSymbol == expected.GeneratorSymbol &&
    supplied.RuntimeSource == expected.RuntimeSource &&
    supplied.OriginalSources.SequenceEqual(expected.OriginalSources) &&
    supplied.PreparedSources.SequenceEqual(expected.PreparedSources) &&
    supplied.DraftSymbols.SequenceEqual(expected.DraftSymbols, StringComparer.Ordinal);

  private static string FreshRuntimePath(IEnumerable<ContractSource> sources) {
    var paths = sources.Select(source => source.Path).ToHashSet(StringComparer.Ordinal);
    var path = ".top-down-pbt/PbtRuntime.dfy";
    while (!paths.Add(path)) { path = ".top-down-pbt/" + Path.GetFileNameWithoutExtension(path) + "0.dfy"; }
    return path;
  }

  private static void ValidateRequest(ContractRuntimeAuthoringRequest request) {
    if (request.SchemaVersion != SchemaVersion || request.Sources == null || request.Sources.Count == 0 ||
        request.Entry == null || string.IsNullOrWhiteSpace(request.Entry.Symbol) || request.TimeoutMilliseconds <= 0) {
      throw new ArgumentException("Invalid runtime authoring schema, sources, entry, or deadline.");
    }
    if ((request.Drafts ?? []).Any(draft => draft == null) ||
        (request.RequestedDraftSymbols ?? []).Any(string.IsNullOrWhiteSpace) ||
        (request.RequestedDraftSymbols ?? []).Distinct(StringComparer.Ordinal).Count() !=
        (request.RequestedDraftSymbols ?? []).Count) {
      throw new ArgumentException("Runtime authoring draft requests must be non-null and unique.");
    }
    if (request.Manifest != null && (request.Manifest.OriginalSources == null ||
        request.Manifest.PreparedSources == null || request.Manifest.DraftSymbols == null)) {
      throw new ArgumentException("Runtime authoring manifests require all dependency and symbol collections.");
    }
    if (request.Sources.Count > MaximumSourceCount || (request.Drafts?.Count ?? 0) > MaximumSourceCount ||
        (request.RequestedDraftSymbols?.Count ?? 0) > MaximumSourceCount ||
        (request.AuthoredSources?.Count ?? 0) > MaximumSourceCount ||
        (request.Manifest?.OriginalSources.Count ?? 0) > MaximumSourceCount ||
        (request.Manifest?.PreparedSources.Count ?? 0) > MaximumSourceCount ||
        (request.Manifest?.DraftSymbols.Count ?? 0) > MaximumSourceCount) {
      throw new ArgumentException("Runtime authoring exceeds the bounded source-count policy.");
    }
    ValidateSourceBudget(request.Sources.Concat(request.AuthoredSources ?? [])
      .Concat((request.Drafts ?? []).Select(draft => new ContractSource(draft.Path, draft.Content, draft.Sha256)))
      .Concat(request.Generator == null ? [] : [request.Generator]), "Runtime authoring request sources");
  }

  private static void ValidatePacketPaths(IReadOnlyList<ContractSource> sources,
    IReadOnlyList<ContractRuntimeDraft> drafts, ContractSource generator, string goalSymbol) {
    var files = sources.Concat(drafts.Select(draft => new ContractSource(draft.Path, draft.Content, draft.Sha256)))
      .Append(generator).ToList();
    if (files.Any(file => file == null || string.IsNullOrWhiteSpace(file.Path) || Path.IsPathRooted(file.Path) ||
          file.Path.Replace('\\', '/').Split('/').Any(part => part is "." or "..") ||
          file.Content == null || ContractHarnessBuilder.Hash(file.Content) != file.Sha256) ||
        files.Select(file => ContractSourceSnapshot.UriFor(file.Path)).Distinct().Count() != files.Count) {
      throw new ArgumentException("Runtime authoring sources and packets require distinct relative paths and matching hashes.");
    }
    if (drafts.Any(draft => draft.Path != ".top-down-pbt/drafts/" + draft.Symbol + ".dfy") ||
        generator.Path != ".top-down-pbt/generators/" + goalSymbol + ".dfy") {
      throw new ArgumentException("Runtime authoring packets require canonical draft and generator paths.");
    }
  }

  private static void ValidateSourceBudget(IEnumerable<ContractSource> sources, string owner) {
    long total = 0;
    var count = 0;
    foreach (var source in sources) {
      count++;
      if (count > MaximumSourceCount || source == null || source.Content == null) {
        throw new ArgumentException(owner + " exceed the bounded source policy.");
      }
      var bytes = Encoding.UTF8.GetByteCount(source.Content);
      if (bytes > MaximumSourceBytes - total) {
        throw new ArgumentException(owner + " exceed the bounded source policy.");
      }
      total += bytes;
    }
  }

  private static string Diagnostics(BatchErrorReporter reporter) => string.Join("\n",
    reporter.AllMessages.Where(message => message.Level == ErrorLevel.Error).Select(message =>
      message.Range.StartToken.Uri + ":" + message.Range.StartToken.line + ":" +
      message.Range.StartToken.col + ": " + message.Message));

  private static string Slice(string content, int start, int length) =>
    Encoding.UTF8.GetString(Encoding.UTF8.GetBytes(content), start, length);

  private static string InsertBytes(string content, int start, string text) => ReplaceBytes(content, start, 0, text);

  private static string ReplaceBytes(string content, int start, int length, string text) {
    var bytes = Encoding.UTF8.GetBytes(content);
    if (start < 0 || length < 0 || start + length > bytes.Length) {
      throw new NotSupportedException("Runtime authoring source span is outside its snapshot.");
    }
    return Encoding.UTF8.GetString(bytes, 0, start) + text +
      Encoding.UTF8.GetString(bytes, start + length, bytes.Length - start - length);
  }
}
