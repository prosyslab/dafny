#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

internal sealed record ContractScreenQuery(string Source, string SourcePath, string Name, int Start, int End) {
  internal ContractScreenProjection? Projection { get; init; }
}
internal sealed record ContractScreenOmittedBody(string SourcePath, string Symbol, int Start, int End);
internal sealed record ContractScreenParsed(Program Program, IReadOnlyList<DefinitionAnalysisResult> OriginalSpans,
  IReadOnlyList<ContractScreenOmittedBody> OmittedBodies, ContractScreenProjection? Projection);
internal sealed record ContractScreenDeclarationKey(string SourcePath, string Kind, string Name, int Start, int End);
internal sealed record ContractScreenProjection(string SourceSetHash, ContractScreenDeclarationKey Target,
  IReadOnlyList<ContractScreenDeclarationKey> Members, IReadOnlyList<ContractScreenDeclarationKey> Modules,
  IReadOnlyDictionary<ContractScreenDeclarationKey, string> References,
  IReadOnlyList<DefinitionAnalysisResult> OriginalSpans, IReadOnlyList<ContractScreenOmittedBody> OmittedBodies);

/// <summary>Resolves a private contracts-only snapshot while retaining the complete original source identity.</summary>
internal static class ContractScreenSourcePreparation {
  internal const string PolicyVersion = "contracts-only-same-module-pure-projection-v1";
  internal static readonly string[] Features = ["int",
    "nat",
    "bool",
    "char",
    "bitvector",
    "sequence",
    "string_as_sequence_of_characters",
    "finite_set",
    "multiset",
    "finite_map",
    "transparent_expression_functions",
    "joint_output_existence",
    "lemma_implication"];

  internal static async Task<ContractScreenParsed> ParseAsync(ErrorReporter reporter,
    IReadOnlyList<ContractSource> sources, CancellationToken cancellationToken,
    ContractScreenQuery? query = null, Action<string, string>? phaseObserver = null,
    ContractScreenProjection? projection = null, ContractEntry? target = null) {
    if (projection == null) {
      if (query != null || target == null) { throw new ArgumentException("projection_target_required"); }
      ValidateOptions(reporter.Options);
      var beforeOptions = DefinitionAnalysis.ContextOptionsIdentity(reporter.Options);
      var discovery = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken, resolve: false, phaseObserver: phaseObserver);
      if (reporter.ErrorCount != 0) { return new(discovery, [], [], null); }
      CheckSourceOptions(discovery, reporter.Options, beforeOptions);
      var keys = RawDeclarations(discovery).ToDictionary(declaration => declaration, declaration => Key(declaration, null));
      var spans = DefinitionAnalysis.AnalyzeSpans(discovery, sources.Select(source => ContractSourceSnapshot.UriFor(source.Path)).ToHashSet());
      var omitted = new List<ContractScreenOmittedBody>();
      foreach (var method in keys.Keys.OfType<Method>().Where(method =>
                 (method.GetType() == typeof(Method) || method.GetType() == typeof(Lemma)) && !method.IsByMethod)) {
        if (method.Body == null) { continue; }
        omitted.Add(new(method.Origin.Uri.LocalPath, method.FullDafnyName,
          method.Body.StartToken.pos, method.Body.EndToken.pos + method.Body.EndToken.val.Length));
        method.ClearBody();
      }
      // Discovery resolves names and types only. It never translates or verifies this ambient program.
      await new ProgramResolver(discovery).Resolve(cancellationToken);
      if (reporter.ErrorCount != 0) { return new(discovery, spans, omitted, null); }
      var selected = ContractCallableSelector.SelectMethod(discovery, target, allowLemmaContract: true);
      if (!keys.TryGetValue(selected, out var targetKey) || selected.EnclosingClass is not DefaultClassDecl ||
          selected.GetType() != typeof(Method) && selected.GetType() != typeof(Lemma)) {
        throw new NotSupportedException("projection_target_kind");
      }
      var module = selected.EnclosingClass.EnclosingModuleDefinition;
      var expressions = selected.SubExpressions.ToList();
      CheckResolvedMember(discovery, selected, false);
      // This restricted fragment has only built-in value types and expression calls.
      // The general runtime closure also follows every initializer of a receiver's
      // class; that is deliberately not a dependency of a static pure expression.
      var pending = new Stack<Function>(expressions.SelectMany(ContractRuntimeObligationTransformer.FunctionReferences));
      var visitedFunctions = new HashSet<Function>();
      var retained = new List<MemberDecl> { selected };
      while (pending.TryPop(out var function)) {
        if (!visitedFunctions.Add(function)) { continue; }
        if (IsSystem(discovery, function)) { throw new NotSupportedException("system_callable_dependency"); }
        if (function.EnclosingClass is not DefaultClassDecl ||
            function.EnclosingClass.EnclosingModuleDefinition != module || !keys.ContainsKey(function)) {
          throw new NotSupportedException("projection_dependency_kind");
        }
        CheckResolvedMember(discovery, function, false);
        retained.Add(function);
        foreach (var dependency in function.SubExpressions.Append(function.Body!).SelectMany(ContractRuntimeObligationTransformer.FunctionReferences)) {
          pending.Push(dependency);
        }
      }
      retained = retained.Distinct().ToList();
      var moduleKeys = new List<ContractScreenDeclarationKey>();
      for (var ancestor = module; ancestor != null && ancestor != discovery.DefaultModuleDef; ancestor = ancestor.EnclosingModule) {
        CheckModule(ancestor);
        if (ancestor.EnclosingLiteralModuleDecl == null || !keys.TryGetValue(ancestor.EnclosingLiteralModuleDecl, out var moduleKey)) {
          throw new NotSupportedException("projection_module_identity");
        }
        moduleKeys.Add(moduleKey);
      }
      foreach (var member in retained) { CheckResolvedMember(discovery, member, false); }
      var retainedKeys = retained.Select(member => keys[member]).ToList();
      var references = retained.ToDictionary(member => keys[member], member =>
        ReferenceIdentity(discovery, member, keys, retainedKeys, moduleKeys, null));
      projection = new(ContractRuntimeTypeEvidence.SourceSetHash(sources), targetKey, retainedKeys, moduleKeys,
        references, spans, omitted);
    }
    return await ParseProjectedAsync(reporter, sources, cancellationToken, query, phaseObserver, projection);
  }

  private static void ValidateOptions(DafnyOptions options) {
    if (!DefinitionAnalysis.SupportsDiagnosticContext(options) ||
        ContractGeneratorProof.ProofOptionFailure(options) != null) {
      throw new NotSupportedException("unsupported_options");
    }
    if (!string.IsNullOrEmpty(options.Get(CommonOptionBag.PartialEvalEntry)) ||
        options.Get(CommonOptionBag.UnrollBoundedQuantifiers) != null) {
      throw new NotSupportedException("unsupported_source_transform");
    }
  }

  private static async Task<ContractScreenParsed> ParseProjectedAsync(ErrorReporter reporter,
    IReadOnlyList<ContractSource> sources, CancellationToken cancellationToken, ContractScreenQuery? query,
    Action<string, string>? phaseObserver, ContractScreenProjection projection) {
    ValidateOptions(reporter.Options);
    var originalSources = sources;
    if (query != null) {
      var bytes = Encoding.UTF8.GetBytes(query.Source);
      var start = Encoding.UTF8.GetCharCount(bytes, 0, query.Start);
      var length = Encoding.UTF8.GetCharCount(bytes, query.Start, query.End - query.Start);
      originalSources = ContractSourceSnapshot.Replace(sources, query.SourcePath, query.Source.Remove(start, length));
    }
    if (ContractRuntimeTypeEvidence.SourceSetHash(originalSources) != projection.SourceSetHash) {
      throw new ArgumentException("projection_source_binding");
    }
    var beforeOptions = DefinitionAnalysis.ContextOptionsIdentity(reporter.Options);
    var program = await ContractSourceSnapshot.ParseAsync(reporter, sources, cancellationToken,
      resolve: false, phaseObserver: phaseObserver);
    if (reporter.ErrorCount != 0) { return new(program, [], [], projection); }
    CheckSourceOptions(program, reporter.Options, beforeOptions);
    var rawKeys = RawDeclarations(program).ToDictionary(declaration => declaration, declaration => Key(declaration, query));
    var seenModules = new HashSet<ModuleDefinition>();
    Prune(program.DefaultModuleDef);
    foreach (var file in program.Files) { Prune(file); }
    // These ranges must be captured before body removal: several AST ranges are lazy.
    var spans = projection.OriginalSpans;
    var omitted = new List<ContractScreenOmittedBody>();
    var originalMembers = new HashSet<MemberDecl>();
    var keptQueries = 0;
    VisitModule(program.DefaultModuleDef);
    if (query != null && keptQueries != 1) { throw new NotSupportedException("generated_query_identity"); }
    await ContractPhaseRecorder.MeasureAsync(phaseObserver, "resolve", cancellationToken,
      () => new ProgramResolver(program).Resolve(cancellationToken));
    if (reporter.ErrorCount == 0) {
      foreach (var module in program.RawModules().Where(module => module != program.SystemModuleManager.SystemModule)) {
        CheckModule(module);
        foreach (var declaration in module.TopLevelDecls) {
          if (declaration is LiteralModuleDecl) { continue; }
          if (declaration is not DefaultClassDecl owner) { throw new NotSupportedException("ambient_declaration:" + declaration.GetType().Name); }
          foreach (var member in owner.Members) {
            if (!originalMembers.Contains(member)) { throw new NotSupportedException("generated_user_declaration"); }
            CheckResolvedMember(program, member, IsQuery(member));
          }
        }
      }
    }
    if (reporter.ErrorCount == 0) {
      var actualMembers = originalMembers.Where(member => !IsQuery(member)).ToList();
      if (!actualMembers.Select(member => rawKeys[member]).ToHashSet().SetEquals(projection.Members)) {
        throw new NotSupportedException("projection_member_identity");
      }
      foreach (var member in actualMembers) {
        if (!projection.References.TryGetValue(rawKeys[member], out var expected) || expected !=
            ReferenceIdentity(program, member, rawKeys, projection.Members, projection.Modules, query)) {
          throw new NotSupportedException("projection_reference_mismatch");
        }
      }
    }
    return new(program, spans, projection.OmittedBodies, projection);

    bool IsQuery(MemberDecl member) => query != null && member is Method && member.Name == query.Name &&
      member.Origin.Uri == ContractSourceSnapshot.UriFor(query.SourcePath) &&
      member.StartToken.pos >= query.Start && member.EndToken.pos < query.End &&
      ContractSourceSnapshot.Find(sources, member.Origin.Uri).Content == query.Source;

    void Prune(ModuleDefinition module) {
      if (!seenModules.Add(module)) { return; }
      foreach (var owner in module.DefaultClasses.OfType<DefaultClassDecl>()) {
        owner.Members.RemoveAll(member => !IsQuery(member) &&
          (!rawKeys.TryGetValue(member, out var key) || !projection.Members.Contains(key)));
        owner.SetMembersBeforeResolution();
      }
      module.SourceDecls.RemoveAll(declaration => declaration is not LiteralModuleDecl ||
        !rawKeys.TryGetValue(declaration, out var key) || !projection.Modules.Contains(key));
      module.PrefixNamedModules.Clear();
      // Fresh parser state only: never prune an already resolved module graph.
      if (module.ResolvedPrefixNamedModules.Count != 0) { throw new NotSupportedException("projection_resolved_raw_module"); }
      foreach (var nested in module.SourceDecls.OfType<LiteralModuleDecl>()) { Prune(nested.ModuleDef); }
      module.PreResolveSnapshotForFormatter();
    }

    void VisitModule(ModuleDefinition module) {
      CheckModule(module);
      foreach (var declaration in module.TopLevelDecls) {
        if (declaration.Attributes != null) { throw new NotSupportedException("source_declaration_attributes"); }
        if (declaration is LiteralModuleDecl nested) { VisitModule(nested.ModuleDef); continue; }
        if (declaration is not DefaultClassDecl owner) { throw new NotSupportedException("ambient_declaration:" + declaration.GetType().Name); }
        foreach (var member in owner.Members) {
          cancellationToken.ThrowIfCancellationRequested();
          originalMembers.Add(member);
          var generatedQuery = IsQuery(member);
          if (member is Method method && (method.GetType() == typeof(Method) || method.GetType() == typeof(Lemma)) && !method.IsByMethod) {
            CheckRawCallable(method);
            if (method.Mod.Expressions?.Count > 0 || method.Mod.Attributes != null) {
              throw new NotSupportedException("method_frame");
            }
            if (generatedQuery) { keptQueries++; continue; }
            if (method.Body != null) {
              omitted.Add(new(member.Origin.Uri.LocalPath, member.FullDafnyName,
                method.Body.StartToken.pos, method.Body.EndToken.pos + method.Body.EndToken.val.Length));
              method.ClearBody();
            }
            AuditRawExpressions(method.SubExpressions);
          } else if (member is Function function && (function.GetType() == typeof(Function) || function.GetType() == typeof(Predicate))) {
            CheckRawCallable(function);
            if (function.Body == null || function.ByMethodBody != null || function.IsOpaque ||
                function.IsMadeImplicitlyOpaque(reporter.Options)) {
              throw new NotSupportedException("unsupported_logical_definition");
            }
            AuditRawExpressions(function.SubExpressions.Append(function.Body));
          } else {
            throw new NotSupportedException("ambient_member:" + member.GetType().Name);
          }
        }
      }
    }
  }

  private static IEnumerable<Declaration> RawDeclarations(Program program) =>
    program.DefaultModuleDef.Descendants().Concat(program.Files.SelectMany(file => file.Descendants()))
      .OfType<Declaration>().Distinct();

  private static void CheckSourceOptions(Program program, DafnyOptions options, string beforeOptions) {
    if (beforeOptions != DefinitionAnalysis.ContextOptionsIdentity(options) ||
        RawDeclarations(program).Any(declaration => Attributes.Contains(declaration.Attributes, "options")) ||
        program.DefaultModuleDef.Descendants().Prepend(program.DefaultModuleDef).OfType<ModuleDefinition>()
          .Any(module => Attributes.Contains(module.Attributes, "options"))) {
      throw new NotSupportedException("source_options");
    }
  }

  private static ContractScreenDeclarationKey Key(Declaration declaration, ContractScreenQuery? query) =>
    new(declaration.Origin.Uri?.ToString() ?? "", declaration.GetType().Name, declaration.Name,
      OriginalOffset(declaration.Origin.Uri, declaration.StartToken.pos, query),
      OriginalOffset(declaration.Origin.Uri, declaration.EndToken.pos + declaration.EndToken.val.Length, query));

  private static int OriginalOffset(Uri? source, int position, ContractScreenQuery? query) =>
    query != null && source == ContractSourceSnapshot.UriFor(query.SourcePath) && position >= query.End
      ? position - (query.End - query.Start) : position;

  private static bool IsSystem(Program program, Declaration declaration) => declaration switch {
    MemberDecl member => member.EnclosingClass.EnclosingModuleDefinition == program.SystemModuleManager.SystemModule,
    TopLevelDecl top => top.EnclosingModuleDefinition == program.SystemModuleManager.SystemModule,
    _ => false
  };

  private static string ReferenceIdentity(Program program, MemberDecl member,
    IReadOnlyDictionary<Declaration, ContractScreenDeclarationKey> keys,
    IReadOnlyList<ContractScreenDeclarationKey> retained, IReadOnlyList<ContractScreenDeclarationKey> modules,
    ContractScreenQuery? query) {
    var facts = new List<string> { member.FullDafnyName };
    var nodes = member.Descendants().Prepend(member).ToList();
    foreach (var node in nodes.OfType<IHasReferences>()) {
      foreach (var reference in node.GetReferences()) {
        facts.Add("reference:" + Position(reference.Referer.StartToken) + ":" + Position(reference.Referer.EndToken) + ":" + Target(reference.Referred));
      }
    }
    var roots = member is Function function ? function.SubExpressions.Append(function.Body!) : ((Method)member).SubExpressions;
    foreach (var expression in ResolvedExpressions(roots)) {
      if (expression is StaticReceiverExpr) { continue; }
      if (expression.Type == null || !SupportedType(program, expression.Type)) { throw new NotSupportedException("projection_expression_type"); }
      facts.Add("type:" + Position(expression.StartToken) + ":" + expression.Type.NormalizeExpandKeepConstraints());
      if (expression is FunctionCallExpr call) { facts.Add("call:" + Position(call.StartToken) + ":" + Target(call.Function)); }
      if (expression is IdentifierExpr identifier) { facts.Add("variable:" + Position(identifier.StartToken) + ":" + Target(identifier.Var)); }
    }
    return ContractHarnessBuilder.Hash(JsonSerializer.Serialize(facts.OrderBy(fact => fact, StringComparer.Ordinal)));

    string Position(IOrigin token) => (token.Uri?.ToString() ?? "") + ":" + OriginalOffset(token.Uri, token.pos, query);
    string Target(IHasNavigationToken target) {
      if (target is Declaration declaration) {
        if (IsSystem(program, declaration)) { return "system:" + declaration.GetType().Name + ":" + declaration.Name; }
        if (declaration is DefaultClassDecl defaultClass) { return "default-class:" + defaultClass.EnclosingModuleDefinition.FullDafnyName; }
        if (keys.TryGetValue(declaration, out var key) && (retained.Contains(key) || modules.Contains(key))) {
          return JsonSerializer.Serialize(key);
        }
        throw new NotSupportedException("projection_reference_outside_closure");
      }
      if (target is IVariable variable && SupportedType(program, variable.Type)) {
        return "variable:" + variable.Name + ":" + Position(variable.NavigationRange.StartToken) + ":" + variable.Type.NormalizeExpandKeepConstraints();
      }
      throw new NotSupportedException("projection_unknown_reference");
    }
  }

  private static void CheckModule(ModuleDefinition module) {
    if (module.Attributes != null || module.Implements != null || module.IsFacade ||
        module.ModuleKind != ModuleKindEnum.Concrete || module.PrefixNamedModules.Count != 0) {
      throw new NotSupportedException("unsupported_module");
    }
  }

  private static void CheckRawCallable(MethodOrFunction callable) {
    var formals = callable.Ins.Concat(callable is Method method ? method.Outs : []);
    if (callable.Attributes != null || callable.TypeArgs.Count != 0 || callable.IsRefining ||
        callable.Reads.Expressions?.Count > 0 || callable.Reads.Attributes != null || callable.Decreases.Attributes != null ||
        callable.Req.Concat(callable.Ens).Any(clause => clause.Attributes != null) ||
        formals.Any(formal => !formal.IsTypeExplicit || formal.Attributes != null || formal.DefaultValue != null)) {
      throw new NotSupportedException("unsupported_callable_header");
    }
  }

  private static void AuditRawExpressions(IEnumerable<Expression> expressions) {
    foreach (var expression in expressions) {
      foreach (var node in expression.DescendantsAndSelf) {
        if (node is StmtExpr) { throw new NotSupportedException("logical_proof_body_unsupported"); }
        if (node is IAttributeBearingDeclaration { Attributes: not null }) {
          throw new NotSupportedException("source_expression_attributes");
        }
      }
    }
  }

  internal static bool SupportedType(Program program, Type type) {
    type = type.NormalizeExpandKeepConstraints();
    if (type is UserDefinedType user) { return ReferenceEquals(user.ResolvedClass, program.SystemModuleManager.NatDecl); }
    if (type is TypeProxy) { return false; }
    return type.IsIntegerType || type.IsBoolType || type.IsCharType || type.IsBitVectorType ||
      type is SeqType sequence && SupportedType(program, sequence.Arg) ||
      type is SetType { Finite: true } set && SupportedType(program, set.Arg) ||
      type is MultiSetType multiset && SupportedType(program, multiset.Arg) ||
      type is MapType { Finite: true } map && SupportedType(program, map.Domain) && SupportedType(program, map.Range);
  }

  private static void CheckResolvedMember(Program program, MemberDecl member, bool generatedQuery) {
    if (member is not MethodOrFunction callable || !callable.IsStatic ||
        callable.Ins.Any(formal => !SupportedType(program, formal.Type))) {
      throw new NotSupportedException("unsupported_callable_type");
    }
    if (member is Method method) {
      if (method.Outs.Any(formal => !SupportedType(program, formal.Type)) ||
          method is Lemma && method.Outs.Count != 0 || method.Body != null && !generatedQuery) {
        throw new NotSupportedException("unsupported_method");
      }
      if (generatedQuery) { return; }
      foreach (var expression in method.SubExpressions) { CheckExpression(program, expression); }
    } else if (member is Function function) {
      if (!SupportedType(program, function.ResultType) || function.Body == null || function.ByMethodDecl != null ||
          function.ReadsHeap || function.IsOpaque || function.IsMadeImplicitlyOpaque(program.Options)) {
        throw new NotSupportedException("unsupported_logical_definition");
      }
      foreach (var expression in function.SubExpressions.Append(function.Body)) { CheckExpression(program, expression); }
    }
  }

  private static void CheckExpression(Program program, Expression root) {
    foreach (var expression in ResolvedExpressions([root])) {
      if (expression is StaticReceiverExpr) { continue; }
      if (expression.Type == null || !SupportedType(program, expression.Type)) {
        throw new NotSupportedException("unsupported_expression_type");
      }
      var supported = expression switch {
        LiteralExpr or IdentifierExpr or BinaryExpr or ConversionExpr or
          SeqSelectExpr or SeqUpdateExpr or DisplayExpression or MapDisplayExpr or MultiSetFormingExpr => true,
        UnaryOpExpr unary => unary.Op is not (UnaryOpExpr.Opcode.Fresh or UnaryOpExpr.Opcode.Allocated),
        ITEExpr conditional => !conditional.IsBindingGuard,
        LetExpr let => let.Exact,
        QuantifierExpr quantifier => quantifier.BoundVars.All(variable => SupportedType(program, variable.Type)),
        SetComprehension set => set.Finite && set.BoundVars.All(variable => SupportedType(program, variable.Type)),
        MapComprehension map => map.Finite && map.BoundVars.All(variable => SupportedType(program, variable.Type)),
        FunctionCallExpr call => call.Function.IsStatic && !call.Function.ReadsHeap,
        MemberSelectExpr select => select.Member.EnclosingClass.EnclosingModuleDefinition == program.SystemModuleManager.SystemModule,
        _ => false
      };
      if (!supported) { throw new NotSupportedException("unsupported_expression:" + expression.GetType().Name); }
    }
  }

  private static IEnumerable<Expression> ResolvedExpressions(IEnumerable<Expression> roots) {
    var seen = new HashSet<Expression>();
    var pending = new Stack<Expression>(roots);
    while (pending.TryPop(out var expression)) {
      expression = expression.Resolved;
      if (!seen.Add(expression)) { continue; }
      yield return expression;
      foreach (var child in expression.SubExpressions) { pending.Push(child); }
    }
  }
}
