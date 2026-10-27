using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Threading;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractRuntimeClause(ContractRuntimeObligation Obligation, Expression Expression,
  IReadOnlyList<IVariable> Variables, Method Owner, bool UnvalidatedCallees = false,
  int? EntryHeapPostcondition = null, bool TypeConstraint = false, string? OriginalSourceHash = null, string? OriginalSourceSetHash = null, string? CallHeapScope = null);
/// <summary>Contains detached runtime sources and the original checks retained for execution.</summary>
public sealed record ContractRuntimeTransformation(IReadOnlyList<ContractSource> Sources,
  IReadOnlyList<ContractRuntimeClause> Clauses, IReadOnlyList<ContractRuntimeDeghostExclusion> Exclusions,
  string MainName, ContractPreparedProgram Prepared, IReadOnlySet<Field> CompiledGhostFields) {
  /// <summary>Whether a matching internal proof omitted the selected entry method's explicit requires checks.</summary>
  public bool EntryRequiresOmitted { get; init; }
}

/// <summary>Creates a detached executable diagnostic copy while preserving original obligation locations.</summary>
public sealed class ContractRuntimeObligationTransformer {
  private readonly Program program;
  private readonly IReadOnlyList<ContractSource> sources;
  private readonly Method goal;
  private readonly MethodOrFunction nativeGoal;
  private readonly Method generator;
  private readonly ContractRuntimeContractModelPlan? contractModels;
  private readonly ContractRuntimeSourceMap? sourceMap;
  private readonly IReadOnlyDictionary<string, string> rejected;
  private readonly IReadOnlySet<string> diagnosticConstructors;
  private readonly List<Edit> edits = [];
  private readonly List<ContractRuntimeClause> clauses = [];
  private readonly List<ContractRuntimeDeghostExclusion> exclusions = [];
  private readonly HashSet<Function> functions;
  private readonly HashSet<MethodOrFunction> reachable;
  private readonly HashSet<DatatypeCtor> reachableDatatypeConstructors = [];
  private readonly HashSet<IteratorDecl> reachableIterators;
  private readonly HashSet<Field> fields;
  private readonly HashSet<Field> compiledGhostFields = [];
  private readonly HashSet<IVariable> variables = [];
  private readonly Dictionary<Method, string> oldDeclarations = [];
  private readonly Dictionary<Method, Dictionary<Expression, IVariable>> oldNames = [];
  private readonly Dictionary<Function, string> specWrappers = [];
  private readonly Function? goalFunction;
  private readonly bool lemmaContract;
  private readonly bool omitEntryRequires;
  private readonly IReadOnlyDictionary<string, ContractRuntimeDecisionMethod> decisionCaps;
  private readonly Dictionary<TopLevelDecl, string?> membershipHelpers = [];
  private readonly Dictionary<DatatypeDecl, string?> recursiveMembershipHelpers = [];
  private readonly Dictionary<Function, string> definitionNames = [];
  private IReadOnlyList<TypeParameter> shapeParameters = [];
  private readonly HashSet<MethodOrFunction> shapedCallables = [];
  private readonly string originalSourceSetHash;
  private readonly Lazy<string> resultFamily;
  private readonly string outputFamily;
  private readonly string runtimeAlias;
  private readonly string runtimeBridge;
  private readonly Dictionary<Uri, SourceText> sourceTextCache = [];
  private int nextName;
  private sealed record PendingOldCapture(Expression Key, Expression Value, IVariable Variable);
  internal sealed record Edit(Uri Uri, int Start, int Length, string Text);
  private sealed class SourceText(ContractSource source) {
    private readonly byte[] bytes = Encoding.UTF8.GetBytes(source.Content);
    private readonly Dictionary<int, int> indices = new() { [0] = 0 };

    internal string Content => source.Content;

    internal int Index(int byteOffset) {
      if (byteOffset < 0 || byteOffset > bytes.Length) {
        throw new ArgumentException("Invalid source token offset.");
      }
      if (!indices.TryGetValue(byteOffset, out var index)) {
        index = Encoding.UTF8.GetCharCount(bytes, 0, byteOffset);
        indices.Add(byteOffset, index);
      }
      return index;
    }

    internal string Slice(int start, int length) {
      var first = Index(start);
      return Content.Substring(first, Index(start + length) - first);
    }
  }

  /// <summary>Prepares runtime obligations, accepting proof omission only through a matching internal certificate.</summary>
  public ContractRuntimeObligationTransformer(Program program, IReadOnlyList<ContractSource> sources, Method goal, ContractRuntimeSourceMap? sourceMap = null, IReadOnlyDictionary<string, string>? rejected = null,
    IReadOnlyDictionary<string, ContractRuntimeDecisionMethod>? decisionCaps = null, IReadOnlySet<string>? diagnosticConstructors = null, string? originalSourceSetHash = null,
    ContractGeneratorProofReport? generatorProof = null, Method? selectedGenerator = null,
    ContractRuntimeContractModelPolicy? contractModelPolicy = null) {
    this.program = program;
    nativeGoal = ContractCallableSelector.NativeCallable(program, goal);
    var generator = selectedGenerator ?? LegacyGenerator(program, goal);
    if (!Members(program).OfType<Method>().Any(method => ReferenceEquals(method, generator)) ||
        generator.EnclosingClass.EnclosingModuleDefinition != goal.EnclosingClass.EnclosingModuleDefinition) {
      throw new ArgumentException("The exact generator must belong to the goal module in the supplied program.", nameof(generator));
    }
    if (selectedGenerator != null && (generator.EnclosingClass is not DefaultClassDecl ||
        generator.Origin.Uri != goal.Origin.Uri ||
        generator.Name != ContractRuntimeGeneratorSignature.Names(goal, generator).MethodName ||
        !ContractRuntimeGeneratorSignature.HasExactMarker(generator, goal.FullDafnyName))) {
      throw new ArgumentException("The selected generator must match the canonical target marker, module and source.", nameof(selectedGenerator));
    }
    // The transformer emits detached text without mutating this resolved program.
    resultFamily = new(() => ContractBodyNames.Family(program, "contractResult"));
    outputFamily = ContractBodyNames.Family(program, "pbtOutput");
    runtimeAlias = ContractBodyNames.Family(program, "PbtRuntimeAlias");
    runtimeBridge = ContractBodyNames.Family(program, "PbtRuntimeBridge");
    this.originalSourceSetHash = originalSourceSetHash ?? ContractRuntimeTypeEvidence.SourceSetHash(sources);
    this.decisionCaps = decisionCaps ?? new Dictionary<string, ContractRuntimeDecisionMethod>();
    this.sources = sources;
    this.goal = goal;
    this.generator = generator;
    contractModels = ContractRuntimeContractModels.Create(program, goal, contractModelPolicy);
    contractModels?.ValidateGenerator(generator);
    lemmaContract = goal is Lemma;
    var verifiedCertificate = generatorProof is {
      Status: ContractGeneratorProofStatus.Verified,
      VerifiedCertificate: { } certificate
    } ? certificate : null;
    var requiredProofChecks = generatorProof?.RequiredNativeChecks?.ToHashSet(StringComparer.Ordinal) ?? new HashSet<string>(StringComparer.Ordinal);
    var coveredProofChecks = generatorProof?.CoveredNativeChecks?.ToHashSet(StringComparer.Ordinal) ?? new HashSet<string>(StringComparer.Ordinal);
    var proofSelectedGenerator = verifiedCertificate != null && !lemmaContract ? generator : null;
    omitEntryRequires = contractModels == null && proofSelectedGenerator != null && requiredProofChecks.Count > 0 &&
      requiredProofChecks.SetEquals(coveredProofChecks) && verifiedCertificate!.Matches(
      program, sources, goal, proofSelectedGenerator, program.Options, requiredProofChecks);

    this.sourceMap = sourceMap;
    this.rejected = rejected ?? new Dictionary<string, string>();
    this.diagnosticConstructors = diagnosticConstructors ?? new HashSet<string>();
    goalFunction = nativeGoal as Function;
    var diagnosticDependencies = new HashSet<Declaration>();
    reachable = DiagnosticReachable(program, nativeGoal,
      generator, diagnosticDependencies).ToHashSet();
    reachableIterators = diagnosticDependencies.OfType<IteratorDecl>()
      .Concat(reachable.Select(callable => callable.EnclosingClass).OfType<IteratorDecl>()).ToHashSet();
    fields = reachable.Where(c => !this.diagnosticConstructors.Contains(c.FullDafnyName))
      .SelectMany(c => c.Descendants()).OfType<MemberSelectExpr>()
      .Select(select => select.Member).OfType<Field>().ToHashSet();
    if (contractModels != null) { fields.UnionWith(contractModels.Fields); }
    foreach (var constructor in reachable.OfType<Constructor>().Where(c => this.diagnosticConstructors.Contains(c.FullDafnyName))) {
      var supplied = ContractDiagnosticConstruction.SuppliedFieldNames(constructor);
      fields.UnionWith(((TopLevelDeclWithMembers)constructor.EnclosingClass).Members.OfType<Field>()
        .Where(field => supplied.Contains(field.Name)));
    }
    functions = reachable.OfType<Function>().Where(f => f.IsGhost && f.Body != null &&
      f is not TwoStateFunction && f.ByMethodBody == null && !this.rejected.ContainsKey(f.FullDafnyName)).ToHashSet();
  }

  public static IEnumerable<MemberDecl> Members(Program program) => program.RawModules()
    .SelectMany(module => module.TopLevelDecls).OfType<TopLevelDeclWithMembers>().SelectMany(type => type.Members);
  private IEnumerable<MemberDecl> Members() => Members(program).Where(m => m.EnclosingClass.EnclosingModuleDefinition.Name is not ("PbtRuntime" or "PbtRandom") && sources.Any(s => ContractSourceSnapshot.UriFor(s.Path) == m.Origin.Uri));
  private IEnumerable<IteratorDecl> Iterators() => program.RawModules()
    .Where(module => module.Name is not ("PbtRuntime" or "PbtRandom"))
    .SelectMany(module => module.TopLevelDecls).OfType<IteratorDecl>()
    .Where(iterator => sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == iterator.Origin.Uri));
  public static IEnumerable<ICallable> Reachable(Program program, MethodOrFunction goal) => ContractHarnessBuilder.ReachableCallables(program, goal);
  public static IEnumerable<MethodOrFunction> DiagnosticReachable(Program program, Method goal) {
    var nativeGoal = ContractCallableSelector.NativeCallable(program, goal);
    return DiagnosticReachable(program, nativeGoal, nativeGoal.EnclosingClass.EnclosingModuleDefinition);
  }

  /// <summary>Execution reachability from a goal callable and one exact generator.</summary>
  public static IEnumerable<MethodOrFunction> DiagnosticReachable(Program program, Method goal, Method generator) =>
    DiagnosticReachable(program, ContractCallableSelector.NativeCallable(program, goal), generator, null);

  /// <summary>Execution reachability from a goal callable and the generator inserted at its module's top level.</summary>
  public static IEnumerable<MethodOrFunction> DiagnosticReachable(Program program, MethodOrFunction goal, Method generator) {
    return DiagnosticReachable(program, goal, generator, null);
  }

  private static IEnumerable<MethodOrFunction> DiagnosticReachable(Program program, MethodOrFunction goal,
    Method generator, ISet<Declaration>? declarationDependencies) {
    IEnumerable<MethodOrFunction> roots = [generator];
    return ExecutionReachable(program, goal is Lemma ? roots : roots.Prepend(goal),
      goal is Lemma ? goal.Ins.Select(formal => formal.Type) : null, declarationDependencies);
  }

  /// <summary>Returns why runtime execution through a structurally reached iterator is unsupported.</summary>
  public static string? UnsupportedRuntimeIterator(Program program, Method goal, Method? generator = null,
    CancellationToken cancellationToken = default) {
    var root = ContractCallableSelector.NativeCallable(program, goal);
    IEnumerable<MethodOrFunction> initialRoots = Enumerable.Empty<MethodOrFunction>();
    if (goal is not Lemma) {
      initialRoots = new[] { root };
    }
    IEnumerable<MethodOrFunction> roots = generator == null
      ? initialRoots
      : goal is Lemma ? new MethodOrFunction[] { generator } : new[] { root, generator };
    var reachable = RuntimeExecutionReachable(program, roots,
      goal is Lemma ? goal.Ins.Select(formal => formal.Type) : null, cancellationToken: cancellationToken);
    var iterator = reachable
      .Select(callable => callable is MemberDecl { EnclosingClass: IteratorDecl declaration } ? declaration : null)
      .OfType<IteratorDecl>().OrderBy(declaration => declaration.FullDafnyName, StringComparer.Ordinal).FirstOrDefault();
    return iterator == null ? null :
      "Runtime execution through iterator '" + iterator.FullDafnyName +
      "' is not supported; choose a goal and generator that do not construct or advance an iterator.";
  }

  /// <summary>Execution reachability using the legacy Generate member in a supplied goal module.</summary>
  public static IEnumerable<MethodOrFunction> DiagnosticReachable(Program program, MethodOrFunction goal,
    ModuleDefinition goalModule) {
    var roots = goalModule.TopLevelDecls.OfType<DefaultClassDecl>().SelectMany(declaration => declaration.Members)
      .OfType<Method>().Where(method => method.Name == "Generate").Cast<MethodOrFunction>();
    return ExecutionReachable(program, goal is Lemma ? roots : roots.Prepend(goal),
      goal is Lemma ? goal.Ins.Select(formal => formal.Type) : null);
  }

  private static Method LegacyGenerator(Program program, Method goal) => Members(program).OfType<Method>()
    .Single(method => method.Name == "Generate" &&
      method.EnclosingClass.EnclosingModuleDefinition == goal.EnclosingClass.EnclosingModuleDefinition);

  private static bool IsRuntimeMainFamily(string name) =>
    name.StartsWith("PbtMain", StringComparison.Ordinal) && name["PbtMain".Length..].All(character => character == '0');

  /// <summary>
  /// Native call-graph reachability extended by edges that execution follows but the call graph omits:
  /// dynamic dispatch from trait members to their overrides, constraints and witnesses of subset types and
  /// newtypes used by reachable code, and class constant initializers evaluated when such objects are read.
  /// </summary>
  public static IReadOnlyList<MethodOrFunction> ExecutionReachable(Program program, IEnumerable<MethodOrFunction> roots,
    IEnumerable<Type>? additionalTypes = null, ISet<Declaration>? declarationDependencies = null,
    IEnumerable<ConstantField>? constantRoots = null, CancellationToken cancellationToken = default) {
    return ExecutionReachable(program, roots, additionalTypes, declarationDependencies, constantRoots, true, cancellationToken);
  }

  internal static IReadOnlyList<MethodOrFunction> RuntimeExecutionReachable(Program program,
    IEnumerable<MethodOrFunction> roots, IEnumerable<Type>? additionalTypes = null,
    ISet<Declaration>? declarationDependencies = null, IEnumerable<ConstantField>? constantRoots = null,
    CancellationToken cancellationToken = default) {
    return ExecutionReachable(program, roots, additionalTypes, declarationDependencies, constantRoots, false, cancellationToken);
  }

  private static IReadOnlyList<MethodOrFunction> ExecutionReachable(Program program,
    IEnumerable<MethodOrFunction> roots, IEnumerable<Type>? additionalTypes,
    ISet<Declaration>? declarationDependencies, IEnumerable<ConstantField>? constantRoots,
    bool includeIteratorTypeEdges, CancellationToken cancellationToken) {
    cancellationToken.ThrowIfCancellationRequested();
    var edges = program.RawModules().SelectMany(module => module.CallGraph.GetVertices().Concat(module.InterModuleCallGraph.GetVertices()))
      .GroupBy(vertex => vertex.N).ToDictionary(group => group.Key, group => group.SelectMany(vertex => vertex.Successors).Select(vertex => vertex.N).Distinct().ToList());
    var overrides = Members(program).Where(member => member.OverriddenMember != null).ToList();
    var reachable = new HashSet<ICallable>();
    var types = new HashSet<TopLevelDecl>();
    var pending = new Stack<ICallable>(roots.Cast<ICallable>().Concat(constantRoots ?? []));
    foreach (var dependency in (additionalTypes ?? []).SelectMany(type => TypeDependencies(type, types))) { pending.Push(dependency); }
    while (pending.TryPop(out var callable)) {
      cancellationToken.ThrowIfCancellationRequested();
      if (!reachable.Add(callable)) { continue; }
      if (callable is Function { ByMethodDecl: { } byMethod }) { pending.Push(byMethod); }
      foreach (var target in edges.GetValueOrDefault(callable) ?? []) {
        cancellationToken.ThrowIfCancellationRequested();
        // The resolver models a mentioned iterator type as a call-graph edge to its declaration.
        // Capability checks omit that pseudo edge while retaining direct _ctor and MoveNext edges.
        if (includeIteratorTypeEdges || target is not IteratorDecl) { pending.Push(target); }
      }
      foreach (var function in callable.Descendants().OfType<Expression>().Select(FunctionReference).OfType<Function>()) {
        cancellationToken.ThrowIfCancellationRequested();
        pending.Push(function);
      }
      if (callable is MemberDecl member) {
        foreach (var implementation in overrides.Where(o => o != member && o.Overrides(member)).OfType<ICallable>()) { pending.Push(implementation); }
      }
      foreach (var dependency in TypesOf(callable).SelectMany(type => TypeDependencies(type, types))) { pending.Push(dependency); }
    }
    declarationDependencies?.UnionWith(reachable.OfType<Declaration>().Concat(types));
    return reachable.OfType<MethodOrFunction>().ToList();

    IEnumerable<Type> TypesOf(ICallable callable) {
      if (callable is MethodOrFunction signature) {
        foreach (var formal in signature.Ins) { yield return formal.Type; }
        if (signature is MethodOrConstructor method) {
          foreach (var formal in method.Outs) { yield return formal.Type; }
        }
        if (signature is Function function) { yield return function.ResultType; }
      }
      if (callable is ConstantField constant) { yield return constant.Type; }
      if (callable is not INode node) { yield break; }
      foreach (var descendant in node.Descendants()) {
        cancellationToken.ThrowIfCancellationRequested();
        if (descendant is Expression { Type: { } type }) { yield return type; }
        if (descendant is VarDeclStmt declaration) {
          foreach (var local in declaration.Locals) { yield return local.Type; }
        }
      }
    }
    IEnumerable<ICallable> TypeDependencies(Type type, HashSet<TopLevelDecl> seen) {
      cancellationToken.ThrowIfCancellationRequested();
      type = type.NormalizeExpandKeepConstraints();
      foreach (var argument in type.TypeArgs) {
        foreach (var dependency in TypeDependencies(argument, seen)) { yield return dependency; }
      }
      if (type is not UserDefinedType { ResolvedClass: { } declaration } || !seen.Add(declaration)) { yield break; }
      foreach (var node in TypeConstraintExpressions(declaration).SelectMany(expression => LogicalNodes(expression).Prepend(expression))) {
        cancellationToken.ThrowIfCancellationRequested();
        if (node is CallStmt call) { yield return call.Method; }
        if (node is not Expression expression) { continue; }
        if (FunctionReference(expression.Resolved) is { } function) { yield return function; }
        if (expression.Resolved is MemberSelectExpr { Member: ConstantField constant }) { yield return constant; }
        if (expression.Type != null) {
          foreach (var dependency in TypeDependencies(expression.Type, seen)) { yield return dependency; }
        }
      }
      foreach (var constant in DefinedConstants(declaration)) { yield return constant; }
      foreach (var dependency in RelatedTypes(declaration).SelectMany(t => TypeDependencies(t, seen))) { yield return dependency; }
    }
  }

  /// <summary>The same diagnostic-name gate applies to selected source dependencies before and after authoring.</summary>
  public static string? UnsupportedDiagnosticNames(IEnumerable<MethodOrFunction> callables,
    IReadOnlyList<ContractSource> sources) {
    var members = callables.Where(member => sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == member.Origin.Uri))
      .ToArray();
    return members.Any(member => !IsRuntimeMainFamily(member.Name) &&
        (member.Name.StartsWith("Pbt", StringComparison.Ordinal) || member.Name.Contains("__pbt_", StringComparison.Ordinal)) ||
        member.Name.StartsWith("pbtTypeShape", StringComparison.Ordinal)) ||
      members.SelectMany(member => member.Descendants()).OfType<IVariable>()
        .Any(variable => variable.Name.StartsWith("pbtTypeShape", StringComparison.Ordinal))
      ? "Reserved Pbt diagnostic name collision." : null;
  }

  /// <summary>Generic callable values cannot carry the diagnostic type-shape parameters.</summary>
  public static string? UnsupportedGenericReferences(IEnumerable<MethodOrFunction> callables) {
    var members = callables.ToArray();
    var generic = members.Where(callable => callable.TypeArgs.Count > 0).ToHashSet();
    return members.SelectMany(callable => callable.Descendants()).OfType<MemberSelectExpr>()
      .Any(select => select.Member is Function function && generic.Contains(function))
      ? "Generic higher-order function references cannot forward diagnostic type shapes." : null;
  }

  // Refinement constraints and witnesses are evaluated with every value of the declared type.
  private static IEnumerable<Expression> TypeConstraintExpressions(TopLevelDecl declaration) => (declaration switch {
    SubsetTypeDecl subset => new[] { subset.Constraint, subset.Witness },
    NewtypeDecl newtype => new[] { newtype.Constraint, newtype.Witness },
    _ => []
  }).OfType<Expression>();

  private static IEnumerable<Type> RelatedTypes(TopLevelDecl declaration) => declaration switch {
    SubsetTypeDecl subset => [subset.Var.Type],
    TypeSynonymDeclBase synonym => [synonym.Rhs],
    NewtypeDecl newtype => [newtype.BaseType],
    ClassLikeDecl classLike => classLike.Members.OfType<Field>().Select(field => field.Type),
    DatatypeDecl datatype => datatype.Ctors.SelectMany(constructor => constructor.Formals).Select(formal => formal.Type),
    _ => Enumerable.Empty<Type>()
  };

  // Constant initializers run when a value of their enclosing type is read.
  private static IEnumerable<ConstantField> DefinedConstants(TopLevelDecl declaration) =>
    declaration is TopLevelDeclWithMembers withMembers
      ? withMembers.Members.OfType<ConstantField>().Where(field => field.Rhs != null)
      : [];

  /// <summary>Collects logical definitions and invoked proof methods without adding compiled by-method bodies.</summary>
  public static IReadOnlyList<MethodOrFunction> LogicalReachable(Program program, IEnumerable<MethodOrFunction> roots,
    IEnumerable<Type>? additionalTypes = null, ISet<Declaration>? declarationDependencies = null,
    IEnumerable<ConstantField>? constantRoots = null) {
    var overrides = Members(program).Where(member => member.OverriddenMember != null).ToList();
    var reachable = new HashSet<ICallable>();
    var types = new HashSet<TopLevelDecl>();
    var pending = new Stack<ICallable>(roots.Cast<ICallable>().Concat(constantRoots ?? []));
    foreach (var type in additionalTypes ?? []) { VisitType(type); }
    while (pending.TryPop(out var callable)) {
      if (!reachable.Add(callable)) { continue; }
      if (callable is MemberDecl member) {
        if (member.OverriddenMember is ICallable parent) { pending.Push(parent); }
        foreach (var implementation in overrides.Where(item => item != member && item.Overrides(member)).OfType<ICallable>()) {
          pending.Push(implementation);
        }
      }
      foreach (var node in LogicalNodes(callable)) { VisitNode(node); }
    }
    declarationDependencies?.UnionWith(reachable.OfType<Declaration>().Concat(types));
    return reachable.OfType<MethodOrFunction>().ToList();

    void VisitNode(INode node) {
      switch (node) {
        case Expression expression:
          if (FunctionReference(expression) is { } function) { pending.Push(function); }
          if (expression is MemberSelectExpr { Member: ConstantField constant }) { pending.Push(constant); }
          if (expression.Type != null) { VisitType(expression.Type); }
          break;
        case CallStmt call:
          pending.Push(call.Method);
          break;
        case Type type:
          VisitType(type);
          break;
        case MethodOrFunction generated:
          pending.Push((ICallable)generated);
          break;
      }
    }

    void VisitType(Type type) {
      type = type.NormalizeExpandKeepConstraints();
      foreach (var argument in type.TypeArgs) { VisitType(argument); }
      if (type is not UserDefinedType { ResolvedClass: { } declaration } || !types.Add(declaration)) { return; }
      foreach (var expression in TypeConstraintExpressions(declaration)) {
        VisitNode(expression);
        foreach (var node in LogicalNodes(expression)) { VisitNode(node); }
      }
      foreach (var constant in DefinedConstants(declaration)) { pending.Push(constant); }
      foreach (var relatedType in RelatedTypes(declaration)) { VisitType(relatedType); }
    }
  }

  // Function.Children also contains ByMethodBody; native call-graph edges can contain compiled-body calls.
  // Walk only the original logical AST, including StmtExpr's proof statements and resolved call children.
  internal static IEnumerable<INode> LogicalNodes(INode root) {
    var seen = new HashSet<INode>(ReferenceEqualityComparer.Instance) { root };
    var pending = new Stack<INode>(Children(root));
    while (pending.TryPop(out var node)) {
      if (!seen.Add(node)) { continue; }
      yield return node;
      foreach (var child in Children(node)) { pending.Push(child); }
    }
    static IEnumerable<INode> Children(INode node) => node is Function function
      ? function.Children.Where(child => !ReferenceEquals(child, function.ByMethodBody)) : node.Children;
  }

  internal static IEnumerable<Function> FunctionReferences(Expression expression) =>
    Expressions(expression).Select(FunctionReference).OfType<Function>();

  internal static Function? FunctionReference(Expression expression) => expression switch {
    FunctionCallExpr call => call.Function,
    MemberSelectExpr { Member: Function function } => function,
    _ => null
  };

  /// <summary>Maps diagnostic insertion ownership to its authoritative source declaration.</summary>
  public static ContractRuntimeClause? BindOriginalOwner(Program originalProgram, ContractRuntimeClause clause) {
    var member = Members(originalProgram).SingleOrDefault(candidate => candidate.FullDafnyName == clause.Owner.FullDafnyName);
    var owner = member switch {
      Method method => method,
      Function function => ContractCallableSelector.DescribeFunction(originalProgram, function),
      _ => null
    };
    return owner == null ? null : clause with { Owner = owner };
  }

  private static IEnumerable<Expression> Expressions(Expression expression) {
    expression = expression.Resolved;
    yield return expression;
    foreach (var child in expression.SubExpressions) {
      foreach (var descendant in Expressions(child)) { yield return descendant; }
    }
  }
  // Verification splits and substituted defaults retain original token positions. Walk each authored binding and
  // declaration default once so only its owning source tree can receive edits.
  private static IEnumerable<INode> SourceNodes(INode node) {
    if (node is DefaultValueExpression) { yield break; }
    node = node is Expression expression ? expression.Resolved : node;
    if (node is DefaultValueExpression) { yield break; }
    yield return node;
    IEnumerable<INode> children = node switch {
      QuantifierExpr quantifier => quantifier.PreResolveSubExpressions,
      FunctionCallExpr call => new INode[] { call.Receiver }.Concat(call.Bindings.ArgumentBindings),
      DatatypeValue value => value.Bindings.ArgumentBindings,
      ActualBindings bindings => bindings.ArgumentBindings,
      _ => node.Children
    };
    foreach (var child in children) {
      foreach (var descendant in SourceNodes(child)) { yield return descendant; }
    }
  }

  private static IEnumerable<Expression> SourceExpressions(Expression expression) =>
    SourceNodes(expression).OfType<Expression>();

  // Constructor defaults execute only when an authored construction reaches that constructor. Follow those
  // constructions through their declaration defaults without widening instrumentation to sibling constructors.
  private IEnumerable<DatatypeCtor> SourceDatatypeConstructors(IEnumerable<MethodOrFunction> roots) {
    var seen = new HashSet<DatatypeCtor>();
    var pending = new Stack<DatatypeCtor>(roots.SelectMany(SourceNodes).OfType<DatatypeValue>()
      .Select(value => value.Ctor).OfType<DatatypeCtor>());
    while (pending.TryPop(out var constructor)) {
      if (!seen.Add(constructor) || constructor.IsGhost || constructor.EnclosingDatatype == null ||
          constructor.EnclosingDatatype.EnclosingModuleDefinition.Name is "PbtRuntime" or "PbtRandom" ||
          !sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == constructor.Origin.Uri)) {
        continue;
      }
      yield return constructor;
      foreach (var nested in constructor.Formals.Where(formal => formal.DefaultValue != null)
                 .SelectMany(formal => SourceNodes(formal.DefaultValue!)).OfType<DatatypeValue>()
                 .Select(value => value.Ctor).OfType<DatatypeCtor>()) {
        pending.Push(nested);
      }
    }
  }

  // Generic diagnostic values are executable; concrete Dafny shape tokens retain their erased type arguments.
  public static bool CompilableType(Type type) {
    if (type.IsRefType || type.AsTypeParameter != null || ContractHarnessBuilder.SupportedType(type)) { return true; }
    var normalized = type.NormalizeExpand();
    return normalized switch {
      SetType { Finite: true } set => CompilableType(set.Arg),
      MapType { Finite: true } map => CompilableType(map.Domain) && CompilableType(map.Range),
      SeqType or MultiSetType => CompilableType(((CollectionType)normalized).Arg),
      _ => false
    };
  }

  public static IReadOnlyList<ContractSource> MakeGeneratorVisible(Program parsed, IReadOnlyList<ContractSource> sources,
    IReadOnlySet<string> constructors) {
    var changes = new List<Edit>();
    var nodes = Declarations(parsed.DefaultModuleDef).ToList();
    foreach (var declaration in nodes.OfType<ClassDecl>()) {
      // Parsed members have no enclosing class yet; qualify through the parsed declaration.
      var selected = declaration.Members.OfType<Constructor>()
        .Where(c => constructors.Contains(declaration.FullDafnyName + "." + c.Name)).ToList();
      if (selected.Count > 0 && Attributes.Find(declaration.Attributes, "extern") is UserSuppliedAttributes attribute) {
        Blank(attribute.OpenBrace, attribute.CloseBrace.pos + 1 - attribute.OpenBrace.pos);
      }
      foreach (var constructor in selected) {
        foreach (var token in constructor.OwnedTokens.Where(t => t.val == "ghost")) { Blank(token, token.val.Length); }
      }
    }
    foreach (var method in nodes.OfType<TopLevelDeclWithMembers>().SelectMany(t => t.Members).OfType<Method>()
               .Where(m => m.IsGhost && m.Body != null)) {
      var body = method.Body!;
      var length = body.EndToken.pos + body.EndToken.val.Length - body.StartToken.pos;
      changes.Add(new(method.Origin.Uri, body.StartToken.pos, length, "{" + new string(' ', length - 2) + "}"));
    }
    foreach (var export in nodes.OfType<ModuleExportDecl>()) {
      var range = export.EntireRange;
      var text = "export " + (export.IsDefault ? "" : export.Name + " ") + "reveals *";
      var remaining = range.Length - Encoding.UTF8.GetByteCount(text);
      // A shorter export cannot be rewritten without shifting offsets; diagnostic parses disable export scopes anyway.
      if (remaining < 0) { continue; }
      changes.Add(new(export.Origin.Uri, range.StartToken.pos, range.Length, text + new string(' ', remaining)));
    }
    return Apply(sources, changes);
    static IEnumerable<TopLevelDecl> Declarations(ModuleDefinition module) {
      foreach (var declaration in module.TopLevelDecls.Concat(module.PrefixNamedModules.Select(m => m.Module))) {
        yield return declaration;
        if (declaration is LiteralModuleDecl nested) {
          foreach (var child in Declarations(nested.ModuleDef)) { yield return child; }
        }
      }
    }
    void Blank(IOrigin token, int length) { changes.Add(new(token.Uri, token.pos, length, new string(' ', length))); }
  }

  public ContractRuntimeTransformation Transform() {
    if (UnsupportedRuntimeIterator(program, goal, generator) is { } iteratorReason) {
      throw new NotSupportedException(iteratorReason);
    }
    if (lemmaContract && !ContractCallableSelector.SupportsLemmaContract(goal)) {
      throw new NotSupportedException("Unsupported contract-only lemma signature.");
    }
    foreach (var formal in goal.Ins.Where(f => !CompilableType(f.Type))) {
      throw new NotSupportedException("non_compilable_input_type: " + formal.Name);
    }
    if (UnsupportedDiagnosticNames(reachable.Where(callable => Members().Contains(callable)), sources) is { } nameReason) {
      throw new NotSupportedException(nameReason);
    }
    exclusions.AddRange(rejected.Select(pair => new ContractRuntimeDeghostExclusion(pair.Key, pair.Value)));
    bool changed;
    do {
      changed = false;
      foreach (var f in functions.ToList()) {
        if (Reason(f.Body!, allowOld: false) != null || f.Req.Any(r => Reason(r.E, false) != null)) {
          functions.Remove(f);
          exclusions.Add(new(f.FullDafnyName, "non_compilable_function"));
          changed = true;
        }
      }
    } while (changed);
    reachableDatatypeConstructors.UnionWith(SourceDatatypeConstructors(reachable.Where(callable =>
      !callable.IsGhost || callable is Function function && functions.Contains(function))));
    shapedCallables.UnionWith(reachable.Where(callable => callable.TypeArgs.Count > 0 &&
      Members().Contains(callable) && (!callable.IsGhost || callable is Function f && functions.Contains(f))));
    if (UnsupportedGenericReferences(reachable.Where(callable =>
          callable.TypeArgs.Count == 0 || shapedCallables.Contains(callable))) is { } genericReason) {
      throw new NotSupportedException(genericReason);
    }
    foreach (var member in reachable) {
      foreach (var formal in member.Ins.Concat(member is MethodOrConstructor m ? m.Outs : []).Where(f => CompilableType(f.Type))) {
        if (!rejected.ContainsKey(member.FullDafnyName + "." + formal.Name)) { variables.Add(formal); }
      }
      if (member is MethodOrConstructor { Body: { } body } && !diagnosticConstructors.Contains(member.FullDafnyName)) {
        foreach (var local in body.Descendants().OfType<VarDeclStmt>().SelectMany(v => v.Locals).Where(v => CompilableType(v.Type))) {
          if (!rejected.ContainsKey(member.FullDafnyName + "." + local.Name)) { variables.Add(local); }
        }
      }
    }
    if (lemmaContract) { variables.UnionWith(goal.Ins); }
    var assertionSites = (lemmaContract ? [] : ExecutableAssertionSites(goal)).ToList();
    var protectedAssertionNodes = assertionSites.SelectMany(site =>
      site.Site.Descendants().Append(site.Site)).ToHashSet();
    do {
      changed = false;
      foreach (var method in reachable.OfType<MethodOrConstructor>().Where(m => m.Body != null)) {
        foreach (var choice in method.Body!.Descendants().OfType<AssignSuchThatStmt>()) {
          var assigned = choice.GetAssignedLocals().Select(identifier => identifier.Var).ToList();
          var unsupported = choice.AssumeToken != null || Reason(choice.Expr, false) != null || choice.Bounds == null ||
            BoundedPool.MissingBounds(assigned, choice.Bounds, BoundedPool.PoolVirtues.Enumerable).Count != 0;
          if (!unsupported) { continue; }
          foreach (var variable in assigned.Where(variable => variable.IsGhost)) {
            if (variables.Remove(variable)) {
              changed = true;
              exclusions.Add(new(method.FullDafnyName + "." + variable.Name, "value_unavailable"));
            }
          }
        }
        foreach (var declaration in method.Body.Descendants().OfType<VarDeclStmt>()
                   .Where(declaration => declaration.Locals.Any(variable => !variables.Contains(variable)))) {
          foreach (var variable in declaration.Locals.Where(variable => variable.IsGhost)) {
            if (variables.Remove(variable)) {
              changed = true;
              exclusions.Add(new(method.FullDafnyName + "." + variable.Name, "value_unavailable"));
            }
          }
        }
        foreach (var assignment in method.Body!.Descendants().OfType<SingleAssignStmt>()) {
          if (assignment.Lhs.Resolved is IdentifierExpr { Var: { IsGhost: true } variable } && variables.Contains(variable) &&
              (assignment.Rhs is not ExprRhs rhs || Reason(rhs.Expr, false) != null)) {
            variables.Remove(variable); changed = true;
            exclusions.Add(new(method.FullDafnyName + "." + variable.Name, "value_unavailable"));
          }
        }
        foreach (var call in method.Body.Descendants().OfType<CallStmt>().Where(c => c.Method.IsGhost)) {
          foreach (var variable in call.Lhs.Select(e => e.Resolved).OfType<IdentifierExpr>().Select(e => e.Var)) {
            if (variables.Remove(variable)) { changed = true; exclusions.Add(new(method.FullDafnyName + "." + variable.Name, "value_unavailable")); }
          }
        }
      }
    } while (changed);
    foreach (var iterator in Iterators()) { EraseUnreachableBody(iterator); }
    foreach (var member in Members()) {
      if (member is Function f && functions.Contains(f)) {
        RemoveKeyword(f, "ghost"); RemoveKeyword(f, "opaque"); RemoveAttribute(f.Attributes, "opaque");
        foreach (var formal in f.Ins.Where(v => v.IsGhost && variables.Contains(v))) { RemoveKeyword(formal, "ghost"); }
        // Erase only the proof statement: replacing its entire tail overlaps nested statement
        // expressions and discards independent instrumentation inside the surviving expression.
        foreach (var statementExpression in SourceExpressions(f.Body!).OfType<StmtExpr>()) { RemoveStatement(statementExpression.S); }
      }
      if (member is Field field && fields.Contains(field) && field.IsGhost && CompilableType(field.Type)) {
        RemoveKeyword(field, "ghost");
        compiledGhostFields.Add(field);
      }
      // An iterator's generated members share the iterator's source range; its body is handled on the declaration.
      if (member.EnclosingClass is not IteratorDecl) { EraseUnreachableBody(member); }
      if (member is MethodOrConstructor { Body: { } body } method && reachable.Contains(method) && (!method.IsGhost || method is Constructor)) {
        if (method is Constructor) { RemoveKeyword(method, "ghost"); }
        foreach (var formal in method.Ins.Concat(method.Outs).Where(f => f.IsGhost && variables.Contains(f))) { RemoveKeyword(formal, "ghost"); }
        foreach (var statement in body.Descendants().OfType<Statement>().Distinct()) {
          if (protectedAssertionNodes.Contains(statement)) { continue; }
          if (statement is VarDeclStmt declaration && declaration.Locals.All(variables.Contains)) { RemoveKeyword(declaration, "ghost"); }
          if (statement is AssertStmt assertion) {
            Replace(statement, assertion.Expr.Resolved is LiteralExpr { Value: false }
              ? RuntimeChecks + ".Unreachable();"
              : "");
          } else if (statement is AssumeStmt or CalcStmt or HideRevealStmt || statement is CallStmt { Method.IsGhost: true, Lhs.Count: 0 } ghostCall && ghostCall.Method is not Constructor ||
                     statement is ForallStmt { Kind: ForallStmt.BodyKind.Proof }) {
            RemoveStatement(statement);
          }
        }
      }
    }
    foreach (var type in reachable.OfType<Constructor>().Select(c => c.EnclosingClass).Distinct()) { RemoveAttribute(type.Attributes, "extern"); }
    var runtimeModule = program.RawModules().Single(module => module.FullDafnyName == "PbtRuntime");
    var runtimeSource = ContractSourceSnapshot.Find(sources, runtimeModule.Origin.Uri);
    Insert(runtimeSource, 0, "module " + runtimeBridge +
      " {\nimport Runtime = PbtRuntime\nexport provides Runtime\n}\nmodule " + runtimeAlias +
      " {\nimport Runtime = " + runtimeBridge + ".Runtime\nexport provides Runtime\n}\n");
    foreach (var module in program.RawModules().Where(m => m != program.DefaultModuleDef &&
               m.Name is not ("PbtRuntime" or "PbtRandom") &&
               sources.Any(s => ContractSourceSnapshot.UriFor(s.Path) == m.Origin.Uri))) {
      foreach (var export in module.TopLevelDecls.OfType<ModuleExportDecl>()) { Replace(export, "export " + (export.IsDefault ? "" : export.Name + " ") + "reveals *"); }
      Insert(module.BodyStartTok.Uri, module.BodyStartTok.pos + 1,
        "\nimport " + runtimeAlias + " = " + runtimeBridge + "\n");
    }
    var goalWrapper = Wrapper(goal, goal.Name + "__pbt_goal", true, null);
    Insert(goal.Origin.Uri, goal.StartToken.pos, goalWrapper);
    oldDeclarations[goal] = "";
    oldNames[goal] = [];
    InstrumentAssertions(assertionSites);
    if (!lemmaContract) { InstrumentLoops(protectedAssertionNodes); }
    if (oldDeclarations[goal].Length > 0) { Insert(goal.Origin.Uri, goal.Body!.StartToken.pos + 1, oldDeclarations[goal]); }
    InstrumentCalls(protectedAssertionNodes);
    InstrumentTypeShapes(protectedAssertionNodes);
    foreach (var constructor in reachable.OfType<Constructor>().Where(c => c.Body != null)) {
      var checks = string.Join("\n", constructor.Req.Select(clause => InternalPrecondition(clause.E, constructor.EnclosingClass.EnclosingModuleDefinition)));
      Insert(constructor.Origin.Uri, constructor.Body!.StartToken.pos + 1, checks);
    }
    foreach (var method in reachable.OfType<Method>().Where(m => !m.IsGhost && m.Body != null &&
               m.EnclosingClass.EnclosingModuleDefinition.Name is not ("PbtRuntime" or "PbtRandom"))) {
      // A forall statement body admits only its assignments, so no location marker may be placed inside it.
      var aggregate = method.Body!.Descendants().OfType<ForallStmt>().SelectMany(f => f.Descendants()).ToHashSet();
      foreach (var statement in method.Body!.Descendants().OfType<BlockLikeStmt>().Prepend(method.Body!).Where(b => !aggregate.Contains(b))
                 .SelectMany(b => b.Body).Where(s => !s.IsGhost).Distinct()) {
        Insert(statement.Origin.Uri, statement.StartToken.pos, Location(statement.Origin));
      }
    }
    var generatorNames = ContractRuntimeGeneratorSignature.Names(goal);
    var receiverName = generatorNames.Receiver;
    var target = goal.IsStatic ? (goal.EnclosingClass is DefaultClassDecl ? "" : goal.EnclosingClass.Name + ".") : receiverName + ".";
    var inputs = generator.Outs.Select(formal => formal.Name).ToList();
    var captures = RuntimeChecks + ".InputValues(" + SerializeValues(goal.Ins) + ");";
    if (!goal.IsStatic) {
      captures = RuntimeChecks + ".InputValues(\"{\" + " +
        SerializeNamed(receiverName!, UserDefinedType.FromTopLevelDecl(goal.Origin, goal.EnclosingClass)) +
        " + \"}\");\n" + captures;
    }
    var randomName = ContractBodyNames.Family(program, "pbtRandom");
    var outputNames = goal.Outs.Select((_, i) => ContractBodyNames.Family(program, "pbtOutput" + i)).ToList();
    var mainName = ContractRuntimeGeneratorSignature.MemberName(goal, "PbtMain");
    var main = "\nmethod " + mainName + "()" + (goal.AllowsNontermination || generator.AllowsNontermination ? " decreases *" : "") +
      " {\nvar " + randomName + " := PbtRandom.New();\n" +
      (contractModels == null ? "" : RuntimeChecks + ".SetModelRandom(" + randomName + ");\n") + Location(generator.Origin) +
      (inputs.Count == 0 ? "" : "var " + string.Join(", ", inputs) + " := ") + generator.Name + "(" + randomName + ");\n" +
      (contractModels?.InitialCode(RuntimeChecks) ?? "") +
      RuntimeChecks + ".Generated();\n" + captures + "\n" +
      (outputNames.Count == 0 ? "" : "var " + string.Join(", ", outputNames) + " := ") + target + goal.Name + "__pbt_goal(" +
      string.Join(", ", goal.Ins.Select(f => f.Name + " := " + f.Name)) + ");\n" + RuntimeChecks + ".Complete();\n}\n";
    var insertion = goal.EnclosingClass is DefaultClassDecl ? goal.StartToken : goal.EnclosingClass.StartToken;
    Insert(goal.Origin.Uri, insertion.pos, main);
    var transformed = Apply(edits);
    var source = ContractSourceSnapshot.Find(sources, goal.Origin.Uri);
    var prepared = new ContractPreparedProgram(program, goal, source,
      new(source.Path, goal.Origin.line, goal.Origin.col, goal.FullDafnyName, source.Sha256), OriginalCallable: nativeGoal, Sources: sources);
    return new(transformed, clauses, exclusions,
      (goal.EnclosingClass.EnclosingModuleDefinition.FullDafnyName is { Length: > 0 } moduleName ? moduleName + "." : "") + mainName, prepared,
      compiledGhostFields) { EntryRequiresOmitted = omitEntryRequires };
  }

  /// <summary>Assertions reached through the target's executable statement tree, excluding proof-only descendants.</summary>
  internal static IEnumerable<AssertStmt> ExecutableAssertions(Method goal) =>
    ExecutableAssertionSites(goal).Select(site => site.Assertion);

  private static IEnumerable<(AssertStmt Assertion, Statement Site)> ExecutableAssertionSites(Method goal) {
    if (goal.Body == null) { yield break; }
    foreach (var site in Visit(goal.Body, true)) { yield return site; }

    static IEnumerable<(AssertStmt Assertion, Statement Site)> Visit(Statement statement, bool root = false) {
      if (statement is BlockByProofStmt { Body: AssertStmt assertion } byProof) {
        yield return (assertion, byProof);
        yield break;
      }
      if (statement is AssertStmt direct) {
        yield return (direct, direct);
        yield break;
      }
      var structuralContainer = statement is BlockLikeStmt or IfStmt or OneBodyLoopStmt or AlternativeStmt;
      var ghostControl = statement switch {
        IfStmt { Guard: { } guard } => ExpressionTester.UsesSpecFeatures(guard),
        WhileStmt { Guard: { } guard } => ExpressionTester.UsesSpecFeatures(guard),
        ForLoopStmt forLoop => ExpressionTester.UsesSpecFeatures(forLoop.Start) ||
          forLoop.End != null && ExpressionTester.UsesSpecFeatures(forLoop.End),
        AlternativeStmt alternatives => alternatives.Alternatives.Any(alternative =>
          ExpressionTester.UsesSpecFeatures(alternative.Guard)),
        _ => false
      };
      if (ghostControl || !root && statement.IsGhost && !structuralContainer ||
          statement is CalcStmt or ForallStmt { Kind: ForallStmt.BodyKind.Proof }) {
        yield break;
      }
      foreach (var child in statement.SubStatements) {
        foreach (var site in Visit(child)) { yield return site; }
      }
    }
  }

  private void InstrumentAssertions(IEnumerable<(AssertStmt Assertion, Statement Site)> sites) {
    foreach (var (assertion, site) in sites) {
      Replace(site, Check(assertion.Expr, ContractRuntimeObligationKind.Assertion, goal, "-1", null,
        stopOnFailure: true));
    }
  }

  // Compiled bodies outside the goal/generator call graph are never executed by a sample. Replacing them
  // with traps keeps unrelated native dependencies out of the diagnostic without touching any contract.
  private void EraseUnreachableBody(IteratorDecl iterator) {
    var module = iterator.EnclosingModuleDefinition;
    if (reachableIterators.Contains(iterator) || iterator.SignatureIsOmitted ||
        module.ModuleKind != ModuleKindEnum.Concrete || !module.ShouldCompile(program.Compilation) ||
        !ProgramResolver.ShouldCompile(iterator)) {
      return;
    }
    if (iterator.Body is { } body) {
      Replace(body, "{ " + RuntimeChecks + ".UnreachableBody(); }");
    } else {
      var end = iterator.EndToken;
      Insert(iterator.Origin.Uri, end.pos + Encoding.UTF8.GetByteCount(end.val + end.TrailingTrivia),
        "\n{ " + RuntimeChecks + ".UnreachableBody(); }\n");
    }
  }

  private void EraseUnreachableBody(MemberDecl member) {
    if (member is not MethodOrFunction callable || reachable.Contains(callable)) { return; }
    if (callable is Constructor constructor) {
      if (constructor.Body is { } constructorBody) {
        if (!((TopLevelDeclWithMembers)constructor.EnclosingClass).Members.OfType<Field>().Any(fields.Contains)) { return; }
        RemoveKeyword(constructor, "ghost");
        Replace(constructorBody, UnreachableConstructorBody(constructor));
      } else if (!constructor.IsGhost && !constructor.IsAbstract &&
                 !constructor.IsExtern(program.Options, out _, out _)) {
        InsertUnreachableBody(constructor, "\n" + UnreachableConstructorBody(constructor));
      }
      return;
    }
    if (callable.IsGhost) { return; }
    if (callable is Method { Body: null } method) {
      if (!method.IsVirtual && !method.IsAbstract && !method.IsExtern(program.Options, out _, out _) &&
          !Attributes.Contains(method.Attributes, "synthesize")) {
        InsertUnreachableBody(method, "\n{ " + RuntimeChecks + ".UnreachableBody(); }");
      }
      return;
    }
    if (callable is Function { Body: null } function) {
      if (!function.IsVirtual && !function.IsAbstract && !function.IsExtern(program.Options, out _, out _)) {
        InsertUnreachableBody(function, " { " + RuntimeChecks + ".UnreachableValue() }");
      }
      return;
    }
    if (callable is Method { Body: { } body }) {
      Replace(body, "{ " + RuntimeChecks + ".UnreachableBody(); }");
    } else if (callable is Function { ByMethodBody: { } byMethodBody }) {
      Replace(byMethodBody, "{ " + RuntimeChecks + ".UnreachableBody(); }");
    } else if (callable is Function { Body: { } expression }) {
      Replace(expression, RuntimeChecks + ".UnreachableValue()");
    }
  }

  private string UnreachableConstructorBody(Constructor constructor) {
    var assignments = new List<string>();
    foreach (var field in ((TopLevelDeclWithMembers)constructor.EnclosingClass).Members.OfType<Field>()
               .Where(field => !field.IsStatic && field.Origin.line > 0 &&
                 (field.IsUserMutable || field is ConstantField { Rhs: null }))) {
      if (!field.IsGhost || fields.Contains(field) && CompilableType(field.Type)) {
        assignments.Add("this." + field.Name + " := " + RuntimeChecks + ".UnreachableValue<" + field.Type + ">();");
      } else {
        var local = "pbtOmitted" + nextName++;
        assignments.Add("ghost var " + local + ": " + field.Type + " :| true; this." + field.Name + " := " + local + ";");
      }
    }
    return "{ " + string.Join("\n", assignments) + " new; " + RuntimeChecks + ".UnreachableBody(); }";
  }

  private void InsertUnreachableBody(MethodOrFunction callable, string text) =>
    Insert(callable.Origin.Uri, callable.EndToken.pos + Encoding.UTF8.GetByteCount(callable.EndToken.val), text);

  private string Wrapper(Method method, string name, bool entry, IOrigin? site, bool goalSite = true) =>
    WithShapes(method.TypeArgs, () => WrapperCore(method, name, entry, site, goalSite));

  private string WrapperCore(Method method, string name, bool entry, IOrigin? site, bool goalSite) {
    oldDeclarations[method] = "";
    oldNames[method] = [];
    var ins = WrapperFormals(method, method.Ins);
    var firstClause = clauses.Count;
    var outs = string.Join(", ", method.Outs.Select(f => (f.IsGhost && !variables.Contains(f) ? "ghost " : "") + f.Name + ": " + f.Type));
    var inputKind = entry ? ContractRuntimeObligationKind.EntryPrecondition : ContractRuntimeObligationKind.CallPrecondition;
    var outputKind = entry ? ContractRuntimeObligationKind.Postcondition : ContractRuntimeObligationKind.CalleePostcondition;
    // Declared subset/newtype constraints belong to the same boundary as the requires and ensures clauses.
    var before = TypeConstraintChecks(method.Ins, entry || goalSite ? inputKind : ContractRuntimeObligationKind.CalleePostcondition, method, site) +
      string.Join("\n", method.Req.Where(_ => !(omitEntryRequires && entry && ReferenceEquals(method, goal)))
        .Select(c => !entry && !goalSite ? InternalPrecondition(c.E, method.EnclosingClass.EnclosingModuleDefinition) : Check(c.E, inputKind, method, "-1", site)));
    var after = string.Join("\n", method.Ens.Select(c => Check(c.E, outputKind, method, "-1", null))) + "\n" +
      TypeConstraintChecks(method.Outs, outputKind, method, null);
    if (entry) {
      before += "\n" + RuntimeChecks + ".CaptureHeap(\"entry\", \"{}\");\n";
    }
    if (entry && clauses.Any(clause => clause.EntryHeapPostcondition != null)) {
      after = "\n" + RuntimeChecks + ".CaptureHeap(\"return\", " + SerializeValues(method.Outs) + ");\n" + after;
    }
    if (method.FunctionFromWhichThisIsByMethodDecl is { ByMethodBody: not null, Body: { } definition } function) {
      // A function-by-method implementation must return exactly the value of the original function definition.
      var equality = Expression.CreateEq(Expression.CreateIdentExpr(method.Outs.Single()), definition, function.ResultType);
      var label = function.Name + "(" + string.Join(", ", function.Ins.Select(f => f.Name)) + ")";
      after += "\n" + Check(equality, outputKind, method, "-1", definition.StartToken, Text(definition),
        (label, definition, function.ResultType), definingFunction: function);
    }
    var invocation = "pbtCall" + nextName++;
    var captureCall = !entry && clauses.Skip(firstClause).Any(clause => clause.CallHeapScope != null);
    var beginCall = "";
    if (captureCall) {
      var inputValues = method.Ins.Select(formal => SerializeNamed(formal.Name, formal.Type)).ToList();
      if (!method.IsStatic) {
        inputValues.Add(SerializeNamed(ContractRuntimeGeneratorSignature.Names(method).Receiver!, "this",
          UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)));
      }
      beginCall = "var " + invocation + " := " + RuntimeChecks + ".BeginCall(" +
        Quote(method.FullDafnyName) + ", " + Encode(inputValues) + ");\n";
      after = RuntimeChecks + ".EndCall(" + Quote(method.FullDafnyName) + ", " + invocation + ", " +
        SerializeValues(method.Outs) + ");\n" + after + "\n" + RuntimeChecks + ".LeaveCall(" + invocation + ");";
    }
    var call = lemmaContract && entry ? "" :
      (method.Outs.Count == 0 ? "" : string.Join(", ", method.Outs.Select(f => f.Name)) + " := ") +
      method.Name + TypeArgumentNames(method.TypeArgs) + "(" + ShapedArguments(method, method.Ins) + ");";
    if (!entry && contractModels?.IsModeled(method) == true) {
      call = contractModels.TransitionCode(method, RuntimeChecks);
    }
    return "\n" + (method.HasStaticKeyword ? "static " : "") + "method " + name + TypeParameters(method.TypeArgs) + "(" + ins + ")" +
      (outs.Length == 0 ? "" : " returns (" + outs + ")") + (method.AllowsNontermination ? "\n decreases *" : "") +
      "\n{\n" + beginCall + before + "\n" + oldDeclarations.GetValueOrDefault(method, "") +
      (entry ? "\n" + RuntimeChecks + ".Executed();\n" : "\n") + call + "\n" + after + "\n}\n";
  }

  private void InstrumentLoops(IReadOnlySet<INode> protectedAssertionNodes) {
    if (goal.Body == null) { throw new NotSupportedException("The goal requires an executable body."); }
    foreach (var loop in goal.Body.Descendants().OfType<OneBodyLoopStmt>()
               .Where(loop => loop.Body != null && !protectedAssertionNodes.Contains(loop))) {
      var number = nextName++;
      var iteration = "pbtIteration" + number;
      var broke = "pbtBroke" + number;
      var entry = string.Join("\n", loop.Invariants.Select(c => Check(c.E, ContractRuntimeObligationKind.LoopInvariantEntry, goal, "0", null)));
      var maintenance = string.Join("\n", loop.Invariants.Select(c => Check(c.E, ContractRuntimeObligationKind.LoopInvariantMaintenance, goal, iteration, null)));
      var prefix = $"var {iteration} := 0; var {broke} := false;\n{entry}\n";
      if (loop is ForLoopStmt forLoop) {
        var index = forLoop.LoopIndex.Name;
        var limit = "pbtLimit" + number;
        var bound = forLoop.End == null ? "" : "var " + limit + " := " + Printer.ExprToString(program.Options, forLoop.End) + ";\n";
        var guard = forLoop.End == null ? "true" : index + (forLoop.GoingUp ? " < " : " > ") + limit;
        Add(loop.Origin.Uri, loop.StartToken.pos, loop.Body!.StartToken.pos - loop.StartToken.pos,
          "{ var " + index + " := " + Printer.ExprToString(program.Options, forLoop.Start) + ";\n" + bound + prefix + "while " + guard + " ");
        if (forLoop.GoingUp) {
          Insert(loop.Origin.Uri, loop.Body.EndToken.pos, index + " := " + index + " + 1;\n");
          foreach (var again in loop.Body.Descendants().OfType<BreakOrContinueStmt>().Where(b => b.IsContinue && b.TargetStmt == loop)) {
            Insert(again.Origin.Uri, again.StartToken.pos, index + " := " + index + " + 1; ");
          }
        } else {
          Insert(loop.Origin.Uri, loop.Body.StartToken.pos + 1, index + " := " + index + " - 1;\n");
        }
        Insert(loop.Origin.Uri, loop.EndToken.pos + loop.EndToken.val.Length, "\n}");
      } else {
        Insert(loop.Origin.Uri, loop.StartToken.pos, prefix);
      }
      Insert(loop.Origin.Uri, loop.Body!.StartToken.pos + 1, $"\nif {iteration} > 0 {{ {maintenance} }}\n{iteration} := {iteration} + 1;\n");
      Insert(loop.Origin.Uri, loop.EndToken.pos + loop.EndToken.val.Length, $"\nif !{broke} && {iteration} > 0 {{ {maintenance} }}\n");
      foreach (var stop in loop.Body.Descendants().OfType<BreakOrContinueStmt>().Where(b => !b.IsContinue && b.TargetStmt == loop)) {
        Insert(stop.Origin.Uri, stop.StartToken.pos, broke + " := true; ");
      }
    }
  }

  private void InstrumentCalls(IReadOnlySet<INode> protectedAssertionNodes) {
    var index = 0;
    var sourceCallables = Members().OfType<MethodOrFunction>().ToHashSet();
    var callables = lemmaContract ? reachable.Where(sourceCallables.Contains) :
      Reachable(program, nativeGoal).OfType<MethodOrFunction>();
    var callableList = callables.DistinctBy(callable => callable.FullDafnyName).ToList();
    foreach (var callable in callableList.Where(callable =>
               !callable.IsGhost || callable is Function function && functions.Contains(function))) {
      var calls = callable.Ins.Where(formal => formal.DefaultValue != null)
        .SelectMany(formal => SourceExpressions(formal.DefaultValue!)).OfType<FunctionCallExpr>().Distinct()
        .Where(call => (!lemmaContract || sourceCallables.Contains(call.Function)) &&
          (!call.Function.IsGhost || functions.Contains(call.Function)) && HasContract(call.Function));
      foreach (var call in calls) {
        var token = call.NameNode.StartToken;
        Add(token.Uri, token.pos, token.val.Length, SpecWrapper(call.Function));
      }
    }
    foreach (var constructor in reachableDatatypeConstructors) {
      var calls = constructor.Formals.Where(formal => formal.DefaultValue != null)
        .SelectMany(formal => SourceExpressions(formal.DefaultValue!)).OfType<FunctionCallExpr>().Distinct()
        .Where(call => (!lemmaContract || sourceCallables.Contains(call.Function)) &&
          (!call.Function.IsGhost || functions.Contains(call.Function)) && HasContract(call.Function));
      foreach (var call in calls) {
        var token = call.NameNode.StartToken;
        Add(token.Uri, token.pos, token.val.Length, SpecWrapper(call.Function));
      }
    }
    var bodies = callableList
      .Select(c => (Callable: c, Body: c switch { MethodOrConstructor m => (INode?)m.Body, Function f => (INode?)f.ByMethodBody ?? f.Body, _ => null }))
      .Where(c => c.Body != null && (!c.Callable.IsGhost || c.Callable is Function f && functions.Contains(f)))
      .Concat(lemmaContract ? [] : new[] { (Callable: (MethodOrFunction)goal, Body: (INode?)goal.Body) })
      .DistinctBy(c => c.Callable.FullDafnyName).ToList();
    foreach (var context in bodies) {
      var goalSite = context.Callable.FullDafnyName == goal.FullDafnyName;
      foreach (var call in SourceNodes(context.Body!).OfType<CallStmt>()
                 .Where(call => !call.Method.IsGhost && !protectedAssertionNodes.Contains(call) &&
                   (!lemmaContract || sourceCallables.Contains(call.Method))).Distinct()) {
        if (call.Method is not Method method) { continue; }
        var name = method.Name + "__pbt_site_" + index++;
        var wrapper = Wrapper(method, name, false, call.Origin, goalSite);
        Insert(method.Origin.Uri, method.StartToken.pos, wrapper);
        var token = call.MethodSelect.MemberNameNode.StartToken;
        Add(token.Uri, token.pos, token.val.Length, name);
      }
      var roots = context.Body is Expression bodyExpression ? [bodyExpression] :
        SourceNodes(context.Body).OfType<Statement>().SelectMany(s => s.NonSpecificationSubExpressions);
      var calls = roots.SelectMany(SourceExpressions).OfType<FunctionCallExpr>().Distinct()
        .Where(call => !protectedAssertionNodes.Contains(call) &&
          (!lemmaContract || sourceCallables.Contains(call.Function)) &&
          (!call.Function.IsGhost || functions.Contains(call.Function)) && HasContract(call.Function));
      foreach (var call in calls) {
        var name = call.Function.Name + "__pbt_site_" + index++;
        Insert(call.Function.Origin.Uri, call.Function.StartToken.pos, CallSiteWrapper(call, name, goalSite));
        var token = call.NameNode.StartToken;
        Add(token.Uri, token.pos, token.val.Length, name);
      }
    }
  }

  private string CallSiteWrapper(FunctionCallExpr call, string name, bool goalSite) =>
    WithShapes(call.Function.TypeArgs, () => CallSiteWrapperCore(call, name, goalSite));

  private string CallSiteWrapperCore(FunctionCallExpr call, string name, bool goalSite) {
    var function = call.Function;
    var descriptor = ContractCallableSelector.DescribeFunction(program, function, resultFamily.Value);
    oldDeclarations[descriptor] = ""; oldNames[descriptor] = [];
    var before = TypeConstraintChecks(descriptor.Ins, goalSite ? ContractRuntimeObligationKind.CallPrecondition : ContractRuntimeObligationKind.CalleePostcondition, descriptor, call.Origin) +
      string.Join("\n", descriptor.Req.Select(c => goalSite ? Check(c.E, ContractRuntimeObligationKind.CallPrecondition, descriptor, "-1", call.Origin) : InternalPrecondition(c.E, descriptor.EnclosingClass.EnclosingModuleDefinition)));
    var after = GuardContracts(function, descriptor, CalleePostconditions(function, descriptor));
    return FunctionWrapper(function, descriptor, name, before, after, function.AllowsNontermination);
  }

  // Calls the original function between the supplied checks; `before` and `after` may add old-state declarations.
  private string FunctionWrapper(Function function, Method descriptor, string name, string before, string after,
    bool decreasesStar) {
    var result = descriptor.Outs.Single();
    return "\n" + (function.HasStaticKeyword ? "static " : "") + "function " + name + TypeParameters(function.TypeArgs) + "(" +
      WrapperFormals(function, descriptor.Ins) + "): " + result.Type +
      (decreasesStar ? "\n decreases *" : "") +
      "\n{ " + before + "\n" + oldDeclarations[descriptor] + "\nvar " + result.Name + " := " +
      function.Name + TypeArgumentNames(function.TypeArgs) + "(" + ShapedArguments(function, descriptor.Ins) +
      ");\n" + after + "\n" + result.Name + " }\n";
  }

  private string InternalPrecondition(Expression expression, ModuleDefinition scope) {
    if (Reason(expression, false) != null) { throw new NotSupportedException("A nested callee precondition is not executable: " + Printer.ExprToString(program.Options, expression)); }
    return "var pbtDomain" + nextName++ + " := " + RuntimeChecks + ".Require(" +
      Printer.ExprToString(program.Options, Render(expression, scope, true)) + ");";
  }

  private string Check(Expression expression, ContractRuntimeObligationKind kind, Method owner, string iteration, IOrigin? site,
    string? clauseText = null, (string Label, Expression Value, Type Type)? extra = null,
    IReadOnlyList<IVariable>? explicitValues = null, bool typeConstraint = false, string? typeTest = null, Function? definingFunction = null,
    string? forceUncheckedReason = null, bool stopOnFailure = false) {
    var pendingOldCaptures = new Dictionary<Expression, PendingOldCapture>();
    var evaluated = new RuntimeSubstituter(node => node is StmtExpr statementExpression
      ? statementExpression.E
      : RewriteState(node, owner, pendingOldCaptures)).Substitute(expression);
    var reason = typeConstraint ? (typeTest == null ? "type_constraint_not_executable" : null) : Reason(evaluated, true);
    if (reason == null && goalFunction != null && !DefinitionAvailable &&
        Expressions(evaluated).Any(node => node is FunctionCallExpr call && call.Function == goalFunction)) {
      // Executing the goal function here would run the implementation under test instead of its definition.
      reason = "non_compilable_function";
    }
    var values = CheckValues(evaluated, owner, explicitValues, typeConstraint, out var heap);
    var unavailable = values.Any(v => !CompilableType(v.Type) || v.IsGhost && !variables.Contains(v));
    // A type-constraint check has no closed-query form; its value either runs through the membership test or is unchecked.
    var noClosedForm = unavailable || heap || reason is "fresh_or_allocated" || typeConstraint;
    var decision = reason == null && !unavailable ? ContractRuntimeDecisionMethod.Runtime :
      noClosedForm ? ContractRuntimeDecisionMethod.Unchecked : ContractRuntimeDecisionMethod.ClosedSmt;
    if (lemmaContract && owner == goal && !typeConstraint) {
      decision = noClosedForm ? ContractRuntimeDecisionMethod.Unchecked : ContractRuntimeDecisionMethod.ClosedSmt;
    }
    int? heapPostcondition = null;
    if ((kind == ContractRuntimeObligationKind.Postcondition && owner == goal && goalFunction == null ||
         kind == ContractRuntimeObligationKind.CalleePostcondition && owner.FunctionFromWhichThisIsByMethodDecl == null &&
         owner.TypeArgs.Count == 0 && owner.EnclosingClass.TypeArgs.Count == 0 &&
         (owner.IsStatic || owner.Ins.All(formal => formal.Name != "receiver"))) &&
        decision != ContractRuntimeDecisionMethod.Runtime && !typeConstraint && reason != "fresh_or_allocated" &&
        owner.Ins.All(formal => CompilableType(formal.Type) && (!formal.IsGhost || variables.Contains(formal))) &&
        owner.Outs.All(formal => !formal.IsGhost && CompilableType(formal.Type)) &&
        (heap || !owner.IsStatic || owner.Ins.Concat(owner.Outs).Any(formal => formal.Type.IsRefType))) {
      var index = owner.Ens.FindIndex(clause => clause.E == expression);
      if (index >= 0) {
        heapPostcondition = index;
        decision = ContractRuntimeDecisionMethod.ClosedSmt;
        noClosedForm = false;
      }
    }
    if (unavailable) { reason = "value_unavailable"; }
    if (forceUncheckedReason != null) { decision = ContractRuntimeDecisionMethod.Unchecked; reason = forceUncheckedReason; }
    var origin = site ?? expression.Origin;
    var source = ContractSourceSnapshot.Find(sources, origin.Uri);
    var location = sourceMap?.ResolveLocation(origin.Uri, origin.pos, owner.FullDafnyName) ?? new(source.Path, origin.line, origin.col, owner.FullDafnyName, source.Sha256);
    var prefix = JsonNamingPolicy.SnakeCaseLower.ConvertName(kind.ToString()) + ":" + location.Path + ":" + location.Line + ":" + location.Column;
    if (decisionCaps.TryGetValue(prefix, out var cap) && cap > decision) {
      // The previous diagnostic resolve erased this check from compiled code, so it may not claim a runtime decision.
      decision = cap == ContractRuntimeDecisionMethod.ClosedSmt && noClosedForm ? ContractRuntimeDecisionMethod.Unchecked : cap;
      reason = "runtime_check_not_compiled";
    }
    if (decision == ContractRuntimeDecisionMethod.Runtime ||
        decision == ContractRuntimeDecisionMethod.ClosedSmt && heapPostcondition == null) {
      CommitOldCaptures(owner, pendingOldCaptures.Values, evaluated);
    } else {
      // Fixed-heap queries restore the original indexed contract, and unchecked clauses are never evaluated.
      // Keep their metadata and checkpoints source-bound without executing or rendering speculative snapshots.
      evaluated = new RuntimeSubstituter(node => node is StmtExpr statementExpression
        ? statementExpression.E
        : null).Substitute(expression);
      values = CheckValues(evaluated, owner, explicitValues, typeConstraint, out _);
    }
    var id = prefix + ":" + clauses.Count;
    var obligation = new ContractRuntimeObligation(id, kind, location.Path, location.Line, location.Column, clauseText ?? Text(expression),
      kind is ContractRuntimeObligationKind.CallPrecondition or ContractRuntimeObligationKind.CalleePostcondition ? owner.FullDafnyName : null,
      decision, decision == ContractRuntimeDecisionMethod.Unchecked ? reason : null, new());
    var specificationExpressions = Expressions(evaluated).ToList();
    var specificationRoots = specificationExpressions.Select(FunctionReference).OfType<Function>()
      .Where(function => function != goalFunction).Distinct().ToList();
    var unvalidated = !typeConstraint && (heapPostcondition != null
      ? ExecutionReachable(program, specificationRoots, specificationExpressions.Select(node => node.Type)).OfType<Function>()
        // A fixed-heap query establishes the typed premise and native call well-definedness. It
        // still cannot validate an unexecuted function implementation's explicit contract.
        .Any(function => function.Req.Count > 0 || function.Ens.Count > 0 || function.ByMethodBody != null)
      : specificationRoots.Any(HasContract));
    clauses.Add(new(obligation, evaluated, values, owner, unvalidated, heapPostcondition, typeConstraint, location.Sha256, originalSourceSetHash,
      heapPostcondition != null && kind == ContractRuntimeObligationKind.CalleePostcondition ? owner.FullDafnyName : null));
    var encodedValues = values.Where(v => CompilableType(v.Type) && (!v.IsGhost || variables.Contains(v))).Select(v => SerializeNamed(v.Name, v.Name, v.Type)).ToList();
    var captures = "";
    string check;
    if (decision == ContractRuntimeDecisionMethod.Runtime) {
      // Only executable rendering uses snapshots; original clauses and proof bindings retain their formals.
      var referenced = Expressions(evaluated).OfType<IdentifierExpr>().Select(identifier => identifier.Var).ToHashSet();
      if (extra is { } additional) {
        referenced.UnionWith(Expressions(additional.Value).OfType<IdentifierExpr>().Select(identifier => identifier.Var));
      }
      Dictionary<IVariable, Expression> outputValues = [];
      foreach (var formal in owner.Outs.Where(formal => referenced.Contains(formal) &&
                 CompilableType(formal.Type) && (!formal.IsGhost || variables.Contains(formal)))) {
        var local = new BoundVar(formal.Origin, outputFamily + nextName++, formal.Type);
        outputValues.Add(formal, Expression.CreateIdentExpr(local));
        captures += "var " + local.Name + " := " + formal.Name + ";\n";
      }
      var substituteOutputs = new RuntimeSubstituter(node => node is IdentifierExpr identifier
        ? outputValues.GetValueOrDefault(identifier.Var) : null);
      // Contract expressions follow the same validity boundary as executable bodies.
      var text = typeTest ?? Printer.ExprToString(program.Options, Render(substituteOutputs.Substitute(evaluated), owner.EnclosingClass.EnclosingModuleDefinition, true, definingFunction));
      if (extra is { } named) {
        encodedValues.Add(SerializeNamed(named.Label, "(" + Printer.ExprToString(program.Options, Render(substituteOutputs.Substitute(named.Value), owner.EnclosingClass.EnclosingModuleDefinition, true, definingFunction)) + ")", named.Type));
      }
      check = $"{RuntimeChecks}.Check({Quote(id)}, {iteration}, {RuntimeChecks}.Evaluated({RuntimeChecks}.BeginCheck() && ({text})), {EncodeFragments(encodedValues)})";
    } else {
      check = $"{RuntimeChecks}.Checkpoint({Quote(id)}, {iteration}, {EncodeFragments(encodedValues)})";
    }
    return Location(origin) + captures + (decision == ContractRuntimeDecisionMethod.Runtime &&
      (kind == ContractRuntimeObligationKind.EntryPrecondition || stopOnFailure)
      ? "if !" + check + (kind == ContractRuntimeObligationKind.EntryPrecondition
        ? " { " + RuntimeChecks + ".Stop(); }" : " { " + RuntimeChecks + ".Unreachable(); }")
      : "var pbtCheck" + nextName++ + " := " + check + ";");
  }

  private List<IVariable> CheckValues(Expression expression, Method owner,
    IReadOnlyList<IVariable>? explicitValues, bool typeConstraint, out bool heap) {
    heap = false;
    List<IVariable> values;
    if (explicitValues != null) {
      values = explicitValues.OrderBy(variable => variable.Name).ToList();
    } else {
      var free = new HashSet<IVariable>();
      FreeVariablesUtil.ComputeFreeVariables(program.Options, expression, free, ref heap);
      values = free.OrderBy(variable => variable.Name).ToList();
    }
    if (lemmaContract && owner == goal && !typeConstraint) {
      // Native queries restore the complete original clause, including erased proof
      // statements that may mention inputs absent from the surviving expression.
      values = values.Concat(owner.Ins).Distinct().OrderBy(variable => variable.Name).ToList();
    }
    return values;
  }

  // Checks that concrete values satisfy the subset-type and newtype constraints declared for these formals.
  private string TypeConstraintChecks(IEnumerable<Formal> formals, ContractRuntimeObligationKind kind, Method owner, IOrigin? site) =>
    string.Join("", formals.Where(formal => HasConstraint(formal.Type, 0)).Select(formal => {
      // Datatype matches compile to lambdas, which cannot capture a C# out parameter.
      var value = !formal.InParam && CompilableType(formal.Type) && (!formal.IsGhost || variables.Contains(formal))
        ? "pbtTypeValue" + nextName++ : formal.Name;
      var membership = Membership(formal.Type, value, 0, owner.EnclosingClass.EnclosingModuleDefinition);
      var capture = value != formal.Name && membership != null ? "var " + value + " := " + formal.Name + ";\n" : "";
      return capture + Check(Expression.CreateBoolLiteral(formal.Origin, true), kind, owner, "-1", site ?? formal.Origin, formal.Name + ": " + formal.Type,
        explicitValues: [formal], typeConstraint: true, typeTest: membership) + "\n";
    }));

  private static bool HasConstraint(Type type, int depth, IReadOnlySet<DatatypeDecl>? enclosing = null) {
    var normalized = type.NormalizeExpandKeepConstraints();
    // Source typing does not reject unverified null assignments to non-null reference formals.
    if (normalized is UserDefinedType { ResolvedClass: NonNullTypeDecl }) { return true; }
    if (normalized.IsArrayType) { return normalized.TypeArgs.Any(argument => HasConstraint(argument, depth + 1, enclosing)); }
    if (normalized is UserDefinedType { ResolvedClass: SubsetTypeDecl or NewtypeDecl { Var: not null } }) { return true; }
    if (normalized is UserDefinedType { ResolvedClass: NewtypeDecl newtype }) { return HasConstraint(newtype.BaseType, depth + 1, enclosing); }
    if (normalized is UserDefinedType { ResolvedClass: DatatypeDecl datatype } reference) {
      // A cycle is a validation obligation, never evidence that the nested values are unconstrained.
      if (enclosing?.Contains(datatype) == true) { return true; }
      var nested = new HashSet<DatatypeDecl>(enclosing ?? new HashSet<DatatypeDecl>()) { datatype };
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, reference.TypeArgs);
      return datatype.Ctors.SelectMany(constructor => constructor.Formals)
        .Any(formal => HasConstraint(formal.Type.Subst(substitution), depth + 1, nested));
    }
    return normalized.AsMapType is { } map
      ? HasConstraint(map.Domain, depth + 1, enclosing) || HasConstraint(map.Range, depth + 1, enclosing)
      : normalized.AsCollectionType is { } collection && HasConstraint(collection.Arg, depth + 1, enclosing);
  }

  // A compilable membership test for `value`, or null when some declared constraint cannot be executed.
  private string? Membership(Type type, string value, int depth, ModuleDefinition site, IReadOnlySet<DatatypeDecl>? enclosing = null) {
    if (!HasConstraint(type, depth)) { return "true"; }
    var normalized = type.NormalizeExpandKeepConstraints();
    string? Combine(string? inner, string? own) => inner == null || own == null ? null : inner == "true" ? own : "(" + inner + ") && (" + own + ")";
    switch (normalized) {
      case UserDefinedType { ResolvedClass: NonNullTypeDecl nonNull } reference:
        return Combine(Membership(nonNull.RhsWithArgument(reference.TypeArgs), value, depth + 1, site, enclosing), "(" + value + " != null)");
      case UserDefinedType { ResolvedClass: SubsetTypeDecl subset } reference:
        return Combine(Membership(subset.RhsWithArgument(reference.TypeArgs), value, depth + 1, site, enclosing),
          subset == program.SystemModuleManager.NatDecl ? "0 <= " + value : MembershipHelper(subset, site) is { } helper ? helper + "(" + value + ")" : null);
      case UserDefinedType { ResolvedClass: NewtypeDecl newtype }: {
          var baseValue = "(" + value + " as " + newtype.BaseType + ")";
          return Combine(Membership(newtype.BaseType, baseValue, depth + 1, site, enclosing),
            newtype.Var == null ? "true" : MembershipHelper(newtype, site) is { } newtypeHelper ? newtypeHelper + baseValue : null);
        }
      case UserDefinedType { ResolvedClass: DatatypeDecl datatype } reference: {
          if (datatype is CoDatatypeDecl ||
              datatype.Ctors.Any(constructor => constructor.IsGhost || constructor.Formals.Any(formal => formal.IsGhost))) { return null; }
          if (enclosing?.Contains(datatype) == true) {
            return RecursiveMembershipHelper(datatype, site) is { } recursive ? recursive + "(" + value + ")" : null;
          }
          var nested = new HashSet<DatatypeDecl>(enclosing ?? new HashSet<DatatypeDecl>()) { datatype };
          var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, reference.TypeArgs);
          var cases = new List<string>();
          foreach (var constructor in datatype.Ctors) {
            var names = constructor.Formals.Select(_ => "pbtField" + nextName++).ToList();
            var tests = constructor.Formals.Select((formal, index) =>
              Membership(formal.Type.Subst(substitution), names[index], depth + 1, site, nested)).ToList();
            if (tests.Any(test => test == null)) { return null; }
            cases.Add("case " + constructor.Name + (names.Count == 0 ? "" : "(" + string.Join(", ", names) + ")") +
              " => " + (tests.Count == 0 ? "true" : string.Join(" && ", tests.Select(test => "(" + test + ")"))));
          }
          return "(match " + value + " " + string.Join(" ", cases) + ")";
        }
    }
    var element = "pbtElement" + depth;
    if (normalized.AsMapType is { } map) {
      var key = Membership(map.Domain, element, depth + 1, site, enclosing);
      var mapped = Membership(map.Range, value + "[" + element + "]", depth + 1, site, enclosing);
      return key == null || mapped == null ? null : "(forall " + element + " :: " + element + " in " + value + " ==> (" + key + ") && (" + mapped + "))";
    }
    if (normalized.AsCollectionType is not { } collection) { return null; }
    var test = Membership(collection.Arg, element, depth + 1, site, enclosing);
    return test == null ? null : "(forall " + element + " :: " + element + " in " + value + " ==> " + test + ")";
  }

  private string? RecursiveMembershipHelper(DatatypeDecl declaration, ModuleDefinition site) {
    if (declaration.TypeArgs.Count != 0) { return null; }
    if (!recursiveMembershipHelpers.TryGetValue(declaration, out var name)) {
      name = declaration.Name + "__pbt_structure";
      // Register before descending so mutual and direct recursion reference the same finite declarations.
      recursiveMembershipHelpers.Add(declaration, name);
      var body = Membership(UserDefinedType.FromTopLevelDecl(declaration.Origin, declaration), "pbtValue", 0,
        declaration.EnclosingModuleDefinition);
      if (body == null) {
        recursiveMembershipHelpers[declaration] = null;
        return null;
      }
      Insert(declaration.Origin.Uri, declaration.StartToken.pos, "\nfunction " + name + "(pbtValue: " + declaration.Name +
        "): bool\n{ " + body + " }\n");
    }
    var target = declaration.EnclosingModuleDefinition;
    var qualifier = site == target ? "" : site.TopLevelDecls.OfType<ModuleDecl>()
      .FirstOrDefault(module => module.Signature?.ModuleDef == target) is { } import ? import.Name + "." : null;
    return name == null || qualifier == null ? null : qualifier + name;
  }

  private string? MembershipHelper(TopLevelDecl declaration, ModuleDefinition site) {
    if (!membershipHelpers.TryGetValue(declaration, out var name)) {
      var (variable, constraint) = declaration switch {
        SubsetTypeDecl subset => (subset.Var, subset.Constraint),
        NewtypeDecl newtype => (newtype.Var, newtype.Constraint),
        _ => ((BoundVar?)null, (Expression?)null)
      };
      name = null;
      if (variable != null && constraint != null && Reason(constraint, false) == null &&
          sources.Any(source => ContractSourceSnapshot.UriFor(source.Path) == declaration.Origin.Uri)) {
        name = declaration.Name + "__pbt_member";
        Insert(declaration.Origin.Uri, declaration.StartToken.pos, "\nfunction " + name + TypeParameters(declaration.TypeArgs) + "(" +
          variable.Name + ": " + variable.Type + "): bool\n{\n" + Printer.ExprToString(program.Options, Render(constraint, declaration.EnclosingModuleDefinition, true)) + "\n}\n");
      }
      membershipHelpers.Add(declaration, name);
    }
    // The helper sits beside the type; the call site names it through its own module or an import of that module.
    var target = declaration.EnclosingModuleDefinition;
    var qualifier = site == target ? "" : site.TopLevelDecls.OfType<ModuleDecl>().FirstOrDefault(m => m.Signature?.ModuleDef == target) is { } import ? import.Name + "." : null;
    return name == null || qualifier == null ? null : qualifier + name;
  }

  private static string TypeParameters(IReadOnlyList<TypeParameter> parameters) => parameters.Count == 0 ? "" :
    "<" + string.Join(", ", parameters.Select(parameter => Printer.TypeParameterToString(parameter).TrimStart('*', '+', '!', '-'))) + ">";

  private static string TypeArgumentNames(IReadOnlyList<TypeParameter> parameters) => parameters.Count == 0 ? "" :
    "<" + string.Join(", ", parameters.Select(parameter => parameter.Name)) + ">";

  private T WithShapes<T>(IReadOnlyList<TypeParameter> parameters, Func<T> action) {
    var previous = shapeParameters;
    shapeParameters = parameters;
    try { return action(); } finally { shapeParameters = previous; }
  }

  private static string ShapeName(int index) => "pbtTypeShape" + index;
  private static IEnumerable<string> ShapeFormals(IReadOnlyList<TypeParameter> parameters) =>
    parameters.Select((_, index) => ShapeName(index) + ": string");
  private IEnumerable<string> OriginalShapeArguments(MethodOrFunction callable) =>
    shapedCallables.Contains(callable) ? callable.TypeArgs.Select((_, index) => ShapeName(index)) : [];
  private static string ShapedFormals(IReadOnlyList<TypeParameter> parameters, IEnumerable<Formal> formals) =>
    string.Join(", ", ShapeFormals(parameters).Concat(formals.Select(formal => formal.Name + ": " + formal.Type)));
  private string WrapperFormals(MethodOrFunction callable, IEnumerable<Formal> formals) =>
    string.Join(", ", ShapeFormals(callable.TypeArgs).Concat(formals.Select(formal =>
      (formal.IsNameOnly ? "nameonly " : "") + formal.Name + ": " + formal.Type +
      (formal.DefaultValue == null ? "" : " := " + RenderDefault(formal.DefaultValue, callable.EnclosingClass.EnclosingModuleDefinition)))));
  private string ShapedArguments(MethodOrFunction callable, IEnumerable<Formal> formals) =>
    string.Join(", ", OriginalShapeArguments(callable).Concat(formals.Select(formal => formal.Name + " := " + formal.Name)));

  // Shape tokens follow Dafny's resolved type applications, never the erased CLR representation.
  private Expression ShapeExpression(Type type) {
    var token = new StringLiteralExpr(Token.NoToken, ContractRuntimeInstrumentation.TypeShapeToken(type, shapeParameters), false) { Type = new SeqType(Type.Char) };
    if (shapeParameters.Count == 0) { return token; }
    var runtimeModule = program.RawModules().Single(module => module.FullDafnyName == "PbtRuntime");
    var runtimeClass = runtimeModule.TopLevelDecls.OfType<TopLevelDeclWithMembers>()
      .Single(declaration => declaration.Name == "PbtChecks");
    var instantiateShape = runtimeClass.Members.OfType<Function>()
      .Single(function => function.Name == "InstantiateShape");
    var arguments = new SeqDisplayExpr(Token.NoToken, shapeParameters.Select((_, index) =>
      (Expression)new IdentifierExpr(Token.NoToken, ShapeName(index)) { Type = new SeqType(Type.Char) }).ToList()) { Type = new SeqType(new SeqType(Type.Char)) };
    var receiverType = new UserDefinedType(Token.NoToken, RuntimeChecks, instantiateShape.EnclosingClass, []);
    return new FunctionCallExpr(Token.NoToken, new Name(Token.NoToken, "InstantiateShape"), new StaticReceiverExpr(Token.NoToken, receiverType, false) { Type = receiverType },
      Token.NoToken, null, [token, arguments]) {
      Function = instantiateShape,
      Type = new SeqType(Type.Char),
      TypeApplication_AtEnclosingClass = [],
      TypeApplication_JustFunction = []
    };
  }

  private string ShapeText(Type type) => Printer.ExprToString(program.Options, ShapeExpression(type));

  private void InstrumentTypeShapes(IReadOnlySet<INode> protectedAssertionNodes) {
    foreach (var callable in shapedCallables.Where(callable => callable is not Method { FunctionFromWhichThisIsByMethodDecl: not null })) {
      var open = ArgumentOpen(callable.NameNode.EndToken);
      Insert(open.Uri, open.pos + 1, string.Join(", ", ShapeFormals(callable.TypeArgs)) + (callable.Ins.Count == 0 ? "" : ", "));
    }
    foreach (var callable in Members().OfType<MethodOrFunction>()) {
      WithShapes(callable.TypeArgs, () => {
        foreach (var call in SourceNodes(callable).OfType<FunctionCallExpr>()
                   .Where(call => shapedCallables.Contains(call.Function) && !protectedAssertionNodes.Contains(call)).Distinct()) {
          if (call.OpenParen != null) {
            Insert(call.OpenParen.Uri, call.OpenParen.pos + 1,
              string.Join(", ", call.TypeApplication_JustFunction.Select(ShapeText)) +
              (call.Bindings.ArgumentBindings.Count == 0 ? "" : ", "));
          }
        }
        foreach (var call in SourceNodes(callable).OfType<CallStmt>()
                   .Where(call => shapedCallables.Contains(call.Method) && !protectedAssertionNodes.Contains(call)).Distinct()) {
          var open = ArgumentOpen(call.MethodSelect.MemberNameNode.EndToken);
          Insert(open.Uri, open.pos + 1, string.Join(", ", call.MethodSelect.TypeApplicationJustMember.Select(ShapeText)) +
            (call.Bindings.ArgumentBindings.Count == 0 ? "" : ", "));
        }
        return true;
      });
    }
    foreach (var constructor in reachableDatatypeConstructors) {
      WithShapes([], () => {
        foreach (var call in constructor.Formals.Where(formal => formal.DefaultValue != null)
                   .SelectMany(formal => SourceNodes(formal.DefaultValue!)).OfType<FunctionCallExpr>()
                   .Where(call => shapedCallables.Contains(call.Function) && !protectedAssertionNodes.Contains(call)).Distinct()) {
          if (call.TypeApplication_JustFunction.Any(type =>
                UsesTypeParameter(type, constructor.EnclosingDatatype!.TypeArgs))) {
            throw new NotSupportedException(
              "Generic datatype constructor defaults cannot forward diagnostic type shapes.");
          }
          if (call.OpenParen != null) {
            Insert(call.OpenParen.Uri, call.OpenParen.pos + 1,
              string.Join(", ", call.TypeApplication_JustFunction.Select(ShapeText)) +
              (call.Bindings.ArgumentBindings.Count == 0 ? "" : ", "));
          }
        }
        return true;
      });
    }
  }

  private static bool UsesTypeParameter(Type type, IReadOnlyCollection<TypeParameter> parameters) {
    type = type.NormalizeExpand();
    return type.AsTypeParameter is { } parameter && parameters.Contains(parameter) ||
      type.TypeArgs.Any(argument => UsesTypeParameter(argument, parameters));
  }

  private static Token ArgumentOpen(Token name) {
    var depth = 0;
    for (var token = name.Next; token != null; token = token.Next) {
      if (token.val == "<") { depth++; }
      if (token.val == ">") { depth--; }
      if (token.val == "(" && depth == 0) { return token; }
    }
    throw new NotSupportedException("Generic diagnostic callable has no source argument list.");
  }

  private bool HasContract(Function function) => function.Req.Count > 0 || function.Ens.Count > 0 || function.ByMethodBody != null || function.Ins.Any(formal => HasConstraint(formal.Type, 0)) || HasConstraint(function.ResultType, 0);

  private bool DefinitionAvailable => goalFunction is { Body: { } body } && Reason(body, false) == null;

  // Definition recursion stays in the detached definition; other calls validate the bodies they evaluate.
  private Expression Render(Expression expression, ModuleDefinition scope, bool wrapCallees, Function? definingFunction = null) =>
    new RuntimeSubstituter(_ => null, call =>
      call.Function == definingFunction || goalFunction != null && call.Function == goalFunction ? DefinitionName(call.Function) :
      wrapCallees && CheckedCallee(call.Function) ? SpecWrapper(call.Function) : null,
      call => shapedCallables.Contains(call.Function) ? call.TypeApplication_JustFunction.Select(ShapeExpression).ToList() : [])
      // Qualify original declarations before adding owned runtime shape helpers.
      // Those synthetic receivers already use their diagnostic source names.
      .Substitute(ContractQueryBuilder.QualifyExpression(program, scope, expression));

  // A declaration default remains in its original lexical scope. Preserve its authored bindings so an omitted
  // nested default is evaluated by that callee's runtime wrapper instead of being expanded at this call site.
  private string RenderDefault(Expression expression, ModuleDefinition scope) =>
    Printer.ExprToString(program.Options,
      new RuntimeSubstituter(_ => null,
        call => (CheckedCallee(call.Function) ? SpecWrapper(call.Function) : call.Name) +
          TypeArguments(call.TypeApplication_JustFunction, scope),
        call => shapedCallables.Contains(call.Function) ? call.TypeApplication_JustFunction.Select(ShapeExpression).ToList() : [],
        preserveWrittenBindings: true).Substitute(expression));

  private string TypeArguments(IReadOnlyList<Type> arguments, ModuleDefinition scope) => arguments.Count == 0 ? "" :
    "<" + string.Join(", ", arguments.Select(argument => ContractQueryBuilder.QualifiedType(program, scope, argument))) + ">";

  private bool CheckedCallee(Function function) => HasContract(function) && (!function.IsGhost || functions.Contains(function));

  private string DefinitionName(Function function) => WithShapes(function.TypeArgs, () => DefinitionNameCore(function));

  private string DefinitionNameCore(Function function) {
    if (definitionNames.TryGetValue(function, out var existing)) { return existing; }
    var name = function.Name + "__pbt_definition";
    definitionNames.Add(function, name);
    var body = new RuntimeSubstituter(node => node is StmtExpr statementExpression ? statementExpression.E : null).Substitute(function.Body!);
    Insert(function.Origin.Uri, function.StartToken.pos, "\n" + (function.HasStaticKeyword ? "static " : "") + "function " + name + TypeParameters(function.TypeArgs) + "(" +
      ShapedFormals(function.TypeArgs, function.Ins) + "): " + function.ResultType + "\n{\n" +
      Printer.ExprToString(program.Options, Render(body, function.EnclosingClass.EnclosingModuleDefinition, true, function)) + "\n}\n");
    return name;
  }

  // Descriptor clauses replace result references; locations and text come from the original function clauses.
  private string CalleePostconditions(Function function, Method descriptor) {
    var checks = string.Join("\n", descriptor.Ens.Select((clause, index) =>
      Check(clause.E, ContractRuntimeObligationKind.CalleePostcondition, descriptor, "-1", function.Ens[index].E.Origin, Text(function.Ens[index].E)))) +
      "\n" + TypeConstraintChecks(descriptor.Outs, ContractRuntimeObligationKind.CalleePostcondition, descriptor, null);
    if (function is { ByMethodBody: not null, Body: { } definition }) {
      var equality = Expression.CreateEq(Expression.CreateIdentExpr(descriptor.Outs.Single()), definition, function.ResultType);
      checks += "\n" + Check(equality, ContractRuntimeObligationKind.CalleePostcondition, descriptor, "-1", definition.StartToken,
        Text(definition), definingFunction: function);
    }
    return checks;
  }

  // Equal pending invocations share an obligation, but distinct arguments or returned values must be checked.
  private string GuardContracts(Function function, Method descriptor, string checks) {
    var key = "(" + string.Join(", ", new[] { "0" }.Concat(function.IsStatic ? [] : new[] { "this" })
      .Concat(descriptor.Ins.Select(f => f.Name)).Append(descriptor.Outs.Single().Name)) + ")";
    var identity = Quote(function.FullDafnyName);
    // Reference equality does not identify a heap state, and unverified by-method bodies may mutate it.
    var repeated = function.IsStatic && function.Reads.Expressions is not { Count: > 0 } &&
      descriptor.Ins.Concat(descriptor.Outs).All(f => ImmutableContractKey(f.Type)) ? "true" :
      "(" + Check(Expression.CreateBoolLiteral(function.Origin, true), ContractRuntimeObligationKind.CalleePostcondition,
        descriptor, "-1", function.Origin, "recursive callee contract", explicitValues: [], forceUncheckedReason: "recursive_heap_contract") + " true)";
    return "var pbtValidate" + nextName++ + " := if " + RuntimeChecks + ".EnterContract(" + identity + ", " +
      key + ") then (" + checks + "\nvar pbtExit" + nextName++ + " := " + RuntimeChecks + ".ExitContract(" +
      identity + ", " + key + "); true) else " + repeated + ";";
  }

  // Datatypes and type parameters may hide references; only these recursively immutable types identify a state.
  private static bool ImmutableContractKey(Type type) {
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: SubsetTypeDecl subset } subsetType) {
      return ImmutableContractKey(subset.RhsWithArgument(subsetType.TypeArgs));
    }
    if (type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: NewtypeDecl newtype } newtypeType) {
      return ImmutableContractKey(newtype.ConcreteBaseType(newtypeType.TypeArgs));
    }
    return type.IsIntegerType || type.IsBoolType || type.IsCharType || type.IsBitVectorType ||
      type.AsSeqType is { } sequence && ImmutableContractKey(sequence.Arg) ||
      type.AsSetType is { Finite: true } set && ImmutableContractKey(set.Arg) ||
      type.AsMultiSetType is { } multiset && ImmutableContractKey(multiset.Arg) ||
      type.AsMapType is { Finite: true } map && ImmutableContractKey(map.Domain) && ImmutableContractKey(map.Range);
  }

  private string SpecWrapper(Function function) => WithShapes(function.TypeArgs, () => SpecWrapperCore(function));

  private string SpecWrapperCore(Function function) {
    if (specWrappers.TryGetValue(function, out var existing)) { return existing; }
    var name = function.Name + "__pbt_spec_" + nextName++;
    specWrappers.Add(function, name);
    var descriptor = ContractCallableSelector.DescribeFunction(program, function, resultFamily.Value);
    oldDeclarations[descriptor] = ""; oldNames[descriptor] = [];
    // Domain uncertainty invalidates the sample just like an unchecked callee postcondition.
    var before = TypeConstraintChecks(descriptor.Ins, ContractRuntimeObligationKind.CalleePostcondition, descriptor, null) +
      string.Join("\n", descriptor.Req.Select(c => Reason(c.E, false) == null
      ? "var pbtDomain" + nextName++ + " := " + RuntimeChecks + ".RequireInSpec(" +
        Printer.ExprToString(program.Options, Render(c.E, function.EnclosingClass.EnclosingModuleDefinition, true)) + ");"
      : Check(c.E, ContractRuntimeObligationKind.CalleePostcondition, descriptor, "-1", c.E.Origin)));
    var after = GuardContracts(function, descriptor, CalleePostconditions(function, descriptor));
    Insert(function.Origin.Uri, function.StartToken.pos, FunctionWrapper(function, descriptor, name, before, after, decreasesStar: false));
    return name;
  }

  private Expression? RewriteState(Expression expression, Method owner,
    IDictionary<Expression, PendingOldCapture> pending) {
    if (expression is OldExpr old && old.At == null && Reason(old.Expr, false) == null) {
      var value = EntryExpression(old.Expr, owner);
      if (value != null) { return PlanOldCapture(old, value, owner, pending); }
      return null;
    }
    if (expression is UnchangedExpr { At: null } unchanged && unchanged.Frame.All(f => f.E.Type.IsRefType && f.E.Type.AsTopLevelTypeWithMembers is not null)) {
      Expression result = Expression.CreateBoolLiteral(expression.Origin, true);
      foreach (var frame in unchanged.Frame) {
        foreach (var field in frame.E.Type.AsTopLevelTypeWithMembers.Members.OfType<Field>().Where(f => !f.IsStatic && (frame.FieldName == null || f.Name == frame.FieldName))) {
          if (!CompilableType(field.Type)) { return null; }
          var current = new MemberSelectExpr(expression.Origin, frame.E, field) { Type = field.Type };
          result = Expression.CreateAnd(result,
            Expression.CreateEq(current, PlanOldCapture(current, current, owner, pending), field.Type));
        }
      }
      return result;
    }
    return null;
  }

  private Expression? EntryExpression(Expression expression, Method owner) {
    var active = new HashSet<IVariable>();
    var unavailable = false;
    Expression? Resolve(Expression node) {
      if (node.Resolved is not IdentifierExpr { Var: LocalVariable local }) { return null; }
      if (!active.Add(local)) { unavailable = true; return null; }
      var assignments = owner.Body?.Descendants().OfType<SingleAssignStmt>()
        .Where(a => a.Lhs.Resolved is IdentifierExpr id && id.Var == local).Distinct().ToList();
      Expression? result = null;
      if (local.Type.IsRefType && assignments is { Count: 1 } && assignments[0].Rhs is ExprRhs rhs &&
          rhs.Expr.Resolved is IdentifierExpr or ThisExpr) {
        result = new RuntimeSubstituter(Resolve).Substitute(rhs.Expr);
      } else { unavailable = true; }
      active.Remove(local);
      return result;
    }
    var resolved = new RuntimeSubstituter(Resolve).Substitute(expression);
    return unavailable ? null : resolved;
  }

  private Expression PlanOldCapture(Expression key, Expression value, Method owner,
    IDictionary<Expression, PendingOldCapture> pending) {
    var committed = oldNames.GetValueOrDefault(owner);
    if (committed != null && committed.TryGetValue(key, out var existing)) {
      return Expression.CreateIdentExpr(existing);
    }
    if (!pending.TryGetValue(key, out var capture)) {
      var variable = new BoundVar(key.Origin, "pbtOld" + nextName++, value.Type);
      capture = new(key, value, variable);
      pending.Add(key, capture);
    }
    return Expression.CreateIdentExpr(capture.Variable);
  }

  private void CommitOldCaptures(Method owner, IEnumerable<PendingOldCapture> pending,
    Expression evaluated) {
    var referenced = Expressions(evaluated).OfType<IdentifierExpr>()
      .Select(identifier => identifier.Var).ToHashSet();
    var committed = oldNames.GetValueOrDefault(owner);
    if (committed == null) {
      committed = [];
      oldNames.Add(owner, committed);
    }
    foreach (var capture in pending.Where(capture => referenced.Contains(capture.Variable))) {
      if (committed.ContainsKey(capture.Key)) { continue; }
      committed.Add(capture.Key, capture.Variable);
      var rendered = Printer.ExprToString(program.Options,
        Render(capture.Value, owner.EnclosingClass.EnclosingModuleDefinition, true));
      oldDeclarations[owner] = oldDeclarations.GetValueOrDefault(owner, "") +
        Location(capture.Key.Origin) + "var " + capture.Variable.Name + " := " + rendered + ";\n";
    }
  }

  private sealed class RuntimeSubstituter(Func<Expression, Expression?> replacement, Func<FunctionCallExpr, string?>? rename = null,
    Func<FunctionCallExpr, IReadOnlyList<Expression>>? prepend = null, bool preserveWrittenBindings = false)
    : Substituter(null!, [], []) {
    public override Expression Substitute(Expression expression) {
      if (expression is QuantifierExpr { SplitQuantifier: not null } quantifier) {
        // The resolver's trigger split distributes the range into each conjunct, which erases the compilable
        // bound shape of the written quantifier. Render and decide the original, unsplit quantifier instead.
        QuantifierExpr unsplit = quantifier is ForallExpr
          ? new ForallExpr(quantifier.Origin, quantifier.BoundVars, quantifier.Range, quantifier.Term, quantifier.Attributes)
          : new ExistsExpr(quantifier.Origin, quantifier.BoundVars, quantifier.Range, quantifier.Term, quantifier.Attributes);
        unsplit.Type = quantifier.Type;
        unsplit.Bounds = quantifier.Bounds;
        return Substitute(unsplit);
      }
      if (expression is FunctionCallExpr call && (rename != null || prepend != null)) {
        var name = rename?.Invoke(call) ?? call.Name;
        var arguments = prepend?.Invoke(call) ?? [];
        if (preserveWrittenBindings) {
          var bindings = arguments.Select(argument => new ActualBinding(null, argument)).Concat(
            call.Bindings.ArgumentBindings.Select(binding => new ActualBinding(binding.FormalParameterName,
              Substitute(binding.Actual), binding.IsGhost))).ToList();
          return new FunctionCallExpr(call.Origin, new Name(call.NameNode.Origin, name), Substitute(call.Receiver),
            call.OpenParen ?? call.Origin, call.CloseParen, new ActualBindings(bindings), call.AtLabel) {
            Function = call.Function,
            Type = call.Type,
            TypeApplication_AtEnclosingClass = call.TypeApplication_AtEnclosingClass,
            TypeApplication_JustFunction = call.TypeApplication_JustFunction,
            IsByMethodCall = call.IsByMethodCall,
            CoCall = call.CoCall,
            CoCallHint = call.CoCallHint
          };
        }
        var copy = (FunctionCallExpr)base.Substitute(call);
        return new FunctionCallExpr(call.Origin, new Name(call.NameNode.Origin, name), copy.Receiver, copy.OpenParen ?? call.Origin,
          copy.CloseParen, arguments.Concat(copy.Args).ToList()) {
          Function = call.Function,
          Type = call.Type,
          TypeApplication_AtEnclosingClass = call.TypeApplication_AtEnclosingClass,
          TypeApplication_JustFunction = call.TypeApplication_JustFunction
        };
      }
      if (preserveWrittenBindings && expression is DatatypeValue value) {
        var bindings = value.Bindings.ArgumentBindings.Select(binding => new ActualBinding(binding.FormalParameterName,
          Substitute(binding.Actual), binding.IsGhost)).ToList();
        return new DatatypeValue(value.Origin, value.DatatypeName, value.MemberName, new ActualBindings(bindings)) {
          Ctor = value.Ctor,
          Type = value.Type,
          InferredTypeArgs = value.InferredTypeArgs,
          InferredPreTypeArgs = value.InferredPreTypeArgs,
          IsCoCall = value.IsCoCall
        };
      }
      if (expression is StaticReceiverExpr receiver) {
        var type = receiver.Type;
        if (receiver.ContainerExpression != null && type.AsTopLevelTypeWithMembers is DefaultClassDecl declaration) {
          type = new UserDefinedType(expression.Origin,
            Printer.ExprToString(DafnyOptions.Default, receiver.ContainerExpression), declaration, type.TypeArgs);
        }
        return new StaticReceiverExpr(expression.Origin, type, receiver.IsImplicit) { Type = type };
      }
      return replacement(expression) ?? base.Substitute(expression);
    }
  }

  private string? Reason(Expression expression, bool allowOld) {
    foreach (var node in Expressions(expression)) {
      if (node is not StaticReceiverExpr && node.Type != null && !CompilableType(node.Type)) { return "non_compilable_type"; }
      if (node is FunctionCallExpr call && call.Function.IsGhost && !functions.Contains(call.Function)) { return "non_compilable_function"; }
      if (node is ComprehensionExpr comprehension && comprehension.UncompilableBoundVars().Count > 0) { return "unbounded_quantifier"; }
      if (node is LetExpr { Exact: false }) { return "let_such_that"; }
      if (node is OldExpr || node is UnchangedExpr) { return "old_state_not_captured"; }
      if (node is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Fresh or UnaryOpExpr.Opcode.Allocated }) { return "fresh_or_allocated"; }
      if (node is IdentifierExpr { Var: { IsGhost: true } variable } && variable is LocalVariable && !variables.Contains(variable)) { return "value_unavailable"; }
    }
    return null;
  }

  public static string IdPrefix(string id) => id[..id.LastIndexOf(':')];
  public static string Literal(string id) => Quote(id)[1..^1];
  public static bool IsCompiled(IReadOnlySet<string> literals, string id) => literals.Contains(Literal(id));

  /// <summary>Literal ids of runtime checks that remain in compiled (non-ghost) code of a resolved diagnostic program.</summary>
  public static IReadOnlySet<string> CompiledCheckLiterals(Program program) {
    var literals = new HashSet<string>(StringComparer.Ordinal);
    foreach (var member in Members(program)) {
      if (member is MethodOrConstructor { IsGhost: false, Body: { } body }) { Visit(body); }
      if (member is Function { IsGhost: false } function) {
        if (function.ByMethodDecl?.Body is { } byMethod) { Visit(byMethod); } else if (function.Body != null) { Visit2(function.Body); }
      }
    }
    return literals;
    void Visit(Statement statement) {
      if (statement.IsGhost) { return; }
      foreach (var expression in statement.NonSpecificationSubExpressions) { Visit2(expression); }
      foreach (var child in statement.SubStatements) { Visit(child); }
    }
    void Visit2(Expression expression) {
      if (!expression.WasResolved()) { return; }
      expression = expression.Resolved;
      if (expression is FunctionCallExpr { Function: { Name: "Check" or "Checkpoint", EnclosingClass.Name: "PbtChecks" } } call &&
          call.Args.Count > 0 && call.Args[0].Resolved is StringLiteralExpr { Value: string literal }) {
        literals.Add(literal);
      }
      if (expression is LetExpr { Exact: true } let) {
        for (var index = 0; index < let.LHSs.Count; index++) {
          if (let.LHSs[index].Vars.Any(variable => !variable.IsGhost)) { Visit2(let.RHSs[index]); }
        }
        Visit2(let.Body);
        return;
      }
      if (expression is StmtExpr statementExpression) { Visit2(statementExpression.E); return; }
      foreach (var child in expression.SubExpressions) { Visit2(child); }
    }
  }

  private static string Quote(string text) => JsonSerializer.Serialize(text, new JsonSerializerOptions { Encoder = System.Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping });
  private string RuntimeChecks => runtimeAlias + ".Runtime.PbtChecks";
  private string Location(IOrigin origin) {
    var location = sourceMap?.ResolveLocation(origin.Uri, origin.pos);
    return "var pbtLocation" + nextName++ + " := " + RuntimeChecks + ".Location(" +
      Quote(location == null ? origin.Uri + ":" + origin.line + ":" + origin.col :
        location.Path + ":" + location.Line + ":" + location.Column) + ");\n";
  }
  private string SerializeNamed(string name, Type type) => SerializeNamed(name, name, type);
  private string SerializeNamed(string label, string value, Type type) => RuntimeChecks + ".SerializeNamed(" +
    Quote(label) + ", " + value + ", " + ShapeText(type) + ")";
  private static string Encode(IReadOnlyList<string> parts) => parts.Count == 0 ? "\"{}\"" : "\"{\" + " + string.Join(" + \",\" + ", parts) + " + \"}\"";
  private static string EncodeFragments(IReadOnlyList<string> parts) => "[" + string.Join(", ", parts) + "]";
  private string Serialize(string name, Type type) => RuntimeChecks + ".Serialize(" + name + ", " + ShapeText(type) + ")";
  private string SerializeValues(IEnumerable<IVariable> values) => Encode(values.Select(v => SerializeNamed(v.Name, v.Type)).ToList());
  private string Text(Node node) {
    var range = node.EntireRange;
    return CachedSourceText(node.Origin.Uri).Slice(range.StartToken.pos, range.Length);
  }
  private void RemoveKeyword(Node node, string keyword) {
    foreach (var token in node.OwnedTokens.Where(t => t.val == keyword)) { Add(token.Uri, token.pos, token.val.Length, ""); }
  }
  private void RemoveAttribute(Attributes? attributes, string name) {
    if (Attributes.Find(attributes, name) is UserSuppliedAttributes attribute && sources.Any(s => ContractSourceSnapshot.UriFor(s.Path) == attribute.OpenBrace.Uri)) {
      Add(attribute.OpenBrace.Uri, attribute.OpenBrace.pos, attribute.CloseBrace.pos + 1 - attribute.OpenBrace.pos, "");
    }
  }
  private void Replace(Node node, string text) { var range = node.EntireRange; Add(node.Origin.Uri, range.StartToken.pos, range.Length, text); }
  private void RemoveStatement(Statement statement) {
    var range = statement.EntireRange;
    // Native reveal/hide ranges and parser-synthesized proof-call assignments stop before their semicolon.
    var ownsTerminator = statement is HideRevealStmt ||
      statement is AssignStatement { Lhss.Count: 0, ResolvedStatements: { Count: 1 } resolved } && resolved[0] is CallStmt;
    var terminator = ownsTerminator && range.EndToken.Next is { val: ";" } next ? next : null;
    var length = terminator == null ? range.Length : terminator.pos + 1 - range.StartToken.pos;
    Add(statement.Origin.Uri, range.StartToken.pos, length, "");
  }
  private void Insert(ContractSource source, int position, string text) => Insert(ContractSourceSnapshot.UriFor(source.Path), position, text);
  private void Insert(Uri uri, int position, string text) => Add(uri, position, 0, text);
  private void Add(Uri uri, int position, int length, string text) { edits.Add(new(uri, position, length, text)); }
  private SourceText CachedSourceText(Uri uri) {
    if (!sourceTextCache.TryGetValue(uri, out var text)) {
      var source = ContractSourceSnapshot.Find(sources, uri);
      text = new(source);
      sourceTextCache.Add(uri, text);
    }
    return text;
  }

  private IReadOnlyList<ContractSource> Apply(List<Edit> edits) =>
    Apply(sources, edits, source => CachedSourceText(ContractSourceSnapshot.UriFor(source.Path)));

  internal static IReadOnlyList<ContractSource> Apply(IReadOnlyList<ContractSource> sources, List<Edit> edits) =>
    Apply(sources, edits, source => new(source));

  private static IReadOnlyList<ContractSource> Apply(IReadOnlyList<ContractSource> sources, List<Edit> edits,
    Func<ContractSource, SourceText> sourceText) => sources.Select(source => {
      var selected = edits.Where(e => e.Uri == ContractSourceSnapshot.UriFor(source.Path)).Distinct().ToList();
      // A replacement owns the strict interior of its source range, so insertions into the replaced source disappear.
      // Empty proof-statement removals also contain their resolved child edits, never boundary siblings.
      selected.RemoveAll(e => selected.Any(other => other != e && other.Length > 0 && (e.Length == 0
        ? other.Start < e.Start && e.Start < other.Start + other.Length
        : other.Text == "" && e.Start >= other.Start && e.Start + e.Length <= other.Start + other.Length)));
      foreach (var left in selected.Where(e => e.Length > 0)) {
        var right = selected.FirstOrDefault(right => !ReferenceEquals(left, right) && right.Length > 0 && left.Start < right.Start + right.Length && right.Start < left.Start + left.Length);
        if (right != null) {
          throw new NotSupportedException("Overlapping diagnostic source replacements are not supported. " +
            source.Path + ": [" + left.Start + ", " + (left.Start + left.Length) + ") -> " + JsonSerializer.Serialize(left.Text) +
            " overlaps [" + right.Start + ", " + (right.Start + right.Length) + ") -> " + JsonSerializer.Serialize(right.Text));
        }
      }
      var text = sourceText(source);
      var output = new StringBuilder();
      var cursor = 0;
      foreach (var group in selected.GroupBy(edit => edit.Start).OrderBy(group => group.Key)) {
        var cursorIndex = text.Index(cursor);
        output.Append(text.Content, cursorIndex, text.Index(group.Key) - cursorIndex);
        foreach (var insertion in group.Where(edit => edit.Length == 0).Reverse()) {
          output.Append(insertion.Text);
        }
        if (group.SingleOrDefault(edit => edit.Length > 0) is { } replacement) {
          output.Append(replacement.Text);
          cursor = replacement.Start + replacement.Length;
        } else {
          cursor = group.Key;
        }
      }
      output.Append(text.Content, text.Index(cursor), text.Content.Length - text.Index(cursor));
      var content = output.ToString();
      return source with { Content = content, Sha256 = ContractHarnessBuilder.Hash(content) };
    }).ToList();
}
