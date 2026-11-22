#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.Triggers;

namespace Microsoft.Dafny;

/// <summary>
/// Computes entry-state frames for the deliberately small, stable fragment of
/// method bodies supported by {:inferModifies}. The result is an ordinary frame;
/// the verifier still checks both the body and every call against it.
/// </summary>
internal class InferModifiesClause {
  internal const string AttributeName = "inferModifies";
  private readonly ErrorReporter reporter;
  private readonly Dictionary<MethodOrConstructor, State> states = new();
  private readonly HashSet<MethodOrConstructor> candidates = new();
  private readonly Dictionary<MethodOrConstructor, List<Effect>> effects = new();
  private enum State { Done, Failed, StrictFailure }

  private sealed record Effect(FrameExpression? Frame, CallStmt? Call);
  private sealed record FrameRoot(MethodOrConstructor Method, IVariable? Variable);
  private sealed record RootEdge(FrameRoot Target, bool Grows, CallStmt Call, long Depth);
  private const string RecursiveGrowth = "recursive frame expansion exceeds the supported structural depth";
  private const string UnsupportedFrame = "frame must use this or an input and constant fields, or a finite set display of these";

  private InferModifiesClause(ErrorReporter reporter) {
    this.reporter = reporter;
  }

  internal static void Run(ModuleDefinition module, ErrorReporter reporter, CompilationData compilation) {
    var pass = new InferModifiesClause(reporter);
    var methods = module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()
      .SelectMany(decl => decl.Members).OfType<MethodOrConstructor>().ToList();
    var inferFromCli = compilation.Options.Get(CommonOptionBag.InferModifiesOption);
    var verifiedUris = inferFromCli ? compilation.VerifiedUris() : null;
    foreach (var method in methods) {
      if (Attributes.Contains(method.Attributes, AttributeName) ||
          (inferFromCli && verifiedUris!.Contains(method.Origin.Uri) &&
           method is Method { IsByMethod: false } && IsEligible(method) &&
           method.Mod.Expressions!.Count == 0 && method.Mod.Attributes == null)) {
        pass.candidates.Add(method);
      }
    }
    pass.InferAll(methods.Where(pass.candidates.Contains).ToList());
  }

  private static bool IsEligible(MethodOrConstructor method) {
    var module = method.EnclosingClass.EnclosingModuleDefinition;
    return method is Method && !method.IsGhost && !method.IsLemmaLike && method.Body != null &&
           method.EnclosingClass is not TraitDecl && method.RefinementBase == null &&
           method.OverriddenMember == null && method.OverriddenMethod == null &&
           !method.IsRefining && module.Implements == null && !UsesAutoContracts(method);
  }

  private static bool UsesAutoContracts(MethodOrConstructor method) {
    var enabled = true;
    if (!Attributes.ContainsBool(method.EnclosingClass.Attributes, "autocontracts", ref enabled) || !enabled) {
      return false;
    }
    enabled = true;
    return !Attributes.ContainsBool(method.Attributes, "autocontracts", ref enabled) || enabled;
  }

  private bool Fail(MethodOrConstructor method, IOrigin origin, string detail, State failure = State.Failed) {
    if (Attributes.Contains(method.Attributes, AttributeName)) {
      reporter.Error(MessageSource.Resolver, origin, $"{{:inferModifies}} cannot infer this effect: {detail}");
      if (failure == State.Failed) {
        failure = State.StrictFailure;
      }
    }
    states[method] = failure;
    return false;
  }

  private void InferAll(List<MethodOrConstructor> methods) {
    // Collect each body once. Failed implicit candidates retain their original
    // contracts, so exclude them from the graph before computing components.
    foreach (var method in methods) {
      if (method.Mod.Expressions!.Count != 0 || method.Mod.Attributes != null) {
        reporter.Error(MessageSource.Resolver, method.Origin,
          "{:inferModifies} cannot be combined with an explicit modifies clause");
        states[method] = State.StrictFailure;
      } else if (!IsEligible(method)) {
        reporter.Error(MessageSource.Resolver, method.Origin,
          "{:inferModifies} is unsupported for this method (ghost, bodyless, refinement, override, trait, constructor, lemma, or autocontracts)");
        states[method] = State.StrictFailure;
      } else {
        var collected = new List<Effect>();
        if (CollectStatement(method, method.Body!, collected, new InferredFrames())) {
          effects.Add(method, collected);
        }
      }
    }

    var order = methods.Select((method, index) => (method, index))
      .ToDictionary(pair => pair.method, pair => pair.index);
    var pending = new Stack<List<MethodOrConstructor>>();

    void PushComponents(List<MethodOrConstructor> remaining) {
      var included = remaining.ToHashSet();
      var graph = new Graph<MethodOrConstructor>();
      foreach (var method in remaining) {
        graph.AddVertex(method);
        foreach (var effect in effects[method]) {
          if (effect.Call is { } call && included.Contains(call.Method)) {
            graph.AddEdge(method, call.Method);
          }
        }
      }
      // Graph lists successors before callers. Reverse when pushing so that
      // components are popped in the same callee-first order.
      foreach (var representative in graph.TopologicallySortedComponents().AsEnumerable().Reverse()) {
        var component = graph.GetSCC(representative);
        component.Sort((left, right) => order[left].CompareTo(order[right]));
        pending.Push(component);
      }
    }

    PushComponents(methods.Where(effects.ContainsKey).ToList());
    while (pending.Count != 0) {
      var component = pending.Pop();
      var first = component[0];
      if (component.Count == 1 && !effects[first].Any(effect => effect.Call?.Method == first)) {
        InferAcyclic(first);
        continue;
      }
      var failedImplicit = InferComponent(component, component.ToHashSet());
      if (failedImplicit != null) {
        // No frame in this component has been published. Drop unsupported
        // implicit candidates, then retry against their original contracts.
        foreach (var method in failedImplicit) {
          states[method] = State.Failed;
          effects.Remove(method);
        }
        var removed = failedImplicit.ToHashSet();
        PushComponents(component.Where(method => !removed.Contains(method)).ToList());
      }
    }
  }

  private void InferAcyclic(MethodOrConstructor method) {
    var frames = new InferredFrames();
    foreach (var effect in effects[method]) {
      if (effect.Frame is { } direct) {
        frames.Add(direct);
      } else if (effect.Call is { } call) {
        if (states.TryGetValue(call.Method, out var state) && state == State.StrictFailure) {
          Fail(method, call.Origin, "callee inference failed", State.StrictFailure);
          return;
        }
        if (!TransferFrames(method, call, call.Method.Mod.Expressions!, frames)) {
          return;
        }
      }
    }
    Publish(method, frames);
  }

  // Returns implicit failures to remove and retry, or null when the component
  // either succeeded or failed as a whole.
  private List<MethodOrConstructor>? InferComponent(List<MethodOrConstructor> methods, HashSet<MethodOrConstructor> members) {
    var frames = methods.ToDictionary(method => method, _ => new InferredFrames());
    var incoming = methods.ToDictionary(method => method, _ => new List<(MethodOrConstructor Caller, CallStmt Call)>());
    var unsupported = new Dictionary<MethodOrConstructor, IOrigin>();
    foreach (var method in methods) {
      foreach (var effect in effects[method]) {
        if (effect.Frame is { } direct) {
          frames[method].Add(direct);
        } else if (effect.Call is { } call) {
          var callee = call.Method;
          if (members.Contains(callee)) {
            incoming[callee].Add((method, call));
          } else {
            if (states.TryGetValue(callee, out var state) && state == State.StrictFailure) {
              Fail(method, call.Origin, "callee inference failed", State.StrictFailure);
              FailComponent(methods);
              return null;
            }
            // Failed implicit candidates keep their original, usually empty, contract.
            if (!TransferFrames(method, call, callee.Mod.Expressions!, frames[method], false)) {
              unsupported.TryAdd(method, call.Origin);
            }
          }
        }
      }
    }

    // Remove all implicit failures before diagnosing strict ones. Retrying may
    // break this component and allow strict methods to use original contracts.
    var implicitFailures = methods.Where(method => unsupported.ContainsKey(method) &&
      !Attributes.Contains(method.Attributes, AttributeName)).ToList();
    if (implicitFailures.Count != 0) {
      return implicitFailures;
    }
    if (unsupported.Count != 0) {
      foreach (var method in methods.Where(unsupported.ContainsKey)) {
        Fail(method, unsupported[method], UnsupportedFrame);
      }
      FailComponent(methods);
      return null;
    }

    // A positive cycle reachable from a seeded frame would grow a path on
    // every turn. Detect it before the frame worklist can branch exponentially.
    var growth = FindRecursiveGrowth(methods, members, frames, out var transferDepth);
    if (growth != null) {
      Fail(growth.Value.Caller, growth.Value.Call.Origin, RecursiveGrowth);
      FailComponent(methods, growth.Value.Call.Origin, RecursiveGrowth);
      return null;
    }

    // This is a conservative fallback for the supported expression fragment.
    // Only reachable root mappings contribute, so unrelated scalar arguments
    // cannot inflate the depth budget. Bounded depth and finite display arity
    // bound the number of possible expression trees.
    long depthLimit = Math.Max(1, frames.Values.SelectMany(f => f.Expressions)
      .Select(frame => ExpressionDepth(frame.E)).DefaultIfEmpty(0).Max()) + transferDepth;
    var pending = new Queue<(MethodOrConstructor Method, FrameExpression Frame)>();
    var substituters = new Dictionary<CallStmt, Substituter>();
    foreach (var method in methods) {
      foreach (var frame in frames[method].Expressions) {
        pending.Enqueue((method, frame));
      }
    }
    while (pending.Count != 0) {
      var (callee, frame) = pending.Dequeue();
      foreach (var (caller, call) in incoming[callee]) {
        if (!substituters.TryGetValue(call, out var substituter)) {
          substituter = CreateSubstituter(call);
          substituters.Add(call, substituter);
        }
        var substituted = substituter.SubstFrameExpr(frame);
        var added = CreateFrame(caller, substituted.E, substituted.FieldName, substituted.Field);
        if (added == null) {
          unsupported.TryAdd(caller, call.Origin);
        } else if (ExpressionDepth(substituted.E) > depthLimit) {
          Fail(caller, call.Origin, RecursiveGrowth);
          FailComponent(methods, call.Origin, RecursiveGrowth);
          return null;
        } else if (frames[caller].Add(added)) {
          pending.Enqueue((caller, added));
        }
      }
    }
    implicitFailures = methods.Where(method => unsupported.ContainsKey(method) &&
      !Attributes.Contains(method.Attributes, AttributeName)).ToList();
    if (implicitFailures.Count != 0) {
      return implicitFailures;
    }
    if (unsupported.Count != 0) {
      foreach (var method in methods.Where(unsupported.ContainsKey)) {
        Fail(method, unsupported[method], UnsupportedFrame);
      }
      FailComponent(methods);
      return null;
    }
    // Publish only after every member has reached a fixed point.
    foreach (var method in methods) {
      Publish(method, frames[method]);
    }
    return null;
  }

  // Roots are method inputs or the receiver. A substitution maps a callee
  // root to zero or more caller roots, with positive weight when it adds a
  // constant-field projection or a set-display wrapper.
  private (MethodOrConstructor Caller, CallStmt Call)? FindRecursiveGrowth(
    List<MethodOrConstructor> methods, HashSet<MethodOrConstructor> members,
    Dictionary<MethodOrConstructor, InferredFrames> frames, out long transferDepth) {
    var nodes = new Dictionary<(MethodOrConstructor, IVariable?), FrameRoot>();
    var outgoing = new Dictionary<FrameRoot, List<RootEdge>>();
    var orderedEdges = new List<(FrameRoot Source, RootEdge Edge, MethodOrConstructor Caller)>();
    FrameRoot GetRoot(MethodOrConstructor method, IVariable? variable) {
      var key = (method, variable);
      if (!nodes.TryGetValue(key, out var node)) {
        node = new FrameRoot(method, variable);
        nodes.Add(key, node);
        outgoing.Add(node, []);
      }
      return node;
    }

    void AddMapping(MethodOrConstructor caller, CallStmt call, IVariable? calleeRoot, Expression actual) {
      var roots = new List<(IVariable? Variable, bool Grows)>();
      if (!FindRoots(caller, actual, false, roots)) {
        // TransferFrames/AddFrame will handle unsupported actuals if used.
        return;
      }
      var source = GetRoot(call.Method, calleeRoot);
      var depth = ExpressionDepth(actual);
      foreach (var (variable, grows) in roots) {
        var edge = new RootEdge(GetRoot(caller, variable), grows, call, depth);
        outgoing[source].Add(edge);
        orderedEdges.Add((source, edge, caller));
      }
    }

    foreach (var caller in methods) {
      foreach (var effect in effects[caller]) {
        if (effect.Call is not { } call || !members.Contains(call.Method)) {
          continue;
        }
        if (!call.Method.IsStatic) {
          AddMapping(caller, call, null, call.Receiver);
        }
        for (var i = 0; i < call.Method.Ins.Count; i++) {
          AddMapping(caller, call, call.Method.Ins[i], call.Args[i]);
        }
      }
    }

    var reachable = new HashSet<FrameRoot>();
    var pending = new Queue<FrameRoot>();
    foreach (var method in methods) {
      foreach (var frame in frames[method].Expressions) {
        var roots = new List<(IVariable? Variable, bool Grows)>();
        // Seed frames have already passed SourceExpression validation.
        if (FindRoots(method, frame.E, false, roots)) {
          foreach (var (variable, _) in roots) {
            var root = GetRoot(method, variable);
            if (reachable.Add(root)) {
              pending.Enqueue(root);
            }
          }
        }
      }
    }
    while (pending.Count != 0) {
      var root = pending.Dequeue();
      foreach (var edge in outgoing[root]) {
        if (reachable.Add(edge.Target)) {
          pending.Enqueue(edge.Target);
        }
      }
    }

    var graph = new Graph<FrameRoot>();
    transferDepth = 0;
    foreach (var root in reachable) {
      graph.AddVertex(root);
      foreach (var edge in outgoing[root]) {
        graph.AddEdge(root, edge.Target);
        transferDepth += edge.Depth;
      }
    }
    // Edges were collected in declaration and statement order.
    foreach (var (source, edge, caller) in orderedEdges) {
      if (reachable.Contains(source) && edge.Grows &&
          graph.GetSCCRepresentative(source) == graph.GetSCCRepresentative(edge.Target)) {
        return (caller, edge.Call);
      }
    }
    return null;
  }

  // Mirrors SourceExpression's supported fragment while recording root paths.
  private static bool FindRoots(MethodOrConstructor method, Expression expression, bool grows,
    List<(IVariable? Variable, bool Grows)> roots) {
    expression = expression.Resolved;
    switch (expression) {
      case ThisExpr when !method.IsStatic:
        roots.Add((null, grows));
        return true;
      case IdentifierExpr id when method.Ins.Contains(id.Var):
        roots.Add((id.Var, grows));
        return true;
      case MemberSelectExpr { Member: ConstantField, AtLabel: null } select when !select.Member.IsStatic:
        return FindRoots(method, select.Obj, true, roots);
      case SetDisplayExpr { Finite: true } display:
        return display.Elements.All(element => FindRoots(method, element, true, roots));
      default:
        return false;
    }
  }

  private void Publish(MethodOrConstructor method, InferredFrames frames) {
    method.Mod.Expressions!.AddRange(frames.Expressions);
    method.InferredModifiesFromCli = frames.Expressions.Count != 0 &&
                                     !Attributes.Contains(method.Attributes, AttributeName);
    states[method] = State.Done;
  }

  private void FailComponent(List<MethodOrConstructor> methods, IOrigin? origin = null, string? detail = null) {
    var strict = methods.Any(method => states.TryGetValue(method, out var state) && state == State.StrictFailure) ||
                 methods.Any(method => Attributes.Contains(method.Attributes, AttributeName));
    foreach (var method in methods) {
      if (!states.ContainsKey(method)) {
        Fail(method, origin ?? method.Origin, detail ?? "callee inference failed in recursive component",
          strict ? State.StrictFailure : State.Failed);
      } else if (strict) {
        states[method] = State.StrictFailure;
      }
    }
  }

  private static long ExpressionDepth(Expression expression) {
    expression = expression.Resolved;
    return 1 + expression.SubExpressions.Select(ExpressionDepth).DefaultIfEmpty(0).Max();
  }

  private static Substituter CreateSubstituter(CallStmt call) {
    var arguments = new Dictionary<IVariable, Expression>();
    for (var i = 0; i < call.Method.Ins.Count; i++) {
      arguments.Add(call.Method.Ins[i], call.Args[i]);
    }
    return new Substituter(call.Receiver, arguments,
      call.MethodSelect.TypeArgumentSubstitutionsAtMemberDeclaration());
  }

  private bool TransferFrames(MethodOrConstructor method, CallStmt call, List<FrameExpression> calleeFrames,
    InferredFrames frames, bool reportFailure = true) {
    // Most methods have no effects; avoid allocating a substituter for them.
    if (calleeFrames.Count == 0) {
      return true;
    }
    var substituter = CreateSubstituter(call);
    foreach (var frame in calleeFrames) {
      var substituted = substituter.SubstFrameExpr(frame);
      var added = CreateFrame(method, substituted.E, substituted.FieldName, substituted.Field);
      if (added == null) {
        return !reportFailure ? false : Fail(method, call.Origin, UnsupportedFrame);
      }
      frames.Add(added);
    }
    return true;
  }

  private bool CollectStatement(MethodOrConstructor method, Statement statement, List<Effect> effects,
    InferredFrames frames) {
    // ProduceStmt.SubStatements omits the resolved updates used for return values.
    if (statement is ProduceStmt { HiddenUpdate: not null } produce) {
      return CollectStatement(method, produce.HiddenUpdate, effects, frames);
    }
    if (statement is ModifyStmt) {
      return Fail(method, statement.Origin, "modify statements are unsupported");
    }
    var firstFrame = frames.Expressions.Count;
    // The verifier uses these summaries even if the body writes less.
    var declaredFrames = statement switch {
      LoopStmt loop => loop.Mod.Expressions,
      OpaqueBlock block => block.Modifies.Expressions,
      _ => null
    };
    if (declaredFrames != null) {
      foreach (var frame in declaredFrames) {
        if (!AddFrame(method, frame.E, frame.FieldName, frame.Field, frames)) {
          return false;
        }
      }
    }
    if (statement is SingleAssignStmt assignment) {
      if (assignment.Rhs is TypeRhs) {
        return Fail(method, statement.Origin, "allocation is unsupported");
      }
      if (!AddLhs(method, assignment.Lhs, frames)) {
        return false;
      }
    } else if (statement is AssignSuchThatStmt suchThat) {
      foreach (var lhs in suchThat.Lhss) {
        if (!AddLhs(method, lhs, frames)) {
          return false;
        }
      }
    } else if (statement is CallStmt call) {
      foreach (var lhs in call.Lhs) {
        if (!AddLhs(method, lhs, frames)) {
          return false;
        }
      }
      if (UsesAutoContracts(call.Method)) {
        return Fail(method, call.Origin, "calls to autocontracts methods are unsupported");
      }
    }
    for (var i = firstFrame; i < frames.Expressions.Count; i++) {
      effects.Add(new Effect(frames.Expressions[i], null));
    }
    if (statement is CallStmt callEffect) {
      effects.Add(new Effect(null, callEffect));
    }
    foreach (var child in statement.SubStatements) {
      if (!CollectStatement(method, child, effects, frames)) {
        return false;
      }
    }
    return true;
  }

  private bool AddLhs(MethodOrConstructor method, Expression lhs, InferredFrames frames) {
    switch (lhs.Resolved) {
      case IdentifierExpr:
        return true;
      case MemberSelectExpr { Member: Field field } select:
        return AddFrame(method, select.Obj, field.Name, field, frames);
      case SeqSelectExpr select:
        return AddFrame(method, select.Seq, null, null, frames);
      case MultiSelectExpr select:
        return AddFrame(method, select.Array, null, null, frames);
      default:
        return Fail(method, lhs.Origin, "unsupported assignment target");
    }
  }

  private bool AddFrame(MethodOrConstructor method, Expression expression, string? fieldName, Field? field,
    InferredFrames frames, IOrigin? failureOrigin = null) {
    var frame = CreateFrame(method, expression, fieldName, field);
    if (frame == null) {
      return Fail(method, failureOrigin ?? expression.Origin, UnsupportedFrame);
    }
    frames.Add(frame);
    return true;
  }

  private static FrameExpression? CreateFrame(MethodOrConstructor method, Expression expression, string? fieldName,
    Field? field) {
    var syntax = SourceExpression(method, expression);
    return syntax == null ? null : new FrameExpression(expression.Origin, syntax, fieldName) {
      DesugaredExpression = expression,
      Field = field
    };
  }

  private sealed class InferredFrames {
    private static readonly IEqualityComparer<Expression> TargetComparer = new LambdaEqualityComparer<Expression>(
      SameTarget, TargetHash);

    private static readonly IEqualityComparer<FrameExpression> FrameComparer = new LambdaEqualityComparer<FrameExpression>(
      (left, right) => left.Field == right.Field && left.FieldName == right.FieldName && SameTarget(left.E, right.E),
      frame => HashCode.Combine(frame.Field, frame.FieldName, TargetHash(frame.E)));

    private readonly HashSet<FrameExpression> seen = new(FrameComparer);
    public List<FrameExpression> Expressions { get; } = [];

    public bool Add(FrameExpression frame) {
      if (!seen.Add(frame)) {
        return false;
      }
      Expressions.Add(frame);
      return true;
    }

    private static bool SameTarget(Expression left, Expression right) {
      left = left.Resolved;
      right = right.Resolved;
      if (left is SetDisplayExpr { Finite: true } leftSet &&
          right is SetDisplayExpr { Finite: true } rightSet) {
        return new HashSet<Expression>(leftSet.Elements, TargetComparer).SetEquals(rightSet.Elements);
      }
      // Implicit and explicit receivers denote the same this parameter.
      return ((left is ThisExpr && right is ThisExpr) || ExprExtensions.ShallowEq_Top(left, right)) &&
             left.SubExpressions.SequenceEqual(right.SubExpressions, TargetComparer);
    }

    private static int TargetHash(Expression expression) {
      expression = expression.Resolved;
      if (expression is SetDisplayExpr { Finite: true } display) {
        var elements = new HashSet<Expression>(display.Elements, TargetComparer);
        var elementHash = 0;
        foreach (var element in elements) {
          elementHash = unchecked(elementHash + TargetHash(element));
        }
        return HashCode.Combine(typeof(SetDisplayExpr), elements.Count, elementHash);
      }
      var hash = new HashCode();
      switch (expression) {
        case IdentifierExpr identifier:
          hash.Add(identifier.Var);
          break;
        case MemberSelectExpr select:
          hash.Add(select.Member);
          break;
      }
      foreach (var child in expression.SubExpressions) {
        hash.Add(TargetHash(child));
      }
      return hash.ToHashCode();
    }
  }

  // Recreate syntax rather than cloning resolved expressions. Export checking
  // resolves these names again in the restricted view and can reject hidden fields.
  private static Expression? SourceExpression(MethodOrConstructor method, Expression expression) {
    expression = expression.Resolved;
    switch (expression) {
      case ThisExpr when !method.IsStatic:
        return new ThisExpr(expression.Origin);
      case IdentifierExpr id when method.Ins.Contains(id.Var):
        return new NameSegment(expression.Origin, id.Var.Name, null);
      case MemberSelectExpr { Member: ConstantField, AtLabel: null } select when !select.Member.IsStatic: {
          var receiver = SourceExpression(method, select.Obj);
          return receiver == null ? null : new ExprDotName(select.Origin, receiver, select.MemberNameNode, null);
        }
      case SetDisplayExpr { Finite: true } display: {
          var elements = new List<Expression>();
          foreach (var element in display.Elements) {
            var source = SourceExpression(method, element);
            if (source == null) {
              return null;
            }
            elements.Add(source);
          }
          return new SetDisplayExpr(display.Origin, true, elements);
        }
      default:
        return null;
    }
  }
}
