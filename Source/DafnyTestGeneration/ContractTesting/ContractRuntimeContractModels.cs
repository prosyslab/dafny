#nullable enable
using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny;
using Type = Microsoft.Dafny.Type;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Explicit finite-domain authorization carried by an empty generator helper.</summary>
public sealed record ContractRuntimeContractModelPolicy(string Goal, BigInteger Lower, BigInteger Upper,
  int MaxCandidates);

/// <summary>Plans concrete diagnostic states without granting proof or source trust.</summary>
public static class ContractRuntimeContractModels {
  public const string AttributeName = "pbt_contract_models";
  public const int MaximumCandidates = 4096;
  public const int MaximumPredicateBytes = 64 * 1024;

  public static async Task<ContractRuntimeContractModelPolicy?> ReadPolicyAsync(ContractSource? generator,
    string goal, DafnyOptions options, CancellationToken cancellationToken) {
    if (generator == null || !generator.Content.Contains(AttributeName, StringComparison.Ordinal)) { return null; }
    var reporter = new BatchErrorReporter(new DafnyOptions(options));
    var parsed = await ContractSourceSnapshot.ParseAsync(reporter, [generator], cancellationToken, resolve: false);
    if (reporter.ErrorCount != 0) {
      throw new NotSupportedException("Invalid contract-model generator source: " +
        string.Join("\n", reporter.AllMessages.Where(message => message.Level == ErrorLevel.Error)
          .Select(message => message.Message)));
    }
    return ReadPolicy(parsed, goal);
  }

  public static ContractRuntimeContractModelPolicy? ReadPolicy(Program program, string goal) {
    // A generator packet has not been resolved: RawModules depends on resolver-owned state.
    var marked = PacketMembers(program.DefaultModuleDef)
      .SelectMany(member => member.Attributes.AsEnumerable().Where(attribute => attribute.Name == AttributeName)
        .Select(attribute => (Member: member, Attribute: attribute))).ToList();
    if (marked.Count == 0) { return null; }
    if (marked.Count != 1) { throw Unsupported("exactly one policy helper is required"); }
    var (member, attribute) = marked[0];
    if (member is not Method { IsGhost: false, IsStatic: true, Body.Body.Count: 0 } helper ||
        helper.EnclosingClass is not DefaultClassDecl || helper.TypeArgs.Count != 0 ||
        helper.Ins.Count != 0 || helper.Outs.Count != 0 || helper.Req.Count != 0 || helper.Ens.Count != 0 ||
        helper.Mod.Expressions?.Count is > 0 || helper.Reads.Expressions?.Count is > 0 ||
        helper.Decreases.Expressions?.Count is > 0 || helper.HasExternAttribute || helper.HasAxiomAttribute) {
      throw Unsupported("policy must be an empty module-level method without parameters or contracts");
    }
    if (attribute.Args.Count != 4 || attribute.Args[0] is not LiteralExpr { Value: string target } || target != goal ||
        !Integer(attribute.Args[1], out var lower) || !Integer(attribute.Args[2], out var upper) ||
        !Integer(attribute.Args[3], out var cap) || lower > upper || cap < 1 || cap > MaximumCandidates) {
      throw Unsupported("policy requires the exact goal, integer lower/upper bounds, and a candidate cap in 1.." + MaximumCandidates);
    }
    return new(target, lower, upper, (int)cap);

    bool Integer(Expression expression, out BigInteger value) => BigInteger.TryParse(
      Printer.ExprToString(program.Options, expression), NumberStyles.AllowLeadingSign,
      CultureInfo.InvariantCulture, out value);

    static IEnumerable<MemberDecl> PacketMembers(ModuleDefinition module) {
      foreach (var declaration in module.TopLevelDecls) {
        if (declaration is TopLevelDeclWithMembers type) {
          foreach (var member in type.Members) { yield return member; }
        } else if (declaration is LiteralModuleDecl nested) {
          foreach (var member in PacketMembers(nested.ModuleDef)) { yield return member; }
        }
      }
    }
  }

  public static ContractRuntimeContractModelPlan? Create(Program program, Method goal,
    ContractRuntimeContractModelPolicy? policy) => policy == null ? null : new(program, goal, policy);

  /// <summary>Validates the same model fragment before an authorable body exists.</summary>
  public static ContractRuntimeContractModelPlan? CreateForAuthoring(Program program, Method goal,
    ContractRuntimeContractModelPolicy? policy) => policy == null ? null : new(program, goal, policy, allowMissingBody: true);

  internal static bool Scalar(Type type) => type.NormalizeExpandKeepConstraints() is BoolType or IntType;
  internal static NotSupportedException Unsupported(string reason) => new("contract_models_unsupported: " + reason);
}

/// <summary>A single flat receiver and its explicitly modeled bodyless extern transitions.</summary>
public sealed class ContractRuntimeContractModelPlan {
  private readonly Program program;
  private readonly Method goal;
  private readonly Formal? root;
  private readonly ClassDecl receiver;
  private readonly IReadOnlyList<Field> allFields;
  private readonly Dictionary<Method, IReadOnlyList<Field>> transitions = [];
  private readonly string prefix;
  public ContractRuntimeContractModelPolicy Policy { get; }
  public IReadOnlyList<Field> Fields { get; }
  public IReadOnlySet<string> ExternSymbols { get; }

  internal ContractRuntimeContractModelPlan(Program program, Method goal, ContractRuntimeContractModelPolicy policy,
    bool allowMissingBody = false) {
    this.program = program;
    this.goal = goal;
    Policy = policy;
    if (policy.Lower > policy.Upper || policy.MaxCandidates is < 1 or > ContractRuntimeContractModels.MaximumCandidates) {
      throw Unsupported("invalid finite-domain policy");
    }
    if (policy.Goal != goal.FullDafnyName || goal is Lemma || !allowMissingBody && goal.Body == null ||
        goal.HasExternAttribute || goal.TypeArgs.Count != 0 || goal.EnclosingClass.TypeArgs.Count != 0) {
      throw Unsupported("the selected goal must be an implemented, nongeneric method");
    }
    var references = goal.Ins.Where(formal => formal.Type.IsRefType).ToList();
    if (goal.IsStatic ? references.Count != 1 : references.Count != 0) {
      throw Unsupported("the goal must have exactly one receiver root and no reference aliases");
    }
    root = goal.IsStatic ? references[0] : null;
    receiver = (root?.Type.AsTopLevelTypeWithMembers ?? goal.EnclosingClass) as ClassDecl
      ?? throw Unsupported("the receiver must be a concrete class");
    if (receiver.TypeArgs.Count != 0 || receiver.Traits.Count != 0 ||
        root != null && !root.Type.IsNonNullRefType ||
        goal.Ins.Where(formal => formal != root).Concat(goal.Outs).Any(formal => !Scalar(formal.Type))) {
      throw Unsupported("only a nonnull flat nongeneric receiver and bool/int formals are supported");
    }
    allFields = receiver.Members.OfType<Field>().Where(field => !field.IsStatic).ToList();
    if (allFields.Any(field => !Scalar(field.Type) || field.IsGhost && !field.IsUserMutable)) {
      throw Unsupported("receiver fields must be bool/int; ghost constants and nested state are unsupported");
    }
    Fields = allFields.Where(field => field.IsGhost).ToList();
    if (Fields.Count == 0) { throw Unsupported("the receiver has no mutable ghost state"); }
    prefix = ContractBodyNames.Family(program, "pbtModel");
    // Family names must also be fresh against source local/formal names, not just declarations.
    if (ContractRuntimeSourcePreparation.Members(program).SelectMany(member => member.Descendants())
        .OfType<IVariable>().Any(variable => variable.Name.StartsWith(prefix, StringComparison.Ordinal))) {
      throw Unsupported("reserved model-local name collision");
    }
    var reachable = ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, [goal]).ToList();
    foreach (var method in reachable.OfType<Method>().Where(method => method.HasExternAttribute && method.Body == null)) {
      if (method.EnclosingClass != receiver || method.IsStatic || method.IsGhost || method.TypeArgs.Count != 0 ||
          method.Ins.Concat(method.Outs).Any(formal => formal.IsGhost || !Scalar(formal.Type))) {
        continue;
      }
      var writable = new HashSet<Field>();
      foreach (var frame in method.Mod.Expressions ?? []) {
        if (frame.E.Resolved is not ThisExpr) { throw Unsupported("extern frames must name this or this`field"); }
        if (frame.FieldName == null) { writable.UnionWith(Fields); } else if (frame.Field is { } field && Fields.Contains(field)) { writable.Add(field); } else { throw Unsupported("extern field frames must name a mutable ghost field"); }
      }
      transitions.Add(method, Fields.Where(writable.Contains).ToList());
    }
    ExternSymbols = transitions.Keys.Select(method => method.FullDafnyName).ToHashSet(StringComparer.Ordinal);
    if (goal.Body != null) { ValidateGoalBody(); }
    // Rendering validates every selected conjunct now, before a compiler or sample is started.
    _ = InitialCode("PbtChecks");
    foreach (var method in transitions.Keys) { _ = TransitionCode(method, "PbtChecks"); }
  }

  public bool IsModeled(MethodOrFunction method) => method is Method m && transitions.ContainsKey(m);

  public void ValidateGenerator(Method generator) {
    // Initialization is after Generate. Generator execution must not observe model-owned state first.
    var dependencies = ContractRuntimeObligationTransformer.RuntimeExecutionReachable(program, [generator]);
    foreach (var callable in dependencies.Where(callable => callable is not Constructor)) {
      var nodes = ReferenceEquals(callable, generator) ? generator.Body!.Descendants() : callable.Descendants();
      if (nodes.OfType<MemberSelectExpr>().Any(select => select.Member is Field field && Fields.Contains(field)) ||
          nodes.OfType<CallStmt>().Any(call => IsModeled(call.Method))) {
        throw Unsupported("generator execution cannot read, write, or call the modeled state before initialization");
      }
    }
  }

  public string InitialCode(string runtimeChecks) {
    var receiverName = root?.Name ?? ContractRuntimeGeneratorSignature.Names(goal).Receiver!;
    var bindings = goal.Ins.Where(formal => formal != root).ToDictionary(formal => (IVariable)formal, formal => formal.Name);
    return Search(goal, Fields, [], receiverName, goal.Req.Select(clause => clause.E), bindings,
      root, root == null, false, "initial", runtimeChecks);
  }

  public string TransitionCode(Method method, string runtimeChecks) {
    if (!transitions.TryGetValue(method, out var writable)) { throw new ArgumentException("Unknown modeled extern.", nameof(method)); }
    var bindings = method.Ins.ToDictionary(formal => (IVariable)formal, formal => formal.Name);
    return Search(method, writable, method.Outs, "this", method.Ens.Select(clause => clause.E), bindings,
      null, true, true, "transition", runtimeChecks);
  }

  private string Search(Method owner, IReadOnlyList<Field> writable, IReadOnlyList<Formal> outputs,
    string receiverName, IEnumerable<Expression> constraints, Dictionary<IVariable, string> bindings,
    Formal? receiverVariable, bool allowThis, bool allowOld, string phase, string runtimeChecks) {
    var types = writable.Select(field => field.Type).Concat(outputs.Select(formal => formal.Type)).ToList();
    var count = BigInteger.One;
    foreach (var type in types) {
      count *= type.IsBoolType ? 2 : Policy.Upper - Policy.Lower + 1;
      if (count > Policy.MaxCandidates) { throw Unsupported("joint candidate domain exceeds the declared cap for " + owner.FullDafnyName); }
    }
    var vector = prefix + "Values";
    var found = prefix + "Found";
    var lambda = prefix + "Candidate";
    string Element(string name, int index, Type type) => type.IsBoolType ? "(" + name + "[" + index + "] == 1)" : name + "[" + index + "]";
    var captures = new List<string>();
    var current = new Dictionary<Field, string>();
    var previous = new Dictionary<Field, string>();
    for (var i = 0; i < allFields.Count; i++) {
      var field = allFields[i];
      var slot = writable.ToList().IndexOf(field);
      if (allowOld || slot < 0) {
        var capture = prefix + "Old" + i;
        captures.Add("var " + capture + " := " + receiverName + "." + field.Name + ";");
        previous.Add(field, capture);
        if (slot < 0) { current.Add(field, capture); }
      }
      if (slot >= 0) { current.Add(field, Element(lambda, slot, field.Type)); }
    }
    for (var i = 0; i < outputs.Count; i++) {
      bindings.Add(outputs[i], Element(lambda, writable.Count + i, outputs[i].Type));
    }
    var renderer = new Renderer(current, previous, bindings, receiverVariable, allowThis, allowOld);
    var conjuncts = new List<string>();
    var predicateLength = 0;
    foreach (var expression in constraints) {
      var rendered = renderer.Render(expression);
      var nextLength = predicateLength + Encoding.UTF8.GetByteCount(rendered) + 2 + (conjuncts.Count == 0 ? 0 : 4);
      if (nextLength > ContractRuntimeContractModels.MaximumPredicateBytes) {
        throw Unsupported("aggregate model predicate exceeds 65536 UTF-8 bytes");
      }
      conjuncts.Add("(" + rendered + ")");
      predicateLength = nextLength;
    }
    var predicate = string.Join(" && ", conjuncts);
    if (predicate.Length == 0) { predicate = "true"; }
    var kinds = "[" + string.Join(", ", types.Select(type => type.IsBoolType ? "true" : "false")) + "]";
    var parameters = kinds + ", " + Policy.Lower.ToString(CultureInfo.InvariantCulture) + ", " +
      Policy.Upper.ToString(CultureInfo.InvariantCulture);
    var lines = captures;
    lines.Add("var " + found + ", " + vector + " := " + runtimeChecks + ".FindModel(" + parameters + ", " +
      Policy.MaxCandidates + ", (" + lambda + ": seq<int>) => " + predicate + ");");
    lines.Add("if !" + found + " { " + runtimeChecks + ".ModelExhausted(\"" + phase + "\", \"" + owner.FullDafnyName + "\"); return; }");
    for (var i = 0; i < writable.Count; i++) {
      lines.Add(receiverName + "." + writable[i].Name + " := " + Element(vector, i, writable[i].Type) + ";");
    }
    for (var i = 0; i < outputs.Count; i++) {
      lines.Add(outputs[i].Name + " := " + Element(vector, writable.Count + i, outputs[i].Type) + ";");
    }
    lines.Add(runtimeChecks + ".ModelChoice(\"" + phase + "\", \"" + owner.FullDafnyName + "\", " + parameters + ", " + vector + ");");
    return string.Join("\n", lines) + "\n";
  }

  private void ValidateGoalBody() {
    foreach (var node in goal.Body!.Descendants()) {
      if (node is TypeRhs || node is IVariable variable && variable.Type.IsRefType && variable != root ||
          node is IdentifierExpr identifier && identifier.Type.IsRefType && identifier.Var != root) {
        throw Unsupported("goal body allocation and receiver aliases are unsupported");
      }
      if (node is Expression expression && expression.Resolved.Type?.IsRefType == true &&
          expression.Resolved is not StaticReceiverExpr && !Root(expression, root, root == null)) {
        throw Unsupported("goal body reference values must be the selected receiver");
      }
      if (node is CallStmt call && (!IsModeled(call.Method) || !Root(call.Receiver, root, root == null))) {
        throw Unsupported("goal method calls must be modeled externs on the selected receiver");
      }
      if (node is MemberSelectExpr { Member: Field field } select && field.EnclosingClass == receiver &&
          !Root(select.Obj, root, root == null)) {
        throw Unsupported("field access through another receiver is unsupported");
      }
    }
  }

  private static bool Root(Expression expression, Formal? root, bool allowThis) => expression.Resolved switch {
    ThisExpr => allowThis,
    IdentifierExpr identifier => root != null && identifier.Var == root,
    _ => false
  };

  private sealed class Renderer(IReadOnlyDictionary<Field, string> current,
    IReadOnlyDictionary<Field, string> previous, IReadOnlyDictionary<IVariable, string> bindings,
    Formal? root, bool allowThis, bool allowOld) {
    private readonly HashSet<Function> active = [];
    private int nodes;
    public string Render(Expression expression) => Render(expression, bindings, allowThis, false);

    private string Render(Expression expression, IReadOnlyDictionary<IVariable, string> variables, bool thisReceiver, bool old) {
      var rendered = RenderCore(expression, variables, thisReceiver, old);
      if (Encoding.UTF8.GetByteCount(rendered) > ContractRuntimeContractModels.MaximumPredicateBytes) {
        throw Unsupported("rendered model predicate exceeds 65536 UTF-8 bytes");
      }
      return rendered;
    }

    private string RenderCore(Expression expression, IReadOnlyDictionary<IVariable, string> variables, bool thisReceiver, bool old) {
      if (++nodes > 4096) { throw Unsupported("expanded model predicate exceeds 4096 nodes"); }
      expression = expression.Resolved;
      if (!Scalar(expression.Type)) { throw Unsupported("model predicates require bool/int expressions"); }
      switch (expression) {
        case LiteralExpr { Value: bool boolValue }: return boolValue ? "true" : "false";
        case LiteralExpr { Value: BigInteger integerValue }: return integerValue.ToString(CultureInfo.InvariantCulture);
        case IdentifierExpr identifier when variables.TryGetValue(identifier.Var, out var variableValue):
          if (old && identifier.Var is Formal { InParam: false }) { throw Unsupported("old outputs are unsupported"); }
          return variableValue;
        case MemberSelectExpr { Member: Field field } select when Root(select.Obj, root, thisReceiver):
          if (!(old ? previous : current).TryGetValue(field, out var selected)) { throw Unsupported("foreign or static model field"); }
          return selected;
        case UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } unary:
          return "!(" + Render(unary.E, variables, thisReceiver, old) + ")";
        case BinaryExpr binary:
          var op = binary.ResolvedOp switch {
            BinaryExpr.ResolvedOpcode.Iff => "<==>",
            BinaryExpr.ResolvedOpcode.Imp => "==>",
            BinaryExpr.ResolvedOpcode.And => "&&",
            BinaryExpr.ResolvedOpcode.Or => "||",
            BinaryExpr.ResolvedOpcode.EqCommon => "==",
            BinaryExpr.ResolvedOpcode.NeqCommon => "!=",
            BinaryExpr.ResolvedOpcode.Lt => "<",
            BinaryExpr.ResolvedOpcode.Le => "<=",
            BinaryExpr.ResolvedOpcode.Gt => ">",
            BinaryExpr.ResolvedOpcode.Ge => ">=",
            BinaryExpr.ResolvedOpcode.Add => "+",
            BinaryExpr.ResolvedOpcode.Sub => "-",
            BinaryExpr.ResolvedOpcode.Mul => "*",
            _ => throw Unsupported("unsupported model operator: " + binary.Op)
          };
          return "(" + Render(binary.E0, variables, thisReceiver, old) + " " + op + " " + Render(binary.E1, variables, thisReceiver, old) + ")";
        case ITEExpr ite:
          return "(if " + Render(ite.Test, variables, thisReceiver, old) + " then " + Render(ite.Thn, variables, thisReceiver, old) +
            " else " + Render(ite.Els, variables, thisReceiver, old) + ")";
        case OldExpr oldExpression when allowOld && !old && oldExpression.At == null:
          return Render(oldExpression.Expr, variables, thisReceiver, true);
        case FunctionCallExpr call:
          var function = call.Function;
          if (function.Body == null || function.IsOpaque || function.HasExternAttribute || function.HasAxiomAttribute ||
              function is TwoStateFunction || function.ByMethodBody != null || function.TypeArgs.Count != 0 ||
              function.EnclosingClass.TypeArgs.Count != 0 || function.Req.Count != 0 || call.AtLabel != null ||
              function.Ins.Any(formal => !Scalar(formal.Type)) ||
              !function.IsStatic && !Root(call.Receiver, root, thisReceiver)) {
            throw Unsupported("only transparent acyclic total scalar definitions may be unfolded: " + function.FullDafnyName);
          }
          var arguments = function.Ins.Select((formal, index) => (formal, Value: Render(call.Args[index], variables, thisReceiver, old)))
            .ToDictionary(pair => (IVariable)pair.formal, pair => pair.Value);
          if (!active.Add(function)) { throw Unsupported("recursive model definition: " + function.FullDafnyName); }
          var body = Render(function.Body, arguments, !function.IsStatic, old);
          active.Remove(function);
          return "(" + body + ")";
        default: throw Unsupported("unsupported model expression: " + expression.GetType().Name);
      }
    }
  }

  private static bool Scalar(Type type) => ContractRuntimeContractModels.Scalar(type);
  private static NotSupportedException Unsupported(string reason) => ContractRuntimeContractModels.Unsupported(reason);
}
