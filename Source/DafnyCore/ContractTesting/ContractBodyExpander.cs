#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Microsoft.Dafny;

/// <summary>
/// Lowers detached resolved bodies to bounded diagnostic Dafny source. Dafny's resolver,
/// compiler and Boogie translator retain responsibility for value and heap semantics.
/// </summary>
public sealed class ContractBodyExpander {
  private readonly Program program;
  private readonly ContractBodyExpansionBudget budget;
  private readonly List<ContractBodyGoal> goals = [];
  private readonly List<ContractBodyFrontier> frontier = [];
  private readonly List<string> abstractCalls = [];
  private readonly List<ContractBodyAbstractCall> capturedCalls = [];
  private readonly List<string> trust = [];
  private readonly List<ContractBodyTraceEvent> traceEvents = [];
  private int serial;
  private string? reachableTarget;
  private int reachableInvocation;
  private readonly string expansionPrefix;
  private readonly string tracePrefix;
  private readonly string capturePrefix;
  private string ExitLabel => expansionPrefix + "Exit";
  private string TraceCount => tracePrefix + "Count";
  private string EntryInvocation => expansionPrefix + "EntryInvocation";

  public ContractBodyExpander(Program program, ContractBodyExpansionBudget? budget = null) {
    this.program = program;
    expansionPrefix = ContractBodyNames.Family(program, "contractExpansion");
    tracePrefix = ContractBodyNames.Family(program, "contractTrace");
    capturePrefix = ContractBodyNames.Family(program, "contractCall");
    this.budget = budget ?? new();
    if (this.budget.MaxCallDepth < 0 || this.budget.MaxLoopIterations < 0 || this.budget.MaxGoals <= 0) {
      throw new ArgumentOutOfRangeException(nameof(budget));
    }
  }

  private sealed record Context(Method Method, Dictionary<IVariable, Expression> Variables,
    Dictionary<TypeParameter, Type> Types, Expression? Receiver, int Depth, string ReturnLabel,
    Dictionary<LabeledStatement, (string Break, string Continue)> Loops, string? Symbol = null);

  public ContractBodyExpansionResult Expand(Method method, Expression? receiver = null, string? targetSymbol = null, int targetInvocation = 0) {
    reachableTarget = targetSymbol;
    reachableInvocation = targetInvocation;
    if (method.Body is not BlockStmt body) {
      throw new NotSupportedException("Bounded body expansion requires an available method block.");
    }
    var detached = new Cloner(cloneResolvedFields: true).CloneBlockStmt(body);
    var source = new StringBuilder();
    var context = new Context(method, [], [], receiver, 0, ExitLabel, []);
    source.AppendLine("label " + ExitLabel + ": {");
    foreach (var output in method.Outs) {
      source.AppendLine("var " + output.Name + ": " + output.Type + ";");
    }
    ReachableEntry(method, method.FullDafnyName, method, source);
    EmitBlock(detached, context, source);
    Goal(method, method, ContractBodyGoalKind.Return, source);
    source.AppendLine("}");
    var traceDeclarations = "ghost var " + EntryInvocation + ": int := 0;\nghost var " + TraceCount + ": int := 1;\n" + string.Join("\n",
      traceEvents.Select(item => "ghost var " + item.Name + "Local: int := 0;"));
    return new(method, detached, traceDeclarations + "\n" + source, goals, frontier, abstractCalls, trust, traceEvents, capturedCalls);
  }

  private string Fresh() => expansionPrefix + serial++;
  private string Print(Expression expression) => Printer.ExprToString(program.Options, expression);
  private Expression Substitute(Expression expression, Context context) =>
    new Substituter(context.Receiver!, context.Variables, context.Types).Substitute(expression);
  private static Expression Identifier(string name, Type type, IOrigin origin) =>
    new IdentifierExpr(origin, new BoundVar(origin, name, type));
  private ContractBodySourcePoint Point(IOrigin origin, Method method) {
    var range = origin.EntireRange ?? origin.ReportingRange;
    return new(method.FullDafnyName, range.StartToken.pos, range.Length, origin.line, origin.col);
  }
  private void Goal(NodeWithOrigin node, Method method, ContractBodyGoalKind kind, StringBuilder source, bool? branch = null, string? symbol = null) {
    var range = node.EntireRange;
    var location = new ContractBodySourcePoint(symbol ?? method.FullDafnyName, range.StartToken.pos, range.Length,
      range.StartToken.line, range.StartToken.col);
    if (branch is { } value) {
      var name = tracePrefix + traceEvents.Count;
      traceEvents.Add(new(name, location, value));
      source.AppendLine(name + "Local := " + TraceCount + "; " + TraceCount + " := " + TraceCount + " + 1;");
    }
    if (goals.Count >= budget.MaxGoals) {
      frontier.Add(new("goal_frontier" + frontier.Count, "goal_bound", Point(node.Origin, method)));
      return;
    }
    var id = "body" + goals.Count;
    goals.Add(new(id, kind, location, branch));
    source.AppendLine(ContractBodyExpansionResult.Marker(id));
  }
  private void ReachableEntry(NodeWithOrigin node, string symbol, Method method, StringBuilder source) {
    if (symbol != reachableTarget) { return; }
    source.AppendLine("if " + EntryInvocation + " == " + reachableInvocation + " {");
    Goal(node, method, ContractBodyGoalKind.EntryReachable, source, symbol: symbol);
    source.AppendLine("} " + EntryInvocation + " := " + EntryInvocation + " + 1;");
  }
  private void Stop(IOrigin origin, Context context, StringBuilder source, string reason) {
    var id = "frontier" + frontier.Count;
    frontier.Add(new(id, reason, Point(origin, context.Method)));
    source.AppendLine("break " + ExitLabel + ";");
  }
  private void EmitBlock(BlockStmt block, Context context, StringBuilder source) {
    var scoped = context with { Variables = new(context.Variables), Loops = new(context.Loops) };
    foreach (var statement in block.Body) {
      EmitStatement(statement, scoped, source);
    }
  }
  private void EmitStatement(Statement statement, Context context, StringBuilder source) {
    switch (statement) {
      case BlockStmt block:
        source.AppendLine("{");
        EmitBlock(block, context, source);
        source.AppendLine("}");
        break;
      case VarDeclStmt declaration:
        foreach (var variable in declaration.Locals) {
          var name = Fresh();
          var type = variable.Type.Subst(context.Types);
          context.Variables[variable] = Identifier(name, type, variable.Origin);
          source.AppendLine((variable.IsGhost ? "ghost " : "") + "var " + name + ": " + type + ";");
        }
        if (declaration.Assign != null) {
          EmitStatement(declaration.Assign, context, source);
        }
        break;
      case AssignStatement { ResolvedStatements: { Count: 1 } resolved } when resolved[0] is CallStmt call:
        EmitCall(call, context, source);
        break;
      case AssignStatement assignment:
        EmitAssignment(assignment.Lhss, assignment.Rhss, context, source, assignment.Origin);
        break;
      case SingleAssignStmt assignment:
        EmitAssignment([assignment.Lhs], [assignment.Rhs], context, source, assignment.Origin);
        break;
      case CallStmt call:
        EmitCall(call, context, source);
        break;
      case IfStmt conditional when !conditional.IsBindingGuard && conditional.Guard != null:
        var guard = EmitExpression(conditional.Guard, context, source);
        source.AppendLine("if " + Print(guard) + " {");
        Goal(conditional.Guard, context.Method, ContractBodyGoalKind.Branch, source, true, context.Symbol);
        EmitBlock(conditional.Thn, context, source);
        source.AppendLine("} else {");
        Goal(conditional.Guard, context.Method, ContractBodyGoalKind.Branch, source, false, context.Symbol);
        if (conditional.Els != null) {
          EmitStatement(conditional.Els, context, source);
        }
        source.AppendLine("}");
        break;
      case WhileStmt loop when loop.Guard != null && loop.Body != null:
        var exit = Fresh();
        source.AppendLine("label " + exit + ": {");
        EmitLoop(loop, context, source, 0, exit);
        source.AppendLine("}");
        break;
      case BreakOrContinueStmt jump when context.Loops.TryGetValue(jump.TargetStmt, out var labels):
        source.AppendLine("break " + (jump.IsContinue ? labels.Continue : labels.Break) + ";");
        break;
      case ReturnStmt returned:
        if (returned.HiddenUpdate != null) {
          EmitStatement(returned.HiddenUpdate, context, source);
        }
        Goal(returned, context.Method, ContractBodyGoalKind.Return, source);
        source.AppendLine("break " + context.ReturnLabel + ";");
        break;
      case AssertStmt assertion:
        var condition = Substitute(assertion.Expr, context);
        source.AppendLine("if !(" + Print(condition) + ") {");
        Goal(assertion, context.Method, ContractBodyGoalKind.AssertionFailure, source);
        source.AppendLine("break " + ExitLabel + "; }");
        break;
      case AssumeStmt assumption:
        trust.Add(context.Method.FullDafnyName + ":" + assumption.Origin.line + ": explicit assume");
        source.AppendLine("assume " + Print(Substitute(assumption.Expr, context)) + ";");
        break;
      case PrintStmt:
        // Printing does not affect symbolic values; the original executable still prints.
        break;
      default:
        Stop(statement.Origin, context, source, "unsupported_statement:" + statement.GetType().Name);
        break;
    }
  }

  private void EmitLoop(WhileStmt loop, Context context, StringBuilder source, int iteration, string exit) {
    var condition = EmitExpression(loop.Guard!, context, source);
    source.AppendLine("if " + Print(condition) + " {");
    if (iteration == budget.MaxLoopIterations) {
      Stop(loop.Origin, context, source, "loop_bound");
    } else {
      Goal(loop.Guard!, context.Method, ContractBodyGoalKind.Branch, source, true, context.Symbol);
      var next = Fresh();
      var inner = context with { Loops = new(context.Loops) { [loop] = (exit, next) } };
      source.AppendLine("label " + next + ": {");
      EmitBlock(loop.Body!, inner, source);
      source.AppendLine("}");
      EmitLoop(loop, context, source, iteration + 1, exit);
    }
    source.AppendLine("} else {");
    Goal(loop.Guard!, context.Method, ContractBodyGoalKind.Branch, source, false, context.Symbol);
    source.AppendLine("}");
  }

  private void EmitAssignment(IReadOnlyList<Expression> left, IReadOnlyList<AssignmentRhs> right,
    Context context, StringBuilder source, IOrigin origin) {
    if (right.Any(rhs => rhs is not ExprRhs)) {
      Stop(origin, context, source, "unsupported_assignment_rhs");
      return;
    }
    // Preserve simultaneous assignment. The existing resolver/translator performs the stores.
    var targets = left.Select(lhs => Print(CaptureTarget(lhs, context, source))).ToList();
    var values = right.Cast<ExprRhs>().Select(rhs => Print(EmitExpression(rhs.Expr, context, source))).ToList();
    source.AppendLine(string.Join(", ", targets) + " := " + string.Join(", ", values) + ";");
  }

  private void EmitCall(CallStmt call, Context context, StringBuilder source) {
    if (call.Method is not Method method) {
      Stop(call.Origin, context, source, "constructor_call");
      return;
    }
    var targets = call.Lhs.Select(lhs => Print(CaptureTarget(lhs, context, source))).ToList();
    if (method.Body == null || Attributes.Contains(method.Attributes, "extern")) {
      var abstractReceiver = method.IsStatic ? null : Bind(EmitExpression(call.Receiver, context, source), source);
      var arguments = call.Args.Select(arg => Bind(EmitExpression(arg, context, source), source)).ToList();
      var abstractTypes = call.MethodSelect.TypeArgumentSubstitutionsWithParents().ToDictionary(pair => pair.Key,
        pair => pair.Value.Subst(context.Types));
      var outputs = method.Outs.Select(output => Identifier(Fresh(), output.Type.Subst(abstractTypes), output.Origin)).ToList();
      foreach (var output in outputs) { source.AppendLine("var " + Print(output) + ": " + output.Type + ";"); }
      var captured = CaptureCall(method, arguments, outputs, abstractReceiver,
        call.MethodSelect.TypeApplicationJustMember.Select(type => type.Subst(context.Types)).ToList());
      source.AppendLine(captured.BeforeMarker);
      var selection = (MemberSelectExpr)new Cloner(cloneResolvedFields: true).CloneExpr(Substitute(call.MethodSelect, context));
      if (abstractReceiver != null) { selection.Obj = abstractReceiver; }
      source.AppendLine((outputs.Count == 0 ? "" : string.Join(", ", outputs.Select(Print)) + " := ") +
        Print(selection) + "(" + string.Join(", ", arguments.Select(Print)) + ");");
      source.AppendLine(captured.AfterMarker);
      if (targets.Count > 0) {
        source.AppendLine(string.Join(", ", targets) + " := " + string.Join(", ", outputs.Select(Print)) + ";");
      }
      return;
    }
    if (context.Depth >= budget.MaxCallDepth || method.Body is not BlockStmt body) {
      Stop(call.Origin, context, source, "call_bound");
      return;
    }
    var types = call.MethodSelect.TypeArgumentSubstitutionsWithParents().ToDictionary(pair => pair.Key,
      pair => pair.Value.Subst(context.Types));
    var variables = new Dictionary<IVariable, Expression>();
    Expression? receiver = null;
    if (!method.IsStatic) {
      receiver = Bind(EmitExpression(call.Receiver, context, source), source);
    }
    for (var index = 0; index < method.Ins.Count; index++) {
      variables[method.Ins[index]] = Bind(EmitExpression(call.Args[index], context, source), source);
    }
    foreach (var output in method.Outs) {
      var name = Fresh();
      var type = output.Type.Subst(types);
      variables[output] = Identifier(name, type, output.Origin);
      source.AppendLine("var " + name + ": " + type + ";");
    }
    var label = Fresh();
    var inner = new Context(method, variables, types, receiver, context.Depth + 1, label, []);
    foreach (var requirement in method.Req) {
      source.AppendLine("if !(" + Print(Substitute(requirement.E, inner)) + ") {");
      Goal(call, context.Method, ContractBodyGoalKind.CallPreconditionFailure, source);
      source.AppendLine("break " + ExitLabel + "; }");
    }
    ReachableEntry(call, method.FullDafnyName, method, source);
    source.AppendLine("label " + label + ": {");
    EmitBlock(body, inner, source);
    source.AppendLine("}");
    if (call.Lhs.Count > 0) {
      source.AppendLine(string.Join(", ", targets) + " := " +
                        string.Join(", ", method.Outs.Select(output => Print(variables[output]))) + ";");
    }
  }

  private ContractBodyAbstractCall CaptureCall(MethodOrFunction callable, IReadOnlyList<Expression> arguments,
    IReadOnlyList<Expression> outputs, Expression? receiver, IReadOnlyList<Type> typeArguments) {
    abstractCalls.Add(callable.FullDafnyName);
    var names = callable is Method method ? method.Outs.Select(output => output.Name).ToList() :
      new List<string> { ((Function)callable).Result?.Name ?? ContractBodyNames.Family(program, "contractResult") };
    var captured = new ContractBodyAbstractCall(capturePrefix + capturedCalls.Count, callable,
      arguments.Select((argument, index) => new ContractBodyCapturedValue(callable.Ins[index].Name, argument.Type, Print(argument))).ToList(),
      outputs.Select((output, index) => new ContractBodyCapturedValue(names[index], output.Type, Print(output))).ToList(),
      receiver == null ? null : new ContractBodyCapturedValue("receiver", receiver.Type, Print(receiver)), typeArguments);
    capturedCalls.Add(captured);
    return captured;
  }

  private Expression CaptureTarget(Expression expression, Context context, StringBuilder source) {
    var target = new Cloner(cloneResolvedFields: true).CloneExpr(Substitute(expression.Resolved, context));
    switch (target) {
      case MemberSelectExpr member:
        member.Obj = Bind(member.Obj, source);
        break;
      case SeqSelectExpr selection:
        selection.Seq = Bind(selection.Seq, source);
        selection.E0 = selection.E0 == null ? null : Bind(selection.E0, source);
        break;
      case MultiSelectExpr selection:
        selection.Array = Bind(selection.Array, source);
        selection.Indices = selection.Indices.Select(index => Bind(index, source)).ToList();
        break;
    }
    return target;
  }

  private Expression Bind(Expression expression, StringBuilder source) {
    var name = Fresh();
    source.AppendLine("var " + name + ": " + expression.Type + " := " + Print(expression) + ";");
    return Identifier(name, expression.Type, expression.Origin);
  }

  private Expression EmitExpression(Expression expression, Context context, StringBuilder source, bool synthetic = false) {
    expression = expression.Resolved;
    if (expression is IdentifierExpr or ThisExpr or LiteralExpr) {
      return Substitute(expression, context);
    }
    if (expression is ITEExpr conditional && !conditional.IsBindingGuard) {
      var guard = EmitExpression(conditional.Test, context, source);
      var name = Fresh();
      var type = conditional.Type.Subst(context.Types);
      source.AppendLine("var " + name + ": " + type + ";");
      source.AppendLine("if " + Print(guard) + " {");
      if (!synthetic) { Goal(conditional.Test, context.Method, ContractBodyGoalKind.Branch, source, true, context.Symbol); }
      var thenValue = EmitExpression(conditional.Thn, context, source);
      source.AppendLine(name + " := " + Print(thenValue) + "; } else {");
      if (!synthetic) { Goal(conditional.Test, context.Method, ContractBodyGoalKind.Branch, source, false, context.Symbol); }
      var elseValue = EmitExpression(conditional.Els, context, source);
      source.AppendLine(name + " := " + Print(elseValue) + "; }");
      return Identifier(name, type, expression.Origin);
    }
    if (expression is BinaryExpr binary && binary.Op is BinaryExpr.Opcode.And or BinaryExpr.Opcode.Or or BinaryExpr.Opcode.Imp) {
      var truth = new LiteralExpr(expression.Origin, true) { Type = Type.Bool };
      var falsity = new LiteralExpr(expression.Origin, false) { Type = Type.Bool };
      return EmitExpression(new ITEExpr(expression.Origin, false, binary.E0,
        binary.Op == BinaryExpr.Opcode.Or ? truth : binary.E1,
        binary.Op == BinaryExpr.Opcode.And ? falsity : binary.Op == BinaryExpr.Opcode.Or ? binary.E1 : truth) { Type = Type.Bool }, context, source, synthetic: true);
    }
    if (expression is FunctionCallExpr abstractCall &&
        (abstractCall.Function.Body == null || Attributes.Contains(abstractCall.Function.Attributes, "extern"))) {
      var receiver = abstractCall.Function.IsStatic ? null : Bind(EmitExpression(abstractCall.Receiver, context, source), source);
      var arguments = abstractCall.Args.Select(argument => Bind(EmitExpression(argument, context, source), source)).ToList();
      var invocation = (FunctionCallExpr)new Cloner(cloneResolvedFields: true).CloneExpr(Substitute(abstractCall, context));
      if (receiver != null) { invocation.Receiver = receiver; }
      for (var index = 0; index < arguments.Count; index++) { invocation.Args[index] = arguments[index]; }
      var result = Identifier(Fresh(), abstractCall.Type.Subst(context.Types), abstractCall.Origin);
      source.AppendLine("var " + Print(result) + ": " + result.Type + ";");
      var captured = CaptureCall(abstractCall.Function, arguments, [result], receiver,
        abstractCall.TypeApplication_JustFunction.Select(type => type.Subst(context.Types)).ToList());
      source.AppendLine(captured.BeforeMarker);
      source.AppendLine(Print(result) + " := " + Print(invocation) + ";");
      source.AppendLine(captured.AfterMarker);
      return result;
    }
    if (expression is FunctionCallExpr call && call.Function.Body != null) {
      if (call.Function.ByMethodDecl is { } byMethod && call.IsByMethodCall) {
        var result = Identifier(Fresh(), call.Type.Subst(context.Types), call.Origin);
        source.AppendLine("var " + Print(result) + ": " + result.Type + ";");
        var selection = new MemberSelectExpr(call.Origin, call.Receiver, byMethod.NameNode) {
          Member = byMethod,
          TypeApplicationAtEnclosingClass = call.TypeApplication_AtEnclosingClass,
          TypeApplicationJustMember = call.TypeApplication_JustFunction
        };
        EmitCall(new CallStmt(call.Origin, [result], selection, call.Args), context, source);
        return result;
      }
      if (context.Depth >= budget.MaxCallDepth || call.Function.IsOpaque ||
          !call.Function.IsRevealedInScope(program.ModuleSigs[context.Method.EnclosingClass.EnclosingModuleDefinition].VisibilityScope)) {
        throw new NotSupportedException("Function body expansion reached a bound or unavailable definition: " + call.Function.FullDafnyName);
      }
      var variables = new Dictionary<IVariable, Expression>();
      for (var index = 0; index < call.Args.Count; index++) {
        variables[call.Function.Ins[index]] = Bind(EmitExpression(call.Args[index], context, source), source);
      }
      var types = call.TypeArgumentSubstitutionsWithParents().ToDictionary(pair => pair.Key,
        pair => pair.Value.Subst(context.Types));
      var inner = context with {
        Variables = variables,
        Types = types,
        Depth = context.Depth + 1,
        Symbol = call.Function.FullDafnyName,
        Receiver = call.Function.IsStatic ? null : Bind(EmitExpression(call.Receiver, context, source), source)
      };
      foreach (var requirement in call.Function.Req) {
        source.AppendLine("if !(" + Print(Substitute(requirement.E, inner)) + ") {");
        Goal(call, context.Method, ContractBodyGoalKind.CallPreconditionFailure, source);
        source.AppendLine("break " + ExitLabel + "; }");
      }
      ReachableEntry(call, call.Function.FullDafnyName, context.Method, source);
      return EmitExpression(call.Function.Body, inner, source);
    }
    // Binders stay intact. Their logical semantics belong to the original Dafny translator.
    if (expression is ComprehensionExpr or LetExpr or MatchExpr or NestedMatchExpr) {
      return Substitute(expression, context);
    }
    return Substitute(new ChildrenCloner(child => EmitExpression(child, context, source)).CloneRoot(expression), context);
  }

  private sealed class ChildrenCloner(Func<Expression, Expression> rewrite) : Cloner(cloneResolvedFields: true) {
    public Expression CloneRoot(Expression expression) => base.CloneExpr(expression);
    public override Expression CloneExpr(Expression expression) => expression == null ? null! : rewrite(expression);
  }
}
