#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;

namespace Microsoft.Dafny;

/// <summary>
/// Pre-resolve AST rewriter that turns opt-in direct self-recursion into recursion on an explicit fuel parameter.
///
/// How to enable:
///   {:autofuel}            uses a default fuel value (currently 100000)
///   {:autofuel 12345}      uses the given default fuel value
///
/// Supported:
/// - Only direct self recursion (a callable calling itself by name in its body)
/// - Recursive calls may use positional or named arguments; the generated fuel argument is passed using a name binding.
/// - Only a limited set of function result types, for which a syntactic neutral value can be constructed pre-resolve:
///   bool, int, nat, seq, set, multiset, map
///
/// Known limitations (pre-resolve, name-based detection):
/// - Calls are detected by simple name patterns like f(..), this.f(..), or .f(..) on implicit/explicit this.
/// - This can miss recursion through qualification (e.g. C.f(..)) or be fooled by a function-valued variable named f.
/// - Mutual recursion is not supported; best-effort detection is performed among other {:autofuel} callables in the same class.
/// </summary>
public class AutoFuelRewriter : IRewriter {
  private const string AttributeName = "autofuel";
  private const string FuelSuffix = "__fuel";
  private const string OutOfFuelSuffix = "__out_of_fuel";
  private const string FuelParamBaseName = "__fuel";
  private const int DefaultFuel = 100000;

  public AutoFuelRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PreResolve(ModuleDefinition moduleDefinition) {
    ArgumentNullException.ThrowIfNull(moduleDefinition);

    foreach (var decl in moduleDefinition.TopLevelDecls!.OfType<TopLevelDeclWithMembers>()) {
      ProcessDecl(decl);
    }
  }

  private void ProcessDecl(TopLevelDeclWithMembers decl) {
    ArgumentNullException.ThrowIfNull(decl);

    // Best-effort mutual recursion detection among other {autofuel} members in the same declaration.
    // We only consider unqualified ApplySuffix calls by name.
    var annotatedCallables = decl.Members!
      .Where(m => m is Function || (m is MethodOrConstructor && m is not Constructor))
      .Where(m => IsEnabled(m.Attributes))
      .Cast<MemberDecl>()
      .ToList();

    var annotatedByName = annotatedCallables
      .GroupBy(m => m.Name)
      .ToDictionary(g => g.Key, g => g.ToList());

    var callsByName = new Dictionary<string, HashSet<string>>();
    foreach (var member in annotatedCallables) {
      callsByName[member.Name] = CollectUnqualifiedCalls(member);
    }

    foreach (var member in annotatedCallables.ToList()) {
      // Skip if best-effort mutual recursion is detected with another annotated callable.
      if (IsInMutualRecursionCycle(member.Name, callsByName, annotatedByName.Keys)) {
        Warn(member.Origin,
          $"[autofuel] Skipping {member.WhatKind} '{member.Name}': mutual recursion is not supported.");
        continue;
      }

      if (member is Function f) {
        TryFuelizeFunction(decl, f);
      } else if (member is MethodOrConstructor moc && member is not Constructor) {
        TryFuelizeMethod(decl, moc);
      }
    }
  }

  private static bool IsInMutualRecursionCycle(string start, Dictionary<string, HashSet<string>> callsByName, IEnumerable<string> candidateNames) {
    // Detect a cycle of length >= 2 in the subgraph induced by "candidateNames".
    // This is intentionally conservative and shallow: it only follows name edges.
    var candidates = new HashSet<string>(candidateNames);
    if (!candidates.Contains(start)) {
      return false;
    }

    // Reachability from start, excluding the trivial self edge.
    var work = new Stack<string>();
    var seen = new HashSet<string> { start };
    foreach (var next in callsByName.GetValueOrDefault(start, new HashSet<string>())) {
      if (candidates.Contains(next) && next != start) {
        work.Push(next);
      }
    }

    while (work.Count != 0) {
      var cur = work.Pop();
      if (!seen.Add(cur)) {
        continue;
      }

      // If cur can reach start, we have a mutual recursion cycle (length >= 2).
      if (callsByName.GetValueOrDefault(cur, new HashSet<string>()).Contains(start)) {
        return true;
      }

      foreach (var next in callsByName.GetValueOrDefault(cur, new HashSet<string>())) {
        if (candidates.Contains(next) && next != start && !seen.Contains(next)) {
          work.Push(next);
        }
      }
    }

    return false;
  }

  private HashSet<string> CollectUnqualifiedCalls(MemberDecl member) {
    var result = new HashSet<string>();
    INode? root = member switch {
      Function f => (INode?)f.Body,
      MethodOrConstructor m => m.Body,
      _ => null
    };

    if (root == null) {
      return result;
    }

    foreach (var apply in FindApplySuffixes(root)) {
      if (TryGetUnqualifiedName(apply.Lhs, out var calleeName)) {
        result.Add(calleeName);
      }
    }

    return result;
  }

  private void TryFuelizeFunction(TopLevelDeclWithMembers enclosingDecl, Function f) {
    ArgumentNullException.ThrowIfNull(enclosingDecl);
    ArgumentNullException.ThrowIfNull(f);

    if (!IsEnabled(f.Attributes)) {
      return;
    }

    if (f.Body == null) {
      Warn(f.Origin, $"[autofuel] Skipping function '{f.Name}': no body.");
      return;
    }

    if (f.ByMethodBody != null) {
      Warn(f.Origin, $"[autofuel] Skipping function '{f.Name}': function-by-method is not supported by autofuel (MVP).");
      return;
    }

    var fuelName = f.Name + FuelSuffix;
    if (enclosingDecl.Members!.Any(m => m.Name == fuelName)) {
      Warn(f.Origin, $"[autofuel] Skipping function '{f.Name}': generated sibling '{fuelName}' already exists.");
      return;
    }

    if (!ContainsDirectSelfCall(f.Body, f.Name)) {
      // Not recursive; do nothing.
      return;
    }

    var outOfFuelName = f.Name + OutOfFuelSuffix;
    if (enclosingDecl.Members!.Any(m => m.Name == outOfFuelName)) {
      Warn(f.Origin, $"[autofuel] Skipping function '{f.Name}': generated sibling '{outOfFuelName}' already exists.");
      return;
    }

    var cloner = new Cloner();

    // Create an out-of-fuel sibling: an "undefined" function that returns an arbitrary value of the right type.
    // We declare it as extern (bodyless non-ghost functions are only allowed when extern).
    var outOfFuel = CreateOutOfFuelFunction(f, outOfFuelName);

    var fuelized = (Function)cloner.CloneMember(f, false);
    fuelized.NameNode = new Name(f.Origin, fuelName);
    fuelized.InheritVisibility(f, false);

    // Add an extra in-parameter: __fuel*: int (avoid collisions with existing parameters).
    var fuelFormalName = FreshFuelFormalName(FuelParamBaseName, fuelized.Ins);
    var fuelFormal = new Formal(f.Origin, fuelFormalName, Type.Int, true, false, null);
    fuelized.Ins.Add(fuelFormal);

    // Replace decreases clause with: decreases fuel
    fuelized.Decreases = new Specification<Expression>([new IdentifierExpr(f.Origin, fuelFormal.Name)], null);

    // Rewrite recursive calls inside the fuelized body: f(...) -> f__fuel(..., __fuel-1)
    RewriteSelfCallsToFuel(fuelized.Body!, f.Name, fuelName, fuelFormal.Name);

    // Guard: if fuel < 0 then <outOfFuel(originalArgs)> else <body>
    var fuelId = new IdentifierExpr(f.Origin, fuelFormal.Name);
    var test = new BinaryExpr(f.Origin, BinaryExpr.Opcode.Lt, fuelId, new LiteralExpr(f.Origin, 0));
    var outOfFuelCall = MakeCallExpr(f.Origin, outOfFuelName,
      f.Ins.Select(p => (Expression)new IdentifierExpr(f.Origin, p.Name)).ToList());
    fuelized.Body = new ITEExpr(f.Origin, false, test, outOfFuelCall, fuelized.Body!);

    // Wrapper: original body becomes a call to the fuelized sibling with default fuel.
    var defaultFuel = GetDefaultFuel(f.Attributes);
    f.Body = MakeCallExpr(f.Origin, fuelName, f.Ins.Select(p => (Expression)new IdentifierExpr(f.Origin, p.Name)).ToList(),
      new LiteralExpr(f.Origin, defaultFuel));

    // Add the new member to the enclosing declaration.
    enclosingDecl.Members!.Add(outOfFuel);
    enclosingDecl.Members!.Add(fuelized);
  }

  private void TryFuelizeMethod(TopLevelDeclWithMembers enclosingDecl, MethodOrConstructor m) {
    ArgumentNullException.ThrowIfNull(enclosingDecl);
    ArgumentNullException.ThrowIfNull(m);

    if (!IsEnabled(m.Attributes)) {
      return;
    }

    if (m.Body == null) {
      Warn(m.Origin, $"[autofuel] Skipping method '{m.Name}': no body.");
      return;
    }

    var fuelName = m.Name + FuelSuffix;
    if (enclosingDecl.Members!.Any(mem => mem.Name == fuelName)) {
      Warn(m.Origin, $"[autofuel] Skipping method '{m.Name}': generated sibling '{fuelName}' already exists.");
      return;
    }

    if (!ContainsDirectSelfCall(m.Body, m.Name)) {
      // Not recursive; do nothing.
      return;
    }

    var cloner = new Cloner();
    var fuelized = (MethodOrConstructor)cloner.CloneMember(m, false);
    fuelized.NameNode = new Name(m.Origin, fuelName);
    fuelized.InheritVisibility(m, false);

    // Add __fuel*: int (avoid collisions with existing parameters).
    var fuelFormalName = FreshFuelFormalName(FuelParamBaseName, fuelized.Ins);
    var fuelFormal = new Formal(m.Origin, fuelFormalName, Type.Int, true, false, null);
    fuelized.Ins.Add(fuelFormal);

    // Replace decreases clause with: decreases fuel
    fuelized.Decreases = new Specification<Expression>([new IdentifierExpr(m.Origin, fuelFormal.Name)], null);

    // Rewrite recursive calls inside the fuelized body.
    RewriteSelfCallsToFuel(fuelized.Body!, m.Name, fuelName, fuelFormal.Name);

    // Add guard at start of the fuelized body:
    // if fuel < 0 { havoc outs; return; }
    var guard = MakeFuelGuardForMethod(m.Origin, fuelFormal.Name, fuelized.Outs);
    fuelized.Body!.Prepend(guard);

    // Wrapper: replace original body with a single call to m__fuel(..., defaultFuel).
    var defaultFuel = GetDefaultFuel(m.Attributes);
    var wrapperCall = MakeMethodCallStmt(m.Origin, fuelName,
      m.Ins.Select(p => (Expression)new IdentifierExpr(m.Origin, p.Name)).ToList(),
      m.Outs.Select(p => (Expression)new IdentifierExpr(m.Origin, p.Name)).ToList(),
      new LiteralExpr(m.Origin, defaultFuel));
    m.SetBody(new BlockStmt(m.Origin, [wrapperCall]));

    enclosingDecl.Members!.Add(fuelized);
  }

  private static bool IsEnabled(Attributes? attributes) {
    var args = Attributes.FindExpressions(attributes, AttributeName);
    return args != null;
  }

  private static int GetDefaultFuel(Attributes? attributes) {
    var args = Attributes.FindExpressions(attributes, AttributeName);
    if (args != null && args.Count >= 1 && args[0] is LiteralExpr { Value: BigInteger bi }) {
      if (bi > int.MaxValue) {
        return int.MaxValue;
      }
      if (bi < 0) {
        return 0;
      }
      return (int)bi;
    }
    return DefaultFuel;
  }

  private void Warn(IOrigin origin, string message) {
    Reporter.Warning(MessageSource.Rewriter, "rw_autofuel", origin, message);
  }

  private static bool ContainsDirectSelfCall(INode root, string name) {
    foreach (var apply in FindApplySuffixes(root)) {
      if (IsSelfCall(apply, name)) {
        return true;
      }
    }
    return false;
  }

  private static IEnumerable<ApplySuffix> FindApplySuffixes(INode root) {
    var stack = new Stack<INode>();
    stack.Push(root);
    while (stack.Count != 0) {
      var node = stack.Pop();
      if (node is ApplySuffix apply) {
        yield return apply;
      }
      foreach (var child in node.PreResolveChildren) {
        if (child != null) {
          stack.Push(child);
        }
      }
    }
  }

  private static bool IsSelfCall(ApplySuffix apply, string name) {
    if (TryGetUnqualifiedName(apply.Lhs, out var calleeName) && calleeName == name) {
      return true;
    }
    if (TryGetThisQualifiedName(apply.Lhs, out calleeName) && calleeName == name) {
      return true;
    }
    return false;
  }

  private static bool TryGetUnqualifiedName(Expression lhs, out string name) {
    lhs = Expression.StripParens(lhs);
    if (lhs is NameSegment ns) {
      name = ns.Name;
      return true;
    }
    name = "";
    return false;
  }

  private static bool TryGetThisQualifiedName(Expression lhs, out string name) {
    lhs = Expression.StripParens(lhs);
    if (lhs is ExprDotName dot) {
      var receiver = Expression.StripParens(dot.Lhs);
      if (receiver is ThisExpr or ImplicitThisExpr) {
        name = dot.SuffixName;
        return true;
      }
    }
    name = "";
    return false;
  }

  private static void RewriteSelfCallsToFuel(INode root, string originalName, string fuelName, string fuelVarName) {
    foreach (var apply in FindApplySuffixes(root)) {
      if (!IsSelfCall(apply, originalName)) {
        continue;
      }

      // Update callee name in-place.
      var lhs = Expression.StripParens(apply.Lhs);
      if (lhs is NameSegment ns) {
        ns.Name = fuelName;
      } else if (lhs is ExprDotName dot) {
        dot.SuffixNameNode = new Name(dot.Origin, fuelName);
      } else {
        // Unexpected: leave as-is. This should not happen given IsSelfCall.
        continue;
      }

      // Add fuel-1 as a named actual argument (works for both positional and named argument calls).
      var fuelId = new IdentifierExpr(apply.Origin, fuelVarName);
      var fuelMinusOne = new BinaryExpr(apply.Origin, BinaryExpr.Opcode.Sub, fuelId, new LiteralExpr(apply.Origin, 1));
      apply.Bindings.ArgumentBindings.Add(new ActualBinding(MakeNameOrigin(apply.Origin, fuelVarName), fuelMinusOne));
    }
  }

  private static string FreshFuelFormalName(string baseName, IEnumerable<Formal> formals) {
    var used = new HashSet<string>(formals.Select(f => f.Name));
    if (!used.Contains(baseName)) {
      return baseName;
    }
    for (var i = 0; ; i++) {
      var candidate = baseName + i;
      if (!used.Contains(candidate)) {
        return candidate;
      }
    }
  }

  private static IOrigin MakeNameOrigin(IOrigin origin, string value) {
    if (origin is Token t) {
      return t.WithVal(value);
    }
    var token = new Token(origin.line, origin.col) {
      Uri = origin.Uri,
      val = value
    };
    return token;
  }

  private static Statement MakeFuelGuardForMethod(IOrigin origin, string fuelVarName, List<Formal> outs) {
    var fuelId = new IdentifierExpr(origin, fuelVarName);
    var test = new BinaryExpr(origin, BinaryExpr.Opcode.Lt, fuelId, new LiteralExpr(origin, 0));

    var thnBody = new List<Statement>();
    if (outs.Count != 0) {
      var lhss = outs.Select(o => (Expression)new IdentifierExpr(origin, o.Name)).ToList();
      var rhss = outs.Select(_ => (AssignmentRhs)new HavocRhs(origin)).ToList();
      thnBody.Add(new AssignStatement(origin, lhss, rhss));
    }
    thnBody.Add(new ReturnStmt(origin, null));
    var thn = new BlockStmt(origin, thnBody);
    return new IfStmt(origin, false, test, thn, null);
  }

  private static Expression MakeCallExpr(IOrigin origin, string callee, List<Expression> positionalArgs, Expression fuelArg) {
    var args = positionalArgs.Select(a => new ActualBinding(null, a)).ToList();
    args.Add(new ActualBinding(null, fuelArg));
    return new ApplySuffix(origin, null, new NameSegment(origin, callee, null), new ActualBindings(args), Token.NoToken);
  }

  private static Expression MakeCallExpr(IOrigin origin, string callee, List<Expression> positionalArgs) {
    var args = positionalArgs.Select(a => new ActualBinding(null, a)).ToList();
    return new ApplySuffix(origin, null, new NameSegment(origin, callee, null), new ActualBindings(args), Token.NoToken);
  }

  private static Function CreateOutOfFuelFunction(Function original, string outOfFuelName) {
    var origin = original.Origin.MakeAutoGenerated();
    var cloner = new Cloner();

    // Keep type parameters and input parameters, but drop contracts to keep verification cheap.
    var typeArgs = original.TypeArgs.ConvertAll(cloner.CloneTypeParam);
    var ins = original.Ins.ConvertAll(p => cloner.CloneFormal(p, false));

    var req = new List<AttributedExpression>();
    var ens = new List<AttributedExpression>();
    var reads = new Specification<FrameExpression>();
    var decreases = new Specification<Expression>();

    // Bodyless, extern, so it's allowed even when non-ghost.
    var attrs = new Attributes(origin, Attributes.ExternAttributeName, [], null);

    var outOfFuel = new Function(
      origin,
      new Name(origin, outOfFuelName),
      original.HasStaticKeyword,
      original.IsGhost,
      isOpaque: false,
      typeArgs,
      ins,
      result: null,
      resultType: cloner.CloneType(original.ResultType),
      req,
      reads,
      ens,
      decreases,
      body: null,
      byMethodTok: null,
      byMethodBody: null,
      attributes: attrs,
      signatureEllipsis: null
    );
    outOfFuel.InheritVisibility(original, false);
    return outOfFuel;
  }

  private static Statement MakeMethodCallStmt(IOrigin origin, string callee, List<Expression> positionalIns, List<Expression> positionalOuts, Expression fuelArg) {
    var args = positionalIns.Select(a => new ActualBinding(null, a)).ToList();
    args.Add(new ActualBinding(null, fuelArg));
    var apply = new ApplySuffix(origin, null, new NameSegment(origin, callee, null), new ActualBindings(args), Token.NoToken);
    var rhs = new ExprRhs(apply);
    var rhss = new List<AssignmentRhs> { rhs };
    return new AssignStatement(origin, positionalOuts, rhss);
  }
}


