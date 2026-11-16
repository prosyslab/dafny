#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

/// <summary>Compiler-resolved opacity and possible function-body exposure in a declaration's dependency closure.</summary>
public record DefinitionBodyVisibility(
  bool IsOpaque,
  IReadOnlyList<string> RevealedFunctions,
  bool RevealsAllFunctions,
  IReadOnlyList<string> ReferencedDeclarations
);

public static partial class DefinitionAnalysis {
  private sealed record DirectBodyVisibilityFacts(
    IReadOnlySet<INode> Dependencies,
    IReadOnlySet<string> RevealedFunctions,
    bool RevealsAllFunctions
  );

  private sealed class BodyVisibilityAnalysis(DafnyOptions options) {
    private readonly Dictionary<INode, DirectBodyVisibilityFacts> directFacts = new(ReferenceEqualityComparer.Instance);

    // Closures are memoized per strongly connected component of the declaration dependency graph.
    private Dictionary<INode, int>? indexOf;
    private string?[] names = [];
    private bool[] unnamed = [];
    private int[] sccOf = [];
    private readonly List<ulong[]> sccClosure = new();
    private readonly List<ulong[]> sccRevealed = new();
    private readonly List<bool> sccRevealsAll = new();
    private string[] revealedNames = [];

    private static bool Analyzable(INode declaration) {
      var module = declaration switch {
        MemberDecl member => member.EnclosingClass?.EnclosingModuleDefinition,
        TopLevelDecl topLevel => topLevel.EnclosingModuleDefinition,
        _ => null
      };
      return module is { SuccessfullyResolved: true };
    }

    private static string? NameOf(INode declaration) => declaration switch {
      MemberDecl member when member.EnclosingClass != null => member.FullDafnyName,
      TypeParameter => null,
      TopLevelDecl topLevel when topLevel.EnclosingModuleDefinition != null => topLevel.FullDafnyName,
      DatatypeCtor { EnclosingDatatype: { } datatype } => datatype.FullDafnyName,
      _ => null
    };

    /// <summary>Discover the dependency graph of all roots once and memoize one closure per component.</summary>
    public void Prepare(IEnumerable<INode> roots) {
      // Phase 1: every declaration reachable from an analyzable root.
      var discovered = new List<INode>();
      var seen = new HashSet<INode>(ReferenceEqualityComparer.Instance);
      var pending = new Stack<INode>();
      foreach (var root in roots.Where(Analyzable)) {
        pending.Push(root);
        while (pending.TryPop(out var current)) {
          if (!seen.Add(current)) {
            continue;
          }
          discovered.Add(current);
          foreach (var dependency in FactsFor(current).Dependencies) {
            pending.Push(dependency);
          }
        }
      }
      // Index declarations in ordinal name order, so a closure enumerates its names already sorted.
      var ordered = discovered.Select(node => (Node: node, Name: NameOf(node)))
        .OrderBy(item => item.Name, StringComparer.Ordinal).ToList();
      var count = ordered.Count;
      indexOf = new Dictionary<INode, int>(count, ReferenceEqualityComparer.Instance);
      names = new string?[count];
      unnamed = new bool[count];
      for (var i = 0; i < count; i++) {
        indexOf[ordered[i].Node] = i;
        names[i] = ordered[i].Name;
        unnamed[i] = ordered[i].Name == null && ordered[i].Node is not TypeParameter;
      }
      var facts = ordered.Select(item => FactsFor(item.Node)).ToArray();
      var adjacency = facts.Select(fact => fact.Dependencies.Select(dependency => indexOf[dependency]).ToArray()).ToArray();
      revealedNames = facts.SelectMany(fact => fact.RevealedFunctions).Distinct(StringComparer.Ordinal)
        .OrderBy(name => name, StringComparer.Ordinal).ToArray();
      var revealedIndex = new Dictionary<string, int>(StringComparer.Ordinal);
      for (var i = 0; i < revealedNames.Length; i++) {
        revealedIndex[revealedNames[i]] = i;
      }
      var words = (count + 63) / 64;
      var revealedWords = (revealedNames.Length + 63) / 64;

      // Phase 2: iterative Tarjan; components complete in reverse topological order.
      sccOf = Enumerable.Repeat(-1, count).ToArray();
      var order = Enumerable.Repeat(-1, count).ToArray();
      var low = new int[count];
      var onStack = new bool[count];
      var stack = new Stack<int>();
      var calls = new Stack<(int Node, int Next)>();
      var counter = 0;
      for (var start = 0; start < count; start++) {
        if (order[start] != -1) {
          continue;
        }
        calls.Push((start, 0));
        while (calls.TryPop(out var frame)) {
          var (node, next) = frame;
          if (next == 0) {
            order[node] = low[node] = counter++;
            stack.Push(node);
            onStack[node] = true;
          }
          var descended = false;
          for (var i = next; i < adjacency[node].Length; i++) {
            var target = adjacency[node][i];
            if (order[target] == -1) {
              calls.Push((node, i + 1));
              calls.Push((target, 0));
              descended = true;
              break;
            }
            if (onStack[target]) {
              low[node] = Math.Min(low[node], order[target]);
            }
          }
          if (descended) {
            continue;
          }
          if (low[node] == order[node]) {
            var component = sccClosure.Count;
            var members = new List<int>();
            int member;
            do {
              member = stack.Pop();
              onStack[member] = false;
              sccOf[member] = component;
              members.Add(member);
            } while (member != node);
            var closure = new ulong[words];
            var revealed = new ulong[revealedWords];
            var revealsAll = false;
            var merged = new HashSet<int>();
            foreach (var current in members) {
              closure[current >> 6] |= 1UL << (current & 63);
              revealsAll |= facts[current].RevealsAllFunctions;
              foreach (var name in facts[current].RevealedFunctions) {
                var bit = revealedIndex[name];
                revealed[bit >> 6] |= 1UL << (bit & 63);
              }
              foreach (var target in adjacency[current]) {
                var other = sccOf[target];
                if (other == component || !merged.Add(other)) {
                  continue;
                }
                var otherClosure = sccClosure[other];
                for (var w = 0; w < words; w++) {
                  closure[w] |= otherClosure[w];
                }
                var otherRevealed = sccRevealed[other];
                for (var w = 0; w < revealedWords; w++) {
                  revealed[w] |= otherRevealed[w];
                }
                revealsAll |= sccRevealsAll[other];
              }
            }
            sccClosure.Add(closure);
            sccRevealed.Add(revealed);
            sccRevealsAll.Add(revealsAll);
          }
          if (calls.TryPeek(out var parent)) {
            low[parent.Node] = Math.Min(low[parent.Node], low[node]);
          }
        }
      }
    }

    private DefinitionBodyVisibility FromClosure(INode declaration, int index) {
      var component = sccOf[index];
      var closure = sccClosure[component];
      var revealsAll = sccRevealsAll[component];
      var referenced = new List<string>();
      string? last = null;
      for (var w = 0; w < closure.Length; w++) {
        var word = closure[w];
        while (word != 0) {
          var bit = (w << 6) + BitOperations.TrailingZeroCount(word);
          word &= word - 1;
          if (bit == index) {
            continue;
          }
          if (names[bit] is { } name) {
            if (!string.Equals(name, last, StringComparison.Ordinal)) {
              referenced.Add(name);
              last = name;
            }
          } else if (unnamed[bit]) {
            revealsAll = true;
          }
        }
      }
      var revealed = new List<string>();
      var revealedBits = sccRevealed[component];
      for (var w = 0; w < revealedBits.Length; w++) {
        var word = revealedBits[w];
        while (word != 0) {
          revealed.Add(revealedNames[(w << 6) + BitOperations.TrailingZeroCount(word)]);
          word &= word - 1;
        }
      }
      return new DefinitionBodyVisibility(
        declaration is MemberDecl memberDeclaration && BoogieGenerator.IsOpaque(memberDeclaration, options),
        revealed, revealsAll, referenced);
    }

    public DefinitionBodyVisibility? For(INode declaration) {
      var module = declaration switch {
        MemberDecl member => member.EnclosingClass?.EnclosingModuleDefinition,
        TopLevelDecl topLevel => topLevel.EnclosingModuleDefinition,
        _ => null
      };
      if (module is not { SuccessfullyResolved: true }) {
        return null;
      }
      if (indexOf != null && indexOf.TryGetValue(declaration, out var prepared)) {
        return FromClosure(declaration, prepared);
      }
      var revealed = new HashSet<string>(StringComparer.Ordinal);
      var referenced = new HashSet<string>(StringComparer.Ordinal);
      var revealsAll = false;
      var visited = new HashSet<INode>(ReferenceEqualityComparer.Instance);
      var pending = new Stack<INode>();
      pending.Push(declaration);
      while (pending.TryPop(out var currentDeclaration)) {
        if (!visited.Add(currentDeclaration)) {
          continue;
        }
        var facts = FactsFor(currentDeclaration);
        if (!ReferenceEquals(currentDeclaration, declaration)) {
          var name = currentDeclaration switch {
            MemberDecl member when member.EnclosingClass != null => member.FullDafnyName,
            TypeParameter => null, // A bound type parameter is not a source declaration dependency.
            TopLevelDecl topLevel when topLevel.EnclosingModuleDefinition != null => topLevel.FullDafnyName,
            DatatypeCtor { EnclosingDatatype: { } datatype } => datatype.FullDafnyName,
            _ => null
          };
          if (name != null) {
            referenced.Add(name);
          } else if (currentDeclaration is not TypeParameter) {
            revealsAll = true;
          }
        }
        revealed.UnionWith(facts.RevealedFunctions);
        revealsAll |= facts.RevealsAllFunctions;
        foreach (var dependency in facts.Dependencies) {
          pending.Push(dependency);
        }
      }
      return new DefinitionBodyVisibility(
        declaration is MemberDecl memberDeclaration && BoogieGenerator.IsOpaque(memberDeclaration, options),
        revealed.OrderBy(name => name, StringComparer.Ordinal).ToList(),
        revealsAll,
        referenced.OrderBy(name => name, StringComparer.Ordinal).ToList());
    }

    private DirectBodyVisibilityFacts FactsFor(INode declaration) {
      if (directFacts.TryGetValue(declaration, out var cached)) {
        return cached;
      }
      var dependencies = new HashSet<INode>(ReferenceEqualityComparer.Instance);
      var revealed = new HashSet<string>(StringComparer.Ordinal);
      var revealsAll = false;
      var visited = new HashSet<INode>(ReferenceEqualityComparer.Instance);
      Visit(declaration);
      var facts = new DirectBodyVisibilityFacts(dependencies, revealed, revealsAll);
      directFacts.Add(declaration, facts);
      return facts;

      void Visit(INode node) {
        if (!visited.Add(node)) {
          return;
        }
        if (node is IAttributeBearingDeclaration attributed) {
          VisitAttributes(attributed.Attributes);
        }
        if (node is Statement statement) {
          VisitAttributes(statement.Attributes);
        }
        if (node is Expression expression) {
          // Instantiated generic types are resolved fields rather than Children;
          // their constraints can reference additional declarations and reveals.
          if (expression.Type != null) {
            Visit(expression.Type);
          }
          if (expression is ConcreteSyntaxExpression { ResolvedExpression: null }) {
            revealsAll = true;
          } else {
            foreach (var componentType in expression.ComponentTypes) {
              Visit(componentType);
            }
          }
        } else if (node is Type type && !ReferenceEquals(type.Normalize(), type)) {
          Visit(type.Normalize());
        }
        if (node is MemberDecl member) {
          VisitEnclosingAttributes(member.EnclosingClass);
          if (member.OverriddenMember != null) {
            dependencies.Add(member.OverriddenMember);
          }
        } else if (node is TopLevelDecl topLevel) {
          VisitModuleAttributes(topLevel.EnclosingModuleDefinition);
        }
        // Reveal rewriters synthesize intrinsic ArrowTypes without a declaration
        // identity; their argument/result types still carry all source edges.
        if (node is IHasReferences references && node is not ArrowType { ResolvedClass: null }) {
          foreach (var reference in references.GetReferences()) {
            if (reference.Referred is Declaration target) {
              dependencies.Add(target);
            } else if (reference.Referred == null) {
              revealsAll = true;
            }
          }
        }
        switch (node) {
          case Function currentFunction:
            // Function.Children exposes ensures expressions without their
            // attribute-bearing wrappers and similarly flattens specifications.
            foreach (var ensures in currentFunction.Ens) {
              Visit(ensures);
            }
            VisitAttributes(currentFunction.Reads.Attributes);
            VisitAttributes(currentFunction.Decreases.Attributes);
            break;
          case MethodOrConstructor currentMethod:
            VisitAttributes(currentMethod.Reads.Attributes);
            VisitAttributes(currentMethod.Mod.Attributes);
            break;
          case FunctionCallExpr { Function: { } function }:
            dependencies.Add(function);
            break;
          case CallStmt { Method: { } method }:
            dependencies.Add(method);
            break;
          case HideRevealStmt { Mode: HideRevealCmd.Modes.Reveal } reveal:
            if (reveal.Wildcard) {
              revealsAll = true;
            }
            foreach (var target in reveal.OffsetMembers) {
              if (target is Function targetFunction) {
                Reveal(targetFunction);
              } else if (target is ConstantField) {
                dependencies.Add(target);
              } else {
                revealsAll = true;
              }
            }
            // Auto-reveals contain resolved calls but no OffsetMembers. Their target
            // methods carry the resolved revealedFunction attribute inspected below.
            if (!reveal.Wildcard && (reveal.Exprs == null ||
                reveal.Exprs.Count > reveal.OffsetMembers.Count + reveal.LabeledAsserts.Count +
                reveal.ResolvedStatements.OfType<CallStmt>().Count(call =>
                  call.Method != null && Attributes.Contains(call.Method.Attributes, "revealedFunction")))) {
              revealsAll = true;
            }
            break;
        }
        // UserDefinedType's NamePath is retained syntax and may be unresolved;
        // its resolved reference plus instantiated TypeArgs carry the semantics.
        var children = node is UserDefinedType userType ? userType.TypeArgs : node.Children;
        foreach (var child in children) {
          // A referenced container contributes its own types/attributes, never all
          // sibling members. Referenced members are enqueued by resolved identity.
          if (child is not MemberDecl) {
            Visit(child);
          }
        }
      }

      void Reveal(Function function) {
        revealed.Add(function.FullDafnyName);
        dependencies.Add(function);
      }

      void VisitAttributes(Attributes? attributes) {
        foreach (var attribute in attributes.AsEnumerable()) {
          if (attribute.Name == "revealedFunction") {
            if (attribute.Args is [var target] && target.Resolved is MemberSelectExpr { Member: Function function }) {
              Reveal(function);
            } else {
              revealsAll = true;
            }
          } else if (attribute.Name == "fuel") {
            // Numeric declaration-local fuel does not identify another function.
            // A function-targeted setting can expose a body even without a reveal.
            if (attribute.Args.Count >= 2 && attribute.Args[0].Resolved is MemberSelectExpr { Member: Function function }) {
              Reveal(function);
            } else if (attribute.Args.Any(argument => argument.Resolved is not LiteralExpr { Value: BigInteger })) {
              revealsAll = true;
            }
          }
          Visit(attribute);
        }
      }

      void VisitEnclosingAttributes(TopLevelDecl? enclosing) {
        if (enclosing != null) {
          VisitAttributes(enclosing.Attributes);
          VisitModuleAttributes(enclosing.EnclosingModuleDefinition);
        }
      }

      void VisitModuleAttributes(ModuleDefinition? enclosing) {
        while (enclosing != null) {
          VisitAttributes(enclosing.Attributes);
          enclosing = enclosing.EnclosingModule;
        }
      }
    }
  }
}
