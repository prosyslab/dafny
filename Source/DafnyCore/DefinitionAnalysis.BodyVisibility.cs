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

    public DefinitionBodyVisibility? For(INode declaration) {
      var module = declaration switch {
        MemberDecl member => member.EnclosingClass?.EnclosingModuleDefinition,
        TopLevelDecl topLevel => topLevel.EnclosingModuleDefinition,
        _ => null
      };
      if (module is not { SuccessfullyResolved: true }) {
        return null;
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
