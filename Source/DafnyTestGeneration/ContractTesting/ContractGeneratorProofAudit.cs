#nullable enable

using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Records the source audit that permits one exact embedded RNG module inside a proof scope.</summary>
internal sealed class ContractGeneratorProofAudit {
  internal const string PolicyVersion = "pbt-direct-generator-proof-v4";
  internal const string PbtRandomModuleName = "PbtRandom";
  internal const string PbtRandomSourceSha256 = "f565ca5d86962c87a6b64f860fb7ba8450dbe5573f6980eb6b5751f577df8f72";

  private readonly Program program;
  private readonly string sourceSetHash;
  private readonly HashSet<Declaration> pinnedRandomDeclarations;

  public string? Failure { get; }
  public string PbtRandomSourceHash { get; }

  private ContractGeneratorProofAudit(Program program, string sourceSetHash,
    HashSet<Declaration> pinnedRandomDeclarations, string? failure, string randomSourceHash) {
    this.program = program;
    this.sourceSetHash = sourceSetHash;
    this.pinnedRandomDeclarations = pinnedRandomDeclarations;
    Failure = failure;
    PbtRandomSourceHash = randomSourceHash;
  }

  internal static string? AuditRawProgram(Program rawProgram, IReadOnlyList<ContractSource> sources,
    Uri generatorUri, string generatorName, string goalFullName, string randomModuleSource) {
    var randomHash = ContractHarnessBuilder.Hash(randomModuleSource);
    if (randomHash != PbtRandomSourceSha256) {
      return "The embedded PbtRandom source does not match the pinned proof library.";
    }
    var exactRandomSources = sources.Where(source => source.Content == randomModuleSource).ToList();
    if (exactRandomSources.Count != 1) {
      return "The pinned PbtRandom source must have exactly one canonical source snapshot.";
    }
    var randomUri = ContractSourceSnapshot.UriFor(exactRandomSources[0].Path);
    var declarations = RawNodes(rawProgram).ToList();
    var randomModules = declarations.OfType<ModuleDefinition>()
      .Where(module => module.Name == PbtRandomModuleName).ToList();
    if (randomModules.Count != 1 || randomModules[0].EnclosingModule is not DefaultModuleDefinition || randomModules[0].Origin.Uri != randomUri) {
      return "The only PbtRandom module must be the exact top-level module from the pinned runtime source.";
    }
    var pinnedRandomModule = randomModules[0];
    var randomUris = new HashSet<Uri> { randomUri };
    var pbtGeneratorCount = 0;
    foreach (var host in declarations.OfType<IAttributeBearingDeclaration>()) {
      var hostNode = host as INode;
      var isRandom = hostNode?.Origin.Uri != null && randomUris.Contains(hostNode.Origin.Uri);
      if (isRandom) { continue; }
      foreach (var attribute in host.Attributes.AsEnumerable()) {
        switch (attribute.Name) {
          case "trigger":
          case "fuel":
            break;
          case "pbt_draft":
            if (host is not MethodOrFunction || attribute.Args.Count != 1 || attribute.Args[0] is not LiteralExpr { Value: string }) {
              return "Malformed or misplaced pbt_draft attribute.";
            }
            break;
          case "pbt_generator":
            if (host is not Method method || method.Origin.Uri != generatorUri || method.Name != generatorName ||
                attribute.Args is not [LiteralExpr { Value: string symbol }] || symbol != goalFullName) {
              return "pbt_generator is permitted only on the exact selected generator for this goal.";
            }
            if (method.Req.Count != 0) {
              return "The selected Generate method must not have authored requires clauses.";
            }
            pbtGeneratorCount++;
            break;
          default:
            return "Unsupported or trust-affecting source attribute: {:" + attribute.Name + "}.";
        }
      }
    }
    if (pbtGeneratorCount != 1) {
      return "The raw source must contain exactly one matching pbt_generator marker.";
    }

    foreach (var module in declarations.OfType<ModuleDefinition>()) {
      if (ReferenceEquals(module, pinnedRandomModule)) { continue; }
      if (module.IsFacade || module.Implements != null || module.ModuleKind != ModuleKindEnum.Concrete) {
        return "Abstract, refining, replaceable or facade modules are outside the bounded proof scope.";
      }
    }
    foreach (var alias in declarations.OfType<AliasModuleDecl>()) {
      if (alias.TargetQId.ToString() != PbtRandomModuleName) {
        return "Only the exact embedded PbtRandom import is supported.";
      }
    }
    if (declarations.OfType<ModuleExportDecl>().Any()) {
      return "Module exports and facade views are outside the bounded proof scope.";
    }
    if (declarations.OfType<LetExpr>().Any(let => !let.Exact)) {
      return "Let-such-that creates retained Skolem axioms and is outside the bounded proof scope.";
    }
    foreach (var topLevel in declarations.OfType<TopLevelDecl>().Where(topLevel => topLevel is not TypeParameter)) {
      if (topLevel.Origin.Uri != null && randomUris.Contains(topLevel.Origin.Uri)) { continue; }
      if (topLevel.IsRefining) {
        return "Refining declarations are outside the bounded proof scope: " + topLevel.Name;
      }
      var supported = topLevel switch {
        DefaultClassDecl => true,
        LiteralModuleDecl => true,
        AliasModuleDecl => true,
        IteratorDecl or TraitDecl or CoDatatypeDecl or AbstractTypeDecl => false,
        ClassDecl classDecl => classDecl.Traits.Count == 0,
        IndDatatypeDecl => true,
        SubsetTypeDecl => true,
        NewtypeDecl newtype => newtype.BaseType != null,
        TypeSynonymDecl synonym => synonym.Rhs != null,
        _ => false
      };
      if (!supported) {
        return "Unsupported top-level declaration in retained source theory: " + topLevel.GetType().Name + " " + topLevel.Name;
      }
    }
    foreach (var member in declarations.OfType<MemberDecl>()) {
      if (member.Origin.Uri != null && randomUris.Contains(member.Origin.Uri)) { continue; }
      if (member.IsRefining || member switch {
        Field or Constructor => false,
        TwoStateFunction or ExtremePredicate or PrefixPredicate or TwoStateLemma or ExtremeLemma or PrefixLemma => true,
        Method or Function => false,
        _ => true
      }) {
        return "Unsupported or refining member in retained source theory: " + member.GetType().Name + " " + member.Name;
      }
    }
    foreach (var callable in declarations.OfType<MethodOrFunction>()) {
      if (callable.Origin.Uri != null && randomUris.Contains(callable.Origin.Uri)) { continue; }
      if (callable is Function { Body: null }) {
        return "Bodyless logical function is outside the bounded proof scope: " + callable.Name;
      }
      if (callable is Function { AllowsNontermination: true } function) {
        return "Logical function or predicate with decreases * is outside the bounded proof scope: " + function.Name;
      }
    }
    foreach (var constant in declarations.OfType<ConstantField>()) {
      if (constant.Origin.Uri != null && randomUris.Contains(constant.Origin.Uri)) { continue; }
      if (constant.Rhs == null) {
        return "Abstract or bodyless constant is outside the bounded proof scope: " + constant.Name;
      }
    }
    return null;
  }

  // Concrete-syntax expressions expose their original children before resolution, not their resolved Children.
  private static IEnumerable<INode> RawNodes(INode root) {
    var seen = new HashSet<INode>(ReferenceEqualityComparer.Instance);
    var pending = new Stack<INode>();
    pending.Push(root);
    while (pending.TryPop(out var node)) {
      if (!seen.Add(node)) { continue; }
      yield return node;
      foreach (var child in node.PreResolveChildren) { pending.Push(child); }
    }
  }

  internal static ContractGeneratorProofAudit BindResolved(Program program, IReadOnlyList<ContractSource> sources,
    string? rawFailure, string randomModuleSource) {
    var randomHash = ContractHarnessBuilder.Hash(randomModuleSource);
    var failure = rawFailure;
    if (randomHash != PbtRandomSourceSha256) {
      failure ??= "The embedded PbtRandom source does not match the pinned proof library.";
    }
    var randomModules = program.RawModules().Where(module => module.Name == PbtRandomModuleName).ToList();
    if (randomModules.Count != 1) {
      failure ??= "The proof source must contain exactly one PbtRandom module.";
    }
    var pinned = new HashSet<Declaration>();
    if (randomModules.Count == 1) {
      var randomModule = randomModules[0];
      var source = sources.SingleOrDefault(candidate => ContractSourceSnapshot.UriFor(candidate.Path) == randomModule.Origin.Uri);
      if (source == null || source.Content != randomModuleSource) {
        failure ??= "PbtRandom must come from the exact extracted embedded runtime resource.";
      }
      foreach (var topLevel in randomModule.TopLevelDecls) {
        pinned.Add(topLevel);
        if (topLevel is TopLevelDeclWithMembers withMembers) {
          foreach (var member in withMembers.Members) { pinned.Add(member); }
          if (topLevel is ClassDecl { NonNullTypeDecl: { } nonNullType }) { pinned.Add(nonNullType); }
        }
      }
    }
    return new(program, ContractRuntimeTypeEvidence.SourceSetHash(sources), pinned, failure, randomHash);
  }

  internal bool IsBoundTo(Program candidate, IReadOnlyList<ContractSource> sources) =>
    ReferenceEquals(program, candidate) && sourceSetHash == ContractRuntimeTypeEvidence.SourceSetHash(sources);

  internal bool IsPinnedRngDeclaration(Declaration declaration) => pinnedRandomDeclarations.Contains(declaration);
}
