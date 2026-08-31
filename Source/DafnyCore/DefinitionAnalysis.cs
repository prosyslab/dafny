#nullable enable
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;

namespace Microsoft.Dafny;

public record DefinitionAnalysisResult(
  string Name,
  string FullName,
  string Kind,
  string EnclosingName,
  int Line,
  int Column,
  int Start,
  int? BodyStart,
  int End,
  string SourcePath,
  bool Ghost,
  bool HasByMethod,
  bool HasLoop,
  bool WorldRelated,
  string DeclarationKind,
  bool HasAxiomAttribute,
  bool HasExternAttribute,
  bool HasVerifyFalseAttribute,
  IReadOnlyList<DefinitionAttribute> Attributes,
  bool HasAssumeStatement,
  bool HasVarDeclaration,
  IReadOnlyList<DefinitionStatement> Statements,
  IReadOnlyList<DefinitionMemberAssignment> MemberAssignments,
  IReadOnlyList<DefinitionCallSite> CallSites,
  IReadOnlyList<DefinitionContractClause> ContractClauses,
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
  IReadOnlyList<string> Returns,
  IReadOnlyList<string> ReturnNames,
  IReadOnlyList<string> Requires,
  IReadOnlyList<string> Ensures,
  IReadOnlyList<string> Modifies,
  IReadOnlyList<DefinitionFormal> ParameterDetails,
  IReadOnlyList<DefinitionFormal> ReturnDetails,
  IReadOnlyList<string> Reads,
  IReadOnlyList<string> Decreases,
  IReadOnlyList<string> SourceModules,
  IReadOnlyList<string> IncludedFiles,
  IReadOnlyList<string> LocalIncludedModules,
  IReadOnlyList<string> ImportedModules,
  IReadOnlyList<DefinitionAnalysisInclude> LocalIncludes,
  bool Recursive,
  IReadOnlyList<string> RecursiveGroup,
  IReadOnlyList<string> Callees,
  IReadOnlyList<string> CallSequence,
  IReadOnlyList<string> CallNames,
  IReadOnlyList<string> DirectPreconditionCallees,
  IReadOnlyList<DefinitionPreconditionCall> DirectPreconditionCalls,
  IReadOnlyList<string> DirectPostconditionCallees,
  IReadOnlyList<DefinitionPostconditionCall> DirectPostconditionCalls,
  string ContractHeaderWithoutAxiom,
  string ContractHeaderWithAxiom,
  IReadOnlyList<DefinitionReference> References,
  IReadOnlyList<string> Dependencies
);

public record DefinitionAnalysisDocument(
  IReadOnlyList<DefinitionAnalysisResult> Definitions,
  DefinitionSourceFacts SourceFacts
);

public record DefinitionSourceFacts(
  IReadOnlyList<DefinitionAnalysisModule> Modules,
  IReadOnlyList<DefinitionAnalysisImport> Imports,
  IReadOnlyList<DefinitionAnalysisInclude> Includes
);

public record DefinitionAnalysisModule(
  string Name,
  string SourcePath,
  int BodyStart,
  int BodyEnd
);

public record DefinitionAnalysisImport(
  string ModuleName,
  string Alias,
  string ResolvedTarget,
  bool HasAlias,
  string ResolvedTargetSourcePath,
  bool Opened,
  string SourcePath,
  int Start,
  int End
);

public record DefinitionFormal(
  string Name,
  string Type,
  bool Ghost
);

public record DefinitionAttribute(
  string Name,
  IReadOnlyList<string> Arguments,
  int Start,
  int End
);

public record DefinitionStatement(
  string Kind,
  int Start,
  int End,
  IReadOnlyList<string> DirectCallTargets
);

public record DefinitionControlContext(
  string Kind,
  int Start,
  int End,
  int BranchIndex,
  int BranchCount,
  int OtherBranchStatementCount,
  string Guard,
  IReadOnlyList<string> Invariants,
  IReadOnlyList<string> Decreases
);

public record DefinitionCallSite(
  string TargetFullName,
  int Start,
  int End,
  IReadOnlyList<string> Arguments,
  IReadOnlyList<string> AssignedNames,
  IReadOnlyList<DefinitionControlContext> ControlPath
);

public record DefinitionContractClause(
  string Kind,
  int Index,
  string Text,
  bool HasExistential,
  bool HasOld,
  IReadOnlyList<string> ReferencedVariables,
  IReadOnlyList<string> ReferencedMembers,
  IReadOnlyList<string> IndexSelections,
  int IndexSelectionCount
);

public record DefinitionMemberAssignment(
  int Start,
  int End,
  string TargetFullName,
  string ReceiverType,
  bool TargetIsGhost
);

public record DefinitionPostconditionCall(
  string TargetFullName,
  int Start,
  int End,
  string Text,
  IReadOnlyList<string?> Arguments
);

public record DefinitionPreconditionCall(
  string TargetFullName,
  int Start,
  int End,
  string Text,
  IReadOnlyList<string?> Arguments
);

public record DefinitionReference(
  string TargetFullName,
  string TargetModule,
  string TargetKind,
  bool IsPattern,
  int Start,
  int End
);

public record DefinitionAnalysisInclude(
  string SourcePath,
  string TargetPath,
  int Start,
  int End
);

public static class DefinitionAnalysis {
  internal static IReadOnlyList<DefinitionAttribute> AttributesFor(INode declaration) {
    if (declaration is not IAttributeBearingDeclaration attributeBearing) {
      return Array.Empty<DefinitionAttribute>();
    }
    return attributeBearing.Attributes.AsEnumerable()
      .OfType<UserSuppliedAttributes>()
      .Where(attribute => attribute.OpenBrace.IsValid && attribute.CloseBrace.IsValid)
      .Select(attribute => new DefinitionAttribute(
        attribute.Name,
        attribute.Args.Select(argument => argument.EntireRange.PrintOriginal()).ToList(),
        attribute.OpenBrace.pos,
        attribute.CloseBrace.pos + attribute.CloseBrace.val.Length))
      .OrderBy(attribute => attribute.Start)
      .ToList();
  }

  public static IReadOnlyList<DefinitionAnalysisResult> Analyze(
    Program program,
    IReadOnlySet<Uri> analysisSourceUris,
    bool includeStatements = false) {
    var sourceFacts = SourceFacts.For(program, analysisSourceUris);
    return Analyze(program, sourceFacts, analysisSourceUris, includeStatements);
  }

  public static DefinitionAnalysisDocument AnalyzeDocument(
    Program program,
    IReadOnlySet<Uri> analysisSourceUris,
    bool includeStatements = false) {
    var (sourceFacts, programFacts) = SourceFacts.ForDocument(program, analysisSourceUris);
    return new DefinitionAnalysisDocument(
      Analyze(program, sourceFacts, analysisSourceUris, includeStatements),
      programFacts);
  }

  private static IReadOnlyList<DefinitionAnalysisResult> Analyze(
    Program program,
    SourceFacts sourceFacts,
    IReadOnlySet<Uri> analysisSourceUris,
    bool includeStatements = false) {
    var allDeclarations = SourceDefinitions(
      program,
      spansOnly: false,
      analysisSourceUris: analysisSourceUris);
    var declarations = allDeclarations
      .Where(declaration => analysisSourceUris.Contains(declaration.Declaration.StartToken.Uri))
      .ToList();
    var callableDeclarations = allDeclarations
      .Where(declaration => declaration.BodyKind is
        DefinitionBodyKind.Function or
        DefinitionBodyKind.FunctionByMethod or
        DefinitionBodyKind.Method)
      .ToList();
    var callTargetIndex = CallTargetIndex.For(callableDeclarations);
    var callableAnalysisDeclarations = declarations
      .Where(declaration => declaration.BodyKind is
        DefinitionBodyKind.Function or
        DefinitionBodyKind.FunctionByMethod or
        DefinitionBodyKind.Method)
      .ToList();
    var callFacts = callableAnalysisDeclarations.ToDictionary(
      declaration => declaration,
      declaration => CalledDefinitions(declaration, callTargetIndex));
    var graph = callFacts.ToDictionary(
      item => item.Key,
      item => item.Value.UniqueCallees);
    var recursionGraph = graph.ToDictionary(
      item => item.Key,
      item => item.Value.Where(callFacts.ContainsKey).ToHashSet());
    var declarationNodes = allDeclarations
      .Where(declaration => declaration.BodyKind != DefinitionBodyKind.FunctionByMethod)
      .ToDictionary(declaration => declaration.Declaration);
    var resolvedDeclarationFacts = ResolvedDeclarationFacts.For(declarations, declarationNodes);
    var recursionFacts = AnalyzeRecursion(recursionGraph);

    var results = declarations
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        sourceFacts,
        recursionFacts,
        graph,
        callFacts,
        declarationNodes,
        resolvedDeclarationFacts,
        includeStatements))
      .ToList();
    return results;
  }

  public static IReadOnlyList<DefinitionAnalysisResult> AnalyzeSpans(
    Program program,
    IReadOnlySet<Uri> analysisSourceUris) {
    var sourceFacts = SourceFacts.For(program, analysisSourceUris);
    var results = SourceDefinitions(program, spansOnly: true, analysisSourceUris: analysisSourceUris)
      .Where(declaration => analysisSourceUris.Contains(declaration.Declaration.StartToken.Uri))
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultForSpans(declaration, sourceFacts))
      .ToList();
    return results;
  }

  private static DefinitionAnalysisResult ResultFor(
    DefinitionNode declaration,
    SourceFacts sourceFacts,
    RecursionFacts recursionFacts,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph,
    IReadOnlyDictionary<DefinitionNode, CallFacts> callFacts,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    ResolvedDeclarationFacts resolvedDeclarationFacts,
    bool includeStatements) {
    return CreateResult(
      declaration,
      sourceFacts,
      recursionFacts.RecursiveDeclarations.Contains(declaration),
      recursionFacts.GroupNames.TryGetValue(declaration, out var groupNames)
        ? groupNames
        : Array.Empty<string>(),
      graph.TryGetValue(declaration, out var callees)
        ? callees.Select(item => item.ReportFullName).OrderBy(name => name, StringComparer.Ordinal).ToList()
        : Array.Empty<string>(),
      callFacts.TryGetValue(declaration, out var calls)
        ? calls.Sequence.Select(item => item.ReportFullName).ToList()
        : Array.Empty<string>(),
      resolvedDeclarationFacts.DirectPreconditionCalleesFor(declaration.Declaration),
      resolvedDeclarationFacts.DirectPreconditionCallsFor(declaration.Declaration),
      resolvedDeclarationFacts.DirectPostconditionCalleesFor(declaration.Declaration),
      resolvedDeclarationFacts.DirectPostconditionCallsFor(declaration.Declaration),
      includeStatements ? declaration.Statements : Array.Empty<DefinitionStatement>(),
      declaration.MemberAssignments,
      declaration.CallSites,
      ContractClausesFor(declaration.Declaration),
      resolvedDeclarationFacts.ReferencesFor(declaration.Declaration),
      DependenciesFor(declaration, graph, declarationNodes));
  }

  private static DefinitionAnalysisResult ResultForSpans(
    DefinitionNode declaration,
    SourceFacts sourceFacts) {
    return CreateResult(
      declaration,
      sourceFacts,
      false,
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<string>(),
      Array.Empty<DefinitionPreconditionCall>(),
      Array.Empty<string>(),
      Array.Empty<DefinitionPostconditionCall>(),
      Array.Empty<DefinitionStatement>(),
      Array.Empty<DefinitionMemberAssignment>(),
      Array.Empty<DefinitionCallSite>(),
      Array.Empty<DefinitionContractClause>(),
      Array.Empty<DefinitionReference>(),
      Array.Empty<string>());
  }

  private static DefinitionAnalysisResult CreateResult(
    DefinitionNode declaration,
    SourceFacts sourceFacts,
    bool recursive,
    IReadOnlyList<string> recursiveGroup,
    IReadOnlyList<string> callees,
    IReadOnlyList<string> callSequence,
    IReadOnlyList<string> directPreconditionCallees,
    IReadOnlyList<DefinitionPreconditionCall> directPreconditionCalls,
    IReadOnlyList<string> directPostconditionCallees,
    IReadOnlyList<DefinitionPostconditionCall> directPostconditionCalls,
    IReadOnlyList<DefinitionStatement> statements,
    IReadOnlyList<DefinitionMemberAssignment> memberAssignments,
    IReadOnlyList<DefinitionCallSite> callSites,
    IReadOnlyList<DefinitionContractClause> contractClauses,
    IReadOnlyList<DefinitionReference> references,
    IReadOnlyList<string> dependencies) {
    return new DefinitionAnalysisResult(
      declaration.Name,
      declaration.ReportFullName,
      declaration.Kind,
      declaration.EnclosingName,
      declaration.Line,
      declaration.Column,
      declaration.Start,
      declaration.BodyStart,
      declaration.End,
      declaration.SourcePath,
      declaration.Ghost,
      declaration.HasByMethod,
      declaration.HasLoop,
      declaration.WorldRelated,
      declaration.DeclarationKind,
      declaration.HasAxiomAttribute,
      declaration.HasExternAttribute,
      declaration.HasVerifyFalseAttribute,
      declaration.DeclarationAttributes,
      declaration.HasAssumeStatement,
      declaration.HasVarDeclaration,
      statements,
      memberAssignments,
      callSites,
      contractClauses,
      declaration.BodyShape,
      declaration.HasBroadExitRangeDisjunct,
      declaration.TypeParameters,
      declaration.TypeParameterNames,
      declaration.Parameters,
      declaration.ParameterNames,
      declaration.Returns,
      declaration.ReturnNames,
      declaration.Requires,
      declaration.Ensures,
      declaration.Modifies,
      declaration.ParameterDetails,
      declaration.ReturnDetails,
      declaration.Reads,
      declaration.Decreases,
      sourceFacts.SourceModules,
      sourceFacts.IncludedFiles,
      sourceFacts.LocalIncludedModulesFor(declaration.SourcePath),
      sourceFacts.ImportedModulesFor(declaration.SourcePath),
      sourceFacts.LocalIncludesFor(declaration.SourcePath),
      recursive,
      recursiveGroup,
      callees,
      callSequence,
      declaration.CallNames,
      directPreconditionCallees,
      directPreconditionCalls,
      directPostconditionCallees,
      directPostconditionCalls,
      declaration.ContractHeaderWithoutAxiom,
      declaration.ContractHeaderWithAxiom,
      references,
      dependencies);
  }

  private static IReadOnlyList<DefinitionContractClause> ContractClausesFor(INode declaration) {
    var clauses = new List<DefinitionContractClause>();
    switch (declaration) {
      case Function function:
        AddClauses("requires", function.Req.Select(item => item.E));
        AddClauses("ensures", function.Ens.Select(item => item.E));
        break;
      case MethodOrConstructor method:
        AddClauses("requires", method.Req.Select(item => item.E));
        AddClauses("ensures", method.Ens.Select(item => item.E));
        break;
    }
    return clauses;

    void AddClauses(string kind, IEnumerable<Expression> expressions) {
      foreach (var expression in expressions) {
        var referencedVariables = new HashSet<string>(StringComparer.Ordinal);
        var referencedMembers = new HashSet<string>(StringComparer.Ordinal);
        var indexSelections = new HashSet<string>(StringComparer.Ordinal);
        var hasExistential = false;
        var hasOld = false;
        var indexSelectionCount = 0;
        Visit(expression);
        clauses.Add(new DefinitionContractClause(
          kind,
          clauses.Count(item => item.Kind == kind),
          expression.EntireRange.PrintOriginal(),
          hasExistential,
          hasOld,
          referencedVariables.OrderBy(item => item, StringComparer.Ordinal).ToList(),
          referencedMembers.OrderBy(item => item, StringComparer.Ordinal).ToList(),
          indexSelections.OrderBy(item => item, StringComparer.Ordinal).ToList(),
          indexSelectionCount));

        void Visit(Expression current) {
          hasExistential |= current is ExistsExpr;
          hasOld |= current is OldExpr;
          if (current is SeqSelectExpr or MultiSelectExpr) {
            indexSelectionCount++;
            indexSelections.Add(current.EntireRange.PrintOriginal());
          }
          if (current is IdentifierExpr identifier) {
            referencedVariables.Add(identifier.Name);
          }
          if (current is MemberSelectExpr { Member: { } member }) {
            referencedMembers.Add(member.FullDafnyName);
          }
          foreach (var child in current.SubExpressions) {
            Visit(child);
          }
        }
      }
    }
  }

  private sealed class ResolvedDeclarationFacts {
    private readonly IReadOnlyDictionary<INode, IReadOnlyList<DefinitionReference>> references;
    private readonly IReadOnlyDictionary<INode, IReadOnlyList<DefinitionPreconditionCall>> directPreconditionCalls;
    private readonly IReadOnlyDictionary<INode, IReadOnlyList<DefinitionPostconditionCall>> directPostconditionCalls;

    private ResolvedDeclarationFacts(
      IReadOnlyDictionary<INode, IReadOnlyList<DefinitionReference>> references,
      IReadOnlyDictionary<INode, IReadOnlyList<DefinitionPreconditionCall>> directPreconditionCalls,
      IReadOnlyDictionary<INode, IReadOnlyList<DefinitionPostconditionCall>> directPostconditionCalls) {
      this.references = references;
      this.directPreconditionCalls = directPreconditionCalls;
      this.directPostconditionCalls = directPostconditionCalls;
    }

    public static ResolvedDeclarationFacts For(
      IReadOnlyList<DefinitionNode> declarations,
      IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
      var uniqueDeclarations = declarations
        .Where(declaration => declaration.BodyKind != DefinitionBodyKind.FunctionByMethod)
        .ToList();
      return new ResolvedDeclarationFacts(
        uniqueDeclarations.ToDictionary(
          declaration => declaration.Declaration,
          declaration => (IReadOnlyList<DefinitionReference>)DefinitionAnalysis.ReferencesFor(
            declaration,
            declarationNodes)),
        uniqueDeclarations.ToDictionary(
          declaration => declaration.Declaration,
          declaration => (IReadOnlyList<DefinitionPreconditionCall>)DefinitionAnalysis.DirectPreconditionCallsFor(
            declaration,
            declarationNodes)),
        uniqueDeclarations.ToDictionary(
          declaration => declaration.Declaration,
          declaration => (IReadOnlyList<DefinitionPostconditionCall>)DefinitionAnalysis.DirectPostconditionCallsFor(
            declaration,
            declarationNodes)));
    }

    public IReadOnlyList<DefinitionReference> ReferencesFor(INode declaration) {
      return references[declaration];
    }

    public IReadOnlyList<string> DirectPreconditionCalleesFor(INode declaration) {
      return directPreconditionCalls[declaration]
        .Select(call => call.TargetFullName)
        .ToList();
    }

    public IReadOnlyList<DefinitionPreconditionCall> DirectPreconditionCallsFor(INode declaration) {
      return directPreconditionCalls[declaration];
    }

    public IReadOnlyList<string> DirectPostconditionCalleesFor(INode declaration) {
      return directPostconditionCalls[declaration]
        .Select(call => call.TargetFullName)
        .ToList();
    }

    public IReadOnlyList<DefinitionPostconditionCall> DirectPostconditionCallsFor(INode declaration) {
      return directPostconditionCalls[declaration];
    }
  }

  private static List<DefinitionPreconditionCall> DirectPreconditionCallsFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    if (declaration.Declaration is not MethodOrFunction methodOrFunction) {
      return [];
    }
    return FunctionCallsIn(methodOrFunction.Req.Select(requires => requires.E))
      .Where(call => call.Function != null && declarationNodes.ContainsKey(call.Function))
      .Select(call => new DefinitionPreconditionCall(
        declarationNodes[call.Function].ReportFullName,
        call.StartToken.pos,
        call.EndToken.pos + call.EndToken.val.Length,
        call.EntireRange.PrintOriginal(),
        call.Args.Select(argument => DirectSpecificationArgument(argument, methodOrFunction)).ToList()))
      .ToList();
  }

  private static List<DefinitionReference> ReferencesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    var references = new List<DefinitionReference>();
    ((Node)declaration.Declaration).Visit(node => {
      if (node is not IHasReferences hasReferences) {
        return true;
      }
      foreach (var reference in hasReferences.GetReferences()) {
        var result = ReferenceFor(
          reference,
          declarationNodes,
          node is MatchCase or IdPattern);
        if (result != null && result.Start >= declaration.Start && result.End <= declaration.End) {
          references.Add(result);
        }
      }
      return true;
    });
    return references
      .Distinct()
      .OrderBy(reference => reference.Start)
      .ThenBy(reference => reference.End)
      .ThenBy(reference => reference.TargetFullName, StringComparer.Ordinal)
      .ToList();
  }

  private static DefinitionReference? ReferenceFor(
    Reference reference,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    bool isPattern) {
    var start = reference.Referer.StartToken.pos;
    var end = reference.Referer.EndToken.pos + reference.Referer.EndToken.val.Length;
    if (declarationNodes.TryGetValue(reference.Referred, out var target)) {
      var suffix = $".{target.Name}";
      var targetModule = target.ReportFullName.EndsWith(suffix, StringComparison.Ordinal)
        ? target.ReportFullName[..^suffix.Length]
        : target.EnclosingName;
      return new DefinitionReference(
        target.ReportFullName,
        targetModule,
        target.Kind,
        isPattern,
        start,
        end);
    }
    if (reference.Referred is DatatypeCtor { EnclosingDatatype: { } datatype } constructor) {
      return new DefinitionReference(
        $"{datatype.FullDafnyName}.{constructor.Name}",
        datatype.EnclosingModuleDefinition.FullDafnyName,
        "constructor",
        isPattern,
        start,
        end);
    }
    return null;
  }

  private static List<DefinitionPostconditionCall> DirectPostconditionCallsFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    if (declaration.Declaration is not MethodOrFunction methodOrFunction) {
      return [];
    }
    return FunctionCallsIn(methodOrFunction.Ens.Select(ensures => ensures.E))
      .Where(call => call.Function != null && declarationNodes.ContainsKey(call.Function))
      .Select(call => new DefinitionPostconditionCall(
        declarationNodes[call.Function].ReportFullName,
        call.StartToken.pos,
        call.EndToken.pos + call.EndToken.val.Length,
        call.EntireRange.PrintOriginal(),
        call.Args.Select(argument => DirectSpecificationArgument(argument, methodOrFunction)).ToList()))
      .ToList();
  }

  private static IEnumerable<FunctionCallExpr> FunctionCallsIn(IEnumerable<Expression> roots) {
    foreach (var root in roots) {
      var pending = new Stack<Expression>();
      pending.Push(root);
      while (pending.Count > 0) {
        var expression = UnwrapExpression(pending.Pop()).Resolved;
        if (expression is FunctionCallExpr call) {
          yield return call;
        }
        foreach (var subExpression in expression.SubExpressions.Reverse()) {
          pending.Push(subExpression);
        }
      }
    }
  }

  private static string? DirectSpecificationArgument(Expression argument, MethodOrFunction declaration) {
    var resolved = UnwrapExpression(argument).Resolved;
    if (resolved is not IdentifierExpr { Var: Formal formal }) {
      return null;
    }
    if (declaration.Ins.Contains(formal)) {
      return formal.Name;
    }
    if (declaration is MethodOrConstructor method && method.Outs.Contains(formal)) {
      return formal.Name;
    }
    return declaration is Function function && ReferenceEquals(function.Result, formal)
      ? formal.Name
      : null;
  }

  private static List<string> DependenciesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    var dependencies = graph.TryGetValue(declaration, out var callees)
      ? callees.Where(node => node.BodyKind != DefinitionBodyKind.FunctionByMethod).ToHashSet()
      : new HashSet<DefinitionNode>();
    foreach (var type in declaration.Types) {
      CollectTypeDependencies(type, declarationNodes, dependencies);
    }
    return dependencies
      .Where(node => node != declaration)
      .Select(node => node.ReportFullName)
      .Distinct()
      .OrderBy(name => name, StringComparer.Ordinal)
      .ToList();
  }

  private static void CollectTypeDependencies(
    Type type,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    ISet<DefinitionNode> dependencies) {
    if (type is UserDefinedType { ResolvedClass: { } resolvedClass } &&
        declarationNodes.TryGetValue(resolvedClass, out var dependency)) {
      dependencies.Add(dependency);
    }
    foreach (var typeArgument in type.TypeArgs) {
      CollectTypeDependencies(typeArgument, declarationNodes, dependencies);
    }
  }

  internal static string SourcePath(INode declaration) {
    var filename = declaration.StartToken.ActualFilename;
    return filename == null ? "" : Path.GetFullPath(filename);
  }

  private static List<DefinitionNode> SourceDefinitions(
    Program program,
    bool spansOnly,
    IReadOnlySet<Uri> analysisSourceUris) {
    var declarations = new List<DefinitionNode>();
    var modules = spansOnly ? ParsedModules(program) : program.Modules();
    foreach (var moduleDefinition in modules) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        var topLevelIsTarget = analysisSourceUris.Contains(topLevelDecl.StartToken.Uri);
        if (topLevelDecl is DatatypeDecl datatypeDecl && (!spansOnly || topLevelIsTarget)) {
          var purpose = NodePurpose(spansOnly, topLevelIsTarget);
          declarations.Add(DefinitionNode.ForDatatype(datatypeDecl, moduleDefinition.Name, purpose));
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var member in topLevelDeclWithMembers.Members.OrderBy(member => member.Origin.pos)) {
          if (AutoGeneratedOrigin.Is(member.Origin)) {
            continue;
          }
          var memberIsTarget = analysisSourceUris.Contains(member.StartToken.Uri);
          if (spansOnly && !memberIsTarget) {
            continue;
          }

          var purpose = NodePurpose(spansOnly, memberIsTarget);
          if (member is Function function) {
            declarations.Add(DefinitionNode.ForFunction(function, moduleDefinition.Name, purpose));
            if (!spansOnly && function.ByMethodBody != null) {
              declarations.Add(DefinitionNode.ForFunctionByMethod(function, moduleDefinition.Name, purpose));
            }
          } else if (member is MethodOrConstructor method && method is not Method { IsByMethod: true }) {
            declarations.Add(DefinitionNode.ForMethod(method, moduleDefinition.Name, purpose));
          } else if (member is ConstantField constant && constant.EnclosingClass is DefaultClassDecl) {
            declarations.Add(DefinitionNode.ForConstant(constant, moduleDefinition.Name, purpose));
          }
        }
      }
    }

    return declarations;

    static DefinitionNodePurpose NodePurpose(
      bool spansOnly,
      bool isTarget) {
      if (spansOnly) {
        return DefinitionNodePurpose.Spans;
      }
      return isTarget ? DefinitionNodePurpose.ResolvedRoot : DefinitionNodePurpose.ResolvedInclude;
    }
  }

  internal static IEnumerable<ModuleDefinition> ParsedModules(Program program) {
    var seen = new HashSet<ModuleDefinition>();
    foreach (var module in Visit(program.DefaultModuleDef)) {
      yield return module;
    }

    IEnumerable<ModuleDefinition> Visit(ModuleDefinition module) {
      if (!seen.Add(module)) {
        yield break;
      }
      yield return module;
      foreach (var nested in module.TopLevelDecls.OfType<LiteralModuleDecl>()) {
        foreach (var nestedModule in Visit(nested.ModuleDef)) {
          yield return nestedModule;
        }
      }
    }
  }

  private sealed record CallTargetIndex(
    IReadOnlyDictionary<Function, DefinitionNode> FunctionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> ByMethodNodes,
    IReadOnlyDictionary<MethodOrConstructor, DefinitionNode> MethodNodes
  ) {
    public static CallTargetIndex For(IReadOnlyList<DefinitionNode> declarations) {
      var functionNodes = new Dictionary<Function, DefinitionNode>();
      var byMethodNodes = new Dictionary<Function, DefinitionNode>();
      var methodNodes = new Dictionary<MethodOrConstructor, DefinitionNode>();
      foreach (var declaration in declarations) {
        switch (declaration.BodyKind) {
          case DefinitionBodyKind.Function:
            functionNodes.Add((Function)declaration.Declaration, declaration);
            break;
          case DefinitionBodyKind.FunctionByMethod:
            byMethodNodes.Add((Function)declaration.Declaration, declaration);
            break;
          case DefinitionBodyKind.Method:
            methodNodes.Add((MethodOrConstructor)declaration.Declaration, declaration);
            break;
          default:
            throw new InvalidOperationException($"Unexpected callable body kind: {declaration.BodyKind}");
        }
      }
      return new CallTargetIndex(functionNodes, byMethodNodes, methodNodes);
    }
  }

  private sealed record CallFacts(
    IReadOnlyList<DefinitionNode> Sequence,
    HashSet<DefinitionNode> UniqueCallees
  );

  private static CallFacts CalledDefinitions(
    DefinitionNode declaration,
    CallTargetIndex callTargetIndex) {
    var sequence = new List<DefinitionNode>();
    var uniqueCallees = new HashSet<DefinitionNode>();

    foreach (var expression in declaration.SpecificationExpressions) {
      CollectExpressionCalls(
        expression,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        sequence,
        uniqueCallees);
    }

    if (declaration.ExpressionBody != null) {
      CollectExpressionCalls(
        declaration.ExpressionBody,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        sequence,
        uniqueCallees);
    }

    if (declaration.StatementBody != null) {
      CollectStatementCalls(
        declaration.StatementBody,
        callTargetIndex.FunctionNodes,
        callTargetIndex.ByMethodNodes,
        callTargetIndex.MethodNodes,
        sequence,
        uniqueCallees);
    }

    return new CallFacts(sequence, uniqueCallees);
  }

  private static void CollectExpressionCalls(
    Expression expression,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    List<DefinitionNode> sequence,
    HashSet<DefinitionNode> uniqueCallees) {
    if (expression is FunctionCallExpr { Function: { } function } functionCall) {
      var nodes = functionCall.IsByMethodCall ? byMethodNodes : functionNodes;
      if (nodes.TryGetValue(function, out var target)) {
        sequence.Add(target);
        uniqueCallees.Add(target);
      }
    }

    foreach (var subExpression in expression.SubExpressions) {
      CollectExpressionCalls(subExpression, functionNodes, byMethodNodes, sequence, uniqueCallees);
    }
  }

  private static void CollectStatementCalls(
    Statement statement,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    IReadOnlyDictionary<MethodOrConstructor, DefinitionNode> methodNodes,
    List<DefinitionNode> sequence,
    HashSet<DefinitionNode> uniqueCallees) {
    if (statement is CallStmt callStmt && methodNodes.TryGetValue(callStmt.Method, out var methodTarget)) {
      sequence.Add(methodTarget);
      uniqueCallees.Add(methodTarget);
    }

    foreach (var expression in statement.SubExpressions) {
      CollectExpressionCalls(expression, functionNodes, byMethodNodes, sequence, uniqueCallees);
    }

    foreach (var subStatement in statement.SubStatements) {
      CollectStatementCalls(subStatement, functionNodes, byMethodNodes, methodNodes, sequence, uniqueCallees);
    }
  }

  internal static bool ContainsLoop(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is LoopStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsLoop);
  }

  internal static bool ContainsAssume(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is AssumeStmt or ExpectStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsAssume);
  }

  internal static bool ContainsVarDeclaration(Statement? statement) {
    if (statement == null) {
      return false;
    }
    if (statement is VarDeclStmt) {
      return true;
    }
    return statement.SubStatements.Any(ContainsVarDeclaration);
  }

  internal static string BodyShape(Expression? expression) {
    if (expression is SeqDisplayExpr { Elements.Count: 0 }) {
      return "empty-seq";
    }
    if (expression is LiteralExpr { Value: bool boolValue }) {
      return boolValue ? "true" : "false";
    }
    if (expression is LiteralExpr { Value: BigInteger integerValue } && integerValue == BigInteger.Zero) {
      return "zero";
    }
    if (expression is StringLiteralExpr { Value: string stringValue } && stringValue.Length == 0) {
      return "empty-string";
    }
    return "";
  }

  internal static bool ContainsBroadExitRangeDisjunct(Expression? expression) {
    if (expression == null) {
      return false;
    }
    if (IsBroadExitRangeDisjunct(expression)) {
      return true;
    }
    return expression.SubExpressions.Any(ContainsBroadExitRangeDisjunct);
  }

  internal static bool IsBroadExitRangeDisjunct(Expression expression) {
    expression = UnwrapExpression(expression);
    return IsExitRange(expression) ||
           expression is BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr &&
           (IsExitRange(binaryExpr.E0) || IsExitRange(binaryExpr.E1));
  }

  internal static bool StatementContainsBroadExitRangeDisjunct(Statement? statement) {
    if (statement == null) {
      return false;
    }
    return statement.SubExpressions.Any(ContainsBroadExitRangeDisjunct) ||
           statement.SubStatements.Any(StatementContainsBroadExitRangeDisjunct);
  }

  private static bool IsExitRange(Expression expression) {
    expression = UnwrapExpression(expression);
    if (expression is ChainingExpression chainingExpression) {
      for (var index = 0; index + 2 < chainingExpression.Operators.Count; index += 1) {
        if (chainingExpression.Operators[index] == BinaryExpr.Opcode.Eq &&
            chainingExpression.Operators[index + 1] == BinaryExpr.Opcode.Or &&
            chainingExpression.Operators[index + 2] == BinaryExpr.Opcode.Eq &&
            ((IsExitEquals(chainingExpression.Operands[index], chainingExpression.Operands[index + 1], 0) &&
              IsExitEquals(chainingExpression.Operands[index + 2], chainingExpression.Operands[index + 3], 1)) ||
             (IsExitEquals(chainingExpression.Operands[index], chainingExpression.Operands[index + 1], 1) &&
              IsExitEquals(chainingExpression.Operands[index + 2], chainingExpression.Operands[index + 3], 0)))) {
          return true;
        }
      }
      return IsExitRange(chainingExpression.E);
    }
    return expression is BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr &&
           ((IsExitEquals(binaryExpr.E0, 0) && IsExitEquals(binaryExpr.E1, 1)) ||
            (IsExitEquals(binaryExpr.E0, 1) && IsExitEquals(binaryExpr.E1, 0)));
  }

  private static bool IsExitEquals(Expression expression, int value) {
    expression = UnwrapExpression(expression);
    if (expression is ChainingExpression { Operators.Count: 1 } chainingExpression &&
        chainingExpression.Operators[0] == BinaryExpr.Opcode.Eq) {
      return (IsExitIdentifier(chainingExpression.Operands[0]) &&
              IsIntegerLiteral(chainingExpression.Operands[1], value)) ||
             (IsExitIdentifier(chainingExpression.Operands[1]) &&
              IsIntegerLiteral(chainingExpression.Operands[0], value));
    }
    if (expression is not BinaryExpr { Op: BinaryExpr.Opcode.Eq } binaryExpr) {
      return false;
    }
    return (IsExitIdentifier(binaryExpr.E0) && IsIntegerLiteral(binaryExpr.E1, value)) ||
           (IsExitIdentifier(binaryExpr.E1) && IsIntegerLiteral(binaryExpr.E0, value));
  }

  private static bool IsExitEquals(Expression left, Expression right, int value) {
    return (IsExitIdentifier(left) && IsIntegerLiteral(right, value)) ||
           (IsExitIdentifier(right) && IsIntegerLiteral(left, value));
  }

  private static bool IsExitIdentifier(Expression expression) {
    expression = UnwrapExpression(expression);
    return expression is IdentifierExpr { Name: "exit" } or NameSegment { Name: "exit" };
  }

  private static bool IsIntegerLiteral(Expression expression, int value) {
    expression = UnwrapExpression(expression);
    return expression is LiteralExpr { Value: BigInteger integerValue } &&
           integerValue == new BigInteger(value);
  }

  internal static Expression UnwrapExpression(Expression expression) {
    while (expression is ParensExpression parensExpression) {
      expression = parensExpression.E;
    }
    return expression;
  }

  internal static bool WorldRelated(MethodOrFunction declaration) {
    return declaration is Function { WhatKind: "predicate" } &&
           declaration.EntireRange.PrintOriginal().Contains("World");
  }

  private sealed record RecursionFacts(
    IReadOnlySet<DefinitionNode> RecursiveDeclarations,
    IReadOnlyDictionary<DefinitionNode, IReadOnlyList<string>> GroupNames
  );

  private static RecursionFacts AnalyzeRecursion(
    Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var recursiveDeclarations = new HashSet<DefinitionNode>();
    var groupNames = new Dictionary<DefinitionNode, IReadOnlyList<string>>();
    foreach (var component in StronglyConnectedComponents(graph)) {
      var first = component.First();
      if (component.Count == 1 && !graph[first].Contains(first)) {
        continue;
      }

      var names = component
        .Select(item => item.ReportFullName)
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToArray();
      foreach (var item in component) {
        recursiveDeclarations.Add(item);
        groupNames.Add(item, names);
      }
    }

    return new RecursionFacts(recursiveDeclarations, groupNames);
  }

  private static List<HashSet<DefinitionNode>> StronglyConnectedComponents(
    Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var index = 0;
    var stack = new Stack<DefinitionNode>();
    var onStack = new HashSet<DefinitionNode>();
    var indexes = new Dictionary<DefinitionNode, int>();
    var lowlinks = new Dictionary<DefinitionNode, int>();
    var components = new List<HashSet<DefinitionNode>>();

    foreach (var node in graph.Keys) {
      if (!indexes.ContainsKey(node)) {
        Visit(node);
      }
    }

    return components;

    void Visit(DefinitionNode node) {
      indexes[node] = index;
      lowlinks[node] = index;
      index += 1;
      stack.Push(node);
      onStack.Add(node);

      foreach (var target in graph[node]) {
        if (!indexes.ContainsKey(target)) {
          Visit(target);
          lowlinks[node] = System.Math.Min(lowlinks[node], lowlinks[target]);
        } else if (onStack.Contains(target)) {
          lowlinks[node] = System.Math.Min(lowlinks[node], indexes[target]);
        }
      }

      if (lowlinks[node] != indexes[node]) {
        return;
      }

      var component = new HashSet<DefinitionNode>();
      while (true) {
        var item = stack.Pop();
        onStack.Remove(item);
        component.Add(item);
        if (ReferenceEquals(item, node)) {
          break;
        }
      }

      components.Add(component);
    }
  }
}

internal sealed record SourceFacts(
  IReadOnlyList<string> SourceModules,
  IReadOnlyList<string> IncludedFiles,
  IReadOnlyList<string> LocalIncludedModules,
  IReadOnlyList<string> ImportedModules,
  IReadOnlyList<DefinitionAnalysisInclude> LocalIncludes,
  DefinitionSourceFacts Structured
) {
  public static SourceFacts For(Program program, IReadOnlySet<Uri> analysisSourceUris) {
    var parsedModules = DefinitionAnalysis.ParsedModules(program).ToList();
    var wiring = ProgramSourceFacts(program, parsedModules);
    return LegacySourceFacts(program, parsedModules, analysisSourceUris, wiring);
  }

  public static (SourceFacts Legacy, DefinitionSourceFacts Program) ForDocument(
    Program program,
    IReadOnlySet<Uri> analysisSourceUris) {
    var parsedModules = DefinitionAnalysis.ParsedModules(program).ToList();
    var wiring = ProgramSourceFacts(program, parsedModules);
    var output = ProgramSourceFacts(program, parsedModules, analysisSourceUris);
    return (
      LegacySourceFacts(program, parsedModules, analysisSourceUris, wiring),
      output);
  }

  private static SourceFacts LegacySourceFacts(
    Program program,
    IReadOnlyList<ModuleDefinition> parsedModules,
    IReadOnlySet<Uri> analysisSourceUris,
    DefinitionSourceFacts wiring) {
    var rootModules = parsedModules
      .Where(module => !module.IsDefaultModule && analysisSourceUris.Contains(module.StartToken.Uri))
      .ToList();

    var rootIncludes = program.Compilation.Includes
      .Where(include => analysisSourceUris.Contains(include.IncluderFilename))
      .ToList();

    return new SourceFacts(
      rootModules.Select(module => module.Name).Distinct().OrderBy(name => name, StringComparer.Ordinal).ToList(),
      rootIncludes.Select(include => Path.GetFileName(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      rootIncludes.Where(IsSameDirectoryDafnyInclude)
        .Select(include => Path.GetFileNameWithoutExtension(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      parsedModules
        .Where(module => analysisSourceUris.Contains(module.StartToken.Uri))
        .SelectMany(module => ImportedModuleNames(program, module))
        .Distinct()
        .OrderBy(name => name, StringComparer.Ordinal)
        .ToList(),
      rootIncludes
        .Where(include => Path.GetExtension(include.IncludedFilename.LocalPath) == ".dfy")
        .Select(include => new DefinitionAnalysisInclude(
          Path.GetFullPath(include.IncluderFilename.LocalPath),
          Path.GetFullPath(include.IncludedFilename.LocalPath),
          include.StartToken.pos,
          include.EndToken.pos + include.EndToken.val.Length))
        .OrderBy(include => include.SourcePath)
        .ThenBy(include => include.Start)
        .ToList(),
      wiring);
  }

  public IReadOnlyList<string> LocalIncludedModulesFor(string sourcePath) {
    var targetPaths = Structured.Includes
      .Where(include => SamePath(include.SourcePath, sourcePath))
      .Select(include => Path.GetFullPath(include.TargetPath))
      .ToHashSet(StringComparer.Ordinal);
    return Structured.Modules
      .Where(module => targetPaths.Contains(Path.GetFullPath(module.SourcePath)))
      .Select(module => module.Name)
      .Distinct()
      .OrderBy(name => name, StringComparer.Ordinal)
      .ToList();
  }

  public IReadOnlyList<string> ImportedModulesFor(string sourcePath) {
    return Structured.Imports
      .Where(importItem => SamePath(importItem.SourcePath, sourcePath))
      .Select(importItem => importItem.ResolvedTarget)
      .Distinct()
      .OrderBy(name => name, StringComparer.Ordinal)
      .ToList();
  }

  public IReadOnlyList<DefinitionAnalysisInclude> LocalIncludesFor(string sourcePath) {
    return Structured.Includes
      .Where(include => SamePath(include.SourcePath, sourcePath))
      .ToList();
  }

  private static bool SamePath(string left, string right) {
    return string.Equals(
      Path.GetFullPath(left),
      Path.GetFullPath(right),
      StringComparison.Ordinal);
  }

  private static DefinitionSourceFacts ProgramSourceFacts(
    Program program,
    IReadOnlyList<ModuleDefinition> parsedModules,
    IReadOnlySet<Uri>? analysisSourceUris = null) {
    var modules = parsedModules
      .Where(module =>
        !module.IsDefaultModule &&
        module.BodyStartTok != Token.NoToken &&
        (analysisSourceUris == null || analysisSourceUris.Contains(module.StartToken.Uri)))
      .Select(module => new DefinitionAnalysisModule(
        module.FullDafnyName,
        DefinitionAnalysis.SourcePath(module),
        module.BodyStartTok.pos,
        module.EndToken.pos))
      .Where(module => module.SourcePath.Length > 0)
      .OrderBy(module => module.SourcePath, StringComparer.Ordinal)
      .ThenBy(module => module.BodyStart)
      .ThenBy(module => module.Name, StringComparer.Ordinal)
      .ToList();
    var imports = parsedModules
      .Where(module => !module.IsDefaultModule)
      .SelectMany(module => module.TopLevelDecls
        .OfType<ModuleDecl>()
        .Where(moduleDecl =>
          analysisSourceUris == null || analysisSourceUris.Contains(moduleDecl.StartToken.Uri))
        .Select(moduleDecl => StructuredImport(module, moduleDecl)))
      .Where(importItem => importItem != null)
      .Cast<DefinitionAnalysisImport>()
      .OrderBy(importItem => importItem.SourcePath, StringComparer.Ordinal)
      .ThenBy(importItem => importItem.Start)
      .ThenBy(importItem => importItem.Alias, StringComparer.Ordinal)
      .ToList();
    var includes = program.Compilation.Includes
      .Where(include =>
        Path.GetExtension(include.IncludedFilename.LocalPath) == ".dfy" &&
        (analysisSourceUris == null || analysisSourceUris.Contains(include.IncluderFilename)))
      .Select(include => new DefinitionAnalysisInclude(
        Path.GetFullPath(include.IncluderFilename.LocalPath),
        Path.GetFullPath(include.IncludedFilename.LocalPath),
        include.StartToken.pos,
        include.EndToken.pos + include.EndToken.val.Length))
      .Distinct()
      .OrderBy(include => include.SourcePath, StringComparer.Ordinal)
      .ThenBy(include => include.Start)
      .ThenBy(include => include.TargetPath, StringComparer.Ordinal)
      .ToList();
    return new DefinitionSourceFacts(modules, imports, includes);
  }

  private static DefinitionAnalysisImport? StructuredImport(
    ModuleDefinition module,
    ModuleDecl moduleDecl) {
    var targetModule = moduleDecl switch {
      AliasModuleDecl alias => alias.Signature?.ModuleDef,
      AbstractModuleDecl abstractModule => abstractModule.OriginalSignature?.ModuleDef,
      _ => null,
    };
    var target = moduleDecl switch {
      AliasModuleDecl alias => targetModule?.FullDafnyName ?? alias.TargetQId.ToString(),
      AbstractModuleDecl abstractModule => targetModule?.FullDafnyName ?? abstractModule.QId.ToString(),
      _ => null,
    };
    var sourcePath = DefinitionAnalysis.SourcePath(moduleDecl);
    if (target == null || sourcePath.Length == 0) {
      return null;
    }
    return new DefinitionAnalysisImport(
      module.FullDafnyName,
      moduleDecl.Name,
      target,
      moduleDecl is not AliasModuleDecl aliasModule || aliasModule.HasAlias,
      targetModule == null ? "" : DefinitionAnalysis.SourcePath(targetModule),
      moduleDecl.Opened,
      sourcePath,
      moduleDecl.StartToken.pos,
      moduleDecl.EndToken.pos + moduleDecl.EndToken.val.Length);
  }

  private static bool IsSameDirectoryDafnyInclude(Include include) {
    if (Path.GetExtension(include.IncludedFilename.LocalPath) != ".dfy") {
      return false;
    }
    return Path.GetDirectoryName(include.IncluderFilename.LocalPath) ==
           Path.GetDirectoryName(include.IncludedFilename.LocalPath);
  }

  private static IEnumerable<string> ImportedModuleNames(Program program, ModuleDefinition module) {
    foreach (var moduleDecl in module.TopLevelDecls.OfType<ModuleDecl>()) {
      if (moduleDecl.Origin.FromIncludeDirective(program)) {
        continue;
      }

      foreach (var importedName in ImportedModuleNames(moduleDecl)) {
        if (importedName.Length > 0) {
          yield return importedName;
        }
      }
    }
  }

  private static IEnumerable<string> ImportedModuleNames(ModuleDecl moduleDecl) {
    if (moduleDecl is AliasModuleDecl alias) {
      foreach (var name in ModuleQualifiedNames(alias.TargetQId)) {
        yield return name;
      }
      if (alias.Signature?.ModuleDef != null) {
        yield return alias.Signature.ModuleDef.Name;
      }
    } else if (moduleDecl is AbstractModuleDecl abstractModule) {
      foreach (var name in ModuleQualifiedNames(abstractModule.QId)) {
        yield return name;
      }
      if (abstractModule.OriginalSignature?.ModuleDef != null) {
        yield return abstractModule.OriginalSignature.ModuleDef.Name;
      }
    }
  }

  private static IEnumerable<string> ModuleQualifiedNames(ModuleQualifiedId qualifiedId) {
    yield return qualifiedId.ToString();
    yield return qualifiedId.Path.Last().Value;
  }
}

internal enum DefinitionBodyKind {
  Function,
  FunctionByMethod,
  Method,
  Datatype,
  Constant
}

internal enum DefinitionNodePurpose {
  ResolvedRoot,
  ResolvedInclude,
  Spans
}

internal sealed record DefinitionReportFacts(
  int Line,
  int Column,
  int Start,
  int? BodyStart,
  int End,
  string SourcePath,
  bool Ghost,
  bool HasByMethod,
  bool HasLoop,
  bool WorldRelated,
  string DeclarationKind,
  bool HasAxiomAttribute,
  bool HasExternAttribute,
  bool HasVerifyFalseAttribute,
  bool HasAssumeStatement,
  bool HasVarDeclaration,
  IReadOnlyList<DefinitionStatement> Statements,
  IReadOnlyList<DefinitionMemberAssignment> MemberAssignments,
  IReadOnlyList<DefinitionCallSite> CallSites,
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
  IReadOnlyList<string> Returns,
  IReadOnlyList<string> ReturnNames,
  IReadOnlyList<string> Requires,
  IReadOnlyList<string> Ensures,
  IReadOnlyList<string> Modifies,
  DefinitionStructuredFacts Structured,
  IReadOnlyList<string> CallNames,
  IReadOnlyList<Type> Types
);

internal sealed record DefinitionStructuredFacts(
  IReadOnlyList<DefinitionFormal> ParameterDetails,
  IReadOnlyList<DefinitionFormal> ReturnDetails,
  IReadOnlyList<string> Reads,
  IReadOnlyList<string> Decreases,
  string ContractHeaderWithoutAxiom,
  string ContractHeaderWithAxiom
) {
  public static readonly DefinitionStructuredFacts Empty = new(
    Array.Empty<DefinitionFormal>(),
    Array.Empty<DefinitionFormal>(),
    Array.Empty<string>(),
    Array.Empty<string>(),
    "",
    "");
}

internal sealed class DefinitionNode(
  INode declaration,
  DefinitionBodyKind bodyKind,
  string name,
  string reportFullName,
  string kind,
  string enclosingName,
  IReadOnlyList<Expression> specificationExpressions,
  Expression? expressionBody,
  Statement? statementBody,
  DefinitionReportFacts? reportFacts
) {
  public INode Declaration { get; } = declaration;
  public DefinitionBodyKind BodyKind { get; } = bodyKind;
  public string Name { get; } = name;
  public string ReportFullName { get; } = reportFullName;
  public string Kind { get; } = kind;
  public string EnclosingName { get; } = enclosingName;
  public IReadOnlyList<Expression> SpecificationExpressions { get; } = specificationExpressions;
  public Expression? ExpressionBody { get; } = expressionBody;
  public Statement? StatementBody { get; } = statementBody;
  public DefinitionReportFacts? ReportFacts { get; } = reportFacts;

  public int Line => ReportFacts!.Line;
  public int Column => ReportFacts!.Column;
  public int Start => ReportFacts!.Start;
  public int? BodyStart => ReportFacts!.BodyStart;
  public int End => ReportFacts!.End;
  public string SourcePath => ReportFacts!.SourcePath;
  public bool Ghost => ReportFacts!.Ghost;
  public bool HasByMethod => ReportFacts!.HasByMethod;
  public bool HasLoop => ReportFacts!.HasLoop;
  public bool WorldRelated => ReportFacts!.WorldRelated;
  public string DeclarationKind => ReportFacts!.DeclarationKind;
  public bool HasAxiomAttribute => ReportFacts!.HasAxiomAttribute;
  public bool HasExternAttribute => ReportFacts!.HasExternAttribute;
  public bool HasVerifyFalseAttribute => ReportFacts!.HasVerifyFalseAttribute;
  public IReadOnlyList<DefinitionAttribute> DeclarationAttributes =>
    DefinitionAnalysis.AttributesFor(Declaration);
  public bool HasAssumeStatement => ReportFacts!.HasAssumeStatement;
  public bool HasVarDeclaration => ReportFacts!.HasVarDeclaration;
  public IReadOnlyList<DefinitionStatement> Statements => ReportFacts!.Statements;
  public IReadOnlyList<DefinitionMemberAssignment> MemberAssignments => ReportFacts!.MemberAssignments;
  public IReadOnlyList<DefinitionCallSite> CallSites => ReportFacts!.CallSites;
  public string BodyShape => ReportFacts!.BodyShape;
  public bool HasBroadExitRangeDisjunct => ReportFacts!.HasBroadExitRangeDisjunct;
  public IReadOnlyList<string> TypeParameters => ReportFacts!.TypeParameters;
  public IReadOnlyList<string> TypeParameterNames => ReportFacts!.TypeParameterNames;
  public IReadOnlyList<string> Parameters => ReportFacts!.Parameters;
  public IReadOnlyList<string> ParameterNames => ReportFacts!.ParameterNames;
  public IReadOnlyList<string> Returns => ReportFacts!.Returns;
  public IReadOnlyList<string> ReturnNames => ReportFacts!.ReturnNames;
  public IReadOnlyList<string> Requires => ReportFacts!.Requires;
  public IReadOnlyList<string> Ensures => ReportFacts!.Ensures;
  public IReadOnlyList<string> Modifies => ReportFacts!.Modifies;
  public IReadOnlyList<DefinitionFormal> ParameterDetails => ReportFacts!.Structured.ParameterDetails;
  public IReadOnlyList<DefinitionFormal> ReturnDetails => ReportFacts!.Structured.ReturnDetails;
  public IReadOnlyList<string> Reads => ReportFacts!.Structured.Reads;
  public IReadOnlyList<string> Decreases => ReportFacts!.Structured.Decreases;
  public string ContractHeaderWithoutAxiom => ReportFacts!.Structured.ContractHeaderWithoutAxiom;
  public string ContractHeaderWithAxiom => ReportFacts!.Structured.ContractHeaderWithAxiom;
  public IReadOnlyList<string> CallNames => ReportFacts!.CallNames;
  public IReadOnlyList<Type> Types => ReportFacts!.Types;

  public static DefinitionNode ForFunction(
    Function function,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    var specificationExpressions = SpecificationExpressionsFor(function);
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeExpressionBody(function.Body);
      reportFacts = new DefinitionReportFacts(
        function.Origin.line,
        function.Origin.col,
        function.StartToken.pos,
        BodyStartOffset(function),
        EndOffset(function),
        DefinitionAnalysis.SourcePath(function),
        function.IsGhost,
        function.ByMethodBody != null,
        false,
        DefinitionAnalysis.WorldRelated(function),
        function.WhatKind,
        function.HasAxiomAttribute,
        function.HasExternAttribute,
        function.HasVerifyFalseAttribute,
        false,
        false,
        Array.Empty<DefinitionStatement>(),
        Array.Empty<DefinitionMemberAssignment>(),
        bodyAnalysis.CallSites,
        DefinitionAnalysis.BodyShape(function.Body),
        specificationExpressions.Any(DefinitionAnalysis.ContainsBroadExitRangeDisjunct) ||
          bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(function.TypeArgs),
        TypeParameterNameTexts(function.TypeArgs),
        ParameterTexts(function),
        ParameterNameTexts(function),
        Array.Empty<string>(),
        Array.Empty<string>(),
        function.Req.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        function.Ens.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        Array.Empty<string>(),
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? StructuredFacts(function, function.Result == null ? [] : [function.Result])
          : DefinitionStructuredFacts.Empty,
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. function.Ins.Select(formal => formal.Type), function.ResultType]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      function,
      DefinitionBodyKind.Function,
      function.Name,
      FullName(function, enclosingName),
      function.WhatKind,
      enclosingName,
      purpose == DefinitionNodePurpose.Spans ? Array.Empty<Expression>() : specificationExpressions,
      purpose == DefinitionNodePurpose.Spans ? null : function.Body,
      null,
      reportFacts);
  }

  public static DefinitionNode ForFunctionByMethod(
    Function function,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeStatementBody(function.ByMethodBody);
      reportFacts = new DefinitionReportFacts(
        function.Origin.line,
        function.Origin.col,
        function.StartToken.pos,
        function.ByMethodBody?.StartToken.pos,
        EndOffset(function),
        DefinitionAnalysis.SourcePath(function),
        function.IsGhost,
        true,
        bodyAnalysis.HasLoop,
        false,
        "by-method",
        function.HasAxiomAttribute,
        function.HasExternAttribute,
        function.HasVerifyFalseAttribute,
        bodyAnalysis.HasAssumeStatement,
        bodyAnalysis.HasVarDeclaration,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionStatement>()
          : bodyAnalysis.Statements,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionMemberAssignment>()
          : bodyAnalysis.MemberAssignments,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionCallSite>()
          : bodyAnalysis.CallSites,
        "",
        bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(function.TypeArgs),
        TypeParameterNameTexts(function.TypeArgs),
        ParameterTexts(function),
        ParameterNameTexts(function),
        Array.Empty<string>(),
        Array.Empty<string>(),
        function.Req.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        function.Ens.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        Array.Empty<string>(),
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? StructuredFacts(function, function.Result == null ? [] : [function.Result])
          : DefinitionStructuredFacts.Empty,
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. function.Ins.Select(formal => formal.Type), function.ResultType]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      function,
      DefinitionBodyKind.FunctionByMethod,
      function.Name,
      FullName(function, enclosingName) + "#by-method",
      "function-by-method",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      purpose == DefinitionNodePurpose.Spans ? null : function.ByMethodBody,
      reportFacts);
  }

  public static DefinitionNode ForMethod(
    MethodOrConstructor method,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    var specificationExpressions = SpecificationExpressionsFor(method);
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeStatementBody(method.Body);
      reportFacts = new DefinitionReportFacts(
        method.Origin.line,
        method.Origin.col,
        method.StartToken.pos,
        BodyStartOffset(method),
        EndOffset(method),
        DefinitionAnalysis.SourcePath(method),
        method.IsGhost,
        false,
        bodyAnalysis.HasLoop,
        false,
        method.WhatKind,
        method.HasAxiomAttribute,
        method.HasExternAttribute,
        method.HasVerifyFalseAttribute,
        bodyAnalysis.HasAssumeStatement,
        bodyAnalysis.HasVarDeclaration,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionStatement>()
          : bodyAnalysis.Statements,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionMemberAssignment>()
          : bodyAnalysis.MemberAssignments,
        purpose == DefinitionNodePurpose.Spans
          ? Array.Empty<DefinitionCallSite>()
          : bodyAnalysis.CallSites,
        "",
        specificationExpressions.Any(DefinitionAnalysis.ContainsBroadExitRangeDisjunct) ||
          bodyAnalysis.HasBroadExitRangeDisjunct,
        TypeParameterTexts(method.TypeArgs),
        TypeParameterNameTexts(method.TypeArgs),
        ParameterTexts(method),
        ParameterNameTexts(method),
        method.Outs.Select(formal => $"{formal.Name}: {formal.Type}").ToList(),
        method.Outs.Select(formal => formal.Name).ToList(),
        method.Req.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        method.Ens.Select(item => item.E.EntireRange.PrintOriginal()).ToList(),
        method.Mod?.Expressions?.Select(item => item.EntireRange.PrintOriginal()).ToList() ?? [],
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? StructuredFacts(method, method.Outs)
          : DefinitionStructuredFacts.Empty,
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. method.Ins.Select(formal => formal.Type), .. method.Outs.Select(formal => formal.Type)]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      method,
      DefinitionBodyKind.Method,
      method.Name,
      FullName(method, enclosingName),
      method is Constructor ? "constructor" : "method",
      enclosingName,
      purpose == DefinitionNodePurpose.Spans ? Array.Empty<Expression>() : specificationExpressions,
      null,
      purpose == DefinitionNodePurpose.Spans ? null : method.Body,
      reportFacts);
  }

  public static DefinitionNode ForDatatype(
    DatatypeDecl datatype,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      reportFacts = new DefinitionReportFacts(
        datatype.Origin.line,
        datatype.Origin.col,
        datatype.StartToken.pos,
        null,
        EndOffset(datatype),
        DefinitionAnalysis.SourcePath(datatype),
        false,
        false,
        false,
        false,
        "datatype",
        datatype.HasAxiomAttribute,
        datatype.HasExternAttribute,
        datatype.HasVerifyFalseAttribute,
        false,
        false,
        Array.Empty<DefinitionStatement>(),
        Array.Empty<DefinitionMemberAssignment>(),
        Array.Empty<DefinitionCallSite>(),
        "",
        false,
        TypeParameterTexts(datatype.TypeArgs),
        TypeParameterNameTexts(datatype.TypeArgs),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        DefinitionStructuredFacts.Empty,
        Array.Empty<string>(),
        purpose == DefinitionNodePurpose.ResolvedRoot
          ? [.. datatype.Ctors.SelectMany(constructor => constructor.Formals).Select(formal => formal.Type)]
          : Array.Empty<Type>());
    }
    return new DefinitionNode(
      datatype,
      DefinitionBodyKind.Datatype,
      datatype.Name,
      FullName(datatype, enclosingName),
      "datatype",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      null,
      reportFacts);
  }

  public static DefinitionNode ForConstant(
    ConstantField constant,
    string enclosingName,
    DefinitionNodePurpose purpose) {
    DefinitionReportFacts? reportFacts = null;
    if (purpose != DefinitionNodePurpose.ResolvedInclude) {
      var bodyAnalysis = AnalyzeExpressionBody(constant.Rhs);
      reportFacts = new DefinitionReportFacts(
        constant.Origin.line,
        constant.Origin.col,
        constant.StartToken.pos,
        constant.Rhs?.StartToken.pos,
        EndOffset(constant),
        DefinitionAnalysis.SourcePath(constant),
        constant.IsGhost,
        false,
        false,
        false,
        constant.WhatKind,
        constant.HasAxiomAttribute,
        constant.HasExternAttribute,
        constant.HasVerifyFalseAttribute,
        false,
        false,
        Array.Empty<DefinitionStatement>(),
        Array.Empty<DefinitionMemberAssignment>(),
        bodyAnalysis.CallSites,
        DefinitionAnalysis.BodyShape(constant.Rhs),
        bodyAnalysis.HasBroadExitRangeDisjunct,
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        Array.Empty<string>(),
        DefinitionStructuredFacts.Empty,
        bodyAnalysis.CallNames,
        purpose == DefinitionNodePurpose.ResolvedRoot ? [constant.Type] : Array.Empty<Type>());
    }
    return new DefinitionNode(
      constant,
      DefinitionBodyKind.Constant,
      constant.Name,
      FullName(constant, enclosingName),
      "constant",
      enclosingName,
      Array.Empty<Expression>(),
      null,
      null,
      reportFacts);
  }

  private static List<Expression> SpecificationExpressionsFor(MethodOrFunction declaration) {
    var expressions = new List<Expression>();
    expressions.AddRange(declaration.Req.Select(item => item.E));
    expressions.AddRange(declaration.Ens.Select(item => item.E));
    if (declaration.Decreases.Expressions != null) {
      expressions.AddRange(declaration.Decreases.Expressions);
    }
    return expressions;
  }

  private static List<string> ParameterTexts(MethodOrFunction declaration) {
    return declaration.Ins
      .Select(formal => $"{formal.Name}: {formal.Type}")
      .ToList();
  }

  private static DefinitionStructuredFacts StructuredFacts(
    MethodOrFunction declaration,
    IEnumerable<Formal> returns) {
    var (withoutAxiom, withAxiom) = ContractHeaders(declaration);
    return new DefinitionStructuredFacts(
      FormalDetails(declaration.Ins),
      FormalDetails(returns),
      declaration.Reads.Expressions?
        .Where(expression => !AutoGeneratedOrigin.Is(expression.Origin) &&
                             !AutoGeneratedOrigin.Is(expression.E.Origin) &&
                             expression.StartToken.pos > declaration.NameNode.EndToken.pos)
        .Select(expression => expression.EntireRange.PrintOriginal())
        .ToList() ?? [],
      declaration.Decreases.Expressions?
        .Where(expression => !AutoGeneratedOrigin.Is(expression.Origin))
        .Select(expression => expression.EntireRange.PrintOriginal())
        .ToList() ?? [],
      withoutAxiom,
      withAxiom);
  }

  private static List<DefinitionFormal> FormalDetails(IEnumerable<Formal> formals) {
    return formals
      .Select(formal => new DefinitionFormal(formal.Name, formal.Type.ToString(), formal.IsGhost))
      .ToList();
  }

  private static (string WithoutAxiom, string WithAxiom) ContractHeaders(MethodOrFunction declaration) {
    var endToken = declaration.BodyStartTok == Token.NoToken
      ? declaration.EndToken
      : declaration.BodyStartTok.ReportingRange.StartToken.Prev;
    if (endToken == null) {
      return ("", "");
    }
    var header = new TokenRange(declaration.StartToken, endToken).PrintOriginal();
    var withoutAxiom = RemoveAxiomAttributes(header, declaration);
    var keyword = DeclarationKeywordToken(declaration);
    var insertionByteOffset = (keyword.Next?.pos ?? declaration.EndToken.pos) - declaration.StartToken.pos;
    var prefix = TextForBytePrefix(header, insertionByteOffset);
    var insertion = RemoveAxiomAttributes(prefix, declaration).Length;
    return (withoutAxiom, withoutAxiom.Insert(insertion, "{:axiom} "));
  }

  private static string RemoveAxiomAttributes(string header, MethodOrFunction declaration) {
    var ranges = declaration.Attributes
      .AsEnumerable()
      .Where(attribute => attribute.Name == Attributes.AxiomAttributeName && attribute.StartToken.IsValid)
      .Select(attribute => (
        Start: attribute.StartToken.pos - declaration.StartToken.pos,
        End: attribute.EndToken.pos + attribute.EndToken.val.Length - declaration.StartToken.pos))
      .Where(range => 0 <= range.Start && range.Start < range.End)
      .OrderByDescending(range => range.Start)
      .ToList();
    foreach (var range in ranges) {
      var start = CharacterIndexForByteOffset(header, range.Start);
      var end = CharacterIndexForByteOffset(header, range.End);
      if (start > 0 && header[start - 1] is ' ' or '\t') {
        while (end < header.Length && header[end] is ' ' or '\t') {
          end++;
        }
      }
      header = header.Remove(start, end - start);
    }
    return header;
  }

  private static Token DeclarationKeywordToken(MethodOrFunction declaration) {
    var keywordWords = declaration.WhatKind.Split(' ', StringSplitOptions.RemoveEmptyEntries).ToHashSet();
    var keyword = declaration.StartToken;
    for (var token = declaration.StartToken;
         token != null && token.pos < declaration.NameNode.StartToken.pos;
         token = token.Next) {
      if (keywordWords.Contains(token.val)) {
        keyword = token;
      }
    }
    return keyword;
  }

  private static int CharacterIndexForByteOffset(string text, int byteOffset) {
    var bytes = Encoding.UTF8.GetBytes(text);
    var boundedOffset = Math.Clamp(byteOffset, 0, bytes.Length);
    return Encoding.UTF8.GetCharCount(bytes, 0, boundedOffset);
  }

  private static string TextForBytePrefix(string text, int byteLength) {
    var bytes = Encoding.UTF8.GetBytes(text);
    return Encoding.UTF8.GetString(bytes, 0, Math.Clamp(byteLength, 0, bytes.Length));
  }

  private static List<string> ParameterNameTexts(MethodOrFunction declaration) {
    return declaration.Ins
      .Select(formal => formal.Name)
      .ToList();
  }

  private static List<string> TypeParameterTexts(List<TypeParameter> typeParameters) {
    return typeParameters
      .Select(typeParameter => typeParameter.EntireRange.PrintOriginal())
      .ToList();
  }

  private static List<string> TypeParameterNameTexts(List<TypeParameter> typeParameters) {
    return typeParameters
      .Select(typeParameter => typeParameter.Name)
      .ToList();
  }

  private sealed record ExpressionBodyAnalysis(
    bool HasBroadExitRangeDisjunct,
    IReadOnlyList<string> CallNames,
    IReadOnlyList<DefinitionCallSite> CallSites
  );

  private sealed record StatementBodyAnalysis(
    bool HasLoop,
    bool HasAssumeStatement,
    bool HasVarDeclaration,
    bool HasBroadExitRangeDisjunct,
    IReadOnlyList<string> CallNames,
    IReadOnlyList<DefinitionStatement> Statements,
    IReadOnlyList<DefinitionMemberAssignment> MemberAssignments,
    IReadOnlyList<DefinitionCallSite> CallSites
  );

  private static ExpressionBodyAnalysis AnalyzeExpressionBody(Expression? expression) {
    var names = new List<string>();
    var callSites = new List<DefinitionCallSite>();
    var hasBroadExitRangeDisjunct = false;
    if (expression != null) {
      VisitExpression(expression);
    }
    return new ExpressionBodyAnalysis(hasBroadExitRangeDisjunct, names, callSites);

    void VisitExpression(Expression current) {
      if (DefinitionAnalysis.IsBroadExitRangeDisjunct(current)) {
        hasBroadExitRangeDisjunct = true;
      }
      if (current is ApplySuffix applySuffix) {
        var name = SyntacticExpressionName(applySuffix.Lhs);
        if (name.Length > 0) {
          names.Add(name);
        }
      }
      if (current is FunctionCallExpr { Function: { } function } call) {
        callSites.Add(new DefinitionCallSite(
          function.FullDafnyName,
          current.Origin.pos,
          EndOffset(current),
          call.Args.Select(argument => argument.EntireRange.PrintOriginal()).ToList(),
          Array.Empty<string>(),
          Array.Empty<DefinitionControlContext>()));
      }
      foreach (var subExpression in current.SubExpressions) {
        VisitExpression(subExpression);
      }
    }
  }

  private static StatementBodyAnalysis AnalyzeStatementBody(Statement? statement) {
    var hasLoop = false;
    var hasAssumeStatement = false;
    var hasVarDeclaration = false;
    var hasBroadExitRangeDisjunct = false;
    if (statement == null) {
      return new StatementBodyAnalysis(false, false, false, false, [], [], [], []);
    }

    var statements = new List<DefinitionStatement>();
    var memberAssignments = new List<DefinitionMemberAssignment>();
    var callSites = new List<DefinitionCallSite>();
    VisitStatement(statement, Array.Empty<DefinitionControlContext>());
    var names = new List<string>();
    CollectStatementCallNames(statement, names);
    return new StatementBodyAnalysis(
      hasLoop,
      hasAssumeStatement,
      hasVarDeclaration,
      hasBroadExitRangeDisjunct,
      names,
      statements,
      memberAssignments,
      callSites);

    void VisitStatement(
      Statement current,
      IReadOnlyList<DefinitionControlContext> controlPath) {
      hasLoop |= current is LoopStmt;
      hasAssumeStatement |= current is AssumeStmt or ExpectStmt;
      hasVarDeclaration |= current is VarDeclStmt;
      if (current is SingleAssignStmt { Lhs.Resolved: MemberSelectExpr memberSelect } assignment &&
          !AutoGeneratedOrigin.Is(assignment.Origin)) {
        memberAssignments.Add(new DefinitionMemberAssignment(
          assignment.StartToken.pos,
          EndOffset(assignment),
          memberSelect.Member.FullDafnyName,
          memberSelect.Obj.Type.NormalizeExpandKeepConstraints().ToString(),
          memberSelect.Member.IsGhost));
      }
      statements.Add(new DefinitionStatement(
        StatementKind(current),
        current.StartToken.pos,
        EndOffset(current),
        DirectCallTargets(current)));
      if (current is CallStmt { Method: { } method } call) {
        callSites.Add(new DefinitionCallSite(
          method.FullDafnyName,
          current.StartToken.pos,
          EndOffset(current),
          call.Args.Select(argument => argument.EntireRange.PrintOriginal()).ToList(),
          call.Lhs.Select(lhs => lhs.EntireRange.PrintOriginal()).ToList(),
          controlPath));
      }
      foreach (var expression in current.SubExpressions) {
        VisitExpression(expression, controlPath);
      }

      switch (current) {
        case IfStmt ifStatement:
          var ifGuard = ifStatement.Guard?.EntireRange.PrintOriginal() ?? "";
          VisitStatement(ifStatement.Thn, AppendContext(controlPath, new DefinitionControlContext(
            "if",
            current.StartToken.pos,
            EndOffset(current),
            0,
            ifStatement.Els == null ? 1 : 2,
            ifStatement.Els == null ? 0 : SubstantiveStatementCount(ifStatement.Els),
            ifGuard,
            Array.Empty<string>(),
            Array.Empty<string>())));
          if (ifStatement.Els != null) {
            VisitStatement(ifStatement.Els, AppendContext(controlPath, new DefinitionControlContext(
              "if",
              current.StartToken.pos,
              EndOffset(current),
              1,
              2,
              SubstantiveStatementCount(ifStatement.Thn),
              ifGuard,
              Array.Empty<string>(),
              Array.Empty<string>())));
          }
          return;
        case AlternativeStmt alternatives:
          for (var index = 0; index < alternatives.Alternatives.Count; index++) {
            var alternative = alternatives.Alternatives[index];
            var branchPath = AppendContext(controlPath, new DefinitionControlContext(
              "alternative",
              current.StartToken.pos,
              EndOffset(current),
              index,
              alternatives.Alternatives.Count,
              alternatives.Alternatives
                .Where((_, otherIndex) => otherIndex != index)
                .Sum(other => other.Body.Sum(SubstantiveStatementCount)),
              alternative.Guard.EntireRange.PrintOriginal(),
              Array.Empty<string>(),
              Array.Empty<string>()));
            foreach (var child in alternative.Body) {
              VisitStatement(child, branchPath);
            }
          }
          return;
        case MatchStmt match:
          for (var index = 0; index < match.Cases.Count; index++) {
            var matchCase = match.Cases[index];
            var branchPath = AppendContext(controlPath, new DefinitionControlContext(
              "match",
              current.StartToken.pos,
              EndOffset(current),
              index,
              match.Cases.Count,
              match.Cases
                .Where((_, otherIndex) => otherIndex != index)
                .Sum(other => other.Body.Sum(SubstantiveStatementCount)),
              matchCase.Ctor.FullName,
              Array.Empty<string>(),
              Array.Empty<string>()));
            foreach (var child in matchCase.Body) {
              VisitStatement(child, branchPath);
            }
          }
          return;
        case LoopStmt loop:
          var guard = loop is WhileStmt whileStatement
            ? whileStatement.Guard?.EntireRange.PrintOriginal() ?? ""
            : "";
          var loopPath = AppendContext(controlPath, new DefinitionControlContext(
            "loop",
            current.StartToken.pos,
            EndOffset(current),
            0,
            1,
            0,
            guard,
            loop.Invariants.Select(invariant => invariant.E.EntireRange.PrintOriginal()).ToList(),
            loop.Decreases.Expressions?.Select(item => item.EntireRange.PrintOriginal()).ToList() ?? []));
          foreach (var child in current.SubStatements) {
            VisitStatement(child, loopPath);
          }
          return;
        default:
          foreach (var child in current.SubStatements) {
            VisitStatement(child, controlPath);
          }
          return;
      }
    }

    void VisitExpression(
      Expression current,
      IReadOnlyList<DefinitionControlContext> controlPath) {
      if (DefinitionAnalysis.IsBroadExitRangeDisjunct(current)) {
        hasBroadExitRangeDisjunct = true;
      }
      if (current is FunctionCallExpr { Function: { } function } call) {
        callSites.Add(new DefinitionCallSite(
          function.FullDafnyName,
          current.Origin.pos,
          EndOffset(current),
          call.Args.Select(argument => argument.EntireRange.PrintOriginal()).ToList(),
          Array.Empty<string>(),
          controlPath));
      }
      foreach (var subExpression in current.SubExpressions) {
        VisitExpression(subExpression, controlPath);
      }
    }

    static IReadOnlyList<DefinitionControlContext> AppendContext(
      IReadOnlyList<DefinitionControlContext> path,
      DefinitionControlContext context) {
      return [.. path, context];
    }

    static int SubstantiveStatementCount(Statement item) {
      var own = item is BlockStmt ? 0 : 1;
      return own + item.SubStatements.Sum(SubstantiveStatementCount);
    }
  }

  private static string StatementKind(Statement statement) {
    return statement switch {
      BreakOrContinueStmt breakOrContinue => breakOrContinue.IsContinue ? "continue" : "break",
      _ => statement.GetType().Name
    };
  }

  private static IReadOnlyList<string> DirectCallTargets(Statement statement) {
    var targets = new List<string>();
    if (statement is CallStmt { Method: { } method }) {
      targets.Add(method.FullDafnyName);
    }
    foreach (var expression in statement.SubExpressions) {
      AddExpressionCallTargets(expression, targets);
    }
    return targets.Distinct().ToList();
  }

  private static void AddExpressionCallTargets(Expression expression, List<string> targets) {
    if (expression is FunctionCallExpr { Function: { } function }) {
      targets.Add(function.FullDafnyName);
    }
    foreach (var subExpression in expression.SubExpressions) {
      AddExpressionCallTargets(subExpression, targets);
    }
  }

  private static void CollectStatementCallNames(Statement statement, List<string> names) {
    foreach (var expression in statement.PreResolveSubExpressions) {
      CollectExpressionCallNames(expression, names);
    }
    foreach (var subStatement in statement.PreResolveSubStatements) {
      CollectStatementCallNames(subStatement, names);
    }
  }

  private static void CollectExpressionCallNames(Expression expression, List<string> names) {
    if (expression is ApplySuffix applySuffix) {
      var name = SyntacticExpressionName(applySuffix.Lhs);
      if (name.Length > 0) {
        names.Add(name);
      }
    }
    foreach (var subExpression in expression.SubExpressions) {
      CollectExpressionCallNames(subExpression, names);
    }
  }

  private static string SyntacticExpressionName(Expression expression) {
    expression = DefinitionAnalysis.UnwrapExpression(expression);
    return expression switch {
      NameSegment nameSegment => nameSegment.Name,
      ExprDotName exprDotName => JoinName(SyntacticExpressionName(exprDotName.Lhs), exprDotName.SuffixName),
      MemberSelectExpr memberSelectExpr => JoinName(SyntacticExpressionName(memberSelectExpr.Obj), memberSelectExpr.MemberName),
      FunctionCallExpr functionCallExpr => JoinName(SyntacticExpressionName(functionCallExpr.Receiver), functionCallExpr.Name),
      _ => ""
    };
  }

  private static string JoinName(string prefix, string suffix) {
    return prefix.Length == 0 ? suffix : $"{prefix}.{suffix}";
  }

  private static int? BodyStartOffset(Declaration declaration) {
    return declaration.BodyStartTok == Token.NoToken ? null : declaration.BodyStartTok.pos;
  }

  private static string FullName(MemberDecl member, string enclosingName) {
    if (member.EnclosingClass != null) {
      return member.FullDafnyName;
    }
    return enclosingName.Length == 0 ? member.Name : $"{enclosingName}.{member.Name}";
  }

  private static string FullName(TopLevelDecl declaration, string enclosingName) {
    if (declaration.EnclosingModuleDefinition != null) {
      return declaration.FullDafnyName;
    }
    return enclosingName.Length == 0 ? declaration.Name : $"{enclosingName}.{declaration.Name}";
  }

  private static int EndOffset(INode node) {
    return node.EndToken.pos + node.EndToken.val.Length;
  }

}
