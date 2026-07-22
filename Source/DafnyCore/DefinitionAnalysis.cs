#nullable enable
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;

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
  bool HasAssumeStatement,
  bool HasVarDeclaration,
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
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
  IReadOnlyList<string> DirectPostconditionCallees,
  IReadOnlyList<string> Dependencies
);

public record DefinitionAnalysisInclude(
  string SourcePath,
  string TargetPath,
  int Start,
  int End
);

public static class DefinitionAnalysis {
  public static IReadOnlyList<DefinitionAnalysisResult> Analyze(Program program) {
    var sourceFacts = SourceFacts.For(program);
    var allDeclarations = SourceDefinitions(program, spansOnly: false, includeIncludes: true);
    var declarations = allDeclarations
      .Where(declaration => !declaration.Declaration.Origin.FromIncludeDirective(program))
      .ToList();
    var callableDeclarations = allDeclarations
      .Where(declaration => declaration.BodyKind != DefinitionBodyKind.Datatype)
      .ToList();
    var callSequences = callableDeclarations.ToDictionary(
      declaration => declaration,
      declaration => CalledDefinitionSequence(declaration, callableDeclarations));
    var graph = callSequences.ToDictionary(
      item => item.Key,
      item => item.Value.ToHashSet());
    var declarationNodes = allDeclarations
      .GroupBy(declaration => declaration.Declaration)
      .ToDictionary(
        group => group.Key,
        group => group.First(node => node.BodyKind != DefinitionBodyKind.FunctionByMethod));
    var recursiveDeclarations = RecursiveDefinitions(graph);
    var recursiveGroups = RecursiveGroups(graph);

    return declarations
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        sourceFacts,
        recursiveDeclarations,
        recursiveGroups,
        graph,
        callSequences,
        declarationNodes,
        resolved: true))
      .ToList();
  }

  public static IReadOnlyList<DefinitionAnalysisResult> AnalyzeSpans(Program program) {
    var sourceFacts = SourceFacts.For(program);
    return RootSourceDefinitions(program, spansOnly: true)
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        sourceFacts,
        new HashSet<DefinitionNode>(),
        new Dictionary<DefinitionNode, HashSet<DefinitionNode>>(),
        new Dictionary<DefinitionNode, HashSet<DefinitionNode>>(),
        new Dictionary<DefinitionNode, List<DefinitionNode>>(),
        new Dictionary<INode, DefinitionNode>(),
        resolved: false))
      .ToList();
  }

  private static DefinitionAnalysisResult ResultFor(
    DefinitionNode declaration,
    SourceFacts sourceFacts,
    IReadOnlySet<DefinitionNode> recursiveDeclarations,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> recursiveGroups,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph,
    IReadOnlyDictionary<DefinitionNode, List<DefinitionNode>> callSequences,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes,
    bool resolved) {
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
      SourcePath(declaration.Declaration),
      declaration.Ghost,
      declaration.HasByMethod,
      declaration.HasLoop,
      declaration.WorldRelated,
      declaration.DeclarationKind,
      declaration.HasAxiomAttribute,
      declaration.HasExternAttribute,
      declaration.HasVerifyFalseAttribute,
      declaration.HasAssumeStatement,
      declaration.HasVarDeclaration,
      declaration.BodyShape,
      declaration.HasBroadExitRangeDisjunct,
      declaration.TypeParameters,
      declaration.TypeParameterNames,
      declaration.Parameters,
      declaration.ParameterNames,
      sourceFacts.SourceModules,
      sourceFacts.IncludedFiles,
      sourceFacts.LocalIncludedModules,
      sourceFacts.ImportedModules,
      sourceFacts.LocalIncludes,
      recursiveDeclarations.Contains(declaration),
      recursiveGroups.TryGetValue(declaration, out var group)
        ? group.Select(item => item.ReportFullName).OrderBy(name => name).ToList()
        : new List<string>(),
      graph.TryGetValue(declaration, out var callees)
        ? callees.Select(item => item.ReportFullName).OrderBy(name => name).ToList()
        : new List<string>(),
      callSequences.TryGetValue(declaration, out var callSequence)
        ? callSequence.Select(item => item.ReportFullName).ToList()
        : new List<string>(),
      declaration.CallNames,
      resolved ? DirectPostconditionCalleesFor(declaration, declarationNodes) : [],
      DependenciesFor(declaration, graph, declarationNodes));
  }

  private static List<string> DirectPostconditionCalleesFor(
    DefinitionNode declaration,
    IReadOnlyDictionary<INode, DefinitionNode> declarationNodes) {
    if (declaration.Declaration is not MethodOrFunction methodOrFunction) {
      return [];
    }
    return methodOrFunction.Ens
      .Select(ensures => UnwrapExpression(ensures.E).Resolved)
      .OfType<FunctionCallExpr>()
      .Where(call => call.Function != null && declarationNodes.ContainsKey(call.Function))
      .Select(call => declarationNodes[call.Function].ReportFullName)
      .ToList();
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
      .OrderBy(name => name)
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

  private static string SourcePath(INode declaration) {
    var filename = declaration.StartToken.ActualFilename;
    return filename == null ? "" : Path.GetFullPath(filename);
  }

  private static List<DefinitionNode> RootSourceDefinitions(Program program, bool spansOnly) {
    return SourceDefinitions(program, spansOnly, includeIncludes: false);
  }

  private static List<DefinitionNode> SourceDefinitions(
    Program program,
    bool spansOnly,
    bool includeIncludes) {
    var declarations = new List<DefinitionNode>();
    var modules = spansOnly ? ParsedModules(program) : program.Modules();
    foreach (var moduleDefinition in modules) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        if (topLevelDecl is DatatypeDecl datatypeDecl &&
            (includeIncludes || !topLevelDecl.Origin.FromIncludeDirective(program))) {
          declarations.Add(DefinitionNode.ForDatatype(datatypeDecl, moduleDefinition.Name));
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var member in topLevelDeclWithMembers.Members.OrderBy(member => member.Origin.pos)) {
          if (AutoGeneratedOrigin.Is(member.Origin)) {
            continue;
          }
          if (!includeIncludes && member.Origin.FromIncludeDirective(program)) {
            continue;
          }

          if (member is Function function) {
            declarations.Add(DefinitionNode.ForFunction(function, moduleDefinition.Name));
            if (!spansOnly && function.ByMethodBody != null) {
              declarations.Add(DefinitionNode.ForFunctionByMethod(function, moduleDefinition.Name));
            }
          } else if (member is MethodOrConstructor method && method is not Method { IsByMethod: true }) {
            declarations.Add(DefinitionNode.ForMethod(method, moduleDefinition.Name));
          }
        }
      }
    }

    return declarations;
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

  private static List<DefinitionNode> CalledDefinitionSequence(
    DefinitionNode declaration,
    IReadOnlyList<DefinitionNode> rootDeclarations) {
    var functionNodes = rootDeclarations
      .Where(node => node.BodyKind == DefinitionBodyKind.Function)
      .ToDictionary(node => (Function)node.Declaration);
    var byMethodNodes = rootDeclarations
      .Where(node => node.BodyKind == DefinitionBodyKind.FunctionByMethod)
      .ToDictionary(node => (Function)node.Declaration);
    var methodNodes = rootDeclarations
      .Where(node => node.BodyKind == DefinitionBodyKind.Method)
      .ToDictionary(node => (MethodOrConstructor)node.Declaration);
    var called = new List<DefinitionNode>();

    foreach (var expression in declaration.SpecificationExpressions) {
      CollectExpressionCalls(expression, functionNodes, byMethodNodes, called);
    }

    if (declaration.ExpressionBody != null) {
      CollectExpressionCalls(declaration.ExpressionBody, functionNodes, byMethodNodes, called);
    }

    if (declaration.StatementBody != null) {
      CollectStatementCalls(declaration.StatementBody, functionNodes, byMethodNodes, methodNodes, called);
    }

    return called;
  }

  private static void CollectExpressionCalls(
    Expression expression,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    List<DefinitionNode> called) {
    if (expression is FunctionCallExpr { Function: { } function } functionCall) {
      var nodes = functionCall.IsByMethodCall ? byMethodNodes : functionNodes;
      if (nodes.TryGetValue(function, out var target)) {
        called.Add(target);
      }
    }

    foreach (var subExpression in expression.SubExpressions) {
      CollectExpressionCalls(subExpression, functionNodes, byMethodNodes, called);
    }
  }

  private static void CollectStatementCalls(
    Statement statement,
    IReadOnlyDictionary<Function, DefinitionNode> functionNodes,
    IReadOnlyDictionary<Function, DefinitionNode> byMethodNodes,
    IReadOnlyDictionary<MethodOrConstructor, DefinitionNode> methodNodes,
    List<DefinitionNode> called) {
    if (statement is CallStmt callStmt && methodNodes.TryGetValue(callStmt.Method, out var methodTarget)) {
      called.Add(methodTarget);
    }

    foreach (var expression in statement.SubExpressions) {
      CollectExpressionCalls(expression, functionNodes, byMethodNodes, called);
    }

    foreach (var subStatement in statement.SubStatements) {
      CollectStatementCalls(subStatement, functionNodes, byMethodNodes, methodNodes, called);
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
    expression = UnwrapExpression(expression);
    if (IsExitRange(expression)) {
      return true;
    }
    if (expression is BinaryExpr { Op: BinaryExpr.Opcode.Or } binaryExpr &&
        (IsExitRange(binaryExpr.E0) || IsExitRange(binaryExpr.E1))) {
      return true;
    }
    return expression.SubExpressions.Any(ContainsBroadExitRangeDisjunct);
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

  private static HashSet<DefinitionNode> RecursiveDefinitions(Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var recursive = graph
      .Where(item => item.Value.Contains(item.Key))
      .Select(item => item.Key)
      .ToHashSet();

    foreach (var component in StronglyConnectedComponents(graph)) {
      if (component.Count > 1) {
        recursive.UnionWith(component);
      }
    }

    return recursive;
  }

  private static Dictionary<DefinitionNode, HashSet<DefinitionNode>> RecursiveGroups(
    Dictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
    var groups = new Dictionary<DefinitionNode, HashSet<DefinitionNode>>();
    foreach (var component in StronglyConnectedComponents(graph)) {
      if (component.Count == 1 && !graph[component.Single()].Contains(component.Single())) {
        continue;
      }

      foreach (var item in component) {
        groups[item] = component;
      }
    }

    return groups;
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
        if (item == node) {
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
  IReadOnlyList<DefinitionAnalysisInclude> LocalIncludes
) {
  public static SourceFacts For(Program program) {
    var rootUris = program.Compilation.RootSourceUris.ToHashSet();
    var rootModules = DefinitionAnalysis.ParsedModules(program)
      .Where(module => !module.IsDefaultModule && !module.Origin.FromIncludeDirective(program))
      .ToList();

    var rootIncludes = program.Compilation.Includes
      .Where(include => rootUris.Contains(include.IncluderFilename))
      .ToList();

    return new SourceFacts(
      rootModules.Select(module => module.Name).Distinct().OrderBy(name => name).ToList(),
      rootIncludes.Select(include => Path.GetFileName(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name)
        .ToList(),
      rootIncludes.Where(IsSameDirectoryDafnyInclude)
        .Select(include => Path.GetFileNameWithoutExtension(include.IncludedFilename.LocalPath))
        .Distinct()
        .OrderBy(name => name)
        .ToList(),
      DefinitionAnalysis.ParsedModules(program)
        .Where(module => !module.Origin.FromIncludeDirective(program))
        .SelectMany(module => ImportedModuleNames(program, module))
        .Distinct()
        .OrderBy(name => name)
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
        .ToList());
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
  Datatype
}

internal sealed record DefinitionNode(
  INode Declaration,
  DefinitionBodyKind BodyKind,
  string Name,
  string ReportFullName,
  string Kind,
  string EnclosingName,
  int Line,
  int Column,
  int Start,
  int? BodyStart,
  int End,
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
  string BodyShape,
  bool HasBroadExitRangeDisjunct,
  IReadOnlyList<string> TypeParameters,
  IReadOnlyList<string> TypeParameterNames,
  IReadOnlyList<string> Parameters,
  IReadOnlyList<string> ParameterNames,
  IReadOnlyList<Expression> SpecificationExpressions,
  IReadOnlyList<string> CallNames,
  Expression? ExpressionBody,
  Statement? StatementBody,
  IReadOnlyList<Type> Types
) {
  public static DefinitionNode ForFunction(Function function, string enclosingName) {
    var specificationExpressions = SpecificationExpressionsFor(function);
    return new DefinitionNode(
      function,
      DefinitionBodyKind.Function,
      function.Name,
      FullName(function, enclosingName),
      function.WhatKind,
      enclosingName,
      function.Origin.line,
      function.Origin.col,
      function.StartToken.pos,
      BodyStartOffset(function),
      EndOffset(function),
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
      DefinitionAnalysis.BodyShape(function.Body),
      ContainsBroadExitRangeDisjunct(specificationExpressions, function.Body, null),
      TypeParameterTexts(function.TypeArgs),
      TypeParameterNameTexts(function.TypeArgs),
      ParameterTexts(function),
      ParameterNameTexts(function),
      specificationExpressions,
      CollectCallNameList(function.Body, null),
      function.Body,
      null,
      [.. function.Ins.Select(formal => formal.Type), function.ResultType]);
  }

  public static DefinitionNode ForFunctionByMethod(Function function, string enclosingName) {
    return new DefinitionNode(
      function,
      DefinitionBodyKind.FunctionByMethod,
      function.Name,
      FullName(function, enclosingName) + "#by-method",
      "function-by-method",
      enclosingName,
      function.Origin.line,
      function.Origin.col,
      function.StartToken.pos,
      function.ByMethodBody?.StartToken.pos,
      EndOffset(function),
      function.IsGhost,
      true,
      DefinitionAnalysis.ContainsLoop(function.ByMethodBody),
      false,
      "by-method",
      function.HasAxiomAttribute,
      function.HasExternAttribute,
      function.HasVerifyFalseAttribute,
      DefinitionAnalysis.ContainsAssume(function.ByMethodBody),
      DefinitionAnalysis.ContainsVarDeclaration(function.ByMethodBody),
      "",
      ContainsBroadExitRangeDisjunct([], null, function.ByMethodBody),
      TypeParameterTexts(function.TypeArgs),
      TypeParameterNameTexts(function.TypeArgs),
      ParameterTexts(function),
      ParameterNameTexts(function),
      [],
      CollectCallNameList(null, function.ByMethodBody),
      null,
      function.ByMethodBody,
      [.. function.Ins.Select(formal => formal.Type), function.ResultType]);
  }

  public static DefinitionNode ForMethod(MethodOrConstructor method, string enclosingName) {
    var specificationExpressions = SpecificationExpressionsFor(method);
    return new DefinitionNode(
      method,
      DefinitionBodyKind.Method,
      method.Name,
      FullName(method, enclosingName),
      method is Constructor ? "constructor" : "method",
      enclosingName,
      method.Origin.line,
      method.Origin.col,
      method.StartToken.pos,
      BodyStartOffset(method),
      EndOffset(method),
      method.IsGhost,
      false,
      DefinitionAnalysis.ContainsLoop(method.Body),
      false,
      method.WhatKind,
      method.HasAxiomAttribute,
      method.HasExternAttribute,
      method.HasVerifyFalseAttribute,
      DefinitionAnalysis.ContainsAssume(method.Body),
      DefinitionAnalysis.ContainsVarDeclaration(method.Body),
      "",
      ContainsBroadExitRangeDisjunct(specificationExpressions, null, method.Body),
      TypeParameterTexts(method.TypeArgs),
      TypeParameterNameTexts(method.TypeArgs),
      ParameterTexts(method),
      ParameterNameTexts(method),
      specificationExpressions,
      CollectCallNameList(null, method.Body),
      null,
      method.Body,
      [.. method.Ins.Select(formal => formal.Type), .. method.Outs.Select(formal => formal.Type)]);
  }

  public static DefinitionNode ForDatatype(DatatypeDecl datatype, string enclosingName) {
    return new DefinitionNode(
      datatype,
      DefinitionBodyKind.Datatype,
      datatype.Name,
      FullName(datatype, enclosingName),
      "datatype",
      enclosingName,
      datatype.Origin.line,
      datatype.Origin.col,
      datatype.StartToken.pos,
      null,
      EndOffset(datatype),
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
      "",
      false,
      TypeParameterTexts(datatype.TypeArgs),
      TypeParameterNameTexts(datatype.TypeArgs),
      [],
      [],
      [],
      [],
      null,
      null,
      [.. datatype.Ctors.SelectMany(constructor => constructor.Formals).Select(formal => formal.Type)]);
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

  private static bool ContainsBroadExitRangeDisjunct(
    IReadOnlyList<Expression> specificationExpressions,
    Expression? expressionBody,
    Statement? statementBody) {
    return specificationExpressions.Any(DefinitionAnalysis.ContainsBroadExitRangeDisjunct) ||
           DefinitionAnalysis.ContainsBroadExitRangeDisjunct(expressionBody) ||
           DefinitionAnalysis.StatementContainsBroadExitRangeDisjunct(statementBody);
  }

  private static List<string> CollectCallNameList(Expression? expressionBody, Statement? statementBody) {
    var names = new List<string>();
    if (expressionBody != null) {
      CollectExpressionCallNames(expressionBody, names);
    }
    if (statementBody != null) {
      CollectStatementCallNames(statementBody, names);
    }
    return names;
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
