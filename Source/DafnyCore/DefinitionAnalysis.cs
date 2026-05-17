#nullable enable
using System.Collections.Generic;
using System.Linq;

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
  bool Ghost,
  bool HasByMethod,
  bool HasLoop,
  bool WorldRelated,
  bool Recursive,
  IReadOnlyList<string> RecursiveGroup,
  IReadOnlyList<string> Callees
);

public static class DefinitionAnalysis {
  public static IReadOnlyList<DefinitionAnalysisResult> Analyze(Program program) {
    var declarations = RootSourceDefinitions(program, spansOnly: false);
    var callableDeclarations = declarations
      .Where(declaration => declaration.BodyKind != DefinitionBodyKind.Datatype)
      .ToList();
    var graph = callableDeclarations.ToDictionary(
      declaration => declaration,
      declaration => CalledDefinitions(declaration, callableDeclarations));
    var recursiveDeclarations = RecursiveDefinitions(graph);
    var recursiveGroups = RecursiveGroups(graph);

    return declarations
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        recursiveDeclarations,
        recursiveGroups,
        graph))
      .ToList();
  }

  public static IReadOnlyList<DefinitionAnalysisResult> AnalyzeSpans(Program program) {
    return RootSourceDefinitions(program, spansOnly: true)
      .OrderBy(declaration => declaration.Start)
      .Select(declaration => ResultFor(
        declaration,
        new HashSet<DefinitionNode>(),
        new Dictionary<DefinitionNode, HashSet<DefinitionNode>>(),
        new Dictionary<DefinitionNode, HashSet<DefinitionNode>>()))
      .ToList();
  }

  private static DefinitionAnalysisResult ResultFor(
    DefinitionNode declaration,
    IReadOnlySet<DefinitionNode> recursiveDeclarations,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> recursiveGroups,
    IReadOnlyDictionary<DefinitionNode, HashSet<DefinitionNode>> graph) {
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
      declaration.Ghost,
      declaration.HasByMethod,
      declaration.HasLoop,
      declaration.WorldRelated,
      recursiveDeclarations.Contains(declaration),
      recursiveGroups.TryGetValue(declaration, out var group)
        ? group.Select(item => item.ReportFullName).OrderBy(name => name).ToList()
        : new List<string>(),
      graph.TryGetValue(declaration, out var callees)
        ? callees.Select(item => item.ReportFullName).OrderBy(name => name).ToList()
        : new List<string>());
  }

  private static List<DefinitionNode> RootSourceDefinitions(Program program, bool spansOnly) {
    var declarations = new List<DefinitionNode>();
    var modules = spansOnly ? ParsedModules(program) : program.Modules();
    foreach (var moduleDefinition in modules) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        if (topLevelDecl is DatatypeDecl datatypeDecl && !topLevelDecl.Origin.FromIncludeDirective(program)) {
          declarations.Add(DefinitionNode.ForDatatype(datatypeDecl, moduleDefinition.Name));
        }

        if (topLevelDecl is not TopLevelDeclWithMembers topLevelDeclWithMembers) {
          continue;
        }

        foreach (var member in topLevelDeclWithMembers.Members.OrderBy(member => member.Origin.pos)) {
          if (member.Origin.FromIncludeDirective(program)) {
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

  private static IEnumerable<ModuleDefinition> ParsedModules(Program program) {
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

  private static HashSet<DefinitionNode> CalledDefinitions(
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
    var called = new HashSet<DefinitionNode>();

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
    HashSet<DefinitionNode> called) {
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
    HashSet<DefinitionNode> called) {
    if (statement.IsGhost) {
      return;
    }

    if (statement is CallStmt callStmt && methodNodes.TryGetValue(callStmt.Method, out var methodTarget)) {
      called.Add(methodTarget);
    }

    foreach (var expression in statement.NonSpecificationSubExpressions) {
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
  Expression? ExpressionBody,
  Statement? StatementBody
) {
  public static DefinitionNode ForFunction(Function function, string enclosingName) {
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
      function.Body,
      null);
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
      null,
      function.ByMethodBody);
  }

  public static DefinitionNode ForMethod(MethodOrConstructor method, string enclosingName) {
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
      null,
      method.Body);
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
      null,
      null);
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
