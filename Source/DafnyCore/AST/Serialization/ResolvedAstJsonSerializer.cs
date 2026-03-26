#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text.Json.Nodes;

namespace Microsoft.Dafny;

public static class ResolvedAstJsonSerializer {
  public static JsonObject Serialize(Program program) {
    return new Serializer().Serialize(program);
  }

  private sealed class Serializer {
    public JsonObject Serialize(Program program) {
      return new JsonObject {
        ["format"] = "dafny-resolved-ast",
        ["version"] = 2,
        ["resolved"] = true,
        ["programName"] = program.Name,
        ["root"] = SerializeNode(program, new HashSet<INode>(NodeReferenceComparer.Instance))
      };
    }

    private JsonObject SerializeNode(INode node, ISet<INode> visited) {
      if (!visited.Add(node)) {
        return CreateNodeObject(node, includeChildren: false, isShared: true);
      }

      var result = CreateNodeObject(node, includeChildren: true, isShared: false);
      var children = node.Children
        .Where(ShouldIncludeChild)
        .Select(child => (JsonNode)SerializeNode(child, visited))
        .ToArray();

      if (children.Length > 0) {
        result["children"] = new JsonArray(children);
      }

      return result;
    }

    private JsonObject CreateNodeObject(INode node, bool includeChildren, bool isShared) {
      var result = new JsonObject {
        ["kind"] = GetKind(node)
      };

      var value = GetValue(node);
      if (value != null) {
        result["value"] = value;
      }

      var resolvedType = GetResolvedType(node);
      if (resolvedType != null) {
        result["resolvedType"] = resolvedType;
      }

      if (isShared) {
        result["shared"] = true;
      }

      if (!includeChildren) {
        return result;
      }

      return result;
    }

    private static bool ShouldIncludeChild(INode child) {
      return child is not Name;
    }

    private static string GetKind(INode node) {
      if (TryGetStringProperty(node, "WhatKind") is { Length: > 0 } whatKind) {
        return NormalizeKind(whatKind) switch {
          "module_definition" => "module",
          "top_level_module_declaration" => "module",
          _ => NormalizeKind(whatKind)
        };
      }

      return node switch {
        Name => "name",
        IdentifierExpr => "identifier",
        LiteralExpr literalExpr => GetLiteralKind(literalExpr),
        BinaryExpr => "binary",
        FunctionCallExpr => "call",
        MemberSelectExpr => "member_select",
        Statement => NormalizeTypeName(node.GetType().Name, "Stmt", "Statement"),
        _ => NormalizeTypeName(node.GetType().Name, "Expr", "Expression", "Decl")
      };
    }

    private static JsonNode? GetValue(INode node) {
      return node switch {
        Name name => JsonValue.Create(name.Value),
        LiteralExpr literalExpr => SerializeLiteralValue(literalExpr.Value),
        BinaryExpr binaryExpr => JsonValue.Create(BinaryExpr.OpcodeString(binaryExpr.Op)),
        FunctionCallExpr functionCallExpr => JsonValue.Create(functionCallExpr.Name),
        MemberSelectExpr memberSelectExpr => JsonValue.Create(memberSelectExpr.MemberName),
        IdentifierExpr identifierExpr => JsonValue.Create(identifierExpr.Name),
        ModuleDefinition moduleDefinition => GetStringValue(moduleDefinition.DafnyName) ??
                                           GetStringValue(TryGetStringProperty(moduleDefinition, "Name")),
        Declaration declaration => GetStringValue(declaration.Name),
        _ => GetStringValue(TryGetStringProperty(node, "Name")) ??
             GetStringValue(TryGetStringProperty(node, "DafnyName"))
      };
    }

    private static string? GetResolvedType(INode node) {
      return node is Expression expression && expression.WasResolved() && expression.Type != null
        ? expression.Type.ToString()
        : null;
    }

    private static JsonNode? SerializeLiteralValue(object? value) {
      return value switch {
        null => null,
        bool boolean => JsonValue.Create(boolean),
        BigInteger integer => JsonValue.Create(integer.ToString()),
        string text => JsonValue.Create(text),
        Microsoft.BaseTypes.BigDec decimalValue => JsonValue.Create(decimalValue.ToString()),
        _ => JsonValue.Create(value.ToString())
      };
    }

    private static JsonNode? GetStringValue(string? value) {
      return value == null ? null : JsonValue.Create(value);
    }

    private static string GetLiteralKind(LiteralExpr literalExpr) {
      return literalExpr switch {
        StringLiteralExpr => "literal.string",
        CharLiteralExpr => "literal.char",
        DecimalLiteralExpr => "literal.real",
        _ => literalExpr.Value switch {
          null => "literal.null",
          bool => "literal.bool",
          BigInteger => "literal.int",
          Microsoft.BaseTypes.BigDec => "literal.real",
          string => "literal.string",
          _ => "literal"
        }
      };
    }

    private static string NormalizeKind(string value) {
      return value.Trim().ToLowerInvariant().Replace(' ', '_');
    }

    private static string NormalizeTypeName(string typeName, params string[] suffixes) {
      var result = typeName;
      foreach (var suffix in suffixes) {
        if (result.EndsWith(suffix, StringComparison.Ordinal)) {
          result = result[..^suffix.Length];
          break;
        }
      }

      return ToSnakeCase(result);
    }

    private static string ToSnakeCase(string value) {
      if (string.IsNullOrEmpty(value)) {
        return value;
      }

      var characters = new List<char>(value.Length * 2) { char.ToLowerInvariant(value[0]) };
      for (var index = 1; index < value.Length; index++) {
        var current = value[index];
        if (char.IsUpper(current) && (char.IsLower(value[index - 1]) || (index + 1 < value.Length && char.IsLower(value[index + 1])))) {
          characters.Add('_');
        }
        characters.Add(char.ToLowerInvariant(current));
      }

      return new string(characters.ToArray());
    }

    private static string? TryGetStringProperty(object value, string propertyName) {
      var property = value.GetType().GetProperty(propertyName);
      if (property?.PropertyType != typeof(string) || property.GetMethod == null || property.GetIndexParameters().Length != 0) {
        return null;
      }

      try {
        return (string?)property.GetValue(value);
      } catch {
        return null;
      }
    }

  }

  private sealed class NodeReferenceComparer : IEqualityComparer<INode> {
    public static readonly NodeReferenceComparer Instance = new();

    public bool Equals(INode? x, INode? y) {
      return ReferenceEquals(x, y);
    }

    public int GetHashCode(INode obj) {
      return RuntimeHelpers.GetHashCode(obj);
    }
  }
}
