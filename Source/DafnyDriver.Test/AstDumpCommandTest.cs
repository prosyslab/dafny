using System.IO;
using System.Text.Json.Nodes;
using Microsoft.Dafny;

namespace DafnyDriver.Test;

public class AstDumpCommandTest {
  [Fact]
  public async Task AstDumpWritesResolvedAstJson() {
    var source = "method M(x: int) returns (y: int) { y := x; }";
    var file = Path.GetTempFileName() + ".dfy";
    var output = Path.GetTempFileName() + ".json";
    await File.WriteAllTextAsync(file, source);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);
      options.Options.OptionArguments[AstDumpCommand.Output] = new FileInfo(output);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.SUCCESS, exitValue);
      Assert.True(File.Exists(output));

      var json = JsonNode.Parse(await File.ReadAllTextAsync(output))!.AsObject();
      Assert.Equal("dafny-resolved-ast", json["format"]!.GetValue<string>());
      Assert.True(json["resolved"]!.GetValue<bool>());
      Assert.NotNull(json["root"]);
      Assert.Null(json["nodes"]);
      Assert.Null(json["symbols"]);
      Assert.Null(json["references"]);
      Assert.NotNull(json["root"]!["kind"]);
      Assert.NotNull(json["root"]!["modules"]);
      Assert.Null(json["root"]!["type"]);
      Assert.Equal(4, json["version"]!.GetValue<int>());
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  [Fact]
  public async Task AstDumpUsesCompactNodesWithoutSourceNoise() {
    var source = "function F(x: int): bool { true } method M(x: int) returns (y: int) { var s := iset{1, 2, 3}; if x == 0 { y := x; } else { y := -x; } }";
    var file = Path.GetTempFileName() + ".dfy";
    var output = Path.GetTempFileName() + ".json";
    await File.WriteAllTextAsync(file, source);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);
      options.Options.OptionArguments[AstDumpCommand.Output] = new FileInfo(output);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.SUCCESS, exitValue);

      var json = JsonNode.Parse(await File.ReadAllTextAsync(output))!.AsObject();
      var root = json["root"]!.AsObject();
      var allNodes = EnumerateNodes(root).ToList();

      Assert.DoesNotContain(allNodes, node => node["source"] != null);
      Assert.DoesNotContain(allNodes, node => node["snippet"] != null);
      Assert.DoesNotContain(allNodes, node => node["kind"]?.GetValue<string>() == "top-level_module_declaration");
      Assert.DoesNotContain(allNodes, node => node["resolvedType"] != null);
      Assert.DoesNotContain(allNodes, node => node["resolvedVariableType"] != null);
      Assert.DoesNotContain(allNodes, node => node["declaredType"] != null);
      Assert.DoesNotContain(allNodes, node => node["returnType"] != null);

      var ifNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "if");
      Assert.NotNull(ifNode);

      Assert.Contains(allNodes, node =>
        node["kind"]?.GetValue<string>() == "identifier" &&
        node["name"]?.GetValue<string>() == "x" &&
        node["type"]!["kind"]?.GetValue<string>() == "int");

      var methodNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "method");
      Assert.NotNull(methodNode);
      Assert.Equal("M", methodNode!["name"]!.GetValue<string>());
      Assert.NotNull(methodNode["parameters"]);
      Assert.NotNull(methodNode["returns"]);
      Assert.NotNull(methodNode["body"]);

      var ifNodeObject = ifNode!.AsObject();
      Assert.NotNull(ifNodeObject["condition"]);
      Assert.NotNull(ifNodeObject["then"]);
      Assert.NotNull(ifNodeObject["else"]);

      var binaryNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "binary");
      Assert.NotNull(binaryNode);
      Assert.NotNull(binaryNode!["operator"]);

      var functionNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "function");
      Assert.NotNull(functionNode);
      Assert.NotNull(functionNode!["parameters"]);
      Assert.NotNull(functionNode["type"]);
      Assert.Equal("bool", functionNode["type"]!["kind"]!.GetValue<string>());
      Assert.True(functionNode["body"] != null || functionNode["byMethodBody"] != null);

      var parameterNode = allNodes.First(node => node["kind"]?.GetValue<string>() == "parameter");
      Assert.Equal("int", parameterNode["type"]!["kind"]!.GetValue<string>());

      var localVariable = allNodes.First(node => node["kind"]?.GetValue<string>() == "local_variable" && node["name"]?.GetValue<string>() == "s");
      Assert.Equal("iset", localVariable["type"]!["kind"]!.GetValue<string>());
      Assert.Equal("int", localVariable["type"]!["element"]!["kind"]!.GetValue<string>());

      var setNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() is "set" or "iset" && node["elements"] != null);
      Assert.NotNull(setNode);
      Assert.NotNull(setNode!["elements"]);
      Assert.Equal("iset", setNode["type"]!["kind"]!.GetValue<string>());
      Assert.Equal("int", setNode["type"]!["element"]!["kind"]!.GetValue<string>());

      var negationNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "negation");
      Assert.NotNull(negationNode);
      Assert.Equal("-", negationNode!["operator"]!.GetValue<string>());
      Assert.NotNull(negationNode["operand"]);
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  [Fact]
  public async Task AstDumpDoesNotWriteOutputOnResolutionErrors() {
    var source = "method M() { var y := z; }";
    var file = Path.GetTempFileName() + ".dfy";
    var output = Path.GetTempFileName() + ".json";
    File.Delete(output);
    await File.WriteAllTextAsync(file, source);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);
      options.Options.OptionArguments[AstDumpCommand.Output] = new FileInfo(output);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.DAFNY_ERROR, exitValue);
      Assert.False(File.Exists(output));
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  [Fact]
  public async Task AstDumpWithoutOutputUsesDefaultPath() {
    var file = Path.GetTempFileName() + ".dfy";
    var defaultOutput = Path.Combine(Path.GetDirectoryName(file)!, Path.GetFileNameWithoutExtension(file) + ".ast.json");
    await File.WriteAllTextAsync(file, "method M() {}");
    File.Delete(defaultOutput);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.SUCCESS, exitValue);
      Assert.True(File.Exists(defaultOutput));
    } finally {
      File.Delete(file);
      File.Delete(defaultOutput);
    }
  }

  [Fact]
  public async Task AstDumpIncludesLocationsForModulesClassesFunctionsAndMethods() {
    var source = "module A { class C { function F(x: int): bool { true } method M(x: int) returns (y: int) { y := x; } } }";
    var file = Path.GetTempFileName() + ".dfy";
    var output = Path.GetTempFileName() + ".json";
    await File.WriteAllTextAsync(file, source);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);
      options.Options.OptionArguments[AstDumpCommand.Output] = new FileInfo(output);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.SUCCESS, exitValue);

      var json = JsonNode.Parse(await File.ReadAllTextAsync(output))!.AsObject();
      var allNodes = EnumerateNodes(json["root"]!.AsObject()).ToList();

      AssertHasLocation(allNodes.First(node => node["kind"]?.GetValue<string>() == "module"));
      AssertHasLocation(allNodes.First(node => node["kind"]?.GetValue<string>() == "class"));
      AssertHasLocation(allNodes.First(node => node["kind"]?.GetValue<string>() == "function"));
      AssertHasLocation(allNodes.First(node => node["kind"]?.GetValue<string>() == "method"));
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  [Fact]
  public async Task AstDumpUsesRecursiveTypeObjects() {
    var source = "method M() { var s := iset{1, 2}; var m: map<int, iset<int>>; }";
    var file = Path.GetTempFileName() + ".dfy";
    var output = Path.GetTempFileName() + ".json";
    await File.WriteAllTextAsync(file, source);

    try {
      var options = DafnyOptions.CreateUsingOldParser(new StringWriter(), null, file);
      options.Options.OptionArguments[AstDumpCommand.Output] = new FileInfo(output);

      var exitValue = await AstDumpCommand.DoDumping(options);

      Assert.Equal(ExitValue.SUCCESS, exitValue);

      var json = JsonNode.Parse(await File.ReadAllTextAsync(output))!.AsObject();
      var allNodes = EnumerateNodes(json["root"]!.AsObject()).ToList();

      var inferredLocal = allNodes.First(node => node["kind"]?.GetValue<string>() == "local_variable" && node["name"]?.GetValue<string>() == "s");
      Assert.Equal("inferred", inferredLocal["typeSource"]!.GetValue<string>());
      Assert.Equal("iset", inferredLocal["type"]!["kind"]!.GetValue<string>());
      Assert.Equal("int", inferredLocal["type"]!["element"]!["kind"]!.GetValue<string>());

      var mapLocal = allNodes.First(node => node["kind"]?.GetValue<string>() == "local_variable" && node["name"]?.GetValue<string>() == "m");
      Assert.Equal("map", mapLocal["type"]!["kind"]!.GetValue<string>());
      Assert.Equal("int", mapLocal["type"]!["key"]!["kind"]!.GetValue<string>());
      Assert.Equal("iset", mapLocal["type"]!["value"]!["kind"]!.GetValue<string>());
      Assert.Equal("int", mapLocal["type"]!["value"]!["element"]!["kind"]!.GetValue<string>());
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  private static IEnumerable<JsonObject> EnumerateNodes(JsonObject node) {
    yield return node;
    foreach (var property in node) {
      switch (property.Value) {
        case JsonObject childObject:
          foreach (var descendant in EnumerateNodes(childObject)) {
            yield return descendant;
          }
          break;
        case JsonArray children:
          foreach (var child in children) {
            if (child is JsonObject arrayChildObject) {
              foreach (var descendant in EnumerateNodes(arrayChildObject)) {
                yield return descendant;
              }
            }
          }
          break;
      }
    }
  }

  private static void AssertHasLocation(JsonObject node) {
    var location = node["location"]!.AsObject();
    Assert.False(string.IsNullOrEmpty(location["file"]!.GetValue<string>()));
    Assert.True(location["line"]!.GetValue<int>() > 0);
    Assert.True(location["column"]!.GetValue<int>() > 0);
  }
}
