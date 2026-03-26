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
      Assert.NotNull(json["root"]!["children"]);
      Assert.Null(json["root"]!["type"]);
    } finally {
      File.Delete(file);
      File.Delete(output);
    }
  }

  [Fact]
  public async Task AstDumpUsesCompactNodesWithoutSourceNoise() {
    var source = "method M(x: int) returns (y: int) { if x == 0 { y := x; } else { y := x + 1; } }";
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
      Assert.DoesNotContain(allNodes, node => node["type"] != null);

      var ifNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "if");
      Assert.NotNull(ifNode);

      Assert.Contains(allNodes, node =>
        node["kind"]?.GetValue<string>() == "identifier" &&
        node["value"]?.GetValue<string>() == "x" &&
        node["resolvedType"]?.GetValue<string>() == "int");

      var methodNode = allNodes.FirstOrDefault(node => node["kind"]?.GetValue<string>() == "method");
      Assert.NotNull(methodNode);
      Assert.Equal("M", methodNode!["value"]!.GetValue<string>());
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

  private static IEnumerable<JsonObject> EnumerateNodes(JsonObject node) {
    yield return node;
    if (node["children"] is not JsonArray children) {
      yield break;
    }

    foreach (var child in children) {
      if (child is JsonObject childObject) {
        foreach (var descendant in EnumerateNodes(childObject)) {
          yield return descendant;
        }
      }
    }
  }
}
