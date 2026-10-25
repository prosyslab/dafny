#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeSourceAuthoringTests {
  private const string Source = "module M { " +
    "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } " +
    "method Goal(x: int) returns (y: int) requires x >= 0 ensures y == x + 1 { y := Helper(x); } }";

  // Preparation places unresolved templates in native source positions and exposes exact private identities.
  [Fact]
  public async Task PrepareInstallsBodyAndGeneratorTemplatesInNamedModule() {
    var result = await Run(Request(ContractRuntimeAuthoringAction.Prepare));

    Assert.Equal(ContractRuntimeAuthoringStatus.Ready, result.Status);
    Assert.Null(result.Drafts);
    Assert.Null(result.Generator);
    Assert.NotNull(result.Manifest);
    Assert.Equal(new[] { "M.Helper" }, result.Manifest.DraftSymbols);
    Assert.Equal("M.Goal", result.Manifest.GeneratorSymbol);
    Assert.NotNull(result.Manifest.RuntimeSource);
    Assert.Contains(result.Manifest.PreparedSources, dependency => dependency == result.Manifest.RuntimeSource);
    var source = Assert.Single(result.Sources!, item => item.Path == "M.dfy").Content;
    Assert.Contains("method Helper(x: int) returns (y: int) ensures y == x + 1", source);
    Assert.Contains("PbtAuthoringTODO_", source);
    Assert.Contains("import PbtRandom", source);
    Assert.Contains("method {:pbt_generator \"M.Goal\"} Generate", source);
    Assert.Contains("ensures (x >= 0)", source);
    Assert.Contains(result.Sources!, item => item.Content == ContractRuntimeInstrumentation.DafnySource);
  }

  // Extraction returns ordinary packets while retaining original contracts and module-local authored helpers.
  [Fact]
  public async Task ExtractsBodyGeneratorAndHelperIntoLegacyPackets() {
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare));
    var authored = prepared.Sources!.Select(source => source.Path == "M.dfy"
      ? source with { Content = Author(source.Content) }
      : source).Select(source => source with { Sha256 = ContractHarnessBuilder.Hash(source.Content) }).ToArray();

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract) with {
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Null(result.Sources);
    Assert.Null(result.Manifest);
    var draft = Assert.Single(result.Drafts!);
    Assert.Equal("M.Helper", draft.Symbol);
    Assert.Equal(".top-down-pbt/drafts/M.Helper.dfy", draft.Path);
    Assert.Contains("ensures y == x + 1", draft.Content);
    Assert.Contains("y := x + 1;", draft.Content);
    Assert.DoesNotContain("pbt-authoring", draft.Content, StringComparison.Ordinal);
    Assert.Equal(draft.Sha256, ContractHarnessBuilder.Hash(draft.Content));
    Assert.Equal(".top-down-pbt/generators/M.Goal.dfy", result.Generator!.Path);
    Assert.Contains("function Seed(): int { 2 }", result.Generator.Content);
    Assert.Contains("x := Seed();", result.Generator.Content);
    Assert.Contains("ensures (x >= 0)", result.Generator.Content);
    Assert.Contains("ensures x == 2", result.Generator.Content);
    Assert.Equal(result.Generator.Sha256, ContractHarnessBuilder.Hash(result.Generator.Content));
  }

  // Editing an original contract outside a native authoring region is rejected before packet extraction.
  [Fact]
  public async Task RejectsOriginalContractEdit() {
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare));
    var authored = prepared.Sources!.Select(source => source.Path == "M.dfy"
      ? Snapshot(source.Path, source.Content.Replace("ensures y == x + 1", "ensures y >= x", StringComparison.Ordinal))
      : source).ToArray();

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Run(
      Request(ContractRuntimeAuthoringAction.Extract) with {
        AuthoredSources = authored,
        Manifest = prepared.Manifest
      }));

    Assert.Contains("signature, contract", error.Message);
  }

  // Automatic generator admission postconditions remain fixed outside the editable generator body.
  [Fact]
  public async Task RejectsGeneratorContractEdit() {
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare));
    var authored = prepared.Sources!.Select(source => source.Path == "M.dfy"
      ? Snapshot(source.Path, ReplaceAfter(source.Content, "method {:pbt_generator",
        "ensures (x >= 0)", "ensures true")) : source).ToArray();

    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Run(
      Request(ContractRuntimeAuthoringAction.Extract) with {
        AuthoredSources = authored,
        Manifest = prepared.Manifest
      }));

    Assert.Contains("signature, contract", error.Message);
  }

  // An untouched TODO view is preparation feedback and never yields reusable campaign packets.
  [Fact]
  public async Task UnfilledTemplatesReturnUnsupportedWithoutPackets() {
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare));

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract) with {
      AuthoredSources = prepared.Sources,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Unsupported, result.Status);
    Assert.Null(result.Drafts);
    Assert.Null(result.Generator);
    Assert.Contains("M.Helper", result.Reason);
    Assert.Contains("M.Goal", result.Reason);
  }

  // A concrete source body takes precedence and is not exposed as an editable draft region.
  [Fact]
  public async Task ConcreteBodyTakesPrecedenceOverRequestedDraft() {
    var source = Source.Replace("assert false;", "y := x + 1;", StringComparison.Ordinal);
    var result = await Run(Request(ContractRuntimeAuthoringAction.Prepare, source));

    Assert.Empty(result.Manifest!.DraftSymbols);
    var view = Assert.Single(result.Sources!, item => item.Path == "M.dfy").Content;
    Assert.Contains("y := x + 1;", view);
    Assert.DoesNotContain("draft-body", view, StringComparison.Ordinal);
  }

  // Inherited packet bodies survive refresh while native extraction restores the original callable contract.
  [Fact]
  public async Task InheritedDraftCannotReplaceOriginalContract() {
    const string inherited =
      "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) ensures y == 0 { y := x + 1; }\n";
    var draft = new ContractRuntimeDraft("M.Helper", ".top-down-pbt/drafts/M.Helper.dfy",
      inherited, ContractHarnessBuilder.Hash(inherited));
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare) with { Drafts = [draft] });
    var authored = prepared.Sources!.Select(source => source.Path == "M.dfy"
      ? Snapshot(source.Path, ReplaceTodoAfter(source.Content, "method {:pbt_generator", "x := 0;"))
      : source).ToArray();

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract) with {
      Drafts = [draft],
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    var extracted = Assert.Single(result.Drafts!);
    Assert.Contains("ensures y == x + 1", extracted.Content);
    Assert.DoesNotContain("ensures y == 0", extracted.Content, StringComparison.Ordinal);
    Assert.Contains("y := x + 1;", extracted.Content);
  }

  // A legal source identifier sharing the TODO prefix cannot impersonate the exact generated placeholder.
  [Fact]
  public async Task ExactPlaceholderDoesNotRejectOriginalPrefixIdentifier() {
    const string source = "module M { " +
      "predicate PbtAuthoringTODO_Predicate(x: int) { x >= 0 } " +
      "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } " +
      "method Goal(x: int) returns (y: int) requires PbtAuthoringTODO_Predicate(x) " +
      "ensures y == x + 1 { y := Helper(x); } }";
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare, source));
    var authored = prepared.Sources!.Select(snapshot => snapshot.Path == "M.dfy"
      ? Snapshot(snapshot.Path, Author(snapshot.Content)) : snapshot).ToArray();

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract, source) with {
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Contains("PbtAuthoringTODO_Predicate", result.Generator!.Content);
  }

  // Authoring requests reject resolver aliases so manifest symbols stay canonical across the wire.
  [Fact]
  public async Task RejectsNoncanonicalRequestedDraftAlias() {
    var error = await Assert.ThrowsAsync<NotSupportedException>(() => Run(
      Request(ContractRuntimeAuthoringAction.Prepare) with {
        RequestedDraftSymbols = ["_module.M.Helper"]
      }));

    Assert.Contains("identify one callable", error.Message);
  }

  // UTF-8 spans preserve unrelated Unicode source while authored Unicode remains inside the extracted body.
  [Fact]
  public async Task UnicodeBodyExtractionPreservesOutsideSourceBytes() {
    const string source = "// 앞쪽 한글\nmodule M { " +
      "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } " +
      "method Goal(x: int) returns (y: int) ensures y == x + 1 { /* 목표 */ y := Helper(x); } }";
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare, source));
    var authored = prepared.Sources!.Select(snapshot => snapshot.Path == "M.dfy"
      ? Snapshot(snapshot.Path, Author(snapshot.Content).Replace("y := x + 1;", "// 본문\ny := x + 1;",
        StringComparison.Ordinal)) : snapshot).ToArray();

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract, source) with {
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Contains("// 본문", Assert.Single(result.Drafts!).Content);
    Assert.Contains("// 앞쪽 한글", Assert.Single(prepared.Sources!, item => item.Path == "M.dfy").Content);
    Assert.Contains("/* 목표 */", Assert.Single(prepared.Sources!, item => item.Path == "M.dfy").Content);
  }

  // Instance draft bodies remain class members while draft helpers and the generator occupy the enclosing module.
  [Fact]
  public async Task InstanceDraftKeepsClassPositionAndModuleHelpers() {
    const string source = "module M { class C { " +
      "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } " +
      "method Goal(x: int) returns (y: int) ensures y == x + 1 { y := Helper(x); } } }";
    var request = new ContractRuntimeAuthoringRequest(1, ContractRuntimeAuthoringAction.Prepare,
      [Snapshot("M.dfy", source)], new("M.C.Goal"), RequestedDraftSymbols: ["M.C.Helper"]);
    var prepared = await Run(request);
    var view = Assert.Single(prepared.Sources!, item => item.Path == "M.dfy").Content;
    var helper = view.IndexOf("method Helper", StringComparison.Ordinal);
    Assert.True(view.IndexOf("-body-begin */", helper, StringComparison.Ordinal) > helper);
    Assert.True(view.IndexOf("method {:pbt_generator", StringComparison.Ordinal) <
      view.IndexOf("class C", StringComparison.Ordinal));
    var authoredText = ReplaceTodoAfter(view, "method {:pbt_generator",
      "receiver := new C; x := DraftSeed();");
    authoredText = ReplaceTodoAfter(authoredText, "method Helper", "y := x + 1;");
    authoredText = InsertBeforeFirstDraftHelperEnd(authoredText, "function DraftSeed(): int { 0 }\n");
    var authored = prepared.Sources!.Select(snapshot => snapshot.Path == "M.dfy"
      ? Snapshot(snapshot.Path, authoredText) : snapshot).ToArray();

    var result = await Run(request with {
      Action = ContractRuntimeAuthoringAction.Extract,
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Contains("function DraftSeed(): int", Assert.Single(result.Drafts!).Content);
    Assert.Contains("returns (receiver: C, x: int)", result.Generator!.Content);
  }

  // Default-module goals use the same prepare/extract path without a synthetic named-module import.
  [Fact]
  public async Task DefaultModulePrepareAndExtract() {
    const string source = "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; } " +
      "method Goal(x: int) returns (y: int) ensures y == x + 1 { y := Helper(x); }";
    var request = new ContractRuntimeAuthoringRequest(1, ContractRuntimeAuthoringAction.Prepare,
      [Snapshot("Default.dfy", source)], new("Goal"), RequestedDraftSymbols: ["Helper"]);
    var prepared = await Run(request);
    var view = Assert.Single(prepared.Sources!, item => item.Path == "Default.dfy").Content;
    Assert.DoesNotContain("import PbtRandom", view, StringComparison.Ordinal);
    var authoredText = ReplaceTodoAfter(view, "method {:pbt_generator", "x := 0;");
    authoredText = ReplaceTodoAfter(authoredText, "method Helper", "y := x + 1;");
    var authored = prepared.Sources!.Select(snapshot => snapshot.Path == "Default.dfy"
      ? Snapshot(snapshot.Path, authoredText) : snapshot).ToArray();

    var result = await Run(request with {
      Action = ContractRuntimeAuthoringAction.Extract,
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Equal("Helper", Assert.Single(result.Drafts!).Symbol);
  }

  // Existing generator and marker-prefix names force fresh native names without confusing region discovery.
  [Fact]
  public async Task ExistingGeneratorAndMarkerPrefixNamesRemainDistinct() {
    const string source = "module M {\n" +
      "datatype PbtAuthoringBegin_collision = PbtAuthoringBegin_collision\n" +
      "method Generate() {}\n" +
      "method Helper(x: int) returns (y: int) ensures y == x + 1 { assert false; }\n" +
      "method Goal(x: int) returns (y: int) ensures y == x + 1 { y := Helper(x); }\n}";
    var prepared = await Run(Request(ContractRuntimeAuthoringAction.Prepare, source));
    var view = Assert.Single(prepared.Sources!, item => item.Path == "M.dfy").Content;
    Assert.Contains("method {:pbt_generator \"M.Goal\"} Generate0", view);
    var authored = prepared.Sources!.Select(snapshot => snapshot.Path == "M.dfy"
      ? Snapshot(snapshot.Path, Author(snapshot.Content)) : snapshot).ToArray();

    var result = await Run(Request(ContractRuntimeAuthoringAction.Extract, source) with {
      AuthoredSources = authored,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Contains("Generate0", result.Generator!.Content);
  }

  // Exact generated sentinel text in completed inherited packet comments is ordinary authored content.
  [Fact]
  public async Task InheritedPacketsMayMentionExactTemplateSentinels() {
    var template = await Run(Request(ContractRuntimeAuthoringAction.Prepare));
    var view = Assert.Single(template.Sources!, item => item.Path == "M.dfy").Content;
    var draftTodo = TodoAfter(view, "method Helper");
    var generatorTodo = TodoAfter(view, "method {:pbt_generator");
    var draftContent = "method {:pbt_draft \"M.Helper\"} Helper(x: int) returns (y: int) " +
      "ensures y == x + 1 { y := x + 1; // " + draftTodo + "\n}\n";
    var generatorContent = "method {:pbt_generator \"M.Goal\"} Generate(r: PbtRandom.Source) " +
      "returns (x: int) { x := 0; // " + generatorTodo + "\n}\n";
    var request = Request(ContractRuntimeAuthoringAction.Prepare) with {
      Drafts = [new("M.Helper", ".top-down-pbt/drafts/M.Helper.dfy", draftContent,
        ContractHarnessBuilder.Hash(draftContent))],
      Generator = Snapshot(".top-down-pbt/generators/M.Goal.dfy", generatorContent)
    };
    var prepared = await Run(request);

    var result = await Run(request with {
      Action = ContractRuntimeAuthoringAction.Extract,
      AuthoredSources = prepared.Sources,
      Manifest = prepared.Manifest
    });

    Assert.Equal(ContractRuntimeAuthoringStatus.Extracted, result.Status);
    Assert.Contains(draftTodo, Assert.Single(result.Drafts!).Content);
    Assert.Contains(generatorTodo, result.Generator!.Content);
  }

  // The additive DTO remains strict camel-case JSON with an echoed action and typed status.
  [Fact]
  public void AuthoringResultUsesTheSharedJsonContract() {
    var json = JsonSerializer.Serialize(new ContractRuntimeAuthoringResult(1,
      ContractRuntimeAuthoringAction.Prepare, ContractRuntimeAuthoringStatus.Ready, "ready"),
      ContractJson.Options);

    Assert.Contains("\"schemaVersion\":1", json);
    Assert.Contains("\"action\":\"prepare\"", json);
    Assert.Contains("\"status\":\"ready\"", json);
  }

  private static string Author(string content) {
    content = ReplaceTodoAfter(content, "method {:pbt_generator", "x := Seed();");
    content = ReplaceTodoAfter(content, "method Helper", "y := x + 1;");
    var contracts = content.IndexOf("-contracts-begin */", StringComparison.Ordinal);
    Assert.True(contracts >= 0);
    content = content.Insert(contracts + "-contracts-begin */".Length, "\nensures x == 2\n");
    var generator = content.IndexOf("method {:pbt_generator", StringComparison.Ordinal);
    var boundary = content.IndexOf("datatype PbtAuthoringEnd_", generator, StringComparison.Ordinal);
    Assert.True(boundary > generator);
    return content.Insert(boundary, "function Seed(): int { 2 }\n");
  }

  private static string ReplaceTodoAfter(string content, string declaration, string replacement) {
    var owner = content.IndexOf(declaration, StringComparison.Ordinal);
    Assert.True(owner >= 0);
    var body = content.IndexOf("-body-begin */", owner, StringComparison.Ordinal);
    var start = content.IndexOf("PbtAuthoringTODO_", body, StringComparison.Ordinal);
    var end = content.IndexOf("();", start, StringComparison.Ordinal);
    Assert.True(body >= 0 && start >= 0 && end > start);
    return content[..start] + replacement + content[(end + 3)..];
  }

  private static string TodoAfter(string content, string declaration) {
    var owner = content.IndexOf(declaration, StringComparison.Ordinal);
    var body = content.IndexOf("-body-begin */", owner, StringComparison.Ordinal);
    var start = content.IndexOf("PbtAuthoringTODO_", body, StringComparison.Ordinal);
    var end = content.IndexOf("()", start, StringComparison.Ordinal);
    Assert.True(owner >= 0 && body >= 0 && start >= 0 && end > start);
    return content[start..end];
  }

  private static string ReplaceAfter(string content, string ownerText, string oldText, string newText) {
    var owner = content.IndexOf(ownerText, StringComparison.Ordinal);
    var start = content.IndexOf(oldText, owner, StringComparison.Ordinal);
    Assert.True(owner >= 0 && start >= 0);
    return content[..start] + newText + content[(start + oldText.Length)..];
  }

  private static string InsertBeforeFirstDraftHelperEnd(string content, string declaration) {
    var boundary = content.IndexOf("datatype PbtAuthoringEnd_", 0, StringComparison.Ordinal);
    Assert.True(boundary >= 0);
    return content.Insert(boundary, declaration);
  }

  private static ContractRuntimeAuthoringRequest Request(ContractRuntimeAuthoringAction action,
    string source = Source) => new(1, action, [Snapshot("M.dfy", source)], new("M.Goal"),
      RequestedDraftSymbols: ["M.Helper"], TimeoutMilliseconds: 30000);

  private static ContractSource Snapshot(string path, string content) =>
    new(path, content, ContractHarnessBuilder.Hash(content));

  private static async Task<ContractRuntimeAuthoringResult> Run(ContractRuntimeAuthoringRequest request) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    options.DisableScopes = true;
    return await ContractRuntimeSourceAuthoring.RunAsync(request, options, CancellationToken.None);
  }
}
