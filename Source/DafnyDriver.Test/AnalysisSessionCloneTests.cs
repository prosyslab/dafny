using System.Text.Json;
using System.Threading.Channels;
using Microsoft.Dafny;
using Xunit;

namespace DafnyDriver.Test;

[Collection("Proof input translation")]
public class AnalysisSessionCloneTests {
  private const string Path = "/workspace/in-memory-session/Clone.dfy";
  private const string Source = "module Clone { method Original() {} }";

  private static AnalysisSessionCommand.Request Analyze(string branch = "default", string source = Source) =>
    new("analysis-" + branch, ["definition-analysis", "--spans-only", Path], "/workspace",
      "role-context", new Dictionary<string, string> { [Path] = source }, SessionId: branch);

  private static JsonElement Evidence(AnalysisSessionCommand.Response response) =>
    JsonSerializer.SerializeToElement(response.NativeEvidence, AnalysisSessionCommand.JsonOptions);

  private static async Task<AnalysisSessionCommand.CloneReceipt> Clone(AnalysisSessionCommand.SessionRegistry registry,
    string target, string parent = "default") {
    var response = await registry.Execute(new AnalysisSessionCommand.Request("clone-" + target,
      Operation: "clone", TargetId: target, SessionId: parent), CancellationToken.None);
    Assert.True(response.Returncode == 0, response.Stderr);
    Assert.Null(response.NativeEvidence);
    return JsonSerializer.Deserialize<AnalysisSessionCommand.CloneReceipt>(response.Stdout, AnalysisSessionCommand.JsonOptions)!;
  }

  // A retained parent can create two children with copied parser seeds and distinct branch epochs.
  [Fact]
  public async Task ParentCreatesTwoIndependentWarmChildren() {
    await using var registry = new AnalysisSessionCommand.SessionRegistry();
    var parent = await registry.Execute(Analyze(), CancellationToken.None);
    Assert.True(parent.Returncode == 0, parent.Stderr);
    var first = await Clone(registry, "first");
    var second = await Clone(registry, "second");
    Assert.True(first.ParsedEntries > 0);
    Assert.Equal(first.ParsedEntries, second.ParsedEntries);
    Assert.Equal(0, first.VerificationEntries);
    Assert.Equal(1, first.SchemaVersion);
    Assert.Equal(first.DaemonEpoch, second.DaemonEpoch);
    Assert.Equal(Evidence(parent).GetProperty("sessionEpoch").GetString(), first.ParentEpoch);
    Assert.NotEqual(first.SessionEpoch, second.SessionEpoch);
    Assert.NotEqual(first.ParentEpoch, first.SessionEpoch);
    var child = await registry.Execute(Analyze("first"), CancellationToken.None);
    Assert.True(child.Returncode == 0, child.Stderr);
    Assert.Equal(parent.Stdout, child.Stdout);
    Assert.Equal(first.SessionEpoch, Evidence(child).GetProperty("sessionEpoch").GetString());
    Assert.Equal("first", Evidence(child).GetProperty("sessionId").GetString());
    Assert.Equal("role-context", Evidence(child).GetProperty("contextId").GetString());
  }

  // Closing the parent leaves both child cache owners usable and child edits stay local.
  [Fact]
  public async Task ParentClosureAndChildEditsPreserveSibling() {
    await using var registry = new AnalysisSessionCommand.SessionRegistry();
    var original = await registry.Execute(Analyze(), CancellationToken.None);
    Assert.True(original.Returncode == 0, original.Stderr);
    await Clone(registry, "first");
    await Clone(registry, "second");
    var close = await registry.Execute(new AnalysisSessionCommand.Request("close-parent", Operation: "close-session"),
      CancellationToken.None);
    Assert.Equal(0, close.Returncode);
    Assert.Null(close.NativeEvidence);
    var changed = await registry.Execute(Analyze("first", "module Clone { method Changed() {} }"), CancellationToken.None);
    Assert.True(changed.Returncode == 0, changed.Stderr);
    var sibling = await registry.Execute(Analyze("second"), CancellationToken.None);
    Assert.True(sibling.Returncode == 0, sibling.Stderr);
    Assert.Equal(original.Stdout, sibling.Stdout);
    Assert.NotEqual(changed.Stdout, sibling.Stdout);
    Assert.NotEqual(0, (await registry.Execute(Analyze(), CancellationToken.None)).Returncode);
  }

  // A cancelled clone removes its reservation so a later clone can use the same target.
  [Fact]
  public async Task CancelledCloneCleansPartialTarget() {
    await using var registry = new AnalysisSessionCommand.SessionRegistry();
    using var cancellation = new CancellationTokenSource();
    await cancellation.CancelAsync();
    var cancelled = await registry.Execute(new AnalysisSessionCommand.Request("cancelled-clone",
      Operation: "clone", TargetId: "retry"), cancellation.Token);
    Assert.Equal(130, cancelled.Returncode);
    Assert.Null(cancelled.NativeEvidence);
    var receipt = await Clone(registry, "retry");
    Assert.Equal("retry", receipt.SessionId);
  }

  // Invalid controls fail explicitly and cannot replace an existing child.
  [Fact]
  public async Task DuplicateAndUnknownCloneControlsFailExplicitly() {
    await using var registry = new AnalysisSessionCommand.SessionRegistry();
    var child = await Clone(registry, "child");
    var duplicate = await registry.Execute(new AnalysisSessionCommand.Request("duplicate", Operation: "clone", TargetId: "child"),
      CancellationToken.None);
    Assert.NotEqual(0, duplicate.Returncode);
    Assert.Null(duplicate.NativeEvidence);
    var unsupported = await registry.Execute(new AnalysisSessionCommand.Request("unknown", Operation: "adopt"),
      CancellationToken.None);
    Assert.Equal(7, unsupported.Returncode);
    Assert.Contains("DAFNY_SESSION_UNSUPPORTED", unsupported.Stderr);
    Assert.Null(unsupported.NativeEvidence);
    var grandchild = await Clone(registry, "grandchild", "child");
    Assert.Equal(child.SessionEpoch, grandchild.ParentEpoch);
  }

  // A branch-scoped cancellation cannot cancel a sibling's active request with the same target ID.
  [Fact]
  public async Task ProtocolCancellationChecksTheOwningBranch() {
    using var input = new ProtocolReader();
    using var output = new ProtocolWriter();
    var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
    var cancelled = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
    var protocol = AnalysisSessionCommand.RunProtocol(new DafnyOptions(input, TextWriter.Null, TextWriter.Null), output,
      async (request, token) => {
        started.TrySetResult();
        using var registration = token.Register(() => cancelled.TrySetResult());
        try {
          await Task.Delay(Timeout.InfiniteTimeSpan, token);
          throw new InvalidOperationException("The bounded fake job must be cancelled.");
        } catch (OperationCanceledException) {
          return new AnalysisSessionCommand.Response(request.Id, 130, "", "cancelled", null);
        }
      });
    input.Send(new AnalysisSessionCommand.Request("job", SessionId: "first"));
    await started.Task.WaitAsync(TimeSpan.FromSeconds(5));
    input.Send(new AnalysisSessionCommand.Request("wrong-cancel", Operation: "cancel", TargetId: "job", SessionId: "second"));
    Assert.Equal("wrong-cancel", (await output.Next()).Id);
    Assert.False(cancelled.Task.IsCompleted);
    input.Send(new AnalysisSessionCommand.Request("right-cancel", Operation: "cancel", TargetId: "job", SessionId: "first"));
    await cancelled.Task.WaitAsync(TimeSpan.FromSeconds(5));
    var replies = new[] { await output.Next(), await output.Next() };
    Assert.Contains(replies, response => response.Id == "job" && response.Returncode == 130);
    Assert.Contains(replies, response => response.Id == "right-cancel" && response.Returncode == 0);
    input.Send(new AnalysisSessionCommand.Request("shutdown", Operation: "shutdown"));
    Assert.Equal("shutdown", (await output.Next()).Id);
    Assert.Equal(0, await protocol.WaitAsync(TimeSpan.FromSeconds(5)));
  }

  // The response frame bound is exact on the JSON line: at the limit passes, one byte more is a clean code-6 reply.
  [Fact]
  public async Task ProtocolRejectsOnlyResponsesAboveTheLimit() {
    Assert.Equal(128 * 1024 * 1024, AnalysisSessionCommand.ResponseLimit);
    const int limit = 4096;
    int Size(AnalysisSessionCommand.Response response) =>
      System.Text.Encoding.UTF8.GetByteCount(JsonSerializer.Serialize(response, AnalysisSessionCommand.JsonOptions));
    var baseSize = Size(new AnalysisSessionCommand.Response("fit", 0, "", "", null));
    using var input = new ProtocolReader();
    using var output = new ProtocolWriter();
    var protocol = AnalysisSessionCommand.RunProtocol(new DafnyOptions(input, TextWriter.Null, TextWriter.Null), output,
      (request, _) => Task.FromResult(new AnalysisSessionCommand.Response(request.Id, 0,
        new string('x', limit - baseSize + (request.Id == "over" ? 1 : 0)), "", null)), limit);
    input.Send(new AnalysisSessionCommand.Request("fit"));
    var fit = await output.Next();
    Assert.Equal(0, fit.Returncode);
    Assert.Equal(limit, Size(fit));
    input.Send(new AnalysisSessionCommand.Request("over"));
    var over = await output.Next();
    Assert.Equal("over", over.Id);
    Assert.Equal(6, over.Returncode);
    Assert.Equal("", over.Stdout);
    Assert.Contains("exceeds the output limit", over.Stderr);
    input.Send(new AnalysisSessionCommand.Request("shutdown", Operation: "shutdown"));
    Assert.Equal("shutdown", (await output.Next()).Id);
    Assert.Equal(0, await protocol.WaitAsync(TimeSpan.FromSeconds(5)));
  }

  // A bounded close-control slot remains available when all eight normal job slots are occupied.
  [Fact]
  public async Task ProtocolAdmitsCloseAtNormalRequestCapacity() {
    using var input = new ProtocolReader();
    using var output = new ProtocolWriter();
    var active = 0;
    var full = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
    var protocol = AnalysisSessionCommand.RunProtocol(new DafnyOptions(input, TextWriter.Null, TextWriter.Null), output,
      async (request, token) => {
        if (request.Operation == "close-session") {
          return new AnalysisSessionCommand.Response(request.Id, 0, "", "", null);
        }
        if (Interlocked.Increment(ref active) == 8) {
          full.TrySetResult();
        }
        try {
          await Task.Delay(Timeout.InfiniteTimeSpan, token);
          throw new InvalidOperationException("The bounded fake job must be cancelled.");
        } catch (OperationCanceledException) {
          return new AnalysisSessionCommand.Response(request.Id, 130, "", "cancelled", null);
        }
      });
    for (var index = 0; index < 8; index++) {
      input.Send(new AnalysisSessionCommand.Request("job" + index));
    }
    await full.Task.WaitAsync(TimeSpan.FromSeconds(5));
    input.Send(new AnalysisSessionCommand.Request("close", Operation: "close-session"));
    var close = await output.Next();
    Assert.Equal("close", close.Id);
    Assert.Equal(0, close.Returncode);
    input.Send(new AnalysisSessionCommand.Request("shutdown", Operation: "shutdown"));
    var replies = new List<AnalysisSessionCommand.Response>();
    for (var index = 0; index < 9; index++) {
      replies.Add(await output.Next());
    }
    Assert.Equal(8, replies.Count(response => response.Returncode == 130));
    Assert.Contains(replies, response => response.Id == "shutdown" && response.Returncode == 0);
    Assert.Equal(0, await protocol.WaitAsync(TimeSpan.FromSeconds(5)));
  }

  private sealed class ProtocolReader : TextReader {
    private readonly Channel<char> characters = Channel.CreateUnbounded<char>();
    public void Send(AnalysisSessionCommand.Request request) {
      foreach (var character in JsonSerializer.Serialize(request, AnalysisSessionCommand.JsonOptions) + "\n") {
        Assert.True(characters.Writer.TryWrite(character));
      }
    }
    public override async Task<int> ReadAsync(char[] buffer, int index, int count) {
      buffer[index] = await characters.Reader.ReadAsync();
      return 1;
    }
  }

  private sealed class ProtocolWriter : StringWriter {
    private readonly Channel<AnalysisSessionCommand.Response> responses = Channel.CreateUnbounded<AnalysisSessionCommand.Response>();
    public override Task WriteLineAsync(string? value) {
      Assert.True(responses.Writer.TryWrite(JsonSerializer.Deserialize<AnalysisSessionCommand.Response>(value!,
        AnalysisSessionCommand.JsonOptions)!));
      return Task.CompletedTask;
    }
    public async Task<AnalysisSessionCommand.Response> Next() =>
      await responses.Reader.ReadAsync().AsTask().WaitAsync(TimeSpan.FromSeconds(5));
  }
}
