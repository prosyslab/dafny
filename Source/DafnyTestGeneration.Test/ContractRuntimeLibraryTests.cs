#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;
using Microsoft.Dafny;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractRuntimeLibraryTests {
  // SHA-256 of the Dafny text pinned after the Runtime/Smt role renaming; changing the file changes source-set hashes.
  private const string DafnySourceSha256 = "b858e89cca9f646e394eb5049cc3b1e481a6c4a07ca8bbfc269cfbbfa335aaa0";

  private static string Sha256(string text) => Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(text))).ToLowerInvariant();

  private static async Task AssertResolves(string path, string content) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    _ = await ContractSourceSnapshot.ParseAsync(reporter, [new(path, content, ContractHarnessBuilder.Hash(content))], CancellationToken.None);
    Assert.True(reporter.ErrorCount == 0, string.Join("\n", reporter.AllMessages.Select(message => message.Message)));
  }

  // The random-stream and runtime-check declarations resolve without any task source.
  [Fact]
  public async Task PbtRuntimeResolvesStandalone() {
    await AssertResolves("PbtRuntime.dfy", ContractRuntimeLibrary.Read("PbtRuntime.dfy"));
  }

  // The checked-in runtime declarations keep the exact snapshot text that reaches proof hashes.
  [Fact]
  public void DafnySourceMatchesTheHashPin() {
    Assert.Equal(DafnySourceSha256, Sha256(ContractRuntimeInstrumentation.DafnySource));
  }

  // A resource name outside the library fails loudly instead of yielding empty text.
  [Fact]
  public void MissingResourceFails() {
    Assert.Throws<InvalidOperationException>(() => ContractRuntimeLibrary.Read("Missing.dfy"));
  }

  // Task-specific configuration literals stay valid C# for an observation path with a quote, backslash and non-ASCII character.
  [Fact]
  public async Task ConfigurationEscapesObservationPath() {
    const string source = "method Entry(x:int) returns(r:int) { r := x; }";
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();
    var reporter = new BatchErrorReporter(options);
    var snapshot = new ContractSource("/tmp/contract-library-config.dfy", source, ContractHarnessBuilder.Hash(source));
    var program = await ContractSourceSnapshot.ParseAsync(reporter, [snapshot], CancellationToken.None);
    Assert.Equal(0, reporter.ErrorCount);
    var goal = ContractCallableSelector.SelectMethod(program, new("Entry"), requireConcreteReceiver: false);
    var prepared = new ContractPreparedProgram(program, goal, snapshot,
      new(snapshot.Path, goal.Origin.line, goal.Origin.col, goal.FullDafnyName, snapshot.Sha256), Sources: [snapshot]);
    var runtime = ContractRuntimeInstrumentation.RuntimeSource("/tmp/o\"b\\s/é.jsonl",
      new ContractRuntimeTransformation([snapshot], [], [], "Entry", prepared, new HashSet<Field>()));
    Assert.Contains("internal const string ObservationPath = \"/tmp/o\\u0022b\\\\s/\\u00E9.jsonl.legacy\";", runtime);
    Assert.Contains("internal const bool RuntimeReferences = true;", runtime);
    Assert.StartsWith(ContractRuntimeLibrary.Read("PbtObservation.cs"), runtime);
  }
}
