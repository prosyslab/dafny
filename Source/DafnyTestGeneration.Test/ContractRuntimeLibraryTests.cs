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
  // SHA-256 values of the Dafny text pinned after the Runtime/Smt role renaming; changing either file changes source-set hashes.
  private const string DafnySourceSha256 = "b858e89cca9f646e394eb5049cc3b1e481a6c4a07ca8bbfc269cfbbfa335aaa0";
  private const string RuntimeDeclarationSha256 = "5d179a05858cd3389ac0d69cdf45ec80f530e3b1cd9418e7cf86ad7a813ae0be";

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

  // The native observation declaration resolves without any task source.
  [Fact]
  public async Task ObservationDeclarationResolvesStandalone() {
    await AssertResolves("PbtObservation.dfy", ContractRuntimeLibrary.Read("PbtObservation.dfy"));
  }

  // The native SMT declaration resolves without any task source.
  [Fact]
  public async Task SmtDeclarationResolvesStandalone() {
    await AssertResolves("PbtSmt.dfy", ContractRuntimeLibrary.Read("PbtSmt.dfy"));
  }

  // The checked-in runtime declarations keep the exact snapshot text that reaches proof hashes.
  [Fact]
  public void DafnySourceMatchesTheHashPin() {
    Assert.Equal(DafnySourceSha256, Sha256(ContractRuntimeInstrumentation.DafnySource));
  }

  // The observation and SMT declarations inserted into each source module keep their pinned text, including the leading line feeds.
  [Fact]
  public void RuntimeDeclarationMatchesTheHashPin() {
    Assert.Equal(RuntimeDeclarationSha256, Sha256("\n" + ContractRuntimeLibrary.Read("PbtObservation.dfy") +
      "\n" + ContractRuntimeLibrary.Read("PbtSmt.dfy")));
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
    var program = await Utils.Parse(reporter, source, uri: new Uri("file:///tmp/contract-library-config.dfy"));
    Assert.Equal(0, reporter.ErrorCount);
    var request = new ContractTestRequest(1, [new("/tmp/contract-library-config.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("Entry"), new Dictionary<string, ContractValue> { ["x"] = new(ContractValueKind.Integer, "6") });
    var prepared = ContractHarnessBuilder.Prepare(program, request);
    var runtime = ContractStubRuntime.RuntimeSource("/tmp/o\"b\\s/é.jsonl", prepared, runtimeReferences: true);
    Assert.Contains("internal const string ObservationPath = \"/tmp/o\\u0022b\\\\s/\\u00E9.jsonl\";", runtime);
    Assert.Contains("internal const bool RuntimeReferences = true;", runtime);
    Assert.StartsWith(ContractRuntimeLibrary.Read("PbtObservation.cs"), runtime);
  }
}
