using System.Diagnostics;
using System.Reflection;
using System.Security.Cryptography;
using DafnyTestGeneration.ContractTesting;

namespace DafnyDriver.Test;

public class ContractRuntimeLibraryCommandTests {
  // Hash of the Dafny text without its final line feed, equal to the pin in ContractRuntimeLibraryTests.
  private const string DafnySourceSha256 = "b858e89cca9f646e394eb5049cc3b1e481a6c4a07ca8bbfc269cfbbfa335aaa0";

  // The command writes the embedded runtime library byte-for-byte and exits successfully.
  [Fact]
  public async Task PrintsEmbeddedRuntimeLibraryBytes() {
    var dafnyBinary = Path.Join(Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location), "DafnyDriver.dll");
    var info = new ProcessStartInfo("dotnet", dafnyBinary + " contract-runtime-library") {
      RedirectStandardOutput = true,
      RedirectStandardError = true,
      UseShellExecute = false
    };
    using var process = Process.Start(info)!;
    using var output = new MemoryStream();
    var copy = process.StandardOutput.BaseStream.CopyToAsync(output);
    var error = await process.StandardError.ReadToEndAsync();
    await copy;
    await process.WaitForExitAsync();

    Assert.True(process.ExitCode == 0, error);
    var bytes = output.ToArray();
    Assert.Equal(new System.Text.UTF8Encoding(false).GetBytes(ContractRuntimeLibrary.Read("PbtRuntime.dfy")), bytes);
    Assert.Equal(DafnySourceSha256, Convert.ToHexString(SHA256.HashData(bytes[..^1])).ToLowerInvariant());
  }
}
