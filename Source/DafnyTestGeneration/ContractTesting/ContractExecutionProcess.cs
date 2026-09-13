using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractProcessResult(int? ExitCode, string StandardOutput, string StandardError, bool Cancelled);

public static class ContractExecutionProcess {
  public static async Task<ContractProcessResult> RunAsync(string executable, IEnumerable<string> arguments,
    string workingDirectory, CancellationToken cancellationToken) {
    var start = new ProcessStartInfo(executable) {
      WorkingDirectory = workingDirectory,
      UseShellExecute = false,
      RedirectStandardOutput = true,
      RedirectStandardError = true
    };
    foreach (var argument in arguments) {
      start.ArgumentList.Add(argument);
    }
    using var process = new Process { StartInfo = start };
    process.Start();
    var stdout = process.StandardOutput.ReadToEndAsync();
    var stderr = process.StandardError.ReadToEndAsync();
    var cancelled = false;
    try {
      await process.WaitForExitAsync(cancellationToken);
    } catch (OperationCanceledException) when (cancellationToken.IsCancellationRequested) {
      cancelled = true;
      // Compilation can itself launch dotnet and compiler children. Reap the entire tree.
      if (!process.HasExited) {
        process.Kill(entireProcessTree: true);
      }
      await process.WaitForExitAsync(CancellationToken.None);
    }
    return new ContractProcessResult(cancelled ? null : process.ExitCode, await stdout, await stderr, cancelled);
  }
}
