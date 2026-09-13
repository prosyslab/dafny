using System;
using System.IO;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;
using System.Collections.Generic;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractExecutionTests {
  // Malformed external source arrays fail validation before a worker can dereference them.
  [Fact]
  public void NullSourceSnapshotIsRejected() {
    var request = new ContractTestRequest(1, [null!], new ContractEntry("Entry"), new Dictionary<string, ContractValue>());
    Assert.Throws<ArgumentException>(() => ContractHarnessBuilder.ValidateRequest(request));
  }

  // Cancelling a running execution reaps the child and preserves cancellation as a distinct outcome.
  [Fact]
  public async Task CancelledProcessIsReaped() {
    if (OperatingSystem.IsWindows()) {
      return;
    }
    using var cancellation = new CancellationTokenSource(TimeSpan.FromMilliseconds(150));
    var result = await ContractExecutionProcess.RunAsync("/bin/sh", ["-c", "sleep 30 & echo $!; wait"], Path.GetTempPath(), cancellation.Token);
    Assert.True(result.Cancelled);
    Assert.Null(result.ExitCode);
    var childId = int.Parse(result.StandardOutput.Trim());
    Assert.DoesNotContain(Process.GetProcesses(), process => process.Id == childId && !process.HasExited);
  }

  // Runtime stdout is captured separately from protocol files and is not parsed as a result.
  [Fact]
  public async Task ProcessOutputRemainsPlainOutput() {
    if (OperatingSystem.IsWindows()) {
      return;
    }
    var result = await ContractExecutionProcess.RunAsync("/bin/sh", ["-c", "printf '{not protocol}'"], Path.GetTempPath(), CancellationToken.None);
    Assert.Equal(0, result.ExitCode);
    Assert.Equal("{not protocol}", result.StandardOutput);
  }
}
