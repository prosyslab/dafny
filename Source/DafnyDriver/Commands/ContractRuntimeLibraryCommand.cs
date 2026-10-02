#nullable enable
using System.CommandLine;
using System.CommandLine.Invocation;
using System.Text;
using System.Threading.Tasks;
using DafnyTestGeneration.ContractTesting;

namespace Microsoft.Dafny;

static class ContractRuntimeLibraryCommand {
  public static Command Create() {
    var command = new Command(
      "contract-runtime-library",
      "Print the PbtRuntime.dfy generator API embedded in this Dafny build.");
    foreach (var option in DafnyCommands.ConsoleOutputOptions) {
      command.AddOption(option);
    }

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(command, Execute);
    return command;
  }

  private static async Task<int> Execute(DafnyOptions options, InvocationContext context) {
    var bytes = new UTF8Encoding(false).GetBytes(ContractRuntimeLibrary.Read("PbtRuntime.dfy"));
    using var output = System.Console.OpenStandardOutput();
    await output.WriteAsync(bytes);
    await output.FlushAsync();
    return (int)ExitValue.SUCCESS;
  }
}
