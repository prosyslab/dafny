using System.Threading;
using System.Threading.Tasks;

namespace DafnyTestGeneration.ContractTesting;

public interface IContractProgramCompiler {
  Task<ContractCompileResult> CompileAsync(ContractCompileRequest request, CancellationToken cancellationToken);
}
