using System.Collections.Generic;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Resolves diagnostic dependencies before the executable copy changes ghost visibility.</summary>
internal sealed class ContractDiagnosticResolver(Program program, ICollection<DafnyDiagnostic> deferred)
  : ProgramResolver(program) {
  protected override ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl declaration) {
    var resolver = new ModuleResolver(this, declaration.Options) {
      reporter = new DeferredGhostReporter(declaration.Options, deferred)
    };
    return resolver.ResolveModuleDeclaration(compilation, declaration);
  }

  private sealed class DeferredGhostReporter(DafnyOptions options, ICollection<DafnyDiagnostic> deferred)
    : BatchErrorReporter(options) {
    // These errors concern the erased/executable boundary only. The final ordinary resolve must
    // reject any that the diagnostic transformation cannot eliminate; type/name errors are never deferred.
    private static readonly HashSet<string> DeferredIds = [
      "r_ghost_var_only_in_specifications",
      "r_only_in_specification",
      "r_ghost_call_only_in_specification_function_3",
      "r_ghost_call_only_in_specification_function_4",
      "r_out_parameter_must_be_ghost",
      "r_out_parameter_must_be_ghost_field",
      "r_no_assign_to_var_in_ghost",
      "r_no_assign_ghost_to_var",
      "r_ghost_constructors_only_in_ghost_context",
      "r_assignment_to_ghost_constructor_only_in_ghost"
    ];

    public override bool MessageCore(DafnyDiagnostic diagnostic) {
      if (diagnostic.Level == ErrorLevel.Error && diagnostic.Source == MessageSource.Resolver &&
          DeferredIds.Contains(diagnostic.ErrorId ?? "")) {
        deferred.Add(diagnostic);
        return true;
      }
      return base.MessageCore(diagnostic);
    }
  }
}
