using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class PartialEvaluator : IRewriter {
  private readonly Program program;

  public PartialEvaluator(Program program, ErrorReporter reporter) : base(reporter) {
    Contract.Requires(program != null);
    this.program = program;
  }

  internal override void PostResolveIntermediate(ModuleDefinition moduleDefinition) {
    var entryName = Reporter.Options.Get(CommonOptionBag.PartialEvalEntry);
    if (string.IsNullOrEmpty(entryName)) {
      return;
    }

    var inlineDepth = Reporter.Options.Get(CommonOptionBag.PartialEvalInlineDepth);
    var entryTargets = new List<ICallable>();
    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(moduleDefinition.TopLevelDecls)) {
      if (decl is Declaration declaration && declaration.Name == entryName) {
        entryTargets.Add(decl);
      }
    }

    if (entryTargets.Count == 0) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Partial evaluation entry '{entryName}' was not found in module '{moduleDefinition.Name}'.");
      return;
    }

    if (entryTargets.Count > 1) {
      Reporter.Warning(MessageSource.Rewriter, ErrorRegistry.NoneId, moduleDefinition.Origin,
        $"Multiple callables named '{entryName}' found; partial evaluation will run on all matches.");
    }

    var evaluator = new PartialEvaluatorEngine(Reporter.Options, moduleDefinition, program.SystemModuleManager, inlineDepth);
    foreach (var target in entryTargets) {
      evaluator.PartialEvalEntry(target);
    }
  }
}
