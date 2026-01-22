using System.CommandLine;
using System.Threading;
using Microsoft.Dafny;

namespace Scripts;

public static class RewriterAstPrinter {
  private const string DefaultTestFileName = "test.dfy";
  private static readonly string DefaultTestFilePath = Path.GetFullPath(
    Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "..", DefaultTestFileName));

  public static Command GetCommand(TextWriter outputWriter) {
    var result = new Command("print-after-rewriters", "Print Dafny source after running rewriters");
    var inputArgument = new Argument<FileInfo>("input", "Dafny source file");
    var outputOption = new Option<FileInfo?>(
      "--output",
      description: "Optional output file path (defaults to stdout)");
    var partialEvalEntryOption = new Option<string?>(
      "--partial-eval-entry",
      description: "Optional entry name for partial evaluation");
    var partialEvalInlineDepthOption = new Option<uint?>(
      "--partial-eval-inline-depth",
      description: "Optional inlining depth for partial evaluation");
    var unrollBoundedQuantifiersOption = new Option<uint?>(
      "--unroll-bounded-quantifiers",
      description: "Optional maximum instances for bounded quantifier unrolling");
    result.AddArgument(inputArgument);
    result.AddOption(outputOption);
    result.AddOption(partialEvalEntryOption);
    result.AddOption(partialEvalInlineDepthOption);
    result.AddOption(unrollBoundedQuantifiersOption);

    result.SetHandler(async (input, output, entryName, inlineDepth, unrollBoundedQuantifiers) =>
        await Handle(input.FullName, output, entryName, inlineDepth, unrollBoundedQuantifiers, outputWriter),
      inputArgument, outputOption, partialEvalEntryOption, partialEvalInlineDepthOption, unrollBoundedQuantifiersOption);

    return result;
  }

  public static Command GetTestCommand(TextWriter outputWriter) {
    var result = new Command(
      "print-after-rewriters-test",
      "Print Dafny source for test.dfy after running rewriters");
    var outputOption = new Option<FileInfo?>(
      "--output",
      description: "Optional output file path (defaults to stdout)");
    var partialEvalEntryOption = new Option<string?>(
      "--partial-eval-entry",
      description: "Optional entry name for partial evaluation");
    var partialEvalInlineDepthOption = new Option<uint?>(
      "--partial-eval-inline-depth",
      description: "Optional inlining depth for partial evaluation");
    var unrollBoundedQuantifiersOption = new Option<uint?>(
      "--unroll-bounded-quantifiers",
      description: "Optional maximum instances for bounded quantifier unrolling");

    result.AddOption(outputOption);
    result.AddOption(partialEvalEntryOption);
    result.AddOption(partialEvalInlineDepthOption);
    result.AddOption(unrollBoundedQuantifiersOption);

    result.SetHandler(async (output, entryName, inlineDepth, unrollBoundedQuantifiers) =>
        await Handle(DefaultTestFilePath, output, entryName, inlineDepth, unrollBoundedQuantifiers, outputWriter),
      outputOption, partialEvalEntryOption, partialEvalInlineDepthOption, unrollBoundedQuantifiersOption);

    return result;
  }

  public static Command GetPartialEvalAndUnrollCommand(TextWriter outputWriter) {
    var result = new Command(
      "print-after-partial-eval-and-unroll",
      "Print Dafny source after running partial evaluation and bounded quantifier unrolling");
    var inputArgument = new Argument<FileInfo>("input", "Dafny source file");
    var outputOption = new Option<FileInfo?>(
      "--output",
      description: "Optional output file path (defaults to stdout)");
    var partialEvalEntryOption = new Option<string?>(
      "--partial-eval-entry",
      description: "Entry name for partial evaluation") {
      IsRequired = true
    };
    var partialEvalInlineDepthOption = new Option<uint?>(
      "--partial-eval-inline-depth",
      description: "Optional inlining depth for partial evaluation");
    var unrollBoundedQuantifiersOption = new Option<uint?>(
      "--unroll-bounded-quantifiers",
      description: "Optional maximum instances for bounded quantifier unrolling");
    partialEvalEntryOption.AddValidator(result => {
      var entryName = result.GetValueOrDefault<string?>();
      if (string.IsNullOrWhiteSpace(entryName)) {
        result.ErrorMessage = "Partial evaluation entry name must be provided.";
      }
    });

    result.AddArgument(inputArgument);
    result.AddOption(outputOption);
    result.AddOption(partialEvalEntryOption);
    result.AddOption(partialEvalInlineDepthOption);
    result.AddOption(unrollBoundedQuantifiersOption);

    result.SetHandler(async (input, output, entryName, inlineDepth, unrollBoundedQuantifiers) =>
        await Handle(input.FullName, output, entryName, inlineDepth, unrollBoundedQuantifiers, outputWriter),
      inputArgument, outputOption, partialEvalEntryOption, partialEvalInlineDepthOption, unrollBoundedQuantifiersOption);

    return result;
  }

  public static async Task Handle(
    string inputFile,
    FileInfo? output,
    string? entryName,
    uint? inlineDepth,
    uint? unrollBoundedQuantifiers,
    TextWriter fallbackWriter) {
    var options = new DafnyOptions(DafnyOptions.Default);
    options.ApplyDefaultOptionsWithoutSettingsDefault();

    if (!string.IsNullOrEmpty(entryName)) {
      options.Set(CommonOptionBag.PartialEvalEntry, entryName);
    }
    if (inlineDepth.HasValue) {
      options.Set(CommonOptionBag.PartialEvalInlineDepth, inlineDepth.Value);
    }
    if (unrollBoundedQuantifiers.HasValue) {
      options.Set(CommonOptionBag.UnrollBoundedQuantifiers, unrollBoundedQuantifiers.Value);
    }

    var reporter = new BatchErrorReporter(options);
    var input = await File.ReadAllTextAsync(inputFile);
    var parseResult = await ProgramParser.Parse(input, new Uri(Path.GetFullPath(inputFile)), reporter);
    if (reporter.HasErrors) {
      ThrowParseErrors(options, reporter);
    }

    var program = parseResult.Program;
    var resolver = new ProgramResolver(program);
    await resolver.Resolve(CancellationToken.None);
    if (reporter.HasErrors) {
      ThrowResolveErrors(options, reporter);
    }

    TextWriter writer = output == null
      ? fallbackWriter
      : new StreamWriter(output.FullName);

    try {
      var printer = new Printer(writer, options);
      printer.PrintProgram(program, true);
    }
    finally {
      if (output != null) {
        await writer.DisposeAsync();
      }
    }
  }

  private static void ThrowParseErrors(DafnyOptions options, BatchErrorReporter reporter) {
    var errors = reporter.AllMessagesByLevel[ErrorLevel.Error];
    var exceptions = errors.Select(diagnostic =>
      new Exception($"Parsing error: {ErrorReporter.FormatDiagnostic(options, diagnostic)}"));
    throw new AggregateException($"{errors.Count} errors occurred during parsing", exceptions);
  }

  private static void ThrowResolveErrors(DafnyOptions options, BatchErrorReporter reporter) {
    var errors = reporter.AllMessagesByLevel[ErrorLevel.Error];
    var exceptions = errors.Select(diagnostic =>
      new Exception($"Resolve error: {ErrorReporter.FormatDiagnostic(options, diagnostic)}"));
    throw new AggregateException($"{errors.Count} errors occurred during resolution", exceptions);
  }
}
