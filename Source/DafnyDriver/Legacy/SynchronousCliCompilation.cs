//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------
// DafnyDriver
//       - main program for taking a Dafny program and verifying it
//---------------------------------------------------------------------------------------------

using System.Collections.Concurrent;
using System.Runtime.InteropServices;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Net.Http;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using System.Diagnostics;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using VC;
using DafnyCore;

namespace Microsoft.Dafny {

  /// <summary>
  /// Calls into different phases of Dafny's compilation pipeline,
  /// such as parsing, resolution, verification and code generation
  /// 
  /// Will be replaced by CompilationManager
  /// </summary>
  public class SynchronousCliCompilation : IDisposable {
    private readonly ExecutionEngine engine;
    private static readonly HttpClient NaturalLanguageHttpClient = new();
    private static readonly JsonSerializerOptions NaturalLanguageRequestJsonOptions = new() {
      PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
      DefaultIgnoreCondition = JsonIgnoreCondition.WhenWritingNull,
      WriteIndented = true
    };
    private static readonly JsonSerializerOptions NaturalLanguageResponseJsonOptions = new() {
      PropertyNameCaseInsensitive = true
    };

    public SynchronousCliCompilation(DafnyOptions dafnyOptions) {
      engine = ExecutionEngine.CreateWithoutSharedCache(dafnyOptions);
    }

    public static async Task<int> Run(DafnyOptions options) {
      options.RunningBoogieFromCommandLine = true;

      var backend = GetBackend(options);
      if (backend == null) {
        return (int)ExitValue.PREPROCESSING_ERROR;
      }
      options.Backend = backend;

      var (getFilesExitCode, dafnyFiles, otherFiles) = await GetDafnyFiles(options);
      if (getFilesExitCode != ExitValue.SUCCESS) {
        return (int)getFilesExitCode;
      }

      using var driver = new SynchronousCliCompilation(options);
      ProofDependencyManager depManager = new();
      var exitValue = await driver.ProcessFilesAsync(dafnyFiles, otherFiles.AsReadOnly(), options, depManager);
      if (options.Get(CommonOptionBag.VerificationLogFormat)?.Any() == true) {
        try {
          LegacyVerificationResultLogger.RaiseTestLoggerEvents(options, depManager);
        } catch (ArgumentException ae) {
          await options.OutputWriter.Status($"*** Error: {ae.Message}");
          exitValue = ExitValue.PREPROCESSING_ERROR;
        }
      }

      options.XmlSink?.Close();

      if (options.Wait) {
        Console.WriteLine("Press Enter to exit.");
        Console.ReadLine();
      }

      return (int)exitValue;
    }

    public static async Task<(ExitValue ExitValue,
      List<DafnyFile> DafnyFiles,
      List<string> OtherFiles)> GetPreparedDafnyFiles(DafnyOptions options) {
      var preparation = await PrepareDafnyFilesAsync(options);
      return (preparation.ExitValue, preparation.PreparedFiles, preparation.OtherFiles);
    }

    public static async Task<ExitValue> PrepareOptionsForCliCompilationAsync(DafnyOptions options) {
      if (!options.Get(CommonOptionBag.NaturalLanguageBlocks)) {
        return ExitValue.SUCCESS;
      }

      var originalRootUris = CollectExplicitRootSourceUris(options);
      var preparation = await PrepareDafnyFilesAsync(options);
      if (preparation.ExitValue != ExitValue.SUCCESS) {
        return preparation.ExitValue;
      }

      ReplaceCliCompilationInputs(options, originalRootUris, preparation.OriginalFiles, preparation.PreparedFiles);
      return ExitValue.SUCCESS;
    }

    private static async Task<(ExitValue ExitValue,
      List<DafnyFile> OriginalFiles,
      List<DafnyFile> PreparedFiles,
      List<string> OtherFiles)> PrepareDafnyFilesAsync(DafnyOptions options) {
      var backend = GetBackend(options);
      if (backend == null) {
        return (ExitValue.PREPROCESSING_ERROR, [], [], []);
      }
      options.Backend = backend;

      if (options.Get(CommonOptionBag.NaturalLanguageBlocks) && options.AllowSourceFolders) {
        ExpandFolderSourceUrisIntoFiles(options);
      }

      var (getFilesExitCode, dafnyFiles, otherFiles) = await GetDafnyFiles(options);
      if (getFilesExitCode != ExitValue.SUCCESS || !options.Get(CommonOptionBag.NaturalLanguageBlocks)) {
        return (getFilesExitCode, dafnyFiles, dafnyFiles, otherFiles);
      }

      using var driver = new SynchronousCliCompilation(options);
      var naturalLanguageExpansion = await driver.ExpandNaturalLanguageBlocksAsync(dafnyFiles, options);
      if (!naturalLanguageExpansion.Success) {
        return (naturalLanguageExpansion.ExitValue, dafnyFiles, [], otherFiles);
      }

      return (ExitValue.SUCCESS, dafnyFiles, naturalLanguageExpansion.RewrittenFiles.ToList(), otherFiles);
    }

    private static HashSet<Uri> CollectExplicitRootSourceUris(DafnyOptions options) {
      var result = new HashSet<Uri>();
      foreach (var uri in options.CliRootSourceUris.Where(uri => uri.IsFile)) {
        result.Add(uri);
      }

      if (options.DafnyProject != null) {
        foreach (var uri in options.DafnyProject.GetRootSourceUris(OnDiskFileSystem.Instance)) {
          result.Add(uri);
        }
      }

      return result;
    }

    private static void ExpandFolderSourceUrisIntoFiles(DafnyOptions options) {
      var expandedUris = new List<Uri>();
      var seenPaths = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
      foreach (var uri in options.CliRootSourceUris) {
        if (!uri.IsFile) {
          expandedUris.Add(uri);
          continue;
        }

        var path = uri.LocalPath;
        if (!Directory.Exists(path)) {
          if (seenPaths.Add(path)) {
            expandedUris.Add(uri);
          }
          continue;
        }

        foreach (var filePath in Directory.GetFiles(path, "*.dfy", SearchOption.AllDirectories).OrderBy(filePath => filePath, StringComparer.OrdinalIgnoreCase)) {
          var fullPath = Path.GetFullPath(filePath);
          if (seenPaths.Add(fullPath)) {
            expandedUris.Add(new Uri(fullPath));
          }
        }
      }

      options.CliRootSourceUris.Clear();
      foreach (var uri in expandedUris) {
        options.CliRootSourceUris.Add(uri);
      }
      options.SourceFolders.Clear();
    }

    private static void ReplaceCliCompilationInputs(
      DafnyOptions options,
      ISet<Uri> originalRootUris,
      IReadOnlyList<DafnyFile> originalFiles,
      IReadOnlyList<DafnyFile> preparedFiles) {
      var preparedRootUris = new List<Uri>();
      for (var index = 0; index < originalFiles.Count && index < preparedFiles.Count; index++) {
        var originalFile = originalFiles[index];
        if (!originalRootUris.Contains(originalFile.Uri)) {
          continue;
        }

        var preparedFile = preparedFiles[index];
        if (preparedFile.Uri.IsFile) {
          preparedRootUris.Add(preparedFile.Uri);
        }
      }

      options.CliRootSourceUris.Clear();
      foreach (var uri in preparedRootUris.Distinct()) {
        options.CliRootSourceUris.Add(uri);
      }

      var projectUri = options.CliRootSourceUris.FirstOrDefault() ?? options.DafnyProject?.Uri ?? new Uri(Directory.GetCurrentDirectory());
      options.DafnyProject = new DafnyProject(null, projectUri, null, new HashSet<string>(), new HashSet<string>(), new Dictionary<string, object>()) {
        ImplicitFromCli = true
      };
    }

    public static async Task<(ExitValue ExitValue,
      List<DafnyFile> DafnyFiles,
      List<string> OtherFiles)> GetDafnyFiles(DafnyOptions options) {
      if (options.Printer is NullPrinter) {
        options.Printer = new DafnyConsolePrinter(options);
      }

      if (options.DafnyProject != null) {
        foreach (var uri in options.DafnyProject.GetRootSourceUris(OnDiskFileSystem.Instance)) {
          options.CliRootSourceUris.Add(uri);
        }
      }

      var dafnyFiles = new List<DafnyFile>();
      var otherFiles = new List<string>();
      var outputWriter = options.OutputWriter;

      var consoleErrorReporter = new ConsoleErrorReporter(options);
      if (options.DafnyProject != null) {
        options.DafnyProject.Errors.CopyDiagnostics(consoleErrorReporter);
        if (options.DafnyProject.Errors.HasErrors) {
          return (ExitValue.PREPROCESSING_ERROR, [], []);
        }
      }

      if (options.UseStdin) {
        var dafnyFile = DafnyFile.HandleStandardInput(options, Token.NoToken);
        dafnyFiles.Add(dafnyFile);
        options.CliRootSourceUris.Add(dafnyFile.Uri);
      } else if (options.CliRootSourceUris.Count == 0) {
        await options.ErrorWriter.WriteLineAsync("*** Error: No input files were specified in command-line. " + options.Environment);
        return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
      }
      if (options.XmlSink != null) {
        string errMsg = options.XmlSink.Open();
        if (errMsg != null) {
          await options.ErrorWriter.WriteLineAsync("*** Error: " + errMsg);
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }
      }
      if (options.ShowEnv == ExecutionEngineOptions.ShowEnvironment.Always) {
        await outputWriter.Status(options.Environment);
      }

      ISet<String> filesSeen = new HashSet<string>();
      var libraryFiles = CommonOptionBag.SplitOptionValueIntoFiles(options.LibraryFiles).ToHashSet();
      foreach (var file in options.CliRootSourceUris.Where(u => u.IsFile).Select(u => u.LocalPath).
                 Concat(libraryFiles).Distinct()) {
        Contract.Assert(file != null);
        var extension = Path.GetExtension(file);
        if (extension != null) { extension = extension.ToLower(); }

        var relative = Path.GetFileName(file);
        bool useRelative = options.UseBaseNameForFileName || relative.StartsWith("-");
        var nameToShow = useRelative ? relative
          : Path.GetRelativePath(Directory.GetCurrentDirectory(), file);
        var supportedExtensions = options.Backend.SupportedExtensions;
        bool isDafnyFile = false;
        try {
          await foreach (var df in DafnyFile.CreateAndValidate(
                           OnDiskFileSystem.Instance, consoleErrorReporter, options, new Uri(Path.GetFullPath(file)),
                           Token.Cli, options.LibraryFiles.Contains(file))) {
            if (!filesSeen.Add(df.CanonicalPath)) {
              continue; // silently ignore duplicate
            }
            dafnyFiles.Add(df);
            isDafnyFile = true;
          }
          if (consoleErrorReporter.FailCompilation) {
            return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
          }
        } catch (ArgumentException) {
          await options.ErrorWriter.WriteLineAsync($"*** Error: {nameToShow}: ");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        } catch (Exception e) {
          await options.ErrorWriter.WriteLineAsync($"*** Error: {nameToShow}: {e.Message}");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }

        if (supportedExtensions.Contains(extension)) {
          // .h files are not part of the build, they are just emitted as includes
          // TODO: This should be delegated to the backend instead (i.e. the CppCompilerBackend)
          if (File.Exists(file) || extension == ".h") {
            otherFiles.Add(file);
          } else {
            await options.OutputWriter.Status($"*** Error: file {nameToShow} not found");
            return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
          }
        } else if (options.AllowSourceFolders && Directory.Exists(file)) {
          options.SourceFolders.Add(file);
        } else if (!isDafnyFile) {
          string errorOnNotRecognized;
          if (options.UsingNewCli && string.IsNullOrEmpty(extension) && file.Length > 0) {
            errorOnNotRecognized =
              $"*** Error: Command-line argument '{nameToShow}' is neither a recognized option nor a filename with a supported extension ({string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions))}).";
          } else if (string.IsNullOrEmpty(extension) && file.Length > 0 && (file[0] == '/' || file[0] == '-')) {
            errorOnNotRecognized =
              $"*** Error: Command-line argument '{nameToShow}' is neither a recognized option nor a filename with a supported extension ({string.Join(", ", Enumerable.Repeat(".dfy", 1).Concat(supportedExtensions))}).";
          } else {
            errorOnNotRecognized =
              $"*** Error: '{nameToShow}': Filename extension '{extension}' is not supported. Input files must be Dafny programs (.dfy) or supported auxiliary files ({string.Join(", ", supportedExtensions)})";
          }

          await options.OutputWriter.Status(errorOnNotRecognized);
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }
      }

      if (dafnyFiles.Count == 0 && options.SourceFolders.Count == 0) {
        if (!options.AllowSourceFolders) {
          options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files");
          // TODO: With the test on CliRootUris.Count above, this code is no longer reachable
          await options.OutputWriter.Status("*** Error: The command-line contains no .dfy files");
          return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
        }

        options.Printer.ErrorWriteLine(Console.Out, "*** Error: The command-line contains no .dfy files or folders");
        //options.Printer.ErrorWriteLine(Console.Out,
        //  "Usage:\ndafny format [--check] [--print] <file/folder> <file/folder>...\nYou can use '.' for the current directory");
        return (ExitValue.PREPROCESSING_ERROR, dafnyFiles, otherFiles);
      }

      // Add standard library .doo files after explicitly provided source files,
      // only because if they are added first, one might be used as the program name,
      // which is not handled well.
      if (options.Get(CommonOptionBag.UseStandardLibraries)) {
        if (options.Backend is LibraryBackend) {
          options.Set(CommonOptionBag.TranslateStandardLibrary, false);
        }

        // For now the standard libraries are still translated from scratch.
        // This creates issues with separate compilation and will be addressed in https://github.com/dafny-lang/dafny/pull/4877
        var asLibrary = !options.Get(CommonOptionBag.TranslateStandardLibrary);

        var reporter = new ConsoleErrorReporter(options);
        if (options.CompilerName is null or "cs" or "java" or "go" or "py" or "js") {
          var targetName = options.CompilerName ?? "notarget";
          var stdlibDooUri = DafnyMain.StandardLibrariesDooUriTarget[targetName];
          options.CliRootSourceUris.Add(stdlibDooUri);
          await foreach (var targetSpecificFile in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, reporter, options, stdlibDooUri, Token.Cli, asLibrary)) {
            dafnyFiles.Add(targetSpecificFile);
          }
        }

        options.CliRootSourceUris.Add(DafnyMain.StandardLibrariesDooUri);
        await foreach (var targetAgnosticFile in DafnyFile.CreateAndValidate(OnDiskFileSystem.Instance, reporter, options, DafnyMain.StandardLibrariesDooUri, Token.Cli, asLibrary)) {
          dafnyFiles.Add(targetAgnosticFile);
        }
      }

      return (ExitValue.SUCCESS, dafnyFiles, otherFiles);
    }

    private static IExecutableBackend GetBackend(DafnyOptions options) {
      if (options.Backend?.TargetId == options.CompilerName) {
        return options.Backend;
      }

      var backends = options.Plugins.SelectMany(p => p.GetCompilers(options)).ToList();
      var backend = backends.LastOrDefault(c => c.TargetId == options.CompilerName);
      if (backend == null) {
        if (options.CompilerName != null) {
          var known = String.Join(", ", backends.Select(c => $"'{c.TargetId}' ({c.TargetName})"));
          options.ErrorWriter.WriteLine(
            $"*** Error: No compiler found for target \"{options.CompilerName}\"{(options.CompilerName.StartsWith("-t") || options.CompilerName.StartsWith("--") ? " (use just a target name, not a -t or --target option)" : "")}; expecting one of {known}");
        } else {
          backend = new NoExecutableBackend(options);
        }
      }

      return backend;
    }

    public async Task<ExitValue> ProcessFilesAsync(IReadOnlyList<DafnyFile/*!*/>/*!*/ dafnyFiles,
      ReadOnlyCollection<string> otherFileNames,
      DafnyOptions options, ProofDependencyManager depManager,
      bool lookForSnapshots = true, string programId = null) {
      Contract.Requires(Cce.NonNullElements(dafnyFiles));
      var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);

      ExitValue exitValue = ExitValue.SUCCESS;

      if (options.VerifySeparately && 1 < dafnyFiles.Count) {
        foreach (var f in dafnyFiles) {
          await options.OutputWriter.Status($"-------------------- {f} --------------------");
          var ev = await ProcessFilesAsync(new List<DafnyFile> { f }, new List<string>().AsReadOnly(), options, depManager, lookForSnapshots, f.FilePath);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (0 < options.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = ExecutionEngine.LookForSnapshots(dafnyFileNames);
        foreach (var s in snapshotsByVersion) {
          var snapshots = new List<DafnyFile>();
          foreach (var f in s) {
            var uri = new Uri(Path.GetFullPath(f));
            snapshots.Add(DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance, new ConsoleErrorReporter(options), options, uri, Token.Cli));
            options.CliRootSourceUris.Add(uri);
          }
          var ev = await ProcessFilesAsync(snapshots, new List<string>().AsReadOnly(), options, depManager, false, programId);
          if (exitValue != ev && ev != ExitValue.SUCCESS) {
            exitValue = ev;
          }
        }
        return exitValue;
      }

      if (options.Get(CommonOptionBag.NaturalLanguageBlocks)) {
        var naturalLanguageExpansion = await ExpandNaturalLanguageBlocksAsync(dafnyFiles, options);
        if (!naturalLanguageExpansion.Success) {
          return naturalLanguageExpansion.ExitValue;
        }
        dafnyFiles = naturalLanguageExpansion.RewrittenFiles;
        dafnyFileNames = DafnyFile.FileNames(dafnyFiles);
      }

      string programName = dafnyFileNames.Count == 1 ? dafnyFileNames[0] : "the_program";
      var (dafnyProgram, err) = await DafnyMain.ParseCheck(options.Input, dafnyFiles, programName, options);
      if (err != null) {
        exitValue = ExitValue.DAFNY_ERROR;
        await options.OutputWriter.Status(err);
      } else if (dafnyProgram != null && !options.NoResolve && !options.NoTypecheck) {

        bool verified;
        PipelineOutcome outcome;
        IDictionary<string, PipelineStatistics> moduleStats;
        dafnyProgram.ProofDependencyManager = depManager;
        if (!options.DafnyVerify) {
          verified = false;
          outcome = PipelineOutcome.Done;
          moduleStats = new Dictionary<string, PipelineStatistics>();
        } else {
          var boogiePrograms =
            await DafnyMain.LargeStackFactory.StartNew(() => Translate(engine.Options, dafnyProgram).ToList());

          string baseName = Cce.NonNull(Path.GetFileName(dafnyFileNames[^1]));
          (verified, outcome, moduleStats) =
            await BoogieAsync(dafnyProgram.Reporter, options, baseName, boogiePrograms, programId);

          if (options.TrackVerificationCoverage) {
            ProofDependencyWarnings.WarnAboutSuspiciousDependenciesUsingStoredPartialResults(options,
              dafnyProgram.Reporter, depManager);
            var coverageReportDir = options.Get(CommonOptionBag.VerificationCoverageReport);
            if (coverageReportDir != null) {
              await new CoverageReporter(options).SerializeVerificationCoverageReport(
                depManager, dafnyProgram,
                boogiePrograms.SelectMany(tp => tp.Item2.AllCoveredElements),
                coverageReportDir);
            }
          }
        }

        bool compiled;
        try {
          compiled = await Compile(dafnyFileNames[0], otherFileNames, dafnyProgram, outcome, moduleStats, verified);
        } catch (UnsupportedFeatureException e) {
          if (!options.Backend.UnsupportedFeatures.Contains(e.Feature)) {
            throw new Exception(
              $"'{e.Feature}' is not an element of the {options.Backend.TargetId} compiler's UnsupportedFeatures set");
          }

          dafnyProgram.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.f_unsupported_feature, e.Token,
            e.Message);
          compiled = false;
        } catch (UnsupportedInvalidOperationException e) {
          // Not having this catch makes all tests running for all compilers take 10-15x longer on Windows,
          // just because of the Dafny compiler.
          dafnyProgram.Reporter.Error(MessageSource.Compiler, GeneratorErrors.ErrorId.f_unsupported_feature, e.Token, e.Message);
          compiled = false;
        }

        var failBecauseOfDiagnostics = dafnyProgram.Reporter.FailCompilationMessage;
        if (!verified && options.DafnyVerify) {
          exitValue = ExitValue.VERIFICATION_ERROR;
        } else if (!compiled) {
          exitValue = ExitValue.COMPILE_ERROR;
        } else if (failBecauseOfDiagnostics != null) {
          exitValue = ExitValue.DAFNY_ERROR;
          await options.OutputWriter.Status($"Returning exit code {exitValue} because {failBecauseOfDiagnostics}");
        }
      }

      if (err == null && dafnyProgram != null && options.PrintStats) {
        await Util.PrintStats(dafnyProgram);
      }
      if (err == null && dafnyProgram != null && options.PrintFunctionCallGraph) {
        await Util.PrintFunctionCallGraph(dafnyProgram);
      }
      if (dafnyProgram != null && options.ExtractCounterexample && exitValue == ExitValue.VERIFICATION_ERROR) {
        await PrintCounterexample(options);
      }

      return exitValue;
    }

    private async Task<(bool Success, ExitValue ExitValue, IReadOnlyList<DafnyFile> RewrittenFiles)> ExpandNaturalLanguageBlocksAsync(
      IReadOnlyList<DafnyFile> originalFiles, DafnyOptions options) {
      if (options.UseStdin) {
        await options.OutputWriter.Status("*** Error: --natural-language-blocks does not support stdin input.");
        return (false, ExitValue.PREPROCESSING_ERROR, originalFiles);
      }

      var originalFileNames = DafnyFile.FileNames(originalFiles);
      var parseProgramName = originalFileNames.Count == 1 ? originalFileNames[0] : "the_program";
      var (parsedProgram, parseErr) = await DafnyMain.Parse(originalFiles, parseProgramName, options);
      if (parseErr != null || parsedProgram == null) {
        await options.OutputWriter.Status(parseErr ?? "Failed to parse program for natural-language expansion.");
        return (false, ExitValue.DAFNY_ERROR, originalFiles);
      }
      var resolveErr = DafnyMain.Resolve(parsedProgram);

      var sourceTexts = LoadSourceTextsForRootFiles(originalFiles, options);
      var tasks = BuildNaturalLanguageTasks(parsedProgram, sourceTexts);
      if (tasks.Count == 0) {
        return (true, ExitValue.SUCCESS, originalFiles);
      }

      var intermediateProductsDirectory = options.Get(CommonOptionBag.NaturalLanguageIntermediateProductsDirectory);
      var emitIntermediateProducts = intermediateProductsDirectory != null;

      var firstRootFile = originalFiles.FirstOrDefault(file => file.Uri.IsFile && file.Extension == DafnyFile.DafnyFileExtension);
      var sourceDirectory = firstRootFile == null
        ? Directory.GetCurrentDirectory()
        : Path.GetDirectoryName(firstRootFile.Uri.LocalPath) ?? Directory.GetCurrentDirectory();
      var exchangeDirectory = intermediateProductsDirectory == null
        ? sourceDirectory
        : Path.GetFullPath(intermediateProductsDirectory.FullName);
      if (emitIntermediateProducts) {
        Directory.CreateDirectory(exchangeDirectory);
      }

      var exchangeBase = Path.Combine(exchangeDirectory, $"{Path.GetFileNameWithoutExtension(parsedProgram.Name)}.nlgen");
      var supportDeclarations = CollectRelevantSupportDeclarations(parsedProgram, sourceTexts);
      var feedback = CollectFeedbackByTask(parsedProgram, resolveErr, tasks);
      var taskStates = tasks.ToDictionary(task => task.TaskId, task => new NaturalLanguageTaskState());

      for (var attempt = 1; attempt <= 10; attempt++) {
        var apiUrl = Environment.GetEnvironmentVariable("DAFNY_NL_API_URL");
        var tasksToRequest = SelectTasksToRequest(attempt, tasks, feedback, taskStates);
        var taskRequestResults = tasksToRequest.Count == 0
          ? []
          : await Task.WhenAll(tasksToRequest.Select(task =>
            SendNaturalLanguageTaskRequestAsync(
              apiUrl,
              parsedProgram,
              task,
              taskStates[task.TaskId],
              supportDeclarations,
              attempt,
              emitIntermediateProducts,
              exchangeBase)));

        foreach (var taskRequestResult in taskRequestResults) {
          if (!taskRequestResult.Success) {
            await options.OutputWriter.Status(taskRequestResult.ErrorMessage);
            if (!emitIntermediateProducts && taskRequestResult.ErrorMessage.Contains("expected natural-language response file not found")) {
              await options.OutputWriter.Status(
                "*** Hint: pass --natural-language-intermediate-products-directory <directory> to emit NL task/response JSON files.");
            }
            return (false, ExitValue.DAFNY_ERROR, originalFiles);
          }
        }

        foreach (var taskRequestResult in taskRequestResults) {
          taskStates[taskRequestResult.Response.TaskId].CurrentResponse = taskRequestResult.Response;
          if (!string.IsNullOrWhiteSpace(taskRequestResult.OpenAiResponseId)) {
            taskStates[taskRequestResult.Response.TaskId].PreviousOpenAiResponseId = taskRequestResult.OpenAiResponseId;
          }
        }

        if (!TryBuildNaturalLanguageResponseFile(tasks, taskStates, out var response, out var responseError)) {
          await options.OutputWriter.Status($"*** Error: invalid NL response file: {responseError}");
          return (false, ExitValue.DAFNY_ERROR, originalFiles);
        }

        if (!TryApplyNaturalLanguageResponses(tasks, sourceTexts, response, out var rewrittenSources,
              out var appliedTaskContexts, out var applyError)) {
          await options.OutputWriter.Status($"*** Error: invalid NL response file: {applyError}");
          return (false, ExitValue.DAFNY_ERROR, originalFiles);
        }

        Dictionary<Uri, string> attemptPaths;
        string temporaryAttemptDirectory = null;
        if (emitIntermediateProducts) {
          attemptPaths = WriteRewrittenSources(originalFiles, rewrittenSources,
            suffix: $".nlgen.attempt{attempt}", outputDirectoryOverride: exchangeDirectory);
        } else {
          temporaryAttemptDirectory = Path.Combine(Path.GetTempPath(), $"dafny-nlgen-{Guid.NewGuid():N}");
          Directory.CreateDirectory(temporaryAttemptDirectory);
          attemptPaths = WriteRewrittenSources(originalFiles, rewrittenSources,
            suffix: $".nlgen.attempt{attempt}", outputDirectoryOverride: temporaryAttemptDirectory);
        }

        var attemptFiles = CreateDafnyFilesFromPaths(originalFiles, attemptPaths, options);
        var attemptSourcePathMap = BuildNaturalLanguageSourcePathMap(attemptPaths);

        (bool Verified, Program Program, NaturalLanguageFeedbackByTask Feedback) verification;
        try {
          verification = await VerifyCandidateFilesAsync(attemptFiles, options, tasks, attemptSourcePathMap);
        }
        finally {
          if (temporaryAttemptDirectory != null) {
            TryDeleteDirectory(temporaryAttemptDirectory);
          }
        }

        if (verification.Verified) {
          var finalPaths = WriteRewrittenSources(originalFiles, rewrittenSources, suffix: ".nlgen");
          var finalFiles = CreateDafnyFilesFromPaths(originalFiles, finalPaths, options);
          await options.OutputWriter.Status(
            $"Natural-language expansion completed after {attempt} attempt(s). Rewritten sources were saved with '.nlgen.dfy' suffix.");
          return (true, ExitValue.SUCCESS, finalFiles);
        }

        feedback = verification.Feedback;
        RecordRetryHistory(attempt, feedback, tasks, taskStates, appliedTaskContexts);
      }

      await options.OutputWriter.Status("*** Error: natural-language expansion exceeded retry limit (10 attempts).");
      return (false, ExitValue.VERIFICATION_ERROR, originalFiles);
    }

    private static async Task<string> CallNaturalLanguageApiAsync(Uri apiUri, bool attachOpenAiApiKey, string requestJson) {
      using var request = new HttpRequestMessage(HttpMethod.Post, apiUri) {
        Content = new StringContent(requestJson, Encoding.UTF8, "application/json")
      };
      request.Headers.Accept.Add(new System.Net.Http.Headers.MediaTypeWithQualityHeaderValue("application/json"));

      if (attachOpenAiApiKey) {
        var openAiApiKey = Environment.GetEnvironmentVariable("OPENAI_API_KEY");
        if (string.IsNullOrWhiteSpace(openAiApiKey)) {
          throw new Exception("OPENAI_API_KEY is required when sending NL requests to the OpenAI Responses API.");
        }
        request.Headers.Authorization = new System.Net.Http.Headers.AuthenticationHeaderValue("Bearer", openAiApiKey);
      }

      using var response = await NaturalLanguageHttpClient.SendAsync(request);
      var responseBody = await response.Content.ReadAsStringAsync();
      if (!response.IsSuccessStatusCode) {
        throw new Exception($"NL API returned {(int)response.StatusCode}: {responseBody}");
      }

      return responseBody;
    }

    private static (Uri ApiUri, bool AttachOpenAiApiKey)? ResolveNaturalLanguageApiEndpoint(string configuredApiUrl) {
      var openAiApiKey = Environment.GetEnvironmentVariable("OPENAI_API_KEY");
      var hasOpenAiApiKey = !string.IsNullOrWhiteSpace(openAiApiKey);
      var effectiveApiUrl = !string.IsNullOrWhiteSpace(configuredApiUrl)
        ? configuredApiUrl!
        : (hasOpenAiApiKey ? "https://api.openai.com/v1/responses" : null);
      if (string.IsNullOrWhiteSpace(effectiveApiUrl)) {
        return null;
      }

      if (!Uri.TryCreate(effectiveApiUrl, UriKind.Absolute, out var apiUri)) {
        throw new Exception($"Invalid natural-language API URL: {effectiveApiUrl}");
      }

      var isLoopback = apiUri.IsLoopback;
      if (!string.Equals(apiUri.Scheme, Uri.UriSchemeHttps, StringComparison.OrdinalIgnoreCase) && !isLoopback) {
        throw new Exception($"Refusing to send natural-language requests over insecure transport to '{apiUri}'. Use HTTPS or a loopback URL for local testing.");
      }

      var isOfficialOpenAiEndpoint =
        string.Equals(apiUri.Scheme, Uri.UriSchemeHttps, StringComparison.OrdinalIgnoreCase) &&
        string.Equals(apiUri.Host, "api.openai.com", StringComparison.OrdinalIgnoreCase) &&
        string.Equals(apiUri.AbsolutePath, "/v1/responses", StringComparison.Ordinal);

      if (hasOpenAiApiKey && !isOfficialOpenAiEndpoint && !isLoopback) {
        throw new Exception($"Refusing to send OPENAI_API_KEY to non-OpenAI endpoint '{apiUri}'. Clear DAFNY_NL_API_URL or use the official OpenAI Responses API URL.");
      }

      return (apiUri, isOfficialOpenAiEndpoint);
    }

    private static async Task<NaturalLanguageTaskRequestResult> SendNaturalLanguageTaskRequestAsync(
      string apiUrl,
      Program program,
      NaturalLanguageTask task,
      NaturalLanguageTaskState taskState,
      IReadOnlyList<NaturalLanguageSupportDeclaration> supportDeclarations,
      int attempt,
      bool emitIntermediateProducts,
      string exchangeBase) {
      var apiEndpoint = ResolveNaturalLanguageApiEndpoint(apiUrl);
      var prompt = BuildNaturalLanguagePrompt(task, supportDeclarations, taskState.RetryHistory);
      var request = CreateOpenAiResponsesRequest(program.Name, task, prompt, attempt,
        apiEndpoint?.AttachOpenAiApiKey == true ? taskState.PreviousOpenAiResponseId : null);

      var requestJson = JsonSerializer.Serialize(request, NaturalLanguageRequestJsonOptions);
      var taskPathSuffix = SanitizeForPath(task.CallableName);
      var requestPath = $"{exchangeBase}.task.{taskPathSuffix}.attempt{attempt}.json";
      if (emitIntermediateProducts) {
        var promptPath = $"{exchangeBase}.prompt.{taskPathSuffix}.attempt{attempt}.txt";
        await File.WriteAllTextAsync(promptPath, prompt, Encoding.UTF8);
        await File.WriteAllTextAsync(requestPath, requestJson);
      }

      var responsePath = $"{exchangeBase}.response.{taskPathSuffix}.attempt{attempt}.json";
      var responseSourceLabel = responsePath;
      string responseJson;
      if (apiEndpoint != null) {
        responseJson = await CallNaturalLanguageApiAsync(apiEndpoint.Value.ApiUri, apiEndpoint.Value.AttachOpenAiApiKey, requestJson);
        responseSourceLabel = "NL API response";
        if (emitIntermediateProducts) {
          await File.WriteAllTextAsync(responsePath, responseJson);
          responseSourceLabel = responsePath;
        }
      } else {
        if (!File.Exists(responsePath)) {
          return new NaturalLanguageTaskRequestResult {
            Success = false,
            ErrorMessage = $"*** Error: expected natural-language response file not found: {responsePath}"
          };
        }
        responseJson = await File.ReadAllTextAsync(responsePath);
      }

      OpenAiResponsesApiResponse openAiResponse;
      try {
        openAiResponse = JsonSerializer.Deserialize<OpenAiResponsesApiResponse>(responseJson, NaturalLanguageResponseJsonOptions)
                         ?? new OpenAiResponsesApiResponse();
      } catch (Exception e) {
        return new NaturalLanguageTaskRequestResult {
          Success = false,
          ErrorMessage = $"*** Error: could not read NL response file '{responseSourceLabel}': {e.Message}"
        };
      }

      var structuredText = ExtractStructuredOutputText(openAiResponse, out var refusalText);
      if (!string.IsNullOrWhiteSpace(refusalText)) {
        return new NaturalLanguageTaskRequestResult {
          Success = false,
          ErrorMessage = $"*** Error: NL API refused task '{task.TaskId}': {refusalText}"
        };
      }
      if (string.IsNullOrWhiteSpace(structuredText)) {
        return new NaturalLanguageTaskRequestResult {
          Success = false,
          ErrorMessage = $"*** Error: NL API response did not contain structured output text for task '{task.TaskId}'."
        };
      }

      NaturalLanguageTaskResponsePayload taskResponsePayload;
      try {
        taskResponsePayload = JsonSerializer.Deserialize<NaturalLanguageTaskResponsePayload>(structuredText, NaturalLanguageResponseJsonOptions)
                              ?? new NaturalLanguageTaskResponsePayload();
      } catch (Exception e) {
        return new NaturalLanguageTaskRequestResult {
          Success = false,
          ErrorMessage = $"*** Error: could not parse structured NL output for task '{task.TaskId}': {e.Message}"
        };
      }

      return new NaturalLanguageTaskRequestResult {
        Success = true,
        OpenAiResponseId = openAiResponse.Id ?? "",
        Response = new NaturalLanguageTaskResponse {
          TaskId = task.TaskId,
          Replacements = taskResponsePayload.Replacements ?? []
        }
      };
    }

    private static OpenAiResponsesRequest CreateOpenAiResponsesRequest(
      string programName,
      NaturalLanguageTask task,
      string prompt,
      int attempt,
      string previousResponseId) {
      var model = Environment.GetEnvironmentVariable("DAFNY_NL_OPENAI_MODEL");
      if (string.IsNullOrWhiteSpace(model)) {
        model = "gpt-5.4";
      }

      return new OpenAiResponsesRequest {
        Model = model,
        PreviousResponseId = string.IsNullOrWhiteSpace(previousResponseId) ? null : previousResponseId,
        Input = prompt,
        Metadata = new Dictionary<string, string> {
          ["program_name"] = programName,
          ["task_id"] = task.TaskId,
          ["callable_name"] = task.CallableName,
          ["attempt"] = attempt.ToString()
        },
        Text = new OpenAiResponsesTextConfiguration {
          Format = new OpenAiResponsesJsonSchemaFormat {
            Type = "json_schema",
            Name = "dafny_nl_replacements",
            Strict = true,
            Schema = CreateNaturalLanguageResponseSchema()
          }
        }
      };
    }

    private static object CreateNaturalLanguageResponseSchema() {
      return new Dictionary<string, object> {
        ["type"] = "object",
        ["additionalProperties"] = false,
        ["properties"] = new Dictionary<string, object> {
          ["replacements"] = new Dictionary<string, object> {
            ["type"] = "array",
            ["items"] = new Dictionary<string, object> {
              ["type"] = "object",
              ["additionalProperties"] = false,
              ["properties"] = new Dictionary<string, object> {
                ["elementId"] = new Dictionary<string, object> { ["type"] = "string" },
                ["code"] = new Dictionary<string, object> { ["type"] = "string" }
              },
              ["required"] = new[] { "elementId", "code" }
            }
          }
        },
        ["required"] = new[] { "replacements" }
      };
    }

    private static string ExtractStructuredOutputText(OpenAiResponsesApiResponse response, out string refusalText) {
      refusalText = "";
      if (!string.IsNullOrWhiteSpace(response.OutputText)) {
        return response.OutputText;
      }

      foreach (var outputItem in response.Output) {
        foreach (var contentItem in outputItem.Content) {
          if (!string.IsNullOrWhiteSpace(contentItem.Refusal)) {
            refusalText = contentItem.Refusal;
            return "";
          }
          if (!string.IsNullOrWhiteSpace(contentItem.Text)) {
            return contentItem.Text;
          }
        }
      }

      return "";
    }

    private async Task<(bool Verified, Program Program, NaturalLanguageFeedbackByTask Feedback)> VerifyCandidateFilesAsync(
      IReadOnlyList<DafnyFile> files,
      DafnyOptions options,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      var fileNames = DafnyFile.FileNames(files);
      var programName = fileNames.Count == 1 ? fileNames[0] : "the_program";
      var (program, err) = await DafnyMain.ParseCheck(options.Input, files, programName, options);
      var feedbackTasks = program == null
        ? tasks.ToList()
        : BuildNaturalLanguageFeedbackTasks(program, tasks, sourcePathMap);
      if (feedbackTasks.Count == 0) {
        feedbackTasks = tasks.ToList();
      }
      if (err != null || program == null) {
        return (false, program, CollectFeedbackByTask(program, err ?? "Parse/resolve failed.", feedbackTasks, sourcePathMap));
      }

      if (!options.DafnyVerify) {
        return (true, program, new NaturalLanguageFeedbackByTask());
      }

      var printer = options.Printer as DafnyConsolePrinter;
      var verificationSnapshot = SnapshotVerificationResults(printer);
      var boogiePrograms =
        await DafnyMain.LargeStackFactory.StartNew(() => Translate(engine.Options, program).ToList());
      var baseName = Cce.NonNull(Path.GetFileName(fileNames[^1]));
      var (verified, _, _) = await BoogieAsync(program.Reporter, options, baseName, boogiePrograms, null);
      if (verified) {
        return (true, program, new NaturalLanguageFeedbackByTask());
      }

      var feedback = CollectFeedbackByTask(program, null, feedbackTasks, sourcePathMap);
      MergeFeedback(feedback, CollectVerificationFeedbackFromResults(
        GetNewVerificationResults(printer, verificationSnapshot), options, feedbackTasks, sourcePathMap));
      if (feedback.FeedbackByTaskId.Count == 0 && feedback.GlobalFeedback.Count == 0) {
        AddUnique(feedback.GlobalFeedback, new NaturalLanguageFailureContext { PrimaryMessage = "Verification failed." });
      }
      return (false, program, feedback);
    }

    private static Dictionary<Uri, string> LoadSourceTextsForRootFiles(
      IReadOnlyList<DafnyFile> files, DafnyOptions options) {
      var result = new Dictionary<Uri, string>();
      foreach (var file in files.Where(f => f.Uri.IsFile && f.Extension == DafnyFile.DafnyFileExtension)) {
        try {
          result[file.Uri] = File.ReadAllText(file.Uri.LocalPath);
        } catch (Exception e) {
          throw new Exception($"Cannot read source file '{options.GetPrintPath(file.Uri.LocalPath)}': {e.Message}");
        }
      }
      return result;
    }

    private static List<NaturalLanguageTask> BuildNaturalLanguageTasks(Program program,
      IReadOnlyDictionary<Uri, string> sourceTexts) {
      var tasks = new List<NaturalLanguageTask>();
      foreach (var callable in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)) {
        if (!TryGetSourceTextForUri(sourceTexts, callable.StartToken.Uri, out var uri, out var sourceText)) {
          continue;
        }

        var collector = new NaturalLanguageCollector();
        collector.Visit(callable, 0);
        if (collector.Elements.Count == 0) {
          continue;
        }

        NormalizeStatementReplacementRanges(collector.Elements, sourceText);

        var callableName = callable switch {
          MemberDecl member => member.FullDafnyName,
          TopLevelDecl topLevel => topLevel.FullDafnyName,
          _ => callable.NameRelativeToModule
        };

        var callableStart = callable.StartToken.pos;
        var callableEnd = callable.EndToken.pos + callable.EndToken.val.Length;
        var callableSource = SafeSlice(sourceText, callableStart, callableEnd);

        tasks.Add(new NaturalLanguageTask {
          TaskId = $"{callableName}@{callable.StartToken.line}:{callable.StartToken.col}",
          CallableName = callableName,
          CallableKind = callable switch {
            Function function => function.WhatKind,
            MethodOrConstructor methodOrConstructor => methodOrConstructor.WhatKind,
            _ => "callable"
          },
          FileUri = uri,
          FilePath = uri.LocalPath,
          CallableStartPos = callableStart,
          CallableEndPosExclusive = callableEnd,
          CallableSource = callableSource,
          Elements = collector.Elements
        });
      }

      return tasks;
    }

    private static IReadOnlyList<NaturalLanguageSupportDeclaration> CollectRelevantSupportDeclarations(
      Program program,
      IReadOnlyDictionary<Uri, string> sourceTexts) {
      var declarations = new List<NaturalLanguageSupportDeclaration>();
      foreach (var callable in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)) {
        if (callable is not Function function) {
          continue;
        }
        if (!TryGetSourceTextForUri(sourceTexts, callable.StartToken.Uri, out var _, out var sourceText)) {
          continue;
        }

        var declarationName = function.FullDafnyName;
        var declarationStart = function.StartToken.pos;
        var declarationEnd = function.EndToken.pos + function.EndToken.val.Length;
        var declarationSource = SafeSlice(sourceText, declarationStart, declarationEnd);
        if (string.IsNullOrWhiteSpace(declarationSource)) {
          continue;
        }

        declarations.Add(new NaturalLanguageSupportDeclaration {
          DeclarationName = declarationName,
          DeclarationKind = function.WhatKind,
          Source = declarationSource
        });
      }

      return declarations;
    }

    private static string BuildNaturalLanguagePrompt(
      NaturalLanguageTask task,
      IReadOnlyList<NaturalLanguageSupportDeclaration> supportDeclarations,
      IReadOnlyList<NaturalLanguageRetryHistoryEntry> retryHistory) {
      var prompt = new StringBuilder();
      prompt.AppendLine("You are generating Dafny code to replace natural-language placeholders inside one callable.");
      prompt.AppendLine();
      prompt.AppendLine($"Callable: {task.CallableName}");
      prompt.AppendLine($"Kind: {task.CallableKind}");
      prompt.AppendLine($"TaskId: {task.TaskId}");
      prompt.AppendLine();
      prompt.AppendLine("Callable source:");
      prompt.AppendLine("```dafny");
      prompt.AppendLine(task.CallableSource);
      prompt.AppendLine("```");
      prompt.AppendLine();
      prompt.AppendLine("Natural-language placeholders to replace:");
      foreach (var element in task.Elements) {
        prompt.AppendLine($"- {element.ElementId}: kind={element.Kind}, inferredType={element.InferredType}, line={element.Line}, column={element.Column}");
        prompt.AppendLine($"  Raw content: {element.RawContent}");
      }

      var usableDeclarations = supportDeclarations
        .Where(declaration => !string.Equals(declaration.DeclarationName, task.CallableName, StringComparison.Ordinal))
        .ToList();
      if (usableDeclarations.Count > 0) {
        prompt.AppendLine();
        prompt.AppendLine("Available predicates and functions you may use:");
        foreach (var declaration in usableDeclarations) {
          prompt.AppendLine($"- {declaration.DeclarationKind} {declaration.DeclarationName}");
          prompt.AppendLine("```dafny");
          prompt.AppendLine(declaration.Source);
          prompt.AppendLine("```");
        }
      }

      if (retryHistory.Count > 0) {
        prompt.AppendLine();
        prompt.AppendLine("Cumulative retry history for this callable:");
        foreach (var historyEntry in retryHistory.OrderBy(entry => entry.Attempt)) {
          prompt.AppendLine($"Attempt {historyEntry.Attempt} replacements:");
          foreach (var replacement in historyEntry.Replacements.OrderBy(replacement => replacement.ElementId)) {
            if ((replacement.Code ?? "").Contains('\n') || (replacement.Code ?? "").Contains('\r')) {
              prompt.AppendLine($"- {replacement.ElementId}:");
              prompt.AppendLine("```dafny");
              prompt.AppendLine(replacement.Code);
              prompt.AppendLine("```");
            } else {
              prompt.AppendLine($"- {replacement.ElementId}: {replacement.Code}");
            }
          }
          prompt.AppendLine("Feedback after that attempt:");
          foreach (var failure in historyEntry.Failures) {
            if (string.IsNullOrWhiteSpace(failure.PrimaryMessage)) {
              continue;
            }
            prompt.AppendLine("```text");
            prompt.AppendLine(failure.PrimaryMessage.TrimEnd());
            prompt.AppendLine("```");
          }
          if (historyEntry.OmittedFailureCount > 0) {
            prompt.AppendLine($"- {historyEntry.OmittedFailureCount} additional diagnostic(s) omitted.");
          }
        }
      }

      prompt.AppendLine();
      prompt.AppendLine("Requirements:");
      prompt.AppendLine("- Return replacement code for every ElementId in this callable.");
      prompt.AppendLine("- For expression placeholders, return only a Dafny expression.");
      prompt.AppendLine("- For statement placeholders, return Dafny statements that replace the placeholder statement.");
      prompt.AppendLine("- Preserve surrounding specifications and verifier obligations.");
      prompt.AppendLine("- Improve on every failed attempt using the cumulative retry history above.");
      prompt.AppendLine("- Do not return markdown fences or explanations.");
      prompt.AppendLine("- The transport response should map each ElementId to replacement code.");
      return prompt.ToString();
    }

    private static bool TryGetSourceTextForUri(
      IReadOnlyDictionary<Uri, string> sourceTexts,
      Uri uri,
      out Uri matchedUri,
      out string sourceText) {
      matchedUri = null;
      sourceText = "";
      if (uri == null || !uri.IsFile) {
        return false;
      }
      if (sourceTexts.TryGetValue(uri, out sourceText)) {
        matchedUri = uri;
        return true;
      }

      var normalizedPath = Path.GetFullPath(uri.LocalPath);
      var alternate = sourceTexts.FirstOrDefault(entry =>
        entry.Key.IsFile && string.Equals(Path.GetFullPath(entry.Key.LocalPath), normalizedPath,
          StringComparison.OrdinalIgnoreCase));
      if (alternate.Key == null) {
        return false;
      }

      matchedUri = alternate.Key;
      sourceText = alternate.Value;
      return true;
    }

    private static void NormalizeStatementReplacementRanges(
      IReadOnlyList<NaturalLanguageElement> elements,
      string sourceText) {
      foreach (var element in elements.Where(element => element.Kind == "statement")) {
        if (element.EndPosExclusive < sourceText.Length && sourceText[element.EndPosExclusive] == ';') {
          element.EndPosExclusive++;
        }
      }
    }

    private static bool TryApplyNaturalLanguageResponses(
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<Uri, string> originalSources,
      NaturalLanguageResponseFile response,
      out Dictionary<Uri, string> rewrittenSources,
      out Dictionary<string, NaturalLanguageAppliedTaskContext> appliedTaskContexts,
      out string error) {
      rewrittenSources = originalSources.ToDictionary(kv => kv.Key, kv => kv.Value);
      appliedTaskContexts = new Dictionary<string, NaturalLanguageAppliedTaskContext>(StringComparer.Ordinal);
      var replacementsByFile = new Dictionary<Uri, List<TextReplacement>>();
      var appliedReplacementsByTaskId = new Dictionary<string, List<NaturalLanguageAppliedReplacement>>(StringComparer.Ordinal);
      var responseByTask = response.Tasks.ToDictionary(task => task.TaskId, task => task);

      foreach (var task in tasks) {
        if (!responseByTask.TryGetValue(task.TaskId, out var taskResponse)) {
          error = $"missing response for task '{task.TaskId}'";
          return false;
        }

        var replacementsById = taskResponse.Replacements.ToDictionary(replacement => replacement.ElementId, replacement => replacement);
        foreach (var element in task.Elements) {
          if (!replacementsById.TryGetValue(element.ElementId, out var replacement)) {
            error = $"missing replacement for element '{element.ElementId}' in task '{task.TaskId}'";
            return false;
          }

          var uri = new Uri(Path.GetFullPath(task.FilePath));
          if (!replacementsByFile.TryGetValue(uri, out var replacementsForUri)) {
            replacementsForUri = [];
            replacementsByFile[uri] = replacementsForUri;
          }
          replacementsForUri.Add(new TextReplacement {
            TaskId = task.TaskId,
            ElementId = element.ElementId,
            StartPos = element.StartPos,
            EndPosExclusive = element.EndPosExclusive,
            Code = replacement.Code ?? ""
          });
        }
      }

      foreach (var (uri, replacements) in replacementsByFile) {
        if (!rewrittenSources.TryGetValue(uri, out var sourceText)) {
          error = $"no source text available for '{uri.LocalPath}'";
          return false;
        }

        var ordered = replacements
          .OrderBy(replacement => replacement.StartPos)
          .ThenBy(replacement => replacement.EndPosExclusive)
          .ToList();
        var rewritten = new StringBuilder(sourceText.Length);
        var cursor = 0;
        foreach (var replacement in ordered) {
          if (replacement.StartPos < 0 || replacement.EndPosExclusive < replacement.StartPos || replacement.EndPosExclusive > sourceText.Length) {
            error = $"invalid replacement range [{replacement.StartPos}, {replacement.EndPosExclusive}) in '{uri.LocalPath}'";
            return false;
          }
          if (replacement.StartPos < cursor) {
            error = $"overlapping replacement range [{replacement.StartPos}, {replacement.EndPosExclusive}) in '{uri.LocalPath}'";
            return false;
          }

          rewritten.Append(sourceText, cursor, replacement.StartPos - cursor);
          var insertedStart = rewritten.Length;
          rewritten.Append(replacement.Code);
          var insertedEnd = rewritten.Length;
          cursor = replacement.EndPosExclusive;

          if (!appliedReplacementsByTaskId.TryGetValue(replacement.TaskId, out var appliedReplacements)) {
            appliedReplacements = [];
            appliedReplacementsByTaskId[replacement.TaskId] = appliedReplacements;
          }
          appliedReplacements.Add(new NaturalLanguageAppliedReplacement {
            ElementId = replacement.ElementId,
            RewrittenStartPos = insertedStart,
            RewrittenEndPosExclusive = insertedEnd
          });
        }
        rewritten.Append(sourceText, cursor, sourceText.Length - cursor);

        var rewrittenText = rewritten.ToString();
        rewrittenSources[uri] = rewrittenText;

        foreach (var task in tasks.Where(task => string.Equals(NormalizeFilePath(task.FilePath), NormalizeFilePath(uri.LocalPath), StringComparison.OrdinalIgnoreCase))) {
          var rewrittenCallableStart = AdjustPositionThroughReplacements(task.CallableStartPos, ordered);
          var rewrittenCallableEnd = AdjustPositionThroughReplacements(task.CallableEndPosExclusive, ordered);
          appliedTaskContexts[task.TaskId] = new NaturalLanguageAppliedTaskContext {
            TaskId = task.TaskId,
            FilePath = NormalizeFilePath(uri.LocalPath),
            CallableStartPos = rewrittenCallableStart,
            CallableEndPosExclusive = rewrittenCallableEnd,
            CallableStartLine = GetLineNumberAtPosition(rewrittenText, rewrittenCallableStart),
            CallableSource = SafeSlice(rewrittenText, rewrittenCallableStart, rewrittenCallableEnd),
            Replacements = appliedReplacementsByTaskId.TryGetValue(task.TaskId, out var appliedReplacements)
              ? appliedReplacements.OrderBy(replacement => replacement.RewrittenStartPos).ToList()
              : []
          };
        }
      }

      error = "";
      return true;
    }

    private static List<NaturalLanguageTask> BuildNaturalLanguageFeedbackTasks(
      Program program,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      var tasksByOriginalPathAndCallable = tasks
        .GroupBy(task => (NormalizeFilePath(task.FilePath), task.CallableName))
        .ToDictionary(
          group => group.Key,
          group => new Queue<NaturalLanguageTask>(group.OrderBy(task => task.CallableStartPos)));

      var result = new List<NaturalLanguageTask>();
      foreach (var callable in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(program.DefaultModuleDef.TopLevelDecls)) {
        if (callable.StartToken.Uri == null || !callable.StartToken.Uri.IsFile) {
          continue;
        }

        var callableName = callable switch {
          MemberDecl member => member.FullDafnyName,
          TopLevelDecl topLevel => topLevel.FullDafnyName,
          _ => callable.NameRelativeToModule
        };
        var originalPath = ResolveOriginalTaskFilePath(callable.StartToken.Uri.LocalPath, sourcePathMap);
        if (!tasksByOriginalPathAndCallable.TryGetValue((originalPath, callableName), out var matchingTasks) || matchingTasks.Count == 0) {
          continue;
        }

        var matchingTask = matchingTasks.Dequeue();
        result.Add(new NaturalLanguageTask {
          TaskId = matchingTask.TaskId,
          CallableName = matchingTask.CallableName,
          FileUri = callable.StartToken.Uri,
          FilePath = callable.StartToken.Uri.LocalPath,
          CallableStartPos = callable.StartToken.pos,
          CallableEndPosExclusive = callable.EndToken.pos + callable.EndToken.val.Length
        });
      }

      return result;
    }

    private static Dictionary<Uri, string> WriteRewrittenSources(
      IReadOnlyList<DafnyFile> originalFiles,
      IReadOnlyDictionary<Uri, string> rewrittenSources,
      string suffix,
      string outputDirectoryOverride = null) {
      var result = new Dictionary<Uri, string>();
      foreach (var original in originalFiles.Where(file => file.Uri.IsFile && file.Extension == DafnyFile.DafnyFileExtension)) {
        if (!rewrittenSources.TryGetValue(original.Uri, out var rewrittenText)) {
          continue;
        }

        var originalPath = original.Uri.LocalPath;
        var outputDirectory = outputDirectoryOverride ?? Path.GetDirectoryName(originalPath) ?? ".";
        Directory.CreateDirectory(outputDirectory);
        var rewrittenPath = Path.Combine(
          outputDirectory,
          Path.GetFileNameWithoutExtension(originalPath) + suffix + DafnyFile.DafnyFileExtension);

        File.WriteAllText(rewrittenPath, rewrittenText);
        result[original.Uri] = rewrittenPath;
      }

      return result;
    }

    private static Dictionary<string, string> BuildNaturalLanguageSourcePathMap(
      IReadOnlyDictionary<Uri, string> rewrittenPathsByOriginalUri) {
      var result = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
      foreach (var (originalUri, rewrittenPath) in rewrittenPathsByOriginalUri) {
        if (!originalUri.IsFile) {
          continue;
        }

        result[NormalizeFilePath(rewrittenPath)] = NormalizeFilePath(originalUri.LocalPath);
      }

      return result;
    }

    private static void TryDeleteDirectory(string directoryPath) {
      try {
        if (Directory.Exists(directoryPath)) {
          Directory.Delete(directoryPath, recursive: true);
        }
      } catch {
        // Best-effort cleanup for temporary NL verification files.
      }
    }

    private static List<DafnyFile> CreateDafnyFilesFromPaths(
      IReadOnlyList<DafnyFile> originalFiles,
      IReadOnlyDictionary<Uri, string> replacementPaths,
      DafnyOptions options) {
      var result = new List<DafnyFile>();
      var reporter = new ConsoleErrorReporter(options);
      foreach (var original in originalFiles) {
        if (!original.Uri.IsFile || !replacementPaths.TryGetValue(original.Uri, out var replacementPath)) {
          result.Add(original);
          continue;
        }

        var replacementUri = new Uri(Path.GetFullPath(replacementPath));
        var asLibrary = original.ShouldNotCompile && original.ShouldNotVerify;
        var rewritten = DafnyFile.HandleDafnyFile(OnDiskFileSystem.Instance, reporter, options, replacementUri, Token.Cli, asLibrary);
        if (rewritten == null) {
          throw new Exception($"Failed to create DafnyFile for rewritten source '{replacementPath}'");
        }

        result.Add(rewritten);
      }

      return result;
    }

    private static string SafeSlice(string sourceText, int start, int endExclusive) {
      if (start < 0 || endExclusive < start || endExclusive > sourceText.Length) {
        return "";
      }
      return sourceText.Substring(start, endExclusive - start);
    }

    private static string SanitizeForPath(string value) {
      var invalidCharacters = Path.GetInvalidFileNameChars();
      var builder = new StringBuilder(value.Length);
      foreach (var character in value) {
        builder.Append(invalidCharacters.Contains(character) || character == ':' || character == '.' ? '_' : character);
      }
      return builder.ToString();
    }

    private static NaturalLanguageFeedbackByTask CollectFeedbackByTask(
      Program program,
      string fallbackError,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, string> sourcePathMap = null) {
      var result = new NaturalLanguageFeedbackByTask();
      if (program?.Reporter is BatchErrorReporter batchReporter) {
        foreach (var diagnostic in batchReporter.AllMessages.Where(message => message.Level == ErrorLevel.Error)) {
          var failure = CreateFailureContext(program.Options, diagnostic, sourcePathMap);
          if (failure == null) {
            continue;
          }

          var owner = tasks.FirstOrDefault(task =>
            diagnostic.Range?.StartToken?.Uri != null &&
            task.FileUri != null &&
            task.FileUri.IsFile &&
            string.Equals(
              ResolveOriginalTaskFilePath(task.FileUri.LocalPath, sourcePathMap),
              ResolveOriginalTaskFilePath(diagnostic.Range.StartToken.Uri.LocalPath, sourcePathMap),
              StringComparison.OrdinalIgnoreCase) &&
            diagnostic.Range.StartToken.pos >= task.CallableStartPos &&
            diagnostic.Range.StartToken.pos < task.CallableEndPosExclusive);
          if (owner == null) {
            AddUnique(result.GlobalFeedback, failure);
            continue;
          }

          if (!result.FeedbackByTaskId.TryGetValue(owner.TaskId, out var feedbackForTask)) {
            feedbackForTask = [];
            result.FeedbackByTaskId[owner.TaskId] = feedbackForTask;
          }
          AddUnique(feedbackForTask, failure);
        }
      }

      if (result.FeedbackByTaskId.Count == 0 && result.GlobalFeedback.Count == 0 && fallbackError != null) {
        AddUnique(result.GlobalFeedback, new NaturalLanguageFailureContext { PrimaryMessage = fallbackError });
      }

      return result;
    }

    private static List<DafnyConsolePrinter.ConsoleLogEntry> SnapshotVerificationResults(DafnyConsolePrinter printer) {
      if (printer == null) {
        return [];
      }

      return printer.VerificationResults.ToList();
    }

    private static IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> GetNewVerificationResults(
      DafnyConsolePrinter printer,
      IReadOnlyList<DafnyConsolePrinter.ConsoleLogEntry> snapshot) {
      if (printer == null) {
        return Enumerable.Empty<DafnyConsolePrinter.ConsoleLogEntry>();
      }

      return printer.VerificationResults.Where(entry => !snapshot.Any(existing => ReferenceEquals(existing, entry)));
    }

    private static NaturalLanguageFeedbackByTask CollectVerificationFeedbackFromResults(
      IEnumerable<DafnyConsolePrinter.ConsoleLogEntry> verificationResults,
      DafnyOptions options,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      var result = new NaturalLanguageFeedbackByTask();
      foreach (var verificationResult in verificationResults) {
        var hadDetailedFeedback = false;
        foreach (var counterexample in verificationResult.Result.Counterexamples ?? []) {
          if (!TryGetCounterexampleFeedback(counterexample, out var token, out var message)) {
            continue;
          }

          hadDetailedFeedback = true;
          AddFeedbackForToken(result, tasks, token, CreateFailureContext(options, token, message, sourcePathMap), sourcePathMap);
        }

        if (!hadDetailedFeedback &&
            TryDescribeVerificationOutcome(verificationResult, out var outcomeToken, out var outcomeMessage)) {
          AddFeedbackForToken(result, tasks, outcomeToken, CreateFailureContext(options, outcomeToken, outcomeMessage, sourcePathMap), sourcePathMap);
        }
      }

      return result;
    }

    private static bool TryGetCounterexampleFeedback(Counterexample counterexample, out IToken token, out string message) {
      switch (counterexample) {
        case CallCounterexample callCounterexample:
          token = callCounterexample.FailingCall.tok;
          message = callCounterexample.FailingCall.Description.FailureDescription;
          return true;
        case ReturnCounterexample returnCounterexample:
          token = returnCounterexample.FailingReturn.tok;
          message = returnCounterexample.FailingReturn.Description.FailureDescription;
          return true;
        case AssertCounterexample assertCounterexample:
          token = assertCounterexample.FailingAssert.tok;
          message = assertCounterexample.FailingAssert.ErrorMessage ??
            assertCounterexample.FailingAssert.Description.FailureDescription;
          return true;
        default:
          token = null;
          message = "";
          return false;
      }
    }

    private static bool TryDescribeVerificationOutcome(
      DafnyConsolePrinter.ConsoleLogEntry verificationResult,
      out IToken token,
      out string message) {
      token = verificationResult.Implementation.Tok;
      var implementationName = verificationResult.Implementation.Name;
      switch (verificationResult.Result.Outcome) {
        case VcOutcome.Errors:
          message = $"Verification failed for '{implementationName}'.";
          return true;
        case VcOutcome.TimedOut:
          message = $"Verification of '{implementationName}' timed out.";
          return true;
        case VcOutcome.OutOfResource:
          message = $"Verification ran out of resources for '{implementationName}'.";
          return true;
        case VcOutcome.OutOfMemory:
          message = $"Verification ran out of memory for '{implementationName}'.";
          return true;
        case VcOutcome.SolverException:
          message = $"Verification encountered a solver exception for '{implementationName}'.";
          return true;
        case VcOutcome.Inconclusive:
          message = $"Verification was inconclusive for '{implementationName}'.";
          return true;
        default:
          message = "";
          return false;
      }
    }

    private static void AddFeedbackForToken(
      NaturalLanguageFeedbackByTask feedback,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IToken token,
      NaturalLanguageFailureContext failure,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      if (failure == null || string.IsNullOrWhiteSpace(failure.PrimaryMessage)) {
        return;
      }

      var owner = FindTaskForToken(token, tasks, sourcePathMap);
      if (owner == null) {
        AddUnique(feedback.GlobalFeedback, failure);
        return;
      }

      if (!feedback.FeedbackByTaskId.TryGetValue(owner.TaskId, out var taskFeedback)) {
        taskFeedback = [];
        feedback.FeedbackByTaskId[owner.TaskId] = taskFeedback;
      }

      AddUnique(taskFeedback, failure);
    }

    private static NaturalLanguageTask FindTaskForToken(
      IToken token,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      if (token == null) {
        return null;
      }

      var dafnyToken = BoogieGenerator.ToDafnyToken(token);
      if (dafnyToken?.Uri == null || !dafnyToken.Uri.IsFile) {
        return null;
      }

      var tokenPath = ResolveOriginalTaskFilePath(dafnyToken.Uri.LocalPath, sourcePathMap);
      return tasks.FirstOrDefault(task =>
        task.FileUri != null &&
        task.FileUri.IsFile &&
        string.Equals(ResolveOriginalTaskFilePath(task.FileUri.LocalPath, sourcePathMap), tokenPath, StringComparison.OrdinalIgnoreCase) &&
        dafnyToken.pos >= task.CallableStartPos &&
        dafnyToken.pos < task.CallableEndPosExclusive);
    }

    private static string ResolveOriginalTaskFilePath(
      string filePath,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      var normalizedPath = NormalizeFilePath(filePath);
      if (sourcePathMap != null && sourcePathMap.TryGetValue(normalizedPath, out var originalPath)) {
        return originalPath;
      }

      return normalizedPath;
    }

    private static string NormalizeFilePath(string filePath) {
      return string.IsNullOrWhiteSpace(filePath) ? "" : Path.GetFullPath(filePath);
    }

    private static void MergeFeedback(NaturalLanguageFeedbackByTask target, NaturalLanguageFeedbackByTask source) {
      foreach (var (taskId, feedback) in source.FeedbackByTaskId) {
        if (!target.FeedbackByTaskId.TryGetValue(taskId, out var targetFeedback)) {
          targetFeedback = [];
          target.FeedbackByTaskId[taskId] = targetFeedback;
        }

        foreach (var failure in feedback) {
          AddUnique(targetFeedback, failure);
        }
      }

      foreach (var failure in source.GlobalFeedback) {
        AddUnique(target.GlobalFeedback, failure);
      }
    }

    private static void AddUnique(List<NaturalLanguageFailureContext> failures, NaturalLanguageFailureContext failure) {
      if (failure == null) {
        return;
      }

      if (!failures.Any(existing => FailureContextsMatch(existing, failure))) {
        failures.Add(failure);
      }
    }

    private static bool FailureContextsMatch(NaturalLanguageFailureContext left, NaturalLanguageFailureContext right) {
      if (left == null || right == null) {
        return false;
      }

      return string.Equals(left.PrimaryLocation, right.PrimaryLocation, StringComparison.Ordinal) &&
             string.Equals(left.PrimaryMessage, right.PrimaryMessage, StringComparison.Ordinal) &&
             string.Equals(left.PrimaryFilePath, right.PrimaryFilePath, StringComparison.OrdinalIgnoreCase) &&
             left.PrimaryStartPos == right.PrimaryStartPos &&
             left.PrimaryEndPosExclusive == right.PrimaryEndPosExclusive &&
             string.Equals(left.Excerpt, right.Excerpt, StringComparison.Ordinal) &&
             left.OverlappingElementIds.SequenceEqual(right.OverlappingElementIds) &&
             RelatedFailureContextsMatch(left.RelatedMessages, right.RelatedMessages);
    }

    private static bool RelatedFailureContextsMatch(
      IReadOnlyList<NaturalLanguageRelatedFailureContext> left,
      IReadOnlyList<NaturalLanguageRelatedFailureContext> right) {
      if (ReferenceEquals(left, right)) {
        return true;
      }
      if (left == null || right == null || left.Count != right.Count) {
        return false;
      }

      for (var i = 0; i < left.Count; i++) {
        if (!string.Equals(left[i].Location, right[i].Location, StringComparison.Ordinal) ||
            !string.Equals(left[i].Message, right[i].Message, StringComparison.Ordinal)) {
          return false;
        }
      }

      return true;
    }

    private static List<NaturalLanguageTask> SelectTasksToRequest(
      int attempt,
      IReadOnlyList<NaturalLanguageTask> tasks,
      NaturalLanguageFeedbackByTask feedback,
      IReadOnlyDictionary<string, NaturalLanguageTaskState> taskStates) {
      if (attempt == 1) {
        return tasks.ToList();
      }

      var failedTaskIds = feedback.FeedbackByTaskId.Keys.ToHashSet();
      foreach (var task in tasks) {
        if (!taskStates.TryGetValue(task.TaskId, out var taskState) || taskState.CurrentResponse == null) {
          failedTaskIds.Add(task.TaskId);
        }
      }

      if (failedTaskIds.Count == 0) {
        if (feedback.GlobalFeedback.Count > 0) {
          return tasks.ToList();
        }
        return [];
      }

      return tasks.Where(task => failedTaskIds.Contains(task.TaskId)).ToList();
    }

    private static bool TryBuildNaturalLanguageResponseFile(
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, NaturalLanguageTaskState> taskStates,
      out NaturalLanguageResponseFile response,
      out string error) {
      response = new NaturalLanguageResponseFile();
      foreach (var task in tasks) {
        if (!taskStates.TryGetValue(task.TaskId, out var taskState) || taskState.CurrentResponse == null) {
          error = $"missing response for task '{task.TaskId}'";
          return false;
        }
        response.Tasks.Add(taskState.CurrentResponse);
      }

      error = "";
      return true;
    }

    private static void RecordRetryHistory(
      int attempt,
      NaturalLanguageFeedbackByTask feedback,
      IReadOnlyList<NaturalLanguageTask> tasks,
      IReadOnlyDictionary<string, NaturalLanguageTaskState> taskStates,
      IReadOnlyDictionary<string, NaturalLanguageAppliedTaskContext> appliedTaskContexts) {
      var feedbackTargets = feedback.FeedbackByTaskId.Keys.ToHashSet();
      var applyGlobalFeedbackToAllTasks = feedbackTargets.Count == 0 && feedback.GlobalFeedback.Count > 0;

      foreach (var task in tasks) {
        if (!taskStates.TryGetValue(task.TaskId, out var taskState) || taskState.CurrentResponse == null) {
          continue;
        }

        var combinedFeedback = new List<NaturalLanguageFailureContext>();
        if (feedback.FeedbackByTaskId.TryGetValue(task.TaskId, out var taskFeedback)) {
          foreach (var failure in taskFeedback) {
            AddUnique(combinedFeedback, failure);
          }
        }
        if (feedback.GlobalFeedback.Count > 0 && (applyGlobalFeedbackToAllTasks || combinedFeedback.Count > 0)) {
          foreach (var failure in feedback.GlobalFeedback.Where(failure => ShouldIncludeGlobalFailureForTask(task.TaskId, failure, appliedTaskContexts))) {
            AddUnique(combinedFeedback, failure);
          }
        }
        if (combinedFeedback.Count == 0) {
          continue;
        }

        var promptFailures = combinedFeedback
          .Select(failure => CreatePromptFailureContext(task.TaskId, failure, appliedTaskContexts))
          .OrderBy(failure => failure.PrimaryFilePath, StringComparer.OrdinalIgnoreCase)
          .ThenBy(failure => failure.PrimaryStartPos)
          .ThenBy(failure => failure.PrimaryMessage, StringComparer.Ordinal)
          .ToList();
        var retainedFailures = promptFailures.Take(3).ToList();

        taskState.RetryHistory.Add(new NaturalLanguageRetryHistoryEntry {
          Attempt = attempt,
          Failures = retainedFailures,
          OmittedFailureCount = Math.Max(0, promptFailures.Count - retainedFailures.Count),
          Replacements = taskState.CurrentResponse.Replacements
            .Select(replacement => new NaturalLanguageReplacementResponse {
              ElementId = replacement.ElementId,
              Code = replacement.Code
            })
            .ToList()
        });
      }
    }

    private static bool ShouldIncludeGlobalFailureForTask(
      string taskId,
      NaturalLanguageFailureContext failure,
      IReadOnlyDictionary<string, NaturalLanguageAppliedTaskContext> appliedTaskContexts) {
      if (failure == null) {
        return false;
      }
      if (string.IsNullOrWhiteSpace(failure.PrimaryFilePath) || failure.PrimaryStartPos < 0) {
        return true;
      }
      if (!appliedTaskContexts.TryGetValue(taskId, out var taskContext)) {
        return true;
      }

      return string.Equals(NormalizeFilePath(taskContext.FilePath), failure.PrimaryFilePath, StringComparison.OrdinalIgnoreCase) &&
             failure.PrimaryStartPos >= taskContext.CallableStartPos &&
             failure.PrimaryStartPos < taskContext.CallableEndPosExclusive;
    }

    private static NaturalLanguageFailureContext CreatePromptFailureContext(
      string taskId,
      NaturalLanguageFailureContext failure,
      IReadOnlyDictionary<string, NaturalLanguageAppliedTaskContext> appliedTaskContexts) {
      return CloneFailureContext(failure);
    }

    private static NaturalLanguageFailureContext CloneFailureContext(NaturalLanguageFailureContext failure) {
      if (failure == null) {
        return null;
      }

      return new NaturalLanguageFailureContext {
        PrimaryLocation = failure.PrimaryLocation,
        PrimaryMessage = failure.PrimaryMessage,
        PrimaryFilePath = failure.PrimaryFilePath,
        PrimaryStartPos = failure.PrimaryStartPos,
        PrimaryEndPosExclusive = failure.PrimaryEndPosExclusive,
        Excerpt = failure.Excerpt,
        RelatedMessages = failure.RelatedMessages
          .Select(related => new NaturalLanguageRelatedFailureContext {
            Location = related.Location,
            Message = related.Message
          })
          .ToList(),
        OverlappingElementIds = failure.OverlappingElementIds.ToList()
      };
    }

    private static NaturalLanguageFailureContext CreateFailureContext(
      DafnyOptions options,
      DafnyDiagnostic diagnostic,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      if (diagnostic == null) {
        return null;
      }

      return new NaturalLanguageFailureContext {
        PrimaryLocation = diagnostic.Range?.ToFileRangeString(options) ?? "",
        PrimaryMessage = RenderDiagnosticBlock(options, diagnostic).TrimEnd(),
        PrimaryFilePath = diagnostic.Range?.StartToken?.Uri != null && diagnostic.Range.StartToken.Uri.IsFile
          ? ResolveOriginalTaskFilePath(diagnostic.Range.StartToken.Uri.LocalPath, sourcePathMap)
          : (string.IsNullOrWhiteSpace(diagnostic.Range?.StartToken?.Filepath)
            ? ""
            : ResolveOriginalTaskFilePath(diagnostic.Range.StartToken.Filepath, sourcePathMap)),
        PrimaryStartPos = diagnostic.Range?.StartToken?.pos ?? -1,
        PrimaryEndPosExclusive = diagnostic.Range == null
          ? -1
          : diagnostic.Range.EndToken.pos + Math.Max(diagnostic.Range.EndLength, 1)
      };
    }

    private static NaturalLanguageFailureContext CreateFailureContext(
      DafnyOptions options,
      IToken token,
      string message,
      IReadOnlyDictionary<string, string> sourcePathMap) {
      if (string.IsNullOrWhiteSpace(message)) {
        return null;
      }

      var dafnyToken = token == null ? null : BoogieGenerator.ToDafnyToken(token);
      return new NaturalLanguageFailureContext {
        PrimaryLocation = dafnyToken?.OriginToString(options) ?? "",
        PrimaryMessage = RenderVerificationFeedbackBlock(options, token, message).TrimEnd(),
        PrimaryFilePath = dafnyToken?.Uri != null && dafnyToken.Uri.IsFile
          ? ResolveOriginalTaskFilePath(dafnyToken.Uri.LocalPath, sourcePathMap)
          : (string.IsNullOrWhiteSpace(dafnyToken?.Filepath)
            ? ""
            : ResolveOriginalTaskFilePath(dafnyToken.Filepath, sourcePathMap)),
        PrimaryStartPos = dafnyToken?.pos ?? -1,
        PrimaryEndPosExclusive = dafnyToken == null
          ? -1
          : dafnyToken.pos + Math.Max(dafnyToken.val?.Length ?? 0, 1)
      };
    }

    private static string RenderDiagnosticBlock(DafnyOptions options, DafnyDiagnostic diagnostic) {
      var block = ErrorReporter.FormatDiagnostic(options, diagnostic).Replace("\n", "\n ");
      if (options.Verbose && !string.IsNullOrEmpty(diagnostic.ErrorId) && diagnostic.ErrorId != "none") {
        block += " (ID: " + diagnostic.ErrorId + ")\n";
        var info = ErrorRegistry.GetDetail(diagnostic.ErrorId);
        if (info != null) {
          block += info;
        }
      } else {
        block += "\n";
      }

      if (options.Get(Snippets.ShowSnippets) && diagnostic.Range.Uri != null) {
        var tw = new StringWriter();
        Snippets.WriteSourceCodeSnippet(options, diagnostic.Range, tw);
        block += tw.ToString();
      }

      foreach (var related in diagnostic.RelatedInformation) {
        var innerMessage = string.IsNullOrEmpty(related.Message)
          ? "Related location"
          : "Related location: " + related.Message;
        block += $"{related.Range.ToFileRangeString(options)}: {innerMessage}\n";
        if (options.Get(Snippets.ShowSnippets)) {
          var tw = new StringWriter();
          Snippets.WriteSourceCodeSnippet(options, related.Range, tw);
          block += tw.ToString();
        }
      }

      return block;
    }

    private static string RenderVerificationFeedbackBlock(DafnyOptions options, IToken token, string message) {
      var printer = new DafnyConsolePrinter(options);
      var writer = new StringWriter();
      printer.ReportBplError(token, message, true, writer);
      return writer.ToString();
    }

    private static string FormatFailureContextForPrompt(NaturalLanguageFailureContext failure) {
      if (failure == null) {
        return "";
      }
      if (string.IsNullOrWhiteSpace(failure.PrimaryLocation)) {
        return failure.PrimaryMessage;
      }
      if (string.IsNullOrWhiteSpace(failure.PrimaryMessage)) {
        return failure.PrimaryLocation;
      }
      return $"{failure.PrimaryLocation}: {failure.PrimaryMessage}";
    }

    private static string FormatRelatedFailureContextForPrompt(NaturalLanguageRelatedFailureContext related) {
      if (related == null) {
        return "";
      }
      if (string.IsNullOrWhiteSpace(related.Location)) {
        return related.Message;
      }
      if (string.IsNullOrWhiteSpace(related.Message)) {
        return related.Location;
      }
      return $"{related.Location}: {related.Message}";
    }

    private static List<string> FindOverlappingElementIds(
      NaturalLanguageAppliedTaskContext taskContext,
      NaturalLanguageFailureContext failure) {
      if (taskContext == null || failure == null || string.IsNullOrWhiteSpace(failure.PrimaryFilePath) || failure.PrimaryStartPos < 0) {
        return [];
      }
      if (!string.Equals(NormalizeFilePath(taskContext.FilePath), failure.PrimaryFilePath, StringComparison.OrdinalIgnoreCase)) {
        return [];
      }

      var failureStart = failure.PrimaryStartPos;
      var failureEnd = failure.PrimaryEndPosExclusive > failureStart ? failure.PrimaryEndPosExclusive : failureStart + 1;
      return taskContext.Replacements
        .Where(replacement => RangesOverlap(failureStart, failureEnd, replacement.RewrittenStartPos, replacement.RewrittenEndPosExclusive))
        .Select(replacement => replacement.ElementId)
        .OrderBy(elementId => elementId, StringComparer.Ordinal)
        .ToList();
    }

    private static bool RangesOverlap(int start1, int end1, int start2, int end2) {
      return start1 < end2 && start2 < end1;
    }

    private static string BuildFailureExcerpt(
      NaturalLanguageAppliedTaskContext taskContext,
      NaturalLanguageFailureContext failure) {
      if (taskContext == null || failure == null || string.IsNullOrWhiteSpace(failure.PrimaryFilePath) ||
          !string.Equals(NormalizeFilePath(taskContext.FilePath), failure.PrimaryFilePath, StringComparison.OrdinalIgnoreCase) ||
          string.IsNullOrEmpty(taskContext.CallableSource)) {
        return "";
      }

      var lines = new List<string>();
      var lineStarts = new List<int>();
      var lineStart = 0;
      for (var i = 0; i < taskContext.CallableSource.Length; i++) {
        if (taskContext.CallableSource[i] == '\r' || taskContext.CallableSource[i] == '\n') {
          lines.Add(taskContext.CallableSource.Substring(lineStart, i - lineStart));
          lineStarts.Add(lineStart);
          if (taskContext.CallableSource[i] == '\r' && i + 1 < taskContext.CallableSource.Length && taskContext.CallableSource[i + 1] == '\n') {
            i++;
          }
          lineStart = i + 1;
        }
      }
      lines.Add(taskContext.CallableSource.Substring(lineStart));
      lineStarts.Add(lineStart);

      var failureLineIndex = -1;
      var caretStart = 0;
      var caretLength = 1;
      if (failure.PrimaryStartPos >= taskContext.CallableStartPos &&
          failure.PrimaryStartPos < taskContext.CallableEndPosExclusive) {
        var localStart = failure.PrimaryStartPos - taskContext.CallableStartPos;
        var localEnd = failure.PrimaryEndPosExclusive > failure.PrimaryStartPos
          ? failure.PrimaryEndPosExclusive - taskContext.CallableStartPos
          : localStart + 1;
        if (localStart >= 0 && localStart < taskContext.CallableSource.Length) {
          for (var i = 0; i < lineStarts.Count; i++) {
            var nextLineStart = i + 1 < lineStarts.Count ? lineStarts[i + 1] : taskContext.CallableSource.Length + 1;
            if (localStart < nextLineStart) {
              failureLineIndex = i;
              var lineStartOffset = lineStarts[i];
              caretStart = Math.Max(0, Math.Min(lines[i].Length, localStart - lineStartOffset));
              var maxEndInLine = lineStartOffset + lines[i].Length;
              var caretEnd = Math.Max(caretStart + 1, Math.Min(Math.Max(localEnd, localStart + 1), maxEndInLine) - lineStartOffset);
              caretLength = Math.Max(1, caretEnd - caretStart);
              break;
            }
          }
        }
      }

      if (failureLineIndex < 0 && TryParseLineAndColumnFromLocation(failure.PrimaryLocation, out var lineNumber, out var column)) {
        var localLineIndex = lineNumber - taskContext.CallableStartLine;
        if (0 <= localLineIndex && localLineIndex < lines.Count) {
          failureLineIndex = localLineIndex;
          caretStart = Math.Max(0, Math.Min(lines[localLineIndex].Length, column));
          caretLength = 1;
        }
      }

      if (failureLineIndex < 0) {
        return "";
      }

      var excerptStartLine = Math.Max(0, failureLineIndex - 2);
      var excerptEndLine = Math.Min(lines.Count - 1, failureLineIndex + 2);
      var numberWidth = (taskContext.CallableStartLine + excerptEndLine).ToString().Length;
      var builder = new StringBuilder();
      for (var i = excerptStartLine; i <= excerptEndLine; i++) {
        var displayedLineNumber = taskContext.CallableStartLine + i;
        builder.AppendLine($"{displayedLineNumber.ToString().PadLeft(numberWidth)} | {lines[i]}");
        if (i == failureLineIndex) {
          builder.AppendLine($"{new string(' ', numberWidth)} | {new string(' ', caretStart)}{new string('^', caretLength)}");
        }
      }

      return builder.ToString().TrimEnd();
    }

    private static bool TryParseLineAndColumnFromLocation(string location, out int line, out int column) {
      line = 0;
      column = 0;
      if (string.IsNullOrWhiteSpace(location)) {
        return false;
      }

      var match = Regex.Match(location, @"\((\d+)(?:,|:)(\d+)");
      if (!match.Success) {
        return false;
      }

      return int.TryParse(match.Groups[1].Value, out line) && int.TryParse(match.Groups[2].Value, out column);
    }

    private static int AdjustPositionThroughReplacements(int originalPosition, IReadOnlyList<TextReplacement> replacements) {
      var adjustedPosition = originalPosition;
      foreach (var replacement in replacements) {
        if (replacement.EndPosExclusive <= originalPosition) {
          adjustedPosition += replacement.Code.Length - (replacement.EndPosExclusive - replacement.StartPos);
        }
      }
      return adjustedPosition;
    }

    private static int GetLineNumberAtPosition(string sourceText, int position) {
      if (position <= 0 || string.IsNullOrEmpty(sourceText)) {
        return 1;
      }

      var clampedPosition = Math.Min(position, sourceText.Length);
      var line = 1;
      for (var i = 0; i < clampedPosition; i++) {
        if (sourceText[i] == '\n') {
          line++;
        }
      }
      return line;
    }

    private sealed class NaturalLanguageCollector : TopDownVisitor<int> {
      private int nextId = 1;
      public List<NaturalLanguageElement> Elements { get; } = [];

      protected override bool VisitOneExpr(Expression expr, ref int state) {
        if (expr is NaturalLanguageExpression naturalLanguageExpression) {
          Elements.Add(new NaturalLanguageElement {
            ElementId = $"nl{nextId++}",
            Kind = "expression",
            StartPos = naturalLanguageExpression.StartToken.pos,
            EndPosExclusive = naturalLanguageExpression.EndToken.pos + naturalLanguageExpression.EndToken.val.Length,
            RawContent = naturalLanguageExpression.RawContent,
            InferredType = naturalLanguageExpression.Type?.ToString() ?? "<unknown>",
            Line = naturalLanguageExpression.Origin.line,
            Column = naturalLanguageExpression.Origin.col
          });
        }

        return base.VisitOneExpr(expr, ref state);
      }

      protected override bool VisitOneStmt(Statement stmt, ref int state) {
        if (stmt is NaturalLanguageStatement naturalLanguageStatement) {
          Elements.Add(new NaturalLanguageElement {
            ElementId = $"nl{nextId++}",
            Kind = "statement",
            StartPos = naturalLanguageStatement.StartToken.pos,
            EndPosExclusive = naturalLanguageStatement.EndToken.pos + naturalLanguageStatement.EndToken.val.Length,
            RawContent = naturalLanguageStatement.RawContent,
            InferredType = "<statement>",
            Line = naturalLanguageStatement.Origin.line,
            Column = naturalLanguageStatement.Origin.col
          });
        }

        return base.VisitOneStmt(stmt, ref state);
      }
    }

    private sealed class NaturalLanguageTask {
      public string TaskId { get; set; } = "";
      public string CallableName { get; set; } = "";
      public string CallableKind { get; set; } = "";
      public Uri FileUri { get; set; }
      public string FilePath { get; set; } = "";
      public int CallableStartPos { get; set; }
      public int CallableEndPosExclusive { get; set; }
      public string CallableSource { get; set; } = "";
      public List<NaturalLanguageElement> Elements { get; set; } = [];
    }

    private sealed class NaturalLanguageSupportDeclaration {
      public string DeclarationName { get; set; } = "";
      public string DeclarationKind { get; set; } = "";
      public string Source { get; set; } = "";
    }

    private sealed class NaturalLanguageElement {
      public string ElementId { get; set; } = "";
      public string Kind { get; set; } = "";
      public int StartPos { get; set; }
      public int EndPosExclusive { get; set; }
      public string RawContent { get; set; } = "";
      public string InferredType { get; set; } = "";
      public int Line { get; set; }
      public int Column { get; set; }

      public NaturalLanguageElementRequest ToRequest() {
        return new NaturalLanguageElementRequest {
          ElementId = ElementId,
          Kind = Kind,
          StartPos = StartPos,
          EndPosExclusive = EndPosExclusive,
          RawContent = RawContent,
          InferredType = InferredType,
          Line = Line,
          Column = Column
        };
      }
    }

    private sealed class TextReplacement {
      public string TaskId { get; set; } = "";
      public string ElementId { get; set; } = "";
      public int StartPos { get; set; }
      public int EndPosExclusive { get; set; }
      public string Code { get; set; } = "";
    }

    private sealed class NaturalLanguageAppliedReplacement {
      public string ElementId { get; set; } = "";
      public int RewrittenStartPos { get; set; }
      public int RewrittenEndPosExclusive { get; set; }
    }

    private sealed class NaturalLanguageAppliedTaskContext {
      public string TaskId { get; set; } = "";
      public string FilePath { get; set; } = "";
      public int CallableStartPos { get; set; }
      public int CallableEndPosExclusive { get; set; }
      public int CallableStartLine { get; set; }
      public string CallableSource { get; set; } = "";
      public List<NaturalLanguageAppliedReplacement> Replacements { get; set; } = [];
    }

    private sealed class NaturalLanguageFailureContext {
      public string PrimaryLocation { get; set; } = "";
      public string PrimaryMessage { get; set; } = "";
      public string PrimaryFilePath { get; set; } = "";
      public int PrimaryStartPos { get; set; } = -1;
      public int PrimaryEndPosExclusive { get; set; } = -1;
      public List<NaturalLanguageRelatedFailureContext> RelatedMessages { get; set; } = [];
      public string Excerpt { get; set; } = "";
      public List<string> OverlappingElementIds { get; set; } = [];
    }

    private sealed class NaturalLanguageRelatedFailureContext {
      public string Location { get; set; } = "";
      public string Message { get; set; } = "";
    }

    private sealed class NaturalLanguagePromptRequest {
      public int Version { get; set; }
      public int Attempt { get; set; }
      public string ProgramName { get; set; } = "";
      public string TaskId { get; set; } = "";
      public string CallableName { get; set; } = "";
      public string CallableKind { get; set; } = "";
      public string Prompt { get; set; } = "";
      public List<NaturalLanguageElementRequest> Elements { get; set; } = [];
      public List<string> RelevantFeedback { get; set; } = [];
    }

    private sealed class NaturalLanguageElementRequest {
      public string ElementId { get; set; } = "";
      public string Kind { get; set; } = "";
      public int StartPos { get; set; }
      public int EndPosExclusive { get; set; }
      public string RawContent { get; set; } = "";
      public string InferredType { get; set; } = "";
      public int Line { get; set; }
      public int Column { get; set; }
    }

    private sealed class NaturalLanguageResponseFile {
      public List<NaturalLanguageTaskResponse> Tasks { get; set; } = [];
    }

    private sealed class NaturalLanguageTaskResponseFile {
      public string TaskId { get; set; } = "";
      public List<NaturalLanguageReplacementResponse> Replacements { get; set; } = [];
    }

    private sealed class NaturalLanguageTaskResponse {
      public string TaskId { get; set; } = "";
      public List<NaturalLanguageReplacementResponse> Replacements { get; set; } = [];
    }

    private sealed class NaturalLanguageTaskRequestResult {
      public bool Success { get; set; }
      public string ErrorMessage { get; set; } = "";
      public string OpenAiResponseId { get; set; } = "";
      public NaturalLanguageTaskResponse Response { get; set; } = new();
    }

    private sealed class NaturalLanguageFeedbackByTask {
      public Dictionary<string, List<NaturalLanguageFailureContext>> FeedbackByTaskId { get; } = [];
      public List<NaturalLanguageFailureContext> GlobalFeedback { get; } = [];
    }

    private sealed class NaturalLanguageTaskState {
      public string PreviousOpenAiResponseId { get; set; } = "";
      public NaturalLanguageTaskResponse CurrentResponse { get; set; }
      public List<NaturalLanguageRetryHistoryEntry> RetryHistory { get; } = [];
    }

    private sealed class NaturalLanguageRetryHistoryEntry {
      public int Attempt { get; set; }
      public List<NaturalLanguageFailureContext> Failures { get; set; } = [];
      public int OmittedFailureCount { get; set; }
      public List<NaturalLanguageReplacementResponse> Replacements { get; set; } = [];
    }

    private sealed class NaturalLanguageReplacementResponse {
      public string ElementId { get; set; } = "";
      public string Code { get; set; } = "";
    }

    private sealed class NaturalLanguageTaskResponsePayload {
      public List<NaturalLanguageReplacementResponse> Replacements { get; set; } = [];
    }

    private sealed class OpenAiResponsesRequest {
      [JsonPropertyName("model")]
      public string Model { get; set; } = "";

      [JsonPropertyName("previous_response_id")]
      public string PreviousResponseId { get; set; }

      [JsonPropertyName("input")]
      public string Input { get; set; } = "";

      [JsonPropertyName("metadata")]
      public Dictionary<string, string> Metadata { get; set; } = [];

      [JsonPropertyName("text")]
      public OpenAiResponsesTextConfiguration Text { get; set; }
    }

    private sealed class OpenAiResponsesTextConfiguration {
      [JsonPropertyName("format")]
      public OpenAiResponsesJsonSchemaFormat Format { get; set; }
    }

    private sealed class OpenAiResponsesJsonSchemaFormat {
      [JsonPropertyName("type")]
      public string Type { get; set; } = "";

      [JsonPropertyName("name")]
      public string Name { get; set; } = "";

      [JsonPropertyName("strict")]
      public bool Strict { get; set; }

      [JsonPropertyName("schema")]
      public object Schema { get; set; }
    }

    private sealed class OpenAiResponsesApiResponse {
      [JsonPropertyName("id")]
      public string Id { get; set; } = "";

      [JsonPropertyName("output_text")]
      public string OutputText { get; set; } = "";

      [JsonPropertyName("output")]
      public List<OpenAiResponsesOutputItem> Output { get; set; } = [];
    }

    private sealed class OpenAiResponsesOutputItem {
      [JsonPropertyName("content")]
      public List<OpenAiResponsesContentItem> Content { get; set; } = [];
    }

    private sealed class OpenAiResponsesContentItem {
      [JsonPropertyName("type")]
      public string Type { get; set; } = "";

      [JsonPropertyName("text")]
      public string Text { get; set; } = "";

      [JsonPropertyName("refusal")]
      public string Refusal { get; set; } = "";
    }
    /// <summary>
    /// Extract the counterexample corresponding to the first failing
    /// assertion and print it to the console
    /// </summary>
    private static async Task PrintCounterexample(DafnyOptions options) {
      var firstCounterexample = ((DafnyConsolePrinter)options.Printer).VerificationResults
        .Select(result => result.Result)
        .Where(result => result.Outcome == VcOutcome.Errors)
        .Select(result => result.Counterexamples)
        .Where(counterexampleList => counterexampleList != null)
        .Select(counterexampleList => counterexampleList.FirstOrDefault(counterexample => counterexample.Model != null))
        .FirstOrDefault(counterexample => counterexample != null);
      if (firstCounterexample == null) {
        return;
      }
      var model = new DafnyModel(firstCounterexample.Model, options);
      await options.OutputWriter.Status($"The following counterexample refers to the following failing assertion:\n{model.ToString()}");
    }

    private static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(ExecutionEngineOptions options, Program dafnyProgram) {
      var modulesCount = BoogieGenerator.VerifiableModules(dafnyProgram).Count();


      foreach (var prog in BoogieGenerator.Translate(dafnyProgram, dafnyProgram.Reporter)) {

        if (options.PrintFile != null) {

          var fileName = modulesCount > 1 ? Dafny.DafnyMain.BoogieProgramSuffix(options.PrintFile, prog.Item1) : options.PrintFile;

          ExecutionEngine.PrintBplFile(options, fileName, prog.Item2, false, false, options.PrettyPrint);
        }

        yield return prog;

      }
    }

    public async Task<(bool IsVerified, PipelineOutcome Outcome, IDictionary<string, PipelineStatistics> ModuleStats)>
      BoogieAsync(
        ErrorReporter errorReporter,
        DafnyOptions options,
        string baseName,
        IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms, string programId) {
      var concurrentModuleStats = new ConcurrentDictionary<string, PipelineStatistics>();
      await using var sw = options.OutputWriter.StatusWriter();
      var writerManager = new ConcurrentToSequentialWriteManager(sw);

      if (options.Verify || options.Get(BoogieOptionBag.HiddenNoVerify)) {
        var before = errorReporter.ErrorCount;
        options.ProcessSolverOptions(errorReporter, Token.Cli);
        if (before != errorReporter.ErrorCount) {
          return (false, PipelineOutcome.FatalError, concurrentModuleStats);
        }
      }

      var moduleTasks = boogiePrograms.Select(async program => {
        await using var moduleWriter = writerManager.AppendWriter();
        // ReSharper disable once AccessToDisposedClosure
        var result = await Task.Run(() =>
          BoogieOnceWithTimerAsync(errorReporter, moduleWriter, options, baseName, programId, program.Item1, program.Item2));
        concurrentModuleStats.TryAdd(program.Item1, result.Stats);
        return result;
      }).ToList();

      await Task.WhenAll(moduleTasks);
      var outcome = moduleTasks.Select(t => t.Result.Outcome)
        .Aggregate(PipelineOutcome.VerificationCompleted, MergeOutcomes);

      var isVerified = moduleTasks.Select(t =>
        DafnyMain.IsBoogieVerified(t.Result.Outcome, t.Result.Stats)).All(x => x);
      return (isVerified, outcome, concurrentModuleStats);
    }

    private async Task<(PipelineOutcome Outcome, PipelineStatistics Stats)> BoogieOnceWithTimerAsync(
      ErrorReporter errorReporter,
      TextWriter output,
      DafnyOptions options,
      string baseName, string programId,
      string moduleName,
      Bpl.Program program) {
      Stopwatch watch = new Stopwatch();
      watch.Start();
      if (options.SeparateModuleOutput) {
        options.Printer.AdvisoryWriteLine(output, "For module: {0}", moduleName);
      }

      var result =
        await await DafnyMain.LargeStackFactory.StartNew(() => DafnyMain.BoogieOnce(errorReporter, options, output, engine, baseName, moduleName, program, programId));

      watch.Stop();

      if (options.SeparateModuleOutput) {
        TimeSpan ts = watch.Elapsed;
        string elapsedTime = $"{ts.Hours:00}:{ts.Minutes:00}:{ts.Seconds:00}";
        options.Printer.AdvisoryWriteLine(output, "Elapsed time: {0}", elapsedTime);
        WriteTrailer(options, output, result.Statistics);
      }

      return result;
    }

    private static PipelineOutcome MergeOutcomes(PipelineOutcome first, PipelineOutcome second) {

      if ((first == PipelineOutcome.VerificationCompleted || first == PipelineOutcome.Done) &&
          second != PipelineOutcome.VerificationCompleted) {
        return second;
      }

      return first;
    }

    public static void WriteTrailer(DafnyOptions options, TextWriter output, PipelineStatistics stats) {
      if (!options.Verify && stats.ErrorCount == 0) {
        output.WriteLine();
        output.Write("{0} did not attempt verification", options.DescriptiveToolName);
        if (stats.InconclusiveCount != 0) {
          output.Write(", {0} inconclusive{1}", stats.InconclusiveCount, Util.Plural(stats.InconclusiveCount));
        }
        if (stats.TimeoutCount != 0) {
          output.Write(", {0} time out{1}", stats.TimeoutCount, Util.Plural(stats.TimeoutCount));
        }
        if (stats.OutOfMemoryCount != 0) {
          output.Write(", {0} out of memory", stats.OutOfMemoryCount);
        }
        if (stats.OutOfResourceCount != 0) {
          output.Write(", {0} out of resource", stats.OutOfResourceCount);
        }
        if (stats.SolverExceptionCount != 0) {
          output.Write(", {0} solver exceptions", stats.SolverExceptionCount);
        }

        output.WriteLine();
        output.Flush();
      } else {
        // This calls a routine within Boogie
        options.Printer.WriteTrailer(output, stats);
      }
    }

    public static void WriteProgramVerificationSummary(DafnyOptions options, IDafnyOutputWriter output, IDictionary<string, PipelineStatistics> moduleStats) {
      var statSum = new PipelineStatistics();
      foreach (var stats in moduleStats) {
        statSum.VerifiedCount += stats.Value.VerifiedCount;
        statSum.ErrorCount += stats.Value.ErrorCount;
        statSum.TimeoutCount += stats.Value.TimeoutCount;
        statSum.OutOfResourceCount += stats.Value.OutOfResourceCount;
        statSum.OutOfMemoryCount += stats.Value.OutOfMemoryCount;
        statSum.SolverExceptionCount += stats.Value.SolverExceptionCount;
        statSum.CachedErrorCount += stats.Value.CachedErrorCount;
        statSum.CachedInconclusiveCount += stats.Value.CachedInconclusiveCount;
        statSum.CachedOutOfMemoryCount += stats.Value.CachedOutOfMemoryCount;
        statSum.CachedTimeoutCount += stats.Value.CachedTimeoutCount;
        statSum.CachedOutOfResourceCount += stats.Value.CachedOutOfResourceCount;
        statSum.CachedSolverExceptionCount += stats.Value.CachedSolverExceptionCount;
        statSum.CachedVerifiedCount += stats.Value.CachedVerifiedCount;
        statSum.InconclusiveCount += stats.Value.InconclusiveCount;
      }

      using var tw = output.StatusWriter();
      WriteTrailer(options, tw, statSum);
    }


    public static async Task<bool> Compile(string fileName, ReadOnlyCollection<string> otherFileNames, Program dafnyProgram,
                               PipelineOutcome oc, IDictionary<string, PipelineStatistics> moduleStats, bool verified) {
      var options = dafnyProgram.Options;
      var resultFileName = options.DafnyPrintCompiledFile ?? fileName;
      bool compiled = true;
      switch (oc) {
        case PipelineOutcome.VerificationCompleted:
          WriteProgramVerificationSummary(options, options.OutputWriter, moduleStats);
          if ((options.Compile && verified && !options.UserConstrainedProcsToCheck) || options.ForceCompile) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, true);
          } else if ((2 <= options.SpillTargetCode && verified && !options.UserConstrainedProcsToCheck) || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, false);
          }
          break;
        case PipelineOutcome.Done:
          WriteProgramVerificationSummary(options, options.OutputWriter, moduleStats);
          if (options.ForceCompile || 3 <= options.SpillTargetCode) {
            compiled = await CompileDafnyProgram(dafnyProgram, resultFileName, otherFileNames, options.ForceCompile);
          }
          break;
        default:
          // error has already been reported to user
          break;
      }
      return compiled;
    }

    #region Compilation

    private record TargetPaths(string Directory, string Filename) {
      private static Func<string, string> DeleteDot = p => p == "." ? "" : p;
      private static Func<string, string> AddDot = p => p == "" ? "." : p;
      private Func<string, string> RelativeToDirectory =
        path => DeleteDot(Path.GetRelativePath(AddDot(Directory), path));

      public string RelativeDirectory => RelativeToDirectory(AddDot(Path.GetDirectoryName(Filename)));
      public string RelativeFilename => RelativeToDirectory(Filename);
      public string SourceDirectory => Path.GetDirectoryName(Filename);
    }

    private static TargetPaths GenerateTargetPaths(DafnyOptions options, string dafnyProgramName) {
      string targetBaseDir = options.Backend.TargetBaseDir(dafnyProgramName);
      string targetExtension = options.Backend.TargetExtension;

      // Note that using Path.ChangeExtension here does the wrong thing when dafnyProgramName has multiple periods (e.g., a.b.dfy)
      string targetBaseName = options.Backend.TargetBasename(dafnyProgramName) + "." + targetExtension;
      string targetDir = Path.Combine(Path.GetDirectoryName(dafnyProgramName), targetBaseDir);

      string targetFilename = Path.Combine(targetDir, targetBaseName);

      return new TargetPaths(Directory: Path.GetDirectoryName(dafnyProgramName), Filename: targetFilename);
    }

    static async Task WriteDafnyProgramToFiles(DafnyOptions options, TargetPaths paths, bool targetProgramHasErrors, string targetProgramText,
      string/*?*/ callToMain, Dictionary<string, string> otherFiles, IDafnyOutputWriter outputWriter) {
      if (targetProgramText.Length != 0) {
        WriteFile(paths.Filename, targetProgramText, callToMain);
      }

      string NormalizeRelativeFilename(string fileName) {
        return RuntimeInformation.IsOSPlatform(OSPlatform.Windows)
          ? fileName.Replace(@"\", "/")
          : fileName;
      }

      var relativeTarget = NormalizeRelativeFilename(paths.RelativeFilename);
      if (targetProgramHasErrors) {
        // Something went wrong during compilation (e.g., the compiler may have found an "assume" statement).
        // As a courtesy, we're still printing the text of the generated target program. We print a message regardless
        // of the Verbose settings.
        await outputWriter.Status($"Wrote textual form of partial target program to {relativeTarget}");
      } else if (options.Verbose) {
        await outputWriter.Status($"Wrote textual form of target program to {relativeTarget}");
      }

      foreach (var (filename, value) in otherFiles) {
        var absoluteFilename = Path.IsPathRooted(filename) ? filename : Path.Join(paths.SourceDirectory, filename);
        WriteFile(absoluteFilename, value);
        if (options.Verbose) {
          await outputWriter.Status($"Additional output written to {NormalizeRelativeFilename(Path.Join(paths.RelativeDirectory, filename))}");
        }
      }
    }

    public static void WriteFile(string filename, string text, string moreText = null) {
      var dir = Path.GetDirectoryName(filename);
      if (dir != "") {
        Directory.CreateDirectory(dir);
      }

      CheckFilenameIsLegal(filename);
      using TextWriter target = new StreamWriter(new FileStream(filename, FileMode.Create));
      target.Write(text);
      if (moreText != null) {
        target.Write(moreText);
      }
    }

    private static void CheckFilenameIsLegal(string filename) {
      // We cannot get the full path correctly on Windows if the file name uses some reserved words
      // For example, Path.GetFullPath("con.txt") will return "//./con" which is incorrect.
      // https://docs.microsoft.com/en-us/windows/win32/fileio/naming-a-file?redirectedfrom=MSDN
      if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
        var problematicNames =
          "CON, PRN, AUX, NUL, COM1, COM2, COM3, COM4, COM5, COM6, COM7, COM8, COM9, LPT1, LPT2, LPT3, LPT4, LPT5, LPT6, LPT7, LPT8, LPT9";
        var problematicRegex =
          new Regex(@"^(.*[/\\]|^)(" +
                    string.Join("|", problematicNames.Split(", ")) + @")(\.[^/\\]*)?$", RegexOptions.IgnoreCase);
        var match = problematicRegex.Match(filename);
        if (match.Success) {
          throw new Exception($"Cannot create a file with the name {filename}." +
                              $" Windows reserves the following file names: {problematicNames}");
        }
      }
    }

    /// <summary>
    /// Generate a target language program from the Dafny program and, if "invokeCompiler" is "true", invoke
    /// the target language compiler to compile it.
    /// </summary>
    public static async Task<bool> CompileDafnyProgram(Program dafnyProgram, string dafnyProgramName,
                                           ReadOnlyCollection<string> otherFileNames, bool invokeCompiler) {
      var rewriters = RewriterCollection.GetRewriters(dafnyProgram.Reporter, dafnyProgram);
      foreach (var rewriter in rewriters) {
        rewriter.PostVerification(dafnyProgram);
      }

      Contract.Requires(dafnyProgram != null);
      Contract.Assert(dafnyProgramName != null);

      var outputWriter = dafnyProgram.Options.OutputWriter;
      var errorWriter = dafnyProgram.Options.ErrorWriter;

      // Compile the Dafny program into a string that contains the target program
      var oldErrorCount = dafnyProgram.Reporter.Count(ErrorLevel.Error);
      var options = dafnyProgram.Options;

      var compiler = options.Backend;
      compiler.OnPreCompile(dafnyProgram.Reporter, otherFileNames);

      // Now that an internal compiler is instantiated, apply any plugin instrumentation.
      foreach (var compilerInstrumenter in options.Plugins.SelectMany(p => p.GetCompilerInstrumenters(dafnyProgram.Reporter))) {
        compiler.InstrumentCompiler(compilerInstrumenter, dafnyProgram);
      }

      if (options.Get(CommonOptionBag.ExecutionCoverageReport) != null
          && compiler.UnsupportedFeatures.Contains(Feature.RuntimeCoverageReport)) {
        throw new UnsupportedFeatureException(dafnyProgram.GetStartOfFirstFileToken(), Feature.RuntimeCoverageReport);
      }

      var hasMain = SinglePassCodeGenerator.HasMain(dafnyProgram, out var mainMethod);
      if (hasMain) {
        mainMethod.IsEntryPoint = true;
        dafnyProgram.MainMethod = mainMethod;
      }
      string targetProgramText;
      var otherFiles = new Dictionary<string, string>();
      {
        var output = new ConcreteSyntaxTree();

        await DafnyMain.LargeStackFactory.StartNew(() => compiler.Compile(dafnyProgram, dafnyProgramName, output));

        var writerOptions = new WriterState();
        var targetProgramTextWriter = new StringWriter();
        var files = new Queue<FileSyntax>();
        output.Render(targetProgramTextWriter, 0, writerOptions, files, compiler.TargetIndentSize);
        targetProgramText = targetProgramTextWriter.ToString();

        while (files.Count > 0) {
          var file = files.Dequeue();
          var otherFileWriter = new StringWriter();
          writerOptions.HasNewLine = false;
          file.Tree.Render(otherFileWriter, 0, writerOptions, files, compiler.TargetIndentSize);
          otherFiles.Add(file.Filename, otherFileWriter.ToString());
        }
      }
      string callToMain = null;
      if (hasMain) {
        var callToMainTree = new ConcreteSyntaxTree();
        string baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
        compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
        callToMain = callToMainTree.MakeString(compiler.TargetIndentSize); // assume there aren't multiple files just to call main
      }
      Contract.Assert(hasMain == (callToMain != null));
      bool targetProgramHasErrors = dafnyProgram.Reporter.Count(ErrorLevel.Error) != oldErrorCount;

      var targetPaths = GenerateTargetPaths(options, dafnyProgramName);
      if (dafnyProgram.Reporter.FailCompilation) {
        await dafnyProgram.Options.OutputWriter.Status($"Translation was aborted because {dafnyProgram.Reporter.FailCompilationMessage}");
        return false;
      }
      // blurt out the code to a file, if requested, or if other target-language files were specified on the command line.
      if (options.SpillTargetCode > 0 || otherFileNames.Count > 0 || (invokeCompiler && !compiler.SupportsInMemoryCompilation) ||
          (invokeCompiler && compiler.TextualTargetIsExecutable && !options.RunAfterCompile)) {
        compiler.CleanSourceDirectory(targetPaths.SourceDirectory);
        await WriteDafnyProgramToFiles(options, targetPaths, targetProgramHasErrors, targetProgramText, callToMain, otherFiles, outputWriter);
      }

      var postGenerateFailed = !await compiler.OnPostGenerate(dafnyProgramName, targetPaths.SourceDirectory, outputWriter);
      if (postGenerateFailed) {
        return false;
      }

      // If we got here, compilation succeeded
      if (!invokeCompiler) {
        return true; // If we're not asked to invoke the target compiler, we can report success
      }

      // compile the program into an assembly
      var (compiledCorrectly, compilationResult) = await compiler.CompileTargetProgram(dafnyProgramName,
        targetProgramText, callToMain, targetPaths.Filename, otherFileNames,
        hasMain && options.RunAfterCompile, outputWriter);
      if (compiledCorrectly && options.RunAfterCompile) {
        if (hasMain) {
          if (options.Verbose) {
            await outputWriter.Status("Running...\n");
          }

          compiledCorrectly = await compiler.RunTargetProgram(dafnyProgramName, targetProgramText, callToMain,
            targetPaths.Filename, otherFileNames, compilationResult, outputWriter);

          if (compiledCorrectly) {
            var coverageReportDir = options.Get(CommonOptionBag.ExecutionCoverageReport);
            if (coverageReportDir != null) {
              var coverageReport = new CoverageReport("Execution Coverage", "Branches", "_tests_actual", dafnyProgram);
              compiler.PopulateCoverageReport(coverageReport);
              await new CoverageReporter(options).SerializeCoverageReports(coverageReport, coverageReportDir);
            }
          }
        } else {
          // make sure to give some feedback to the user
          if (options.Verbose) {
            await outputWriter.Status("Program compiled successfully");
          }
        }
      }
      return compiledCorrectly;
    }

    #endregion

    public void Dispose() {
      engine.Dispose();
    }
  }
}
