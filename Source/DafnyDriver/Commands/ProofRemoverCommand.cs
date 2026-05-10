#nullable enable
using System;
using System.Collections.Generic;
using System.CommandLine;
using System.CommandLine.Invocation;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace Microsoft.Dafny;

public static class ProofRemoverCommand {
  private static readonly Option<FileInfo?> Output = new("--output",
    "Write the preprocessed Dafny source to this file instead of stdout.");

  static ProofRemoverCommand() {
    OptionRegistry.RegisterOption(Output, OptionScope.Cli);
  }

  public static Command Create() {
    var result = new Command("proof-remover",
      "Strip proof-facing specification clauses and unreachable function/predicate declarations from a Dafny Core source file.");
    result.AddArgument(DafnyCommands.FileArgument);
    result.AddOption(Output);

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, Execute);
    return result;
  }

  private static async Task<int> Execute(DafnyOptions options, InvocationContext _) {
    var input = options.Get(DafnyCommands.FileArgument);
    if (input == null) {
      await options.ErrorWriter.WriteLineAsync("preprocess-core requires one Dafny input file.");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    if (!input.Exists) {
      await options.ErrorWriter.WriteLineAsync($"Dafny input file does not exist: {input.FullName}");
      return (int)ExitValue.PREPROCESSING_ERROR;
    }

    var originalText = await File.ReadAllTextAsync(input.FullName);
    var preprocessed = DafnyProofRemover.Preprocess(originalText);
    var output = options.Get(Output);
    if (output == null) {
      await options.OutputWriter.Code(preprocessed);
    } else {
      await File.WriteAllTextAsync(output.FullName, preprocessed);
    }

    return (int)ExitValue.SUCCESS;
  }
}

public static class DafnyCorePreprocessor {
  public static string Preprocess(string source) {
    return DafnyProofRemover.Preprocess(source);
  }
}

public static class DafnyProofRemover {
  private static readonly Regex Identifier = new(@"\b[A-Za-z_][A-Za-z0-9_]*\b", RegexOptions.Compiled);

  private static readonly Regex FunctionOrPredicate = new(
    @"^[ \t]*(?:ghost[ \t]+)?(?<kind>function|predicate)(?:[ \t]+method)?(?:[ \t]+\{:[^}\n]*\})*[ \t]+(?<name>[A-Za-z_][A-Za-z0-9_]*)\b",
    RegexOptions.Compiled | RegexOptions.Multiline);

  private static readonly Regex SpecClause = new(
    @"^(?<indent>[ \t]*)(?:free[ \t]+)?(?<keyword>requires|ensures|decreases|reads|modifies|invariant)\b",
    RegexOptions.Compiled | RegexOptions.Multiline);

  private static readonly Regex ClauseDepthDelims = new(@"[(){}\[\]]", RegexOptions.Compiled);
  private static readonly Regex ClauseContinuationPrefix = new(@"^(?:&&|\|\||==>|=>|::|[+\-*/%&|^!=<>?:.]|[)\]])", RegexOptions.Compiled);
  private static readonly Regex ClauseContinuationSuffix = new(@"(?:&&|\|\||==>|=>|::|[+\-/%&^!=<>?:.,])$", RegexOptions.Compiled);

  public static string Preprocess(string source) {
    var withoutClauses = StripSpecClauses(source);
    return PruneUnusedFunctionAndPredicateDeclarations(withoutClauses);
  }

  private static string StripSpecClauses(string source) {
    var masked = MaskCommentsAndStrings(source);
    return RemoveSpans(source, SpecClauseSpans(masked));
  }

  private static List<Span> SpecClauseSpans(string maskedSource) {
    var spans = new List<Span>();
    var lines = SplitLines(maskedSource);
    var lineStarts = LineStartOffsets(lines);
    var lineIndex = 0;

    while (lineIndex < lines.Count) {
      var match = SpecClause.Match(lines[lineIndex]);
      if (!match.Success) {
        lineIndex += 1;
        continue;
      }

      var clauseIndent = match.Groups["indent"].Length;
      var nextIndex = FirstLineAfterClause(lines, lineIndex, clauseIndent, match.Index + match.Length);
      spans.Add(new Span(lineStarts[lineIndex], lineStarts[nextIndex]));
      lineIndex = nextIndex;
    }

    return spans;
  }

  private static int FirstLineAfterClause(IReadOnlyList<string> lines, int clauseLineIndex, int clauseIndent,
    int clauseBodyStart) {
    var lineIndex = clauseLineIndex + 1;
    var clauseDepth = ClauseDepthDelta(lines[clauseLineIndex][clauseBodyStart..]);
    var needsContinuation = ClauseContinuationNeeded(lines[clauseLineIndex][clauseBodyStart..]);

    while (lineIndex < lines.Count) {
      var line = lines[lineIndex];
      if (string.IsNullOrWhiteSpace(line)) {
        lineIndex += 1;
        continue;
      }

      if (clauseDepth <= 0 && !needsContinuation && LeadingIndent(line) <= clauseIndent &&
          !ClauseContinuationStarts(line)) {
        return lineIndex;
      }

      clauseDepth += ClauseDepthDelta(line);
      if (clauseDepth < 0) {
        clauseDepth = 0;
      }

      needsContinuation = ClauseContinuationNeeded(line) || clauseDepth > 0;
      lineIndex += 1;
    }

    return lines.Count;
  }

  private static int ClauseDepthDelta(string line) {
    var delta = 0;
    foreach (Match match in ClauseDepthDelims.Matches(line)) {
      delta += "({[".Contains(match.Value) ? 1 : -1;
    }

    return delta;
  }

  private static bool ClauseContinuationStarts(string line) {
    return ClauseContinuationPrefix.IsMatch(line.Trim());
  }

  private static bool ClauseContinuationNeeded(string line) {
    var stripped = line.Trim();
    if (stripped.Length == 0) {
      return false;
    }

    if (stripped.EndsWith("||")) {
      return true;
    }

    if (stripped.EndsWith("|")) {
      return stripped.Length >= 2 && char.IsWhiteSpace(stripped[^2]);
    }

    return ClauseContinuationSuffix.IsMatch(stripped);
  }

  private static int LeadingIndent(string line) {
    var index = 0;
    while (index < line.Length && (line[index] == ' ' || line[index] == '\t')) {
      index += 1;
    }

    return index;
  }

  private static string PruneUnusedFunctionAndPredicateDeclarations(string source) {
    var masked = MaskCommentsAndStrings(source);
    var declarations = FunctionAndPredicateDeclarations(masked);
    if (declarations.Count == 0) {
      return source;
    }

    var declarationNames = declarations.Select(declaration => declaration.Name).ToHashSet();
    var rootText = BlankSpans(source, declarations.Select(declaration => new Span(declaration.Start, declaration.End)));
    var keptNames = ReferencedNames(rootText, declarationNames);
    var declarationRefs = DeclarationReferences(source, declarations, declarationNames);

    var changed = true;
    while (changed) {
      changed = false;
      foreach (var name in keptNames.ToArray()) {
        if (!declarationRefs.TryGetValue(name, out var refs)) {
          continue;
        }

        foreach (var referencedName in refs) {
          if (keptNames.Add(referencedName)) {
            changed = true;
          }
        }
      }
    }

    var removedSpans = declarations.
      Where(declaration => !keptNames.Contains(declaration.Name)).
      Select(declaration => new Span(declaration.Start, declaration.End)).
      ToList();
    return RemoveSpans(source, removedSpans);
  }

  private static List<DeclarationSpan> FunctionAndPredicateDeclarations(string maskedSource) {
    var declarations = new List<DeclarationSpan>();
    foreach (Match match in FunctionOrPredicate.Matches(maskedSource)) {
      var bodyStart = maskedSource.IndexOf('{', match.Index + match.Length);
      if (bodyStart < 0) {
        continue;
      }

      var bodyEnd = MatchingBraceEnd(maskedSource, bodyStart);
      if (bodyEnd == null) {
        continue;
      }

      declarations.Add(new DeclarationSpan(match.Groups["name"].Value, match.Index, bodyEnd.Value));
    }

    return declarations;
  }

  private static int? MatchingBraceEnd(string maskedSource, int bodyStart) {
    var depth = 0;
    for (var index = bodyStart; index < maskedSource.Length; index++) {
      if (maskedSource[index] == '{') {
        depth += 1;
      } else if (maskedSource[index] == '}') {
        depth -= 1;
        if (depth == 0) {
          return index + 1;
        }
      }
    }

    return null;
  }

  private static Dictionary<string, HashSet<string>> DeclarationReferences(string source,
    IEnumerable<DeclarationSpan> declarations, HashSet<string> declarationNames) {
    var refsByName = declarationNames.ToDictionary(name => name, _ => new HashSet<string>());
    foreach (var declaration in declarations) {
      var declarationText = source[declaration.Start..declaration.End];
      refsByName[declaration.Name].UnionWith(ReferencedNames(declarationText, declarationNames));
    }

    return refsByName;
  }

  private static HashSet<string> ReferencedNames(string source, HashSet<string> declarationNames) {
    var masked = MaskCommentsAndStrings(source);
    return Identifier.Matches(masked).
      Select(match => match.Value).
      Where(declarationNames.Contains).
      ToHashSet();
  }

  private static string BlankSpans(string source, IEnumerable<Span> spans) {
    var chars = source.ToCharArray();
    foreach (var span in spans) {
      for (var index = span.Start; index < span.End; index++) {
        if (chars[index] != '\n') {
          chars[index] = ' ';
        }
      }
    }

    return new string(chars);
  }

  private static string RemoveSpans(string source, List<Span> spans) {
    if (spans.Count == 0) {
      return source;
    }

    var pieces = new List<string>();
    var cursor = 0;
    foreach (var span in MergedSpans(spans)) {
      pieces.Add(source[cursor..span.Start]);
      cursor = span.End;
    }

    pieces.Add(source[cursor..]);
    return string.Concat(pieces);
  }

  private static List<Span> MergedSpans(IEnumerable<Span> spans) {
    var merged = new List<Span>();
    foreach (var span in spans.OrderBy(span => span.Start)) {
      if (merged.Count == 0 || span.Start > merged[^1].End) {
        merged.Add(span);
      } else {
        merged[^1] = new Span(merged[^1].Start, int.Max(merged[^1].End, span.End));
      }
    }

    return merged;
  }

  private static string MaskCommentsAndStrings(string source) {
    var chars = source.ToCharArray();
    var index = 0;
    while (index < source.Length) {
      if (StartsWithAt(source, index, "//")) {
        index = MaskLineComment(chars, source, index);
      } else if (StartsWithAt(source, index, "/*")) {
        index = MaskBlockComment(chars, source, index);
      } else if (StartsWithAt(source, index, "@\"")) {
        index = MaskVerbatimString(chars, source, index);
      } else if (source[index] == '"') {
        index = MaskQuotedLiteral(chars, source, index, '"');
      } else if (source[index] == '\'') {
        index = MaskQuotedLiteral(chars, source, index, '\'');
      } else {
        index += 1;
      }
    }

    return new string(chars);
  }

  private static int MaskLineComment(char[] chars, string source, int start) {
    var index = start;
    while (index < source.Length && source[index] != '\n') {
      chars[index] = ' ';
      index += 1;
    }

    return index;
  }

  private static int MaskBlockComment(char[] chars, string source, int start) {
    var depth = 1;
    chars[start] = ' ';
    chars[start + 1] = ' ';
    var index = start + 2;
    while (index < source.Length && depth > 0) {
      if (StartsWithAt(source, index, "/*")) {
        chars[index] = ' ';
        chars[index + 1] = ' ';
        index += 2;
        depth += 1;
      } else if (StartsWithAt(source, index, "*/")) {
        chars[index] = ' ';
        chars[index + 1] = ' ';
        index += 2;
        depth -= 1;
      } else {
        if (chars[index] != '\n') {
          chars[index] = ' ';
        }
        index += 1;
      }
    }

    return index;
  }

  private static int MaskVerbatimString(char[] chars, string source, int start) {
    chars[start] = ' ';
    chars[start + 1] = ' ';
    var index = start + 2;
    while (index < source.Length) {
      if (source[index] == '"') {
        chars[index] = ' ';
        index += 1;
        if (index < source.Length && source[index] == '"') {
          chars[index] = ' ';
          index += 1;
          continue;
        }

        return index;
      }

      if (chars[index] != '\n') {
        chars[index] = ' ';
      }
      index += 1;
    }

    return index;
  }

  private static int MaskQuotedLiteral(char[] chars, string source, int start, char quote) {
    chars[start] = ' ';
    var index = start + 1;
    var escaped = false;
    while (index < source.Length) {
      var current = source[index];
      if (current != '\n') {
        chars[index] = ' ';
      }

      index += 1;
      if (escaped) {
        escaped = false;
      } else if (current == '\\') {
        escaped = true;
      } else if (current == quote) {
        return index;
      }
    }

    return index;
  }

  private static List<string> SplitLines(string source) {
    var lines = new List<string>();
    var start = 0;
    for (var index = 0; index < source.Length; index++) {
      if (source[index] == '\n') {
        lines.Add(source[start..(index + 1)]);
        start = index + 1;
      }
    }

    if (start < source.Length) {
      lines.Add(source[start..]);
    }

    return lines;
  }

  private static List<int> LineStartOffsets(IEnumerable<string> lines) {
    var offsets = new List<int>();
    var offset = 0;
    foreach (var line in lines) {
      offsets.Add(offset);
      offset += line.Length;
    }

    offsets.Add(offset);
    return offsets;
  }

  private static bool StartsWithAt(string source, int index, string value) {
    if (index + value.Length > source.Length) {
      return false;
    }

    for (var offset = 0; offset < value.Length; offset++) {
      if (source[index + offset] != value[offset]) {
        return false;
      }
    }

    return true;
  }

  private readonly record struct DeclarationSpan(string Name, int Start, int End);
  private readonly record struct Span(int Start, int End);
}
