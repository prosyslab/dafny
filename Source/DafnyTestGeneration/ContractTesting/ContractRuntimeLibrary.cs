using System;
using System.IO;
using System.Text;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Loads the checked-in Dafny and C# runtime library text that ships as embedded resources.</summary>
public static class ContractRuntimeLibrary {
  private const string ResourcePrefix = "DafnyTestGeneration.ContractTesting.Library.";

  /// <summary>Returns the named library file, rejecting a missing resource or carriage returns that would change hashed text.</summary>
  public static string Read(string name) {
    using var stream = typeof(ContractRuntimeLibrary).Assembly.GetManifestResourceStream(ResourcePrefix + name)
      ?? throw new InvalidOperationException($"Contract runtime library resource '{name}' is missing.");
    using var reader = new StreamReader(stream, new UTF8Encoding(false));
    var text = reader.ReadToEnd();
    if (text.Contains('\r')) {
      throw new InvalidOperationException($"Contract runtime library resource '{name}' must use LF line endings.");
    }
    return text;
  }

  /// <summary>Returns the named library file without its single terminating line feed, matching the text a source constant would hold.</summary>
  public static string ReadWithoutTerminator(string name) {
    var text = Read(name);
    if (!text.EndsWith('\n') || text.EndsWith("\n\n", StringComparison.Ordinal)) {
      throw new InvalidOperationException($"Contract runtime library resource '{name}' must end with exactly one line feed.");
    }
    return text[..^1];
  }
}
