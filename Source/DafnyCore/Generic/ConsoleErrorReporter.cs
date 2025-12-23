namespace Microsoft.Dafny;

public class ConsoleErrorReporter(DafnyOptions options) : BatchErrorReporter(options) {

  public override bool MessageCore(DafnyDiagnostic diagnostic) {
    var stored = base.MessageCore(diagnostic);
    if (!stored) {
      return false;
    }

    if (Options.Get(CommonOptionBag.SuppressWarnings) && diagnostic.Level != ErrorLevel.Error) {
      return false;
    }

    if (Options is not { PrintTooltips: true } && diagnostic.Level == ErrorLevel.Info) {
      return false;
    }

    Options.OutputWriter.WriteDiagnostic(diagnostic);

    return true;
  }
}