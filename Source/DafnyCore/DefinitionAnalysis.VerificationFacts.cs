#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public static partial class DefinitionAnalysis {
  private static IReadOnlyList<DefinitionVerificationTarget> VerificationFactsFor(
    IEnumerable<ICanVerify> verificationTargets,
    IReadOnlySet<Uri> analysisSourceUris) {
    return verificationTargets
      .Where(target => analysisSourceUris.Contains(target.Origin.Uri))
      .Distinct()
      .Select(target => new DefinitionVerificationTarget(
        target.FullDafnyName,
        SourcePath(target),
        VerificationAttributesFor(target)))
      .OrderBy(target => target.SourcePath, StringComparer.Ordinal)
      .ThenBy(target => target.FullName, StringComparer.Ordinal)
      .ToList();
  }

  private static IReadOnlyList<DefinitionAttribute> VerificationAttributesFor(ICanVerify target) {
    var result = AttributesFor(target).ToList();
    if (target is IAttributeBearingDeclaration declaration) {
      foreach (var attribute in declaration.Attributes.AsEnumerable().OfType<UserSuppliedAtAttribute>()) {
        if (attribute.UserSuppliedName is not { } name || !attribute.AtSign.IsValid) {
          continue;
        }
        // These built-ins expand to the corresponding legacy verifier attributes.
        name = name switch {
          "TimeLimit" => "timeLimit",
          "TimeLimitMultiplier" => "timeLimitMultiplier",
          _ => name
        };
        result.Add(new DefinitionAttribute(
          name,
          attribute.UserSuppliedPreResolveArguments.Select(argument => argument.EntireRange.PrintOriginal()).ToList(),
          attribute.AtSign.pos,
          TokenEnd(attribute.EndToken)));
      }
    }
    return result.OrderBy(attribute => attribute.Start).ToList();
  }
}
