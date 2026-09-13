using System;
using System.Collections.Generic;
using System.IO;
using System.Text.Json;
using System.Linq;
using System.Globalization;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyTestGeneration.ContractTesting;

public sealed record ContractObservation(string Name, ContractValue Value);
public enum ContractRuntimeOperation { Precondition, Realize, EntryStart, EntryEnd }
public sealed record ContractCallObservation(string Symbol, IReadOnlyDictionary<string, ContractValue> Inputs,
  ContractRuntimeOperation Operation = ContractRuntimeOperation.Realize, ContractValue? Receiver = null,
  IReadOnlyList<ContractHeapObject>? Heap = null, IReadOnlyDictionary<string, ContractValue>? Outputs = null,
  int? Invocation = null, IReadOnlyList<string>? TypeArguments = null);

public static class ContractStateObserver {
  public static IReadOnlyList<ContractBranchObservation> Branches(IReadOnlyDictionary<string, ContractValue> observations) =>
    observations.Where(pair => pair.Key.StartsWith("$branch/", StringComparison.Ordinal))
      .Select(pair => {
        var parts = pair.Key.Split('/');
        if (parts.Length != 6 || pair.Value.Kind != ContractValueKind.Boolean || pair.Value.Value is not ("true" or "false")) {
          throw new JsonException("Malformed runtime branch observation.");
        }
        return (Order: int.Parse(parts[1], CultureInfo.InvariantCulture),
          Value: new ContractBranchObservation(parts[2], int.Parse(parts[3], CultureInfo.InvariantCulture),
            int.Parse(parts[4], CultureInfo.InvariantCulture), int.Parse(parts[5], CultureInfo.InvariantCulture), pair.Value.Value == "true"));
      }).OrderBy(item => item.Order).Select(item => item.Value).ToList();

  public static async Task<IReadOnlyDictionary<string, ContractValue>> ReadAsync(string path, CancellationToken cancellationToken) {
    var result = new Dictionary<string, ContractValue>(StringComparer.Ordinal);
    foreach (var line in await File.ReadAllLinesAsync(path, cancellationToken)) {
      var observation = JsonSerializer.Deserialize<ContractObservation>(line, ContractJson.Options)
        ?? throw new JsonException("Null runtime observation.");
      if (!result.TryAdd(observation.Name, observation.Value)) {
        throw new JsonException("Duplicate output observation: " + observation.Name);
      }
    }
    return result;
  }
}
