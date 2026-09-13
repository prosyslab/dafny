#nullable enable
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>Reserves a source identifier family against all resolved user declarations.</summary>
public static class ContractBodyNames {
  public static string Family(Program program, string preferred) {
    var nodes = program.RawModules().SelectMany(module => module.Descendants()).ToList();
    var names = nodes.OfType<IVariable>().Select(variable => variable.Name)
      .Concat(nodes.OfType<MemberDecl>().Select(member => member.Name))
      .Concat(nodes.OfType<TopLevelDecl>().Select(declaration => declaration.Name))
      .Concat(nodes.OfType<DatatypeCtor>().Select(constructor => constructor.Name))
      .Concat(program.RawModules().Select(module => module.Name)).ToHashSet();
    while (names.Any(name => name.Contains(preferred, System.StringComparison.Ordinal))) { preferred += "0"; }
    return preferred;
  }
}

public sealed record ContractBodyExpansionBudget(int MaxCallDepth = 3, int MaxLoopIterations = 3, int MaxGoals = 64);
public enum ContractBodyGoalKind { Branch, Return, AssertionFailure, CallPreconditionFailure, EntryReachable }
public sealed record ContractBodySourcePoint(string Symbol, int Position, int Length, int Line, int Column);
public sealed record ContractBodyGoal(string Id, ContractBodyGoalKind Kind, ContractBodySourcePoint Location,
  bool? BranchValue = null);
public sealed record ContractBodyTraceEvent(string Name, ContractBodySourcePoint Location, bool Value);
public sealed record ContractBodyCapturedValue(string Name, Type Type, string Expression);
public sealed record ContractBodyAbstractCall(string Id, MethodOrFunction Callable,
  IReadOnlyList<ContractBodyCapturedValue> Inputs, IReadOnlyList<ContractBodyCapturedValue> Outputs,
  ContractBodyCapturedValue? Receiver = null, IReadOnlyList<Type>? TypeArguments = null) {
  public string BeforeMarker => "/*contract_call_before:" + Id + "*/";
  public string AfterMarker => "/*contract_call_after:" + Id + "*/";
}
public sealed record ContractBodyFrontier(string Id, string Reason, ContractBodySourcePoint Location);
public sealed record ContractBodyExpansionResult(Method OriginalMethod, BlockStmt DetachedBody, string BodySource,
  IReadOnlyList<ContractBodyGoal> Goals, IReadOnlyList<ContractBodyFrontier> Frontier,
  IReadOnlyList<string> AbstractCalls, IReadOnlyList<string> TrustDependencies,
  IReadOnlyList<ContractBodyTraceEvent> TraceEvents, IReadOnlyList<ContractBodyAbstractCall> CapturedCalls) {
  public static string Marker(string id) => "/*contract_target:" + id + "*/";
}
