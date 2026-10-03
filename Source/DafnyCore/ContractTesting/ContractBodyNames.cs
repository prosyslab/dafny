#nullable enable
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
