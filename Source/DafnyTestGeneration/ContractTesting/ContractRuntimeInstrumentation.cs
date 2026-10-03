using System;
using System.Collections.Generic;
using System.Linq;
using System.Text.Json;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>Supplies the diagnostic-only random stream and append-only runtime check recorder.</summary>
public static class ContractRuntimeInstrumentation {
  /// <summary>Dafny declarations of the diagnostic random stream and runtime check recorder, loaded from the checked-in library.</summary>
  public static readonly string DafnySource = ContractRuntimeLibrary.ReadWithoutTerminator("PbtRuntime.dfy");

  /// <summary>Returns the C# text compiled beside the diagnostic program: the checked-in library plus the per-task configuration class.</summary>
  public static string RuntimeSource(string observationPath, ContractRuntimeTransformation transformation) {
    var program = transformation.Prepared.Program;
    var compiledGhostFields = transformation.CompiledGhostFields;
    string RuntimeTypeName(TopLevelDecl declaration) =>
      ((declaration.EnclosingModuleDefinition.TryToAvoidName ? declaration.EnclosingModuleDefinition.GetCompileName(program.Options) + "." : "") +
       declaration.GetFullCompileName(program.Options)).Replace("@", "");
    var heapShapes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<ClassDecl>()
      .Where(declaration => declaration.TypeArgs.Count == 0)
      .Select(declaration => new {
        runtimeType = RuntimeTypeName(declaration),
        type = declaration.FullDafnyName,
        fields = declaration.Members.OfType<Field>().Where(field => (!field.IsGhost || compiledGhostFields.Contains(field)) && !field.IsStatic)
          .Select(field => new {
            name = field.Name,
            runtimeName = field.GetCompileName(program.Options).Replace("@", ""),
            shape = TypeShape(field.Type)
          }).ToList()
      }).ToList();
    var shapes = program.RawModules().SelectMany(module => module.TopLevelDecls).OfType<DatatypeDecl>()
      .Where(datatype => datatype.TypeArgs.Count == 0 || datatype is not CoDatatypeDecl)
      .SelectMany(datatype => datatype.Ctors.Where(constructor => !constructor.IsGhost && constructor.Formals.All(formal => !formal.IsGhost))
        .Select(constructor => new {
          runtimeType = (RuntimeTypeName(datatype) + (datatype.IsRecordType ? "" : "_" + constructor.GetCompileName(program.Options)) +
            (datatype.TypeArgs.Count == 0 ? "" : "`" + datatype.TypeArgs.Count)).Replace("@", ""),
          constructor = datatype.FullDafnyName + "." + constructor.Name,
          typeArguments = datatype.TypeArgs.Count,
          fields = constructor.Formals.Select((formal, index) => new {
            name = formal.Name,
            runtimeName = "_" + (formal.HasName ? formal.CompileName : "a" + index),
            shape = TypeShape(formal.Type, datatype.TypeArgs)
          }).ToList()
        })).ToList();
    // The configuration class follows the library text because the first library file starts with using directives;
    // the later files use fully qualified names so that concatenation stays valid.
    return ContractRuntimeLibrary.Read("PbtObservation.cs") + ContractRuntimeLibrary.Read("ContractRuntimeProfile.cs") + $$"""
      namespace DafnyContractRuntime {
      internal static class ContractRuntimeConfiguration {
        internal const bool RuntimeReferences = true;
        internal const bool ProfileRuntime = true;
        internal const string ObservationPath = {{JsonSerializer.Serialize(observationPath + ".legacy")}};
        internal const string HeapShapes = {{JsonSerializer.Serialize(JsonSerializer.Serialize(heapShapes))}};
        internal const string DatatypeShapes = {{JsonSerializer.Serialize(JsonSerializer.Serialize(shapes))}};
      }
      }

      """ + "\n" + ContractRuntimeLibrary.Read("PbtChecks.cs") + ContractRuntimeLibrary.Read("PbtRandom.cs");
  }

  internal static string TypeShapeToken(Microsoft.Dafny.Type type, IReadOnlyList<TypeParameter>? parameters = null) => Convert.ToBase64String(
    System.Text.Encoding.UTF8.GetBytes(JsonSerializer.Serialize(TypeShape(type, parameters))));

  private static object TypeShape(Microsoft.Dafny.Type type, IReadOnlyList<TypeParameter>? parameters = null) {
    if (type.IsArrayType) {
      return new Dictionary<string, object> { ["kind"] = "reference", ["type"] = ContractHeapFactory.ArrayTypeName(type) };
    }
    type = type.NormalizeToAncestorType();
    if (type.AsTypeParameter is { } parameter) {
      return new Dictionary<string, object> { ["kind"] = "parameter", ["index"] = parameters?.ToList().IndexOf(parameter) ?? -1 };
    }
    if (type.AsDatatype != null) {
      return new Dictionary<string, object> {
        ["kind"] = "datatype",
        ["arguments"] = type.TypeArgs.Select(argument => TypeShape(argument, parameters)).ToList()
      };
    }
    if (type.AsBitVectorType is { } bitvector) {
      return new Dictionary<string, object> { ["kind"] = "bitvector", ["width"] = bitvector.Width };
    }
    if (type.IsIntegerType) {
      return new Dictionary<string, object> { ["kind"] = "integer" };
    }
    if (type.AsSeqType is { } sequence) {
      return new Dictionary<string, object> { ["kind"] = "sequence", ["element"] = TypeShape(sequence.Arg, parameters) };
    }
    if (type.AsSetType is { } set) {
      return new Dictionary<string, object> { ["kind"] = "set", ["element"] = TypeShape(set.Arg, parameters) };
    }
    if (type.AsMultiSetType is { } multiset) {
      return new Dictionary<string, object> { ["kind"] = "multiset", ["element"] = TypeShape(multiset.Arg, parameters) };
    }
    if (type.AsMapType is { } map) {
      return new Dictionary<string, object> {
        ["kind"] = "map",
        ["key"] = TypeShape(map.Domain, parameters),
        ["value"] = TypeShape(map.Range, parameters)
      };
    }
    return new Dictionary<string, object> { ["kind"] = "other" };
  }
}
