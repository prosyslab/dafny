using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

internal sealed record ContractDiagnosticConstructor(ClassDecl Class, IReadOnlyList<Field> Fields,
  IReadOnlyList<Field> Omitted, IOrigin Origin) {
  public string Declaration => ContractHeapFactory.ConstructorDeclaration(Fields, Omitted);
}

/// <summary>Validates explicit generator constructor shapes using the fixed heap's construction rules.</summary>
public static class ContractDiagnosticConstruction {
  internal const string AttributeName = "pbt_heap_constructor";

  internal static IReadOnlyList<ContractDiagnosticConstructor> Parse(Program program, Method goal, Method generator) {
    var classes = ContractHeapFactory.ClassDeclarations(program);
    var selected = new HashSet<ClassDecl>();
    var result = new List<ContractDiagnosticConstructor>();
    foreach (var attribute in generator.Attributes.AsEnumerable().Where(attribute => attribute.Name == AttributeName)) {
      if (attribute.Args.Count == 0 || attribute.Args.Any(argument => argument is not LiteralExpr { Value: string })) {
        throw new NotSupportedException("pbt_heap_constructor requires a class name and optional fully qualified field name strings.");
      }
      var names = attribute.Args.Cast<LiteralExpr>().Select(argument => (string)argument.Value!).ToList();
      var declaration = classes.SingleOrDefault(candidate => candidate.FullDafnyName == names[0])
        ?? throw new NotSupportedException("Unknown diagnostic constructor class: " + names[0]);
      if (!selected.Add(declaration)) { throw new NotSupportedException("Duplicate diagnostic constructor class: " + names[0]); }
      ContractHeapFactory.ValidateClass(program, goal, declaration);
      var fields = new List<Field>();
      foreach (var name in names.Skip(1)) {
        var field = declaration.Members.OfType<Field>().SingleOrDefault(field => !field.IsStatic && field.FullDafnyName == name)
          ?? throw new NotSupportedException("Unknown or foreign diagnostic constructor instance field: " + name);
        if (fields.Contains(field)) { throw new NotSupportedException("Duplicate diagnostic constructor field: " + name); }
        fields.Add(field);
      }
      var shape = new ContractHeapObject("diagnostic", declaration.FullDafnyName,
        fields.ToDictionary(field => field.Name, _ => new ContractValue(ContractValueKind.Null)));
      var (_, omitted) = ContractHeapFactory.ValidateFields(declaration, shape);
      // Repeat against the final resolved diagnostic to include dependencies introduced by drafts/generators.
      ContractHeapFactory.AuditOmittedFields(program, goal, omitted.ToHashSet());
      result.Add(new(declaration, fields, omitted, attribute is UserSuppliedAttributes supplied ? supplied.OpenBrace : generator.Origin));
    }
    return result;
  }

  /// <summary>Rejects omitted ghost state used by the resolved goal, generator, or installed drafts.</summary>
  public static void AuditResolved(Program program, Method goal, IReadOnlySet<string> constructorNames) {
    var generated = ContractRuntimeObligationTransformer.Members(program).OfType<Constructor>()
      .Where(constructor => constructorNames.Contains(constructor.FullDafnyName)).ToList();
    var omitted = generated.SelectMany(constructor => ((TopLevelDeclWithMembers)constructor.EnclosingClass).Members.OfType<Field>()
      .Where(field => field.IsGhost && !field.IsStatic && constructor.Ins.All(formal => formal.Name != field.Name))).ToHashSet();
    foreach (var root in ContractRuntimeObligationTransformer.DiagnosticReachable(program, goal)) {
      ContractHeapFactory.AuditOmittedFields(program, root, omitted, generated.Cast<ICallable>().ToHashSet());
    }
  }
}
