using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

/// <summary>One generated diagnostic constructor, its source text and the instance fields it supplies.</summary>
internal sealed record ContractDiagnosticConstructor(ClassDecl Class, string Name, IReadOnlyList<Field> Supplied,
  IReadOnlyList<Field> Omitted, string Declaration, IOrigin Origin);

/// <summary>Validates generator constructor shapes, including nested allocations, using the fixed heap's construction rules.</summary>
public static class ContractDiagnosticConstruction {
  internal const string AttributeName = "pbt_heap_constructor";
  internal const string SuppliedAttributeName = "pbt_supplied_fields";

  // A supplied field takes a constructor parameter (Nested == null) or a nested diagnostic allocation.
  private sealed record Shape(ClassDecl Class, IReadOnlyList<(Field Field, Shape? Nested)> Supplied,
    IReadOnlyList<Field> Omitted) {
    // Uses of a class share one generated constructor only when their shapes are identical.
    public string Key => Class.FullDafnyName + "(" + string.Join(",", Supplied.Select(entry =>
      entry.Field.Name + (entry.Nested == null ? "" : "=" + entry.Nested.Key))) + ")";

    // Nested parameters are exposed by the enclosing constructor under their field-path name.
    public IEnumerable<(string Name, Field Field, bool Direct)> Parameters => Supplied.SelectMany(entry =>
      entry.Nested == null
        ? new (string Name, Field Field, bool Direct)[] { (entry.Field.Name, entry.Field, true) }
        : entry.Nested.Parameters.Select(parameter => (entry.Field.Name + "_" + parameter.Name, parameter.Field, false)));
  }

  private sealed record FieldPath(string Name, IReadOnlyList<string> Segments);

  internal static IReadOnlyList<ContractDiagnosticConstructor> Parse(Program program, Method goal, Method generator) {
    var classes = ContractHeapFactory.ClassDeclarations(program);
    var roots = new List<(Shape Shape, IOrigin Origin)>();
    foreach (var attribute in generator.Attributes.AsEnumerable().Where(attribute => attribute.Name == AttributeName)) {
      if (attribute.Args.Count == 0 || attribute.Args.Any(argument => argument is not LiteralExpr { Value: string })) {
        throw new NotSupportedException("pbt_heap_constructor requires a class name and optional fully qualified field name strings.");
      }
      var names = attribute.Args.Cast<LiteralExpr>().Select(argument => (string)argument.Value!).ToList();
      var declaration = classes.SingleOrDefault(candidate => candidate.FullDafnyName == names[0])
        ?? throw new NotSupportedException("Unknown diagnostic constructor class: " + names[0]);
      if (roots.Any(root => root.Shape.Class == declaration)) {
        throw new NotSupportedException("Duplicate diagnostic constructor class: " + names[0]);
      }
      var paths = names.Skip(1).Select(name => ParsePath(declaration, name)).ToList();
      roots.Add((BuildShape(program, goal, declaration, paths, [declaration]),
        attribute is UserSuppliedAttributes supplied ? supplied.OpenBrace : generator.Origin));
    }
    return Emit(program, roots);
  }

  /// <summary>Returns the instance fields a generated diagnostic constructor declares as supplied.</summary>
  internal static IReadOnlySet<string> SuppliedFieldNames(Constructor constructor) =>
    (Attributes.FindExpressions(constructor.Attributes, SuppliedAttributeName) ?? [])
      .Select(argument => argument is LiteralExpr { Value: string name } ? name
        : throw new NotSupportedException("Malformed generated diagnostic constructor metadata."))
      .ToHashSet(StringComparer.Ordinal);

  /// <summary>Rejects omitted ghost state used by the resolved goal, generator, or installed drafts.</summary>
  public static void AuditResolved(Program program, Method goal, IReadOnlySet<string> constructorNames) {
    var generated = ContractRuntimeObligationTransformer.Members(program).OfType<Constructor>()
      .Where(constructor => constructorNames.Contains(constructor.FullDafnyName)).ToList();
    var omitted = generated.SelectMany(constructor => ((TopLevelDeclWithMembers)constructor.EnclosingClass).Members.OfType<Field>()
      .Where(field => field.IsGhost && !field.IsStatic && !SuppliedFieldNames(constructor).Contains(field.Name))).ToHashSet();
    foreach (var root in ContractRuntimeObligationTransformer.DiagnosticReachable(program, goal)) {
      ContractHeapFactory.AuditOmittedFields(program, root, omitted, generated.Cast<ICallable>().ToHashSet());
    }
  }

  private static FieldPath ParsePath(ClassDecl declaration, string name) {
    var prefix = declaration.FullDafnyName + ".";
    var segments = name.StartsWith(prefix, StringComparison.Ordinal) ? name[prefix.Length..].Split('.') : [];
    if (segments.Length == 0 || segments.Any(segment => segment.Length == 0)) {
      throw new NotSupportedException("Unknown or foreign diagnostic constructor instance field: " + name);
    }
    return new(name, segments);
  }

  // Explicit paths come first in annotation order; unmentioned non-null object fields are then
  // allocated by default when possible, and any remaining ghost field keeps an omitted witness.
  private static Shape BuildShape(Program program, Method goal, ClassDecl declaration, IReadOnlyList<FieldPath> paths,
    IReadOnlyList<ClassDecl> stack) {
    ContractHeapFactory.ValidateClass(program, goal, declaration);
    var fields = InstanceFields(declaration);
    var supplied = new List<(Field Field, Shape? Nested)>();
    foreach (var group in paths.GroupBy(path => path.Segments[0], StringComparer.Ordinal)) {
      var field = fields.SingleOrDefault(candidate => candidate.Name == group.Key)
        ?? throw new NotSupportedException("Unknown or foreign diagnostic constructor instance field: " + group.First().Name);
      var direct = group.Where(path => path.Segments.Count == 1).ToList();
      if (direct.Count > 1) { throw new NotSupportedException("Duplicate diagnostic constructor field: " + direct[1].Name); }
      if (direct.Count == 1 && group.Count() > 1) {
        throw new NotSupportedException("Diagnostic constructor field is both a parameter and a nested allocation: " + direct[0].Name);
      }
      if (direct.Count == 1) {
        supplied.Add((field, null));
        continue;
      }
      var nested = FieldClass(field) ?? throw new NotSupportedException(
        "Nested diagnostic construction requires a class-typed field: " + group.First().Name);
      supplied.Add((field, BuildShape(program, goal, nested,
        group.Select(path => new FieldPath(path.Name, path.Segments.Skip(1).ToList())).ToList(), stack.Append(nested).ToList())));
    }
    foreach (var field in fields.Where(field => supplied.All(entry => entry.Field != field))) {
      if (DefaultClass(program, goal, field, stack) is { } nested) {
        supplied.Add((field, BuildShape(program, goal, nested, [], stack.Append(nested).ToList())));
      }
    }
    var shape = new ContractHeapObject("diagnostic", declaration.FullDafnyName,
      supplied.ToDictionary(entry => entry.Field.Name, _ => new ContractValue(ContractValueKind.Null)));
    var (_, omitted) = ContractHeapFactory.ValidateFields(declaration, shape);
    // Repeat against the final resolved diagnostic to include dependencies introduced by drafts/generators.
    ContractHeapFactory.AuditOmittedFields(program, goal, omitted.ToHashSet());
    return new(declaration, supplied, omitted);
  }

  // A non-null field of a constructible class is allocated by default unless that would recurse.
  private static ClassDecl? DefaultClass(Program program, Method goal, Field field, IReadOnlyList<ClassDecl> stack) {
    if (field.Type.AsNonNullRefType == null || FieldClass(field) is not { } nested || stack.Contains(nested)) { return null; }
    var nestedStack = stack.Append(nested).ToList();
    return ContractHeapFactory.IsDiagnosticConstructible(program, goal, nested) && InstanceFields(nested)
      .All(member => member.IsGhost || DefaultClass(program, goal, member, nestedStack) != null) ? nested : null;
  }

  private static ClassDecl? FieldClass(Field field) {
    var type = field.Type.AsNonNullRefType?.ResolvedClass is NonNullTypeDecl nonNull
      ? nonNull.Class
      : (field.Type.NormalizeExpandKeepConstraints() as UserDefinedType)?.ResolvedClass;
    return type is ClassDecl declaration and not ArrayClassDecl ? declaration : null;
  }

  private static IReadOnlyList<Field> InstanceFields(ClassDecl declaration) =>
    declaration.Members.OfType<Field>().Where(field => field.Origin.line > 0 && !field.IsStatic).ToList();

  // Explicit annotations own each class's generator-facing name; other shapes receive private names.
  private static IReadOnlyList<ContractDiagnosticConstructor> Emit(Program program, IReadOnlyList<(Shape Shape, IOrigin Origin)> roots) {
    var names = new Dictionary<string, string>(StringComparer.Ordinal);
    var ordered = new List<(Shape Shape, IOrigin Origin)>();
    var counts = new Dictionary<ClassDecl, int>();
    foreach (var (shape, origin) in roots) {
      names.Add(shape.Key, ContractHeapFactory.ConstructorName);
      ordered.Add((shape, origin));
    }
    foreach (var (shape, origin) in roots) { Name(shape, origin); }
    return ordered.Select(item => new ContractDiagnosticConstructor(item.Shape.Class, names[item.Shape.Key],
      item.Shape.Supplied.Select(entry => entry.Field).ToList(), item.Shape.Omitted,
      Declaration(program, item.Shape, names), item.Origin)).ToList();

    void Name(Shape shape, IOrigin origin) {
      foreach (var nested in shape.Supplied.Select(entry => entry.Nested).OfType<Shape>()) {
        if (!names.ContainsKey(nested.Key)) {
          var index = counts.GetValueOrDefault(nested.Class) + 1;
          counts[nested.Class] = index;
          names.Add(nested.Key, ContractHeapFactory.ConstructorName + "_" + index);
          ordered.Add((nested, origin));
        }
        Name(nested, origin);
      }
    }
  }

  private static string Declaration(Program program, Shape shape, IReadOnlyDictionary<string, string> names) {
    var scope = shape.Class.EnclosingModuleDefinition;
    var parameters = shape.Parameters.ToList();
    var locals = parameters.Select(parameter => parameter.Name).ToHashSet(StringComparer.Ordinal);
    if (locals.Count != parameters.Count) {
      throw new NotSupportedException("Diagnostic constructor parameter names collide for " + shape.Class.FullDafnyName + ".");
    }
    var formals = string.Join(", ", parameters.Select(parameter => (parameter.Field.IsGhost ? "ghost " : "") + parameter.Name + ": " +
      (parameter.Direct ? parameter.Field.Type.ToString() : ContractQueryBuilder.QualifiedType(program, scope, parameter.Field.Type))));
    var lines = new List<string>();
    foreach (var (field, nested) in shape.Supplied) {
      if (nested == null) {
        lines.Add($"    this.{field.Name} := {field.Name};");
        continue;
      }
      var local = Fresh("contractNested");
      var arguments = string.Join(", ", nested.Parameters.Select(parameter => field.Name + "_" + parameter.Name));
      lines.Add($"    var {local} := new {ContractHeapFactory.SourceTypeName(program, scope, nested.Class)}.{names[nested.Key]}({arguments});");
      lines.Add($"    this.{field.Name} := {local};");
    }
    foreach (var field in shape.Omitted) {
      var witness = Fresh("contractOmittedGhostWitness");
      lines.Add($"    ghost var {witness}: {field.Type} :| true;");
      lines.Add($"    this.{field.Name} := {witness};");
    }
    var supplied = string.Join(", ", shape.Supplied.Select(entry => "\"" + entry.Field.Name + "\""));
    var body = string.Join("\n", lines);
    return $"\n  constructor {{:{SuppliedAttributeName}{(supplied.Length == 0 ? "" : " " + supplied)}}} {names[shape.Key]}({formals}) {{" +
      (body.Length == 0 ? "" : "\n" + body + "\n  ") + "}\n";

    string Fresh(string prefix) {
      var index = 0;
      while (!locals.Add(prefix + index)) { index++; }
      return prefix + index;
    }
  }
}
