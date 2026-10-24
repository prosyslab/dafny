using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;

namespace DafnyTestGeneration.ContractTesting;

public static class ContractQueryBuilder {
  public const string QueryName = "ContractDiagnosticQuery";
  public const string TargetMarker = "contract_query_target";
  public static string Name(ContractPreparedProgram prepared) => ContractBodyNames.Family(prepared.Program, QueryName);

  /// <summary>Builds a native assertion over concrete inputs and, for methods, all legal outputs jointly.</summary>
  internal static ContractScreenQuery BuildScreen(ContractPreparedProgram prepared,
    IReadOnlyDictionary<string, ContractValue> inputs, bool domain, bool negate) {
    var method = prepared.Method;
    var scope = method.EnclosingClass.EnclosingModuleDefinition;
    var parameters = string.Join(", ", method.Ins.Select(formal => formal.Name + ": " +
      QualifiedType(prepared.Program, scope, formal.Type)));
    var bindings = method.Ins.Select(formal => "requires " + formal.Name + " == " +
      ContractModelCodec.ToDafny(inputs[formal.Name]));
    var precondition = Conjunction(method.Req.Select(clause => RenderExpression(prepared, clause.E)));
    var postcondition = Conjunction(method.Ens.Select(clause => RenderExpression(prepared, clause.E)));
    var assertion = domain ? precondition : method.Outs.Count == 0 ? postcondition :
      "(exists " + string.Join(", ", method.Outs.Select(formal => formal.Name + ": " +
        QualifiedType(prepared.Program, scope, formal.Type))) + " :: " + postcondition + ")";
    if (negate) { assertion = "!(" + assertion + ")"; }
    var name = Name(prepared);
    var declaration = "\nghost method " + name + "(" + parameters + ")\n" +
      string.Join("\n", bindings) + "\n" + (domain ? "" : "requires " + precondition + "\n") +
      "{ assert {:error \"" + TargetMarker + "\"} " + assertion + "; }\n";
    var offset = method.StartToken.pos;
    var bytes = System.Text.Encoding.UTF8.GetBytes(prepared.Source.Content);
    var characterOffset = System.Text.Encoding.UTF8.GetCharCount(bytes, 0, offset);
    return new(prepared.Source.Content.Insert(characterOffset, declaration), prepared.Source.Path, name,
      offset, offset + System.Text.Encoding.UTF8.GetByteCount(declaration));
  }

  public static string Build(ContractPreparedProgram prepared, ContractTestRequest request,
    ContractQueryKind kind, IReadOnlyDictionary<string, ContractValue>? outputs = null, bool negate = false,
    IReadOnlyDictionary<string, ContractValue>? observations = null, IReadOnlyList<string>? choiceConstraints = null,
    Expression? postconditionClause = null) {
    if (kind == ContractQueryKind.ContractRealization) {
      throw new System.NotSupportedException("Joint-output realizability requires the dedicated contract screen.");
    }
    if (kind == ContractQueryKind.PremiseConsistency) { RequireInitializerDefinitions(prepared); }
    var method = prepared.Method;
    var formals = method.Ins.Concat(outputs == null ? [] : method.Outs).ToList();
    var parameterParts = formals.Select(formal => formal.Name + ": " + formal.Type).ToList();
    if (!method.IsStatic) {
      parameterParts.Add(prepared.ReceiverName + ": " + method.EnclosingClass.Name);
    }
    if (!string.IsNullOrEmpty(prepared.Heap?.QueryParameters)) {
      parameterParts.Add(prepared.Heap.QueryParameters);
    }
    var parameters = string.Join(", ", parameterParts);
    var bindings = method.Ins.Select(formal => formal.Name + " == " + ContractHarnessBuilder.InputExpression(prepared, request, formal.Name)).ToList();
    if (!method.IsStatic) {
      bindings.Add(prepared.ReceiverName + " == " + prepared.Heap!.ReferenceExpression(request.Entry.Receiver!.Value!));
    }
    bindings.AddRange(prepared.Heap?.InitialConstraints ?? []);
    bindings.AddRange(choiceConstraints ?? []);
    if (outputs != null) {
      bindings.AddRange(method.Outs.Select(formal => formal.Name + " == " +
        (prepared.Heap != null
          ? prepared.Heap.ValueExpression(outputs[formal.Name], formal.Type)
          : ContractModelCodec.ToDafny(outputs[formal.Name], method.EnclosingClass.EnclosingModuleDefinition.FullDafnyName))));
    }
    var precondition = Conjunction(method.Req.Select(clause => RenderExpression(prepared, clause.E)));
    var postcondition = postconditionClause == null ? Conjunction(method.Ens.Select(clause => RenderExpression(prepared, clause.E))) :
      RenderExpression(prepared, postconditionClause);
    var assertion = kind switch {
      ContractQueryKind.PremiseConsistency => "false",
      ContractQueryKind.EntryPrecondition or ContractQueryKind.CallPrecondition => precondition,
      _ => postcondition
    };
    if (negate) {
      assertion = "!(" + assertion + ")";
    }
    // The property under test occurs only in the assertion. In particular, no call to the
    // selected method introduces its ensures as an assumption into this diagnostic query.
    var assignments = observations != null ? prepared.Heap?.QueryAssignments(observations) : "";
    IEnumerable<Expression> expressions = kind == ContractQueryKind.PremiseConsistency ?
      outputs == null ? [] : method.Req.Select(clause => clause.E) :
      kind is ContractQueryKind.EntryPrecondition or ContractQueryKind.CallPrecondition ? method.Req.Select(clause => clause.E) :
      postconditionClause == null ? method.Ens.Select(clause => clause.E) : [postconditionClause];
    var types = formals.Select(formal => formal.Type).Concat(prepared.Heap?.Slots.SelectMany(slot =>
      slot.Fields.Concat(slot.OmittedGhostFields).Select(field => field.Type)) ?? []);
    var reveals = RevealDefinitions(prepared.Program, method.EnclosingClass.EnclosingModuleDefinition, expressions, types,
      requireDefinitions: kind == ContractQueryKind.PremiseConsistency);
    return ContractHarnessBuilder.Insert(prepared, $"\nmethod {Name(prepared)}({parameters})\n" +
      string.Join("\n", bindings.Select(binding => "requires " + binding)) + "\n" +
      (outputs != null ? "requires " + precondition + "\n" : "") +
      (observations != null ? prepared.Heap?.QueryModifies : "") + "\n" +
      $"{{ {reveals}\n{assignments}\nassert {{:error \"{TargetMarker}\"}} {assertion}; }}\n");
  }

  public static string BuildClosedClause(ContractPreparedProgram prepared, ContractRuntimeClause clause,
    IReadOnlyDictionary<string, ContractValue> values, bool negate = false) {
    var scope = clause.Owner.EnclosingClass.EnclosingModuleDefinition;
    var module = scope.FullDafnyName;
    var parameters = string.Join(", ", clause.Variables.Select(v => v.Name + ": " +
      QualifiedType(prepared.Program, scope, v.Type)));
    var bindings = string.Join("\n", clause.Variables.Select(v => "requires " + v.Name + " == " + ContractModelCodec.ToDafny(
      QualifyValue(prepared.Program, scope, values[v.Name], v.Type), module)));
    var expression = Printer.ExprToString(prepared.Program.Options, QualifyExpression(prepared.Program, scope, clause.Expression));
    var reveals = RevealDefinitions(prepared.Program, scope, [clause.Expression], clause.Variables.Select(variable => variable.Type));
    var declaration = "\nmethod " + Name(prepared) + "(" + parameters + ")\n" + bindings +
      "\n{ " + reveals + "\nassert {:error \"" + TargetMarker + "\"} " + (negate ? "!(" : "(") + expression + "); }\n";
    var source = ContractSourceSnapshot.Find(prepared.SourceSnapshots, clause.Owner.Origin.Uri);
    var insertion = clause.Owner.EnclosingClass is DefaultClassDecl ? clause.Owner.StartToken.pos : clause.Owner.EnclosingClass.StartToken.pos;
    var index = System.Text.Encoding.UTF8.GetCharCount(System.Text.Encoding.UTF8.GetBytes(source.Content), 0, insertion);
    return source.Content.Insert(index, declaration);
  }

  public static string RenderExpression(ContractPreparedProgram prepared, Expression expression, ModuleDefinition? queryScope = null) {
    var method = prepared.Method;
    Expression? receiver = method.IsStatic ? null : new IdentifierExpr(method.Origin, prepared.ReceiverName) {
      Type = UserDefinedType.FromTopLevelDecl(method.Origin, method.EnclosingClass)
    };
    return Printer.ExprToString(prepared.Program.Options,
      new QuerySubstituter(prepared.Program, queryScope ?? method.EnclosingClass.EnclosingModuleDefinition, receiver).Substitute(expression));
  }

  /// <summary>Qualifies resolved declarations for an expression inserted into the supplied source module.</summary>
  public static Expression QualifyExpression(Program program, ModuleDefinition scope, Expression expression) =>
    new QuerySubstituter(program, scope, null).Substitute(expression);

  internal static string BuildInitialTypeProof(ContractPreparedProgram prepared,
    IReadOnlyList<(ContractValue Value, Type Type)> values) {
    var scope = prepared.Method.EnclosingClass.EnclosingModuleDefinition;
    var declarations = values.Select((item, index) => {
      var typeName = QualifiedType(prepared.Program, scope, item.Type);
      var value = ContractModelCodec.ToDafny(QualifyValue(prepared.Program, scope, item.Value, item.Type), scope.FullDafnyName);
      if (item.Type.NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: NewtypeDecl }) {
        value = "(" + value + " as " + typeName + ")";
      }
      return "ghost var contractInitialValue" + index + ": " + typeName + " := " + value + ";";
    });
    var reveals = RevealDefinitions(prepared.Program, scope, [], values.Select(item => item.Type), requireDefinitions: true);
    // No parameters or requires can assume the membership being proved. Native
    // assignment WD checks the complete declared type and every nested constructor.
    return ContractHarnessBuilder.Insert(prepared, "\nghost method " + Name(prepared) + "()\n{\n" +
      reveals + "\n" + string.Join("\n", declarations) + "\nassert {:error \"" + TargetMarker + "\"} true;\n}\n");
  }

  private static ContractValue QualifyValue(Program program, ModuleDefinition scope, ContractValue value, Type type) {
    type = type.NormalizeExpand();
    if (value.Kind == ContractValueKind.Datatype && type.AsDatatype is { } datatype) {
      var constructor = datatype.Ctors.Single(candidate => ContractHeapFactory.NamesConstructor(value.Constructor, datatype, candidate));
      var substitution = TypeParameter.SubstitutionMap(datatype.TypeArgs, type.TypeArgs);
      return value with {
        Constructor = ContractHeapFactory.SourceTypeName(program, scope, datatype) + "." + constructor.Name,
        Fields = constructor.Formals.ToDictionary(formal => formal.Name,
          formal => QualifyValue(program, scope, value.Fields![formal.Name], formal.Type.Subst(substitution)))
      };
    }
    if (value.Items != null && type.AsCollectionType is { } collection) {
      return value with { Items = value.Items.Select(item => QualifyValue(program, scope, item, collection.Arg)).ToList() };
    }
    if (value.Entries != null && type.AsMapType is { } map) {
      return value with {
        Entries = value.Entries.Select(entry => new ContractMapEntry(
        QualifyValue(program, scope, entry.Key, map.Domain), QualifyValue(program, scope, entry.Value, map.Range))).ToList()
      };
    }
    return value;
  }

  internal static string QualifiedType(Program program, ModuleDefinition scope, Type type) {
    type = type.NormalizeExpandKeepConstraints();
    if (type is UserDefinedType { ResolvedClass: TypeParameter } parameter) {
      return parameter.TypeName(program.Options, scope, parseAble: true);
    }
    if (type is UserDefinedType { ResolvedClass: { } declaration } applied) {
      // Captured types may come from a separate resolved snapshot of the same source.
      var natural = program.SystemModuleManager.NatDecl;
      if (declaration is SubsetTypeDecl && declaration.FullDafnyName == natural.FullDafnyName &&
          declaration.EnclosingModuleDefinition.FullDafnyName == natural.EnclosingModuleDefinition.FullDafnyName) {
        return "nat";
      }
      var arguments = applied.TypeArgs.Select(argument => QualifiedType(program, scope, argument)).ToList();
      if (declaration is TupleTypeDecl) { return "(" + string.Join(", ", arguments) + ")"; }
      return ContractHeapFactory.SourceTypeName(program, scope, declaration) +
        (declaration is ClassLikeDecl { IsReferenceTypeDecl: true } ? "?" : "") +
        (arguments.Count == 0 ? "" : "<" + string.Join(", ", arguments) + ">");
    }
    return type switch {
      SeqType sequence => "seq<" + QualifiedType(program, scope, sequence.Arg) + ">",
      SetType set => (set.Finite ? "set<" : "iset<") + QualifiedType(program, scope, set.Arg) + ">",
      MultiSetType multiset => "multiset<" + QualifiedType(program, scope, multiset.Arg) + ">",
      MapType map => (map.Finite ? "map<" : "imap<") + QualifiedType(program, scope, map.Domain) + ", " + QualifiedType(program, scope, map.Range) + ">",
      _ => type.ToString()
    };
  }

  private static string RevealDefinitions(Program program, ModuleDefinition scope, IEnumerable<Expression> expressions,
    IEnumerable<Type> types, bool requireDefinitions = false) {
    var roots = expressions.SelectMany(ContractRuntimeObligationTransformer.FunctionReferences).Distinct().ToList();
    var functions = ContractRuntimeObligationTransformer.ExecutionReachable(program, roots, types).OfType<Function>()
      .Where(function => function.IsOpaque || Attributes.Contains(function.Attributes, "opaque") || function.IsMadeImplicitlyOpaque(program.Options))
      .OrderBy(function => function.FullDafnyName, System.StringComparer.Ordinal).ToList();
    if (requireDefinitions && functions.Any(function => !AutoRevealFunctionDependencies.IsRevealable(scope.AccessibleMembers, function))) {
      throw new System.NotSupportedException("Original opaque definitions required for premise consistency are unavailable in the diagnostic import view.");
    }
    functions = functions.Where(function => AutoRevealFunctionDependencies.IsRevealable(scope.AccessibleMembers, function)).ToList();
    return string.Join("\n", functions.Select(function => AutoRevealFunctionDependencies.BuildRevealStmt(function, function.Origin, scope))
      .Where(statement => statement != null).Select(statement => Printer.StatementToString(program.Options, statement)));
  }

  private static void RequireInitializerDefinitions(ContractPreparedProgram prepared) {
    var roots = (prepared.Heap?.Slots ?? []).SelectMany(slot => slot.Fields.Concat(slot.OmittedGhostFields))
      .OfType<ConstantField>().Where(field => field.Rhs != null).ToHashSet();
    if (roots.Count == 0) { return; }
    var dependencies = new HashSet<Declaration>();
    ContractRuntimeObligationTransformer.ExecutionReachable(prepared.Program, [], declarationDependencies: dependencies, constantRoots: roots);
    var scope = prepared.Method.EnclosingClass.EnclosingModuleDefinition;
    var hidden = dependencies.Where(declaration => declaration is Function { Body: not null } ||
        declaration is ConstantField { Rhs: not null } constant && !roots.Contains(constant))
      .Where(declaration => !AutoRevealFunctionDependencies.IsRevealable(scope.AccessibleMembers, declaration))
      .OrderBy(declaration => declaration.Name, System.StringComparer.Ordinal).FirstOrDefault();
    if (hidden != null) {
      // The diagnostic export reveals captured readonly fields themselves. It does
      // not reveal private/provided-only initializer dependencies. A model of that
      // weaker view cannot establish consistency with their original definitions.
      throw new System.NotSupportedException("Original initializer definition unavailable in diagnostic import view: " +
        (hidden is MemberDecl member ? member.FullDafnyName : hidden.Name));
    }
  }

  private sealed class QuerySubstituter(Program program, ModuleDefinition scope, Expression? receiver) : Substituter(receiver!, [], []) {
    public override Expression Substitute(Expression expression) {
      if (expression is StaticReceiverExpr staticReceiver) {
        var type = staticReceiver.Type;
        var isImplicit = false;
        if (type.AsTopLevelTypeWithMembers is { } declaration) {
          var name = declaration is DefaultClassDecl ?
            ContractHeapFactory.SourceModuleName(program, scope, declaration.EnclosingModuleDefinition) :
            ContractHeapFactory.SourceTypeName(program, scope, declaration);
          isImplicit = name.Length == 0;
          type = new UserDefinedType(expression.Origin, isImplicit ? declaration.Name : name, declaration,
            type.TypeArgs.Select(QualifyType).ToList());
        }
        return new StaticReceiverExpr(expression.Origin, type, isImplicit) { Type = type };
      }
      if (expression is DatatypeValue { Ctor.EnclosingDatatype: { } datatype } value &&
          !value.MemberName.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
        var substituted = (DatatypeValue)base.Substitute(value);
        return new DatatypeValue(value.Origin, ContractHeapFactory.SourceTypeName(program, scope, datatype),
          value.MemberName, substituted.Arguments) {
          Ctor = value.Ctor,
          InferredTypeArgs = substituted.InferredTypeArgs.Select(QualifyType).ToList(),
          IsCoCall = value.IsCoCall,
          Type = substituted.Type
        };
      }
      var result = base.Substitute(expression);
      // The base substituter can return an original node, and resolved clones
      // retain these type lists. Detach before replacing their rendered names.
      if (result is FunctionCallExpr call) {
        var qualified = new FunctionCallExpr(new Cloner(cloneResolvedFields: true), call) {
          TypeApplication_AtEnclosingClass = call.TypeApplication_AtEnclosingClass.Select(QualifyType).ToList(),
          TypeApplication_JustFunction = call.TypeApplication_JustFunction.Select(QualifyType).ToList()
        };
        return qualified;
      }
      if (result is MemberSelectExpr member) {
        var qualified = new MemberSelectExpr(new Cloner(cloneResolvedFields: true), member) {
          TypeApplicationAtEnclosingClass = member.TypeApplicationAtEnclosingClass.Select(QualifyType).ToList(),
          TypeApplicationJustMember = member.TypeApplicationJustMember.Select(QualifyType).ToList()
        };
        return qualified;
      }
      return result;
    }

    private Type QualifyType(Type type) {
      type = type.NormalizeExpandKeepConstraints();
      if (type is UserDefinedType { ResolvedClass: TypeParameter }) {
        return type;
      }
      var arguments = type.TypeArgs.Select(QualifyType).ToList();
      if (type is UserDefinedType { ResolvedClass: { } declaration } applied &&
          type is not ArrowType && declaration is not (TupleTypeDecl or DefaultClassDecl) &&
          !ArrowType.IsPartialArrowTypeName(applied.Name) && !ArrowType.IsTotalArrowTypeName(applied.Name)) {
        var natural = program.SystemModuleManager.NatDecl;
        var name = declaration is SubsetTypeDecl && declaration.FullDafnyName == natural.FullDafnyName &&
          declaration.EnclosingModuleDefinition.FullDafnyName == natural.EnclosingModuleDefinition.FullDafnyName
          ? "nat" : ContractHeapFactory.SourceTypeName(program, scope, declaration);
        if (declaration is ClassLikeDecl { IsReferenceTypeDecl: true }) {
          name += "?";
        }
        return new UserDefinedType(applied.Origin, name, declaration, arguments);
      }
      return arguments.Count == 0 ? type : type.ReplaceTypeArguments(arguments);
    }
  }

  private static string Conjunction(IEnumerable<string> expressions) {
    var clauses = expressions.Select(expression => "(" + expression + ")").ToList();
    return clauses.Count == 0 ? "true" : string.Join(" && ", clauses);
  }
}
