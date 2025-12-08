using System;
using System.IO;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Nodes;
using DafnyCore;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public enum AstPrintModes {
    Everything,
    Serialization, // Serializing the program to a file for lossless loading later
    NoIncludes,
    NoGhostOrIncludes
  }

  public record AstPrintFlags(bool UseOriginalDafnyNames = false);

  public partial class AstPrinter {
    private DafnyOptions options;
    private const int AtAttributesOnSameLineIndent = -1;
    static AstPrinter() {}

    public static readonly Option<AstPrintModes> PrintMode = new("--print-mode", () => AstPrintModes.Everything, @"
Everything - Print everything listed below.
Serialization - print the source that will be included in a compiled dll.
NoIncludes - disable printing of {:verify false} methods
    incorporated via the include mechanism, as well as datatypes and
    fields included from other files.
NoGhost - disable printing of functions, ghost methods, and proof
    statements in implementation methods. It also disables anything
    NoIncludes disables.".TrimStart()) {
      IsHidden = true
    };

    TextWriter wr;
    JsonNode json;
    AstPrintModes printMode;
    bool afterResolver;
    bool printingExportSet = false;
    bool printingDesugared = false;
    private readonly AstPrintFlags printFlags;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(wr != null);
    }

    public AstPrinter(TextWriter wr, JsonNode json, DafnyOptions options) {
      Contract.Requires(wr != null);
      this.wr = wr;
      this.json = json;
      this.options = options;
      this.printFlags = printFlags ?? new AstPrintFlags();
    }

    public void PrintJson() {
      var options = new JsonSerializerOptions { WriteIndented = true };
      Console.WriteLine(json!.ToJsonString(options));
    }

    public void PrintProgram(Program prog, bool afterResolver) {
      Contract.Requires(prog != null);
      this.afterResolver = afterResolver;
      if (options.ShowEnv != Bpl.ExecutionEngineOptions.ShowEnvironment.Never) {
        wr.WriteLine("// " + options.Version);
        wr.WriteLine("// " + options.Environment);
      }
      wr.WriteLine();
      PrintTopLevelDecls(prog.Compilation, prog.DefaultModuleDef.TopLevelDecls, 0, null);
      foreach (var tup in prog.DefaultModuleDef.PrefixNamedModules) {
        var decls = new List<TopLevelDecl>() { tup.Module };
        PrintTopLevelDecls(prog.Compilation, decls, 0, tup.Parts);
      }
      wr.Flush();
      PrintJson();
    }

    public void PrintTopLevelDecls(CompilationData compilation, IEnumerable<TopLevelDecl> decls, int indent,
      IEnumerable<IOrigin>/*?*/ prefixIds) {
      Contract.Requires(decls != null);
      foreach (TopLevelDecl d in decls) {
        Contract.Assert(d != null);
        var project = compilation.Options.DafnyProject;
        if (PrintModeSkipGeneral(project, d.Origin)) { continue; }
        if (d is AbstractTypeDecl) {
        } else if (d is NewtypeDecl) {
        } else if (d is SubsetTypeDecl subsetTypeDecl) {
        } else if (d is TypeSynonymDecl) {
        } else if (d is DatatypeDecl) {
        } else if (d is IteratorDecl) {
        } else if (d is DefaultClassDecl defaultClassDecl) {
          JsonNode members = PrintMembers(defaultClassDecl.Members, indent, project);
          json["members"] = members;
        } else if (d is ClassLikeDecl) {
        } else if (d is ClassLikeDecl) {
        } else if (d is ValuetypeDecl) {
        } else if (d is ModuleDecl md) {
        } else {
          Contract.Assert(false); // unexpected TopLevelDecl
        }
      }
    }

    private void PrintSubsetTypeDecl(SubsetTypeDecl dd, int indent) {
      Indent(indent);
      PrintClassMethodHelper("type", dd.Attributes, dd.Name + TPCharacteristicsSuffix(dd.Characteristics), dd.TypeArgs);
      wr.Write(" = ");
      wr.Write(dd.Var.DisplayName);
      if (ShowType(dd.Var.Type)) {
        wr.Write(": ");
        PrintType(dd.Rhs);
      }

      if (dd is NonNullTypeDecl) {
        wr.Write(" ");
      } else {
        wr.WriteLine();
        Indent(indent + IndentAmount);
      }

      wr.Write("| ");
      PrintExpression(dd.Constraint, true);
      if (dd.WitnessKind != SubsetTypeDecl.WKind.CompiledZero) {
        if (dd is NonNullTypeDecl) {
          wr.Write(" ");
        } else {
          wr.WriteLine();
          Indent(indent + IndentAmount);
        }

        PrintWitnessClause(dd);
      }

      wr.WriteLine();
    }

    private void PrintWitnessClause(RedirectingTypeDecl dd) {
      Contract.Requires(dd != null);
      Contract.Requires(dd.WitnessKind != SubsetTypeDecl.WKind.CompiledZero);

      switch (dd.WitnessKind) {
        case SubsetTypeDecl.WKind.Ghost:
          wr.Write("ghost ");
          goto case SubsetTypeDecl.WKind.Compiled;
        case SubsetTypeDecl.WKind.Compiled:
          wr.Write("witness ");
          PrintExpression(dd.Witness, true);
          break;
        case SubsetTypeDecl.WKind.OptOut:
          wr.Write("witness *");
          break;
        case SubsetTypeDecl.WKind.Special:
          wr.Write("/*special witness*/");
          break;
        case SubsetTypeDecl.WKind.CompiledZero:
        default:
          Contract.Assert(false);  // unexpected WKind
          break;
      }
    }

    void PrintModuleExportDecl(CompilationData compilation, ModuleExportDecl m, int indent, DafnyProject project) {
      Contract.Requires(m != null);

      if (m.RevealAll) {
        Indent(indent);
        wr.WriteLine("reveals *");
      }
      if (m.ProvideAll) {
        Indent(indent);
        wr.WriteLine("provides *");
      }
      var i = 0;
      while (i < m.Exports.Count) {
        var start = i;
        var bodyKind = m.Exports[start].Opaque;
        do {
          i++;
        } while (i < m.Exports.Count && m.Exports[i].Opaque == bodyKind);
        // print [start..i)
        Indent(indent);
        wr.Write("{0} ", bodyKind ? "provides" : "reveals");
        wr.WriteLine(Util.Comma(i - start, j => m.Exports[start + j].ToString()));

        if (options.DafnyPrintResolvedFile != null) {
          Contract.Assert(!printingExportSet);
          printingExportSet = true;
          Indent(indent);
          wr.WriteLine("/*----- exported view:");
          for (int j = start; j < i; j++) {
            var id = m.Exports[j];
            if (id.Decl is TopLevelDecl) {
              PrintTopLevelDecls(compilation, new List<TopLevelDecl> { (TopLevelDecl)id.Decl }, indent + IndentAmount, null);
            } else if (id.Decl is MemberDecl) {
              PrintMembers([(MemberDecl)id.Decl], indent + IndentAmount, project);
            }
          }
          Indent(indent);
          wr.WriteLine("-----*/");
          Contract.Assert(printingExportSet);
          printingExportSet = false;
        }
      }
    }

    public void PrintModuleDefinition(CompilationData compilation, ModuleDefinition module, VisibilityScope scope, int indent, IEnumerable<IOrigin>/*?*/ prefixIds) {
      Contract.Requires(module != null);
      Contract.Requires(0 <= indent);
      Type.PushScope(scope);
      PrintAttributes(module.Attributes, indent, () => {
        if (module.ModuleKind == ModuleKindEnum.Abstract) {
          wr.Write("abstract ");
        }
        if (module.ModuleKind == ModuleKindEnum.Replaceable) {
          wr.Write("replaceable ");
        }
        wr.Write("module");
      });
      wr.Write(" ");
      if (prefixIds != null) {
        foreach (var p in prefixIds) {
          wr.Write("{0}.", p.val);
        }
      }
      wr.Write("{0} ", module.Name);
      if (module.Implements != null) {
        var kindString = module.Implements.Kind switch {
          ImplementationKind.Refinement => "refines",
          ImplementationKind.Replacement => "replaces",
          _ => throw new ArgumentOutOfRangeException()
        };
        wr.Write($"{kindString} {module.Implements.Target} ");
      }
      if (!module.TopLevelDecls.Any()) {
        wr.WriteLine("{ }");
      } else {
        wr.WriteLine("{");
        PrintTopLevelDeclsOrExportedView(compilation, module, indent);
        Indent(indent);
        wr.WriteLine("}");
      }
      Type.PopScope(scope);
    }

    void PrintTopLevelDeclsOrExportedView(CompilationData compilation, ModuleDefinition module, int indent) {
      var decls = module.TopLevelDecls;
      // only filter based on view name after resolver.
      if (afterResolver && options.DafnyPrintExportedViews.Count != 0) {
        var views = options.DafnyPrintExportedViews.ToHashSet();
        decls = decls.Where(d => views.Contains(d.FullName));
      }
      PrintTopLevelDecls(compilation, decls, indent + IndentAmount, null);
      foreach (var tup in module.PrefixNamedModules) {
        PrintTopLevelDecls(compilation, new TopLevelDecl[] { tup.Module }, indent + IndentAmount, tup.Parts);
      }
    }

    void PrintIteratorSignature(IteratorDecl iter, int indent) {
      Indent(indent);
      PrintClassMethodHelper("iterator", iter.Attributes, iter.Name, iter.TypeArgs);
      if (iter.IsRefining) {
        wr.Write(" ...");
      } else {
        PrintFormals(iter.Ins, iter);
        if (iter.Outs.Count != 0) {
          if (iter.Ins.Count + iter.Outs.Count <= 3) {
            wr.Write(" yields ");
          } else {
            wr.WriteLine();
            Indent(indent + 2 * IndentAmount);
            wr.Write("yields ");
          }
          PrintFormals(iter.Outs, iter);
        }
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", iter.Requires, ind);
      if (iter.Reads.Expressions != null) {
        PrintFrameSpecLine("reads", iter.Reads, ind);
      }
      if (iter.Modifies.Expressions != null) {
        PrintFrameSpecLine("modifies", iter.Modifies, ind);
      }
      PrintSpec("yield requires", iter.YieldRequires, ind);
      PrintSpec("yield ensures", iter.YieldEnsures, ind);
      PrintSpec("ensures", iter.Ensures, ind);
      PrintDecreasesSpec(iter.Decreases, ind);
      wr.WriteLine();
    }

    private void PrintIteratorClass(IteratorDecl iter, int indent, DafnyProject project) {
      PrintClassMethodHelper("class", null, iter.Name, iter.TypeArgs);
      wr.WriteLine(" {");
      PrintMembers(iter.Members, indent + IndentAmount, project);
      Indent(indent); wr.WriteLine("}");

      Contract.Assert(iter.NonNullTypeDecl != null);
      PrintSubsetTypeDecl(iter.NonNullTypeDecl, indent);
    }

    public void PrintClass(ClassLikeDecl c, int indent, DafnyProject project) {
      Contract.Requires(c != null);

      Indent(indent);
      PrintClassMethodHelper(c is TraitDecl ? "trait" : "class", c.Attributes, c.Name, c.TypeArgs);
      if (c.IsRefining) {
        wr.Write(" ...");
      } else {
        PrintExtendsClause(c);
      }

      if (c.Members.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        PrintMembers(c.Members, indent + IndentAmount, project);
        Indent(indent);
        wr.WriteLine("}");
      }

      if (options.DafnyPrintResolvedFile != null && c.NonNullTypeDecl != null) {
        if (!printingExportSet) {
          Indent(indent); wr.WriteLine("/*-- non-null type");
        }
        PrintSubsetTypeDecl(c.NonNullTypeDecl, indent);
        if (!printingExportSet) {
          Indent(indent); wr.WriteLine("*/");
        }
      }
    }

    private void PrintExtendsClause(TopLevelDeclWithMembers c) {
      string sep = " extends ";
      foreach (var trait in c.Traits) {
        wr.Write(sep);
        PrintType(trait);
        sep = ", ";
      }
    }

    public JsonNode PrintMembers(List<MemberDecl> members, int indent, DafnyProject project) {
      Contract.Requires(members != null);
      JsonNode membersJson = new JsonArray();
      int state = 0;  // 0 - no members yet; 1 - previous member was a field; 2 - previous member was non-field
      foreach (MemberDecl m in members) {
        if (PrintModeSkipGeneral(project, m.Origin)) { continue; }
        if (printMode == AstPrintModes.Serialization && Attributes.Contains(m.Attributes, "auto_generated")) {
          // omit this declaration
        } else if (m is MethodOrConstructor methodOrConstructor) {
          JsonNode decl = PrintMethod(methodOrConstructor, indent, false);
          membersJson.AsArray().Add(decl);
        } else if (m is Field) {
        } else if (m is Function) {
          JsonNode decl = PrintFunction((Function)m, indent, false);
          membersJson.AsArray().Add(decl);
        } else {
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected member
        }
      }
      return membersJson;
    }

    /// <summary>
    /// Prints no space before "kind", but does print a space before "attrs" and "name".
    /// </summary>
    void PrintClassMethodHelper(string kind, Attributes attrs, string name, List<TypeParameter> typeArgs) {
      Contract.Requires(kind != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);

      PrintAttributes(attrs, AtAttributesOnSameLineIndent, () => {
        wr.Write(kind);
      });

      if (ArrowType.IsArrowTypeName(name)) {
        PrintArrowType(ArrowType.ANY_ARROW, name, typeArgs);
      } else if (ArrowType.IsPartialArrowTypeName(name)) {
        PrintArrowType(ArrowType.PARTIAL_ARROW, name, typeArgs);
      } else if (ArrowType.IsTotalArrowTypeName(name)) {
        PrintArrowType(ArrowType.TOTAL_ARROW, name, typeArgs);
      } else if (SystemModuleManager.IsTupleTypeName(name)) {
        wr.Write(" /*{0}*/ ({1})", name, Util.Comma(typeArgs, TypeParamString));
      } else {
        wr.Write(" {0}", name);
        PrintTypeParams(typeArgs);
      }
    }

    private void PrintTypeParams(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(
        typeArgs.All(tp => tp.IsAutoCompleted) ||
        typeArgs.All(tp => !tp.IsAutoCompleted));

      if (typeArgs.Count != 0 && !typeArgs[0].IsAutoCompleted) {
        wr.Write("<{0}>", Util.Comma(typeArgs, TypeParamString));
      }
    }

    public static string TypeParameterToString(TypeParameter tp) {
      return TypeParamVariance(tp) + tp.Name + TPCharacteristicsSuffix(tp.Characteristics, true);
    }

    public string TypeParamString(TypeParameter tp) {
      Contract.Requires(tp != null);
      var paramString = TypeParamVariance(tp) + tp.Name + TPCharacteristicsSuffix(tp.Characteristics);
      foreach (var typeBound in tp.TypeBounds) {
        paramString += $" extends {typeBound.TypeName(options, null, true)}";
      }
      return paramString;
    }

    public static string TypeParamVariance(TypeParameter tp) {
      switch (tp.VarianceSyntax) {
        case TPVarianceSyntax.Covariant_Permissive:
          return "*";
        case TPVarianceSyntax.Covariant_Strict:
          return "+";
        case TPVarianceSyntax.NonVariant_Permissive:
          return "!";
        case TPVarianceSyntax.NonVariant_Strict:
          return "";
        case TPVarianceSyntax.Contravariance:
          return "-";
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new Cce.UnreachableException();
      }
    }

    private void PrintArrowType(string arrow, string internalName, List<TypeParameter> typeArgs) {
      Contract.Requires(arrow != null);
      Contract.Requires(internalName != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(1 <= typeArgs.Count);  // argument list ends with the result type
      wr.Write(" /*{0}*/ ", internalName);
      int arity = typeArgs.Count - 1;
      if (arity != 1) {
        wr.Write("(");
      }
      wr.Write(Util.Comma(arity, i => TypeParamString(typeArgs[i])));
      if (arity != 1) {
        wr.Write(")");
      }
      wr.Write(" {0} {1}", arrow, TypeParamString(typeArgs[arity]));
    }

    private void PrintTypeInstantiation(List<Type> typeArgs) {
      Contract.Requires(typeArgs == null || typeArgs.Count != 0);
      wr.Write(Type.TypeArgsToString(options, typeArgs));
    }

    public void PrintDatatype(DatatypeDecl dt, int indent, DafnyProject dafnyProject) {
      Contract.Requires(dt != null);
      Indent(indent);
      PrintClassMethodHelper(dt is IndDatatypeDecl ? "datatype" : "codatatype", dt.Attributes, dt.Name, dt.TypeArgs);
      PrintExtendsClause(dt);
      wr.Write(" =");
      string sep = "";
      foreach (DatatypeCtor ctor in dt.Ctors) {
        wr.Write(sep);
        PrintClassMethodHelper(ctor.IsGhost ? " ghost" : "", ctor.Attributes, ctor.Name, []);
        if (ctor.Formals.Count != 0) {
          PrintFormals(ctor.Formals, null);
        }
        sep = " |";
      }
      if (dt.Members.Count == 0) {
        wr.WriteLine();
      } else {
        wr.WriteLine(" {");
        // PrintMembers(dt.Members, indent + IndentAmount, dafnyProject);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    /// <summary>
    /// Prints a space before each attribute.
    /// For @-Attributes, prints a newline and indent after each @-Attribute
    /// Use an indent of -1 to put just a space after the @-Attribute
    /// </summary>
    public void PrintAttributes(Attributes a, bool atAttributes, int indent = -1) {
      if (a != null) {
        PrintAttributes(a.Prev, atAttributes, indent);
        if (a is UserSuppliedAtAttribute usaa && atAttributes) {
          PrintOneAtAttribute(usaa);
          if (indent >= 0) {
            wr.WriteLine();
            Indent(indent);
          } else {
            wr.Write(" ");
          }
        } else if (!(a is UserSuppliedAtAttribute) && !atAttributes) {
          wr.Write(" ");
          PrintOneAttribute(a);
        }
      }
    }

    // @-Attributes are printed first, then the keywords typically, then the regular attributes
    public void PrintAttributes(Attributes a, int indent, Action printBetween) {
      PrintAttributes(a, true, indent);
      printBetween();
      PrintAttributes(a, false, indent);
    }

    public void PrintOneAtAttribute(UserSuppliedAtAttribute usaa) {
      Contract.Requires(usaa != null);
      wr.Write(UserSuppliedAtAttribute.AtName);
      PrintExpression(usaa.Arg, false, -1);
    }
    public void PrintOneAttribute(Attributes a, string nameSubstitution = null) {
      Contract.Requires(a != null);
      var name = nameSubstitution ?? a.Name;
      var usAttribute = name.StartsWith("_") || (options.DisallowExterns && name == "extern");
      wr.Write("{1}{{:{0}", name, usAttribute ? "/*" : "");
      if (a.Args != null) {
        PrintAttributeArgs(a.Args, false);
      }
      wr.Write("}}{0}", usAttribute ? "*/" : "");

    }

    public void PrintAttributeArgs(List<Expression> args, bool isFollowedBySemicolon) {
      Contract.Requires(args != null);
      string prefix = " ";
      foreach (var arg in args) {
        Contract.Assert(arg != null);
        wr.Write(prefix);
        prefix = ", ";
        PrintExpression(arg, isFollowedBySemicolon);
      }
    }

    public void PrintField(Field field, int indent) {
      Contract.Requires(field != null);
      Indent(indent);

      PrintAttributes(field.Attributes, indent, () => {
        if (field.HasStaticKeyword) {
          wr.Write("static ");
        }
        if (field.IsGhost) {
          wr.Write("ghost ");
        }
        if (!field.IsMutable) {
          wr.Write("const");
        } else {
          wr.Write("var");
        }
      });
      wr.Write(" {0}", field.Name);
      if (ShowType(field.Type)) {
        wr.Write(": ");
        PrintType(field.Type);
      }
      if (field is ConstantField) {
        var c = (ConstantField)field;
        if (c.Rhs != null) {
          wr.Write(" := ");
          PrintExpression(c.Rhs, true);
        }
      } else if (!field.IsUserMutable && field.IsMutable) {
        wr.Write("  // non-assignable");
      }
      wr.WriteLine();
    }

    public JsonNode PrintFunction(Function f, int indent, bool printSignatureOnly) {
      Contract.Requires(f != null);
      JsonNode fdecl = new JsonObject{["kind"] = "FunctionDeclaration"};
      fdecl["name"] = f.Name;
      return fdecl;
    }

    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2; // The amount of indent for each new scope
    void Indent(int amount) {
      Contract.Requires(0 <= amount);
      wr.Write(new String(' ', amount));
    }

    private bool PrintModeSkipFunctionOrMethod(bool IsGhost, Attributes attributes, string name) {
      if (printMode == AstPrintModes.NoGhostOrIncludes && IsGhost) { return true; }
      if (printMode == AstPrintModes.NoIncludes || printMode == AstPrintModes.NoGhostOrIncludes) {
        bool verify = true;
        if (Attributes.ContainsBool(attributes, "verify", ref verify) && !verify) { return true; }
        if (name.Contains("INTERNAL") || name.StartsWith(HideRevealStmt.RevealLemmaPrefix)) { return true; }
      }
      return false;
    }
    public JsonNode PrintMethod(MethodOrConstructor method, int indent, bool printSignatureOnly) {
      Contract.Requires(method != null);
      JsonNode decl = new JsonObject{["kind"] = "MethodOrConstructorDeclaration"};
      decl["name"] = method.Name;
      return decl;
    }

    private bool PrintModeSkipGeneral(DafnyProject project, IOrigin tok) {
      return (printMode == AstPrintModes.NoIncludes || printMode == AstPrintModes.NoGhostOrIncludes)
             && tok.Uri != null && !project.ContainsSourceFile(tok.Uri);
    }

    void PrintKTypeIndication(ExtremePredicate.KType kType) {
      switch (kType) {
        case ExtremePredicate.KType.Nat:
          wr.Write("[nat]");
          break;
        case ExtremePredicate.KType.ORDINAL:
          wr.Write("[ORDINAL]");
          break;
        case ExtremePredicate.KType.Unspecified:
          break;
        default:
          Contract.Assume(false);  // unexpected KType value
          break;
      }
    }

    internal void PrintFormals(List<Formal> ff, ICallable/*?*/ context, string name = null) {
      Contract.Requires(ff != null);
      if (name != null && name.EndsWith("#")) {
        wr.Write("[");
        PrintFormal(ff[0], false);
        wr.Write("]");
        ff = [.. ff.Skip(1)];
      }
      wr.Write("(");
      string sep = "";
      foreach (Formal f in ff) {
        Contract.Assert(f != null);
        wr.Write(sep);
        sep = ", ";
        PrintFormal(f, (context is TwoStateLemma || context is TwoStateFunction) && f.InParam);
      }
      wr.Write(")");
    }

    void PrintFormal(Formal f, bool showNewKeyword) {
      Contract.Requires(f != null);
      if (showNewKeyword && !f.IsOld) {
        wr.Write("new ");
      }
      if (f.IsOlder) {
        Contract.Assert(f.HasName);
        wr.Write("older ");
      }
      if (f.IsGhost) {
        wr.Write("ghost ");
      }
      if (f.IsNameOnly) {
        Contract.Assert(f.HasName);
        wr.Write("nameonly ");
      }
      if (f.HasName) {
        wr.Write("{0}: ", f.DisplayName);
      }
      PrintType(f.Type);
      if (f.DefaultValue != null) {
        wr.Write(" := ");
        PrintExpression(f.DefaultValue, false);
      }
    }

    internal void PrintDecreasesSpec(Specification<Expression> decs, int indent) {
      Contract.Requires(decs != null);
      if (printMode == AstPrintModes.NoGhostOrIncludes) {
        return;
      }
      if (decs.Expressions != null && decs.Expressions.Count != 0) {
        wr.WriteLine();
        Indent(indent);
        PrintAttributes(decs.Attributes, indent, () => {
          wr.Write("decreases");
        });
        wr.Write(" ");
        PrintExpressionList(decs.Expressions, true);
      }
    }

    internal void PrintFrameSpecLine(string kind, Specification<FrameExpression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      if (ee != null && ee.Expressions != null && ee.Expressions.Count != 0) {
        wr.WriteLine();
        Indent(indent);
        PrintAttributes(ee.Attributes, indent, () => {
          wr.Write("{0}", kind);
        });
        wr.Write(" ");
        PrintFrameExpressionList(ee.Expressions);
      }
    }

    internal void PrintSpec(string kind, List<AttributedExpression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      if (printMode == AstPrintModes.NoGhostOrIncludes) { return; }
      foreach (AttributedExpression e in ee) {
        Contract.Assert(e != null);
        wr.WriteLine();
        Indent(indent);
        wr.Write("{0}", kind);
        PrintAttributedExpression(e);
      }
    }

    void PrintAttributedExpression(AttributedExpression e) {
      Contract.Requires(e != null);

      if (e.HasAttributes()) {
        PrintAttributes(e.Attributes, AtAttributesOnSameLineIndent, () => {
        });
      }

      wr.Write(" ");
      if (e.Label != null) {
        wr.Write("{0}: ", e.Label.Name);
      }
      PrintExpression(e.E, true);
    }

    // ----------------------------- PrintType -----------------------------

    public void PrintType(Type ty) {
      Contract.Requires(ty != null);
      wr.Write(ty.TypeName(options, null, true));
    }

    public void PrintType(string prefix, Type ty) {
      Contract.Requires(prefix != null);
      Contract.Requires(ty != null);
      if (options.DafnyPrintResolvedFile != null) {
        ty = TypeRefinementWrapper.NormalizeSansRefinementWrappers(ty);
      }
      string s = ty.TypeName(options, null, true);
      if (ty is TypeRefinementWrapper or not TypeProxy && !s.StartsWith("_")) {
        wr.Write("{0}{1}", prefix, s);
      }
    }

    public string TPCharacteristicsSuffix(TypeParameterCharacteristics characteristics) {
      return TPCharacteristicsSuffix(characteristics, options.DafnyPrintResolvedFile != null);
    }

    public static string TPCharacteristicsSuffix(TypeParameterCharacteristics characteristics, bool printInferredTypeCharacteristics) {
      string s = null;
      if (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Required ||
          (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.InferredRequired && printInferredTypeCharacteristics)) {
        s = "==";
      }
      if (characteristics.HasCompiledValue) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "0";
      } else if (characteristics.IsNonempty) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "00";
      }
      if (characteristics.ContainsNoReferenceTypes) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "!new";
      }
      if (s == null) {
        return "";
      } else {
        return "(" + s + ")";
      }
    }

    bool ShowType(Type t) {
      Contract.Requires(t != null);
      return !(t is TypeProxy) || options.DafnyPrintResolvedFile != null;
    }
  }
}
