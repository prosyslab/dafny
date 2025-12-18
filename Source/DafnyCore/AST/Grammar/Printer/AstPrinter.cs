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
    static AstPrinter() { }

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

    JsonNode json;
    AstPrintModes printMode;
    bool afterResolver;
    bool printingExportSet = false;
    bool printingDesugared = false;
    private readonly AstPrintFlags printFlags;


    public AstPrinter(JsonNode json, DafnyOptions options) {
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
      PrintTopLevelDecls(prog.Compilation, prog.DefaultModuleDef.TopLevelDecls, null);
      foreach (var tup in prog.DefaultModuleDef.PrefixNamedModules) {
        var decls = new List<TopLevelDecl>() { tup.Module };
        PrintTopLevelDecls(prog.Compilation, decls, tup.Parts);
      }
      PrintJson();
    }

    public JsonNode PrintTopLevelDecls(CompilationData compilation, IEnumerable<TopLevelDecl> decls,
      IEnumerable<IOrigin>/*?*/ prefixIds) {
      Contract.Requires(decls != null);
      JsonArray topLevelDeclsJson = new JsonArray();
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
          JsonNode members = PrintMembers(defaultClassDecl.Members, project);
          topLevelDeclsJson.Add(members);
        } else if (d is ClassLikeDecl) {
        } else if (d is ClassLikeDecl) {
        } else if (d is ValuetypeDecl) {
        } else if (d is ModuleDecl md) {
        } else {
          Contract.Assert(false); // unexpected TopLevelDecl
        }
      }
      return topLevelDeclsJson;
    }

    private void PrintSubsetTypeDecl(SubsetTypeDecl dd) {
      throw new NotImplementedException();
    }

    private void PrintWitnessClause(RedirectingTypeDecl dd) {
      throw new NotImplementedException();
    }

    void PrintModuleExportDecl(CompilationData compilation, ModuleExportDecl m, DafnyProject project) {
      throw new NotImplementedException();
    }

    public void PrintModuleDefinition(CompilationData compilation, ModuleDefinition module, VisibilityScope scope, IEnumerable<IOrigin>/*?*/ prefixIds) {
      throw new NotImplementedException();
    }

    void PrintTopLevelDeclsOrExportedView(CompilationData compilation, ModuleDefinition module) {
      var decls = module.TopLevelDecls;
      // only filter based on view name after resolver.
      if (afterResolver && options.DafnyPrintExportedViews.Count != 0) {
        var views = options.DafnyPrintExportedViews.ToHashSet();
        decls = decls.Where(d => views.Contains(d.FullName));
      }
      PrintTopLevelDecls(compilation, decls, null);
      foreach (var tup in module.PrefixNamedModules) {
        PrintTopLevelDecls(compilation, new TopLevelDecl[] { tup.Module }, tup.Parts);
      }
    }

    void PrintIteratorSignature(IteratorDecl iter) {
      throw new NotImplementedException();
    }

    private void PrintIteratorClass(IteratorDecl iter, DafnyProject project) {
      throw new NotImplementedException();
    }

    public void PrintClass(ClassLikeDecl c, DafnyProject project) {
      throw new NotImplementedException();
    }

    private void PrintExtendsClause(TopLevelDeclWithMembers c) {
      throw new NotImplementedException();
    }

    public JsonArray PrintMembers(List<MemberDecl> members, DafnyProject project) {
      Contract.Requires(members != null);
      JsonArray membersJson = new JsonArray();
      foreach (MemberDecl m in members) {
        if (PrintModeSkipGeneral(project, m.Origin)) { continue; }
        if (printMode == AstPrintModes.Serialization && Attributes.Contains(m.Attributes, "auto_generated")) {
          // omit this declaration
        } else if (m is MethodOrConstructor methodOrConstructor) {
          JsonNode decl = PrintMethod(methodOrConstructor, false);
          membersJson.Add(decl);
        } else if (m is Field) {
        } else if (m is Function) {
          JsonNode decl = PrintFunction((Function)m, false);
          membersJson.Add(decl);
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
      throw new NotImplementedException();
    }

    private void PrintTypeParams(List<TypeParameter> typeArgs) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    private void PrintTypeInstantiation(List<Type> typeArgs) {
      throw new NotImplementedException();
    }

    public void PrintDatatype(DatatypeDecl dt, DafnyProject dafnyProject) {
      throw new NotImplementedException();
    }

    /// <summary>
    /// Prints a space before each attribute.
    /// For @-Attributes, prints a newline and indent after each @-Attribute
    /// Use an indent of -1 to put just a space after the @-Attribute
    /// </summary>
    public void PrintAttributes(Attributes a, bool atAttributes) {
      throw new NotImplementedException();
    }

    // @-Attributes are printed first, then the keywords typically, then the regular attributes
    public void PrintAttributes(Attributes a, Action printBetween) {
      PrintAttributes(a, true);
      printBetween();
      PrintAttributes(a, false);
    }

    public void PrintOneAtAttribute(UserSuppliedAtAttribute usaa) {
      throw new NotImplementedException();
    }
    public void PrintOneAttribute(Attributes a, string nameSubstitution = null) {
      throw new NotImplementedException();

    }

    public void PrintAttributeArgs(List<Expression> args) {
      throw new NotImplementedException();
    }

    public void PrintField(Field field) {
      throw new NotImplementedException();
    }

    public JsonNode PrintFunction(Function f, bool printSignatureOnly) {
      Contract.Requires(f != null);
      JsonNode funJson = new JsonObject { ["kind"] = "FunctionDecl" };
      funJson["name"] = f.Name;
      JsonNode formals = PrintFormals(f.Ins, f, f.Name);
      funJson["formals"] = formals;
      if (f.Result != null || (f is not Predicate && f is not ExtremePredicate && f is not TwoStatePredicate && f is not PrefixPredicate)) {
        if (f.Result != null) {
          JsonNode resultJson = PrintFormal(f.Result, false);
          funJson["result"] = resultJson;
        }
        JsonNode resultTypeJson = PrintType(f.ResultType);
        funJson["resultType"] = resultTypeJson;
      }
      return funJson;
    }

    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2; // The amount of indent for each new scope
    void Indent(int amount) {
      throw new NotImplementedException();
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

    public JsonNode PrintMethod(MethodOrConstructor method, bool printSignatureOnly) {
      Contract.Requires(method != null);
      JsonNode methodJson = new JsonObject { ["kind"] = "MethodDecl" };
      methodJson["name"] = method.Name;
      JsonNode formals = PrintFormals(method.Ins, method, method.Name);
      methodJson["formals"] = formals;
      return methodJson;
    }

    private bool PrintModeSkipGeneral(DafnyProject project, IOrigin tok) {
      return (printMode == AstPrintModes.NoIncludes || printMode == AstPrintModes.NoGhostOrIncludes)
             && tok.Uri != null && !project.ContainsSourceFile(tok.Uri);
    }

    void PrintKTypeIndication(ExtremePredicate.KType kType) {
      throw new NotImplementedException();
    }

    internal JsonNode PrintFormals(List<Formal> ff, ICallable/*?*/ context, string name = null) {
      Contract.Requires(ff != null);
      JsonNode formalsJson = new JsonArray();
      foreach (Formal f in ff) {
        Contract.Assert(f != null);
        JsonNode formalJson = PrintFormal(f, (context is TwoStateLemma || context is TwoStateFunction) && f.InParam);
        formalsJson.AsArray().Add(formalJson);
      }
      return formalsJson;
    }

    JsonNode PrintFormal(Formal f, bool showNewKeyword) {
      Contract.Requires(f != null);
      JsonNode formalJson = new JsonObject { ["kind"] = "Formal" };
      if (f.HasName) {
        formalJson["name"] = f.DisplayName;
      }
      formalJson["type"] = PrintType(f.Type);
      if (f.DefaultValue != null) {
        // This printer emits JSON. Default values are represented structurally, not via text printing.
        formalJson["hasDefaultValue"] = true;
      }
      return formalJson;
    }

    internal void PrintDecreasesSpec(Specification<Expression> decs) {
      throw new NotImplementedException();
    }

    internal void PrintFrameSpecLine(string kind, Specification<FrameExpression> ee) {
      throw new NotImplementedException();
    }

    internal void PrintSpec(string kind, List<AttributedExpression> ee) {
      throw new NotImplementedException();
    }

    void PrintAttributedExpression(AttributedExpression e) {
      throw new NotImplementedException();
    }

    // ----------------------------- PrintType -----------------------------

    public JsonNode PrintType(Type ty) {
      Contract.Requires(ty != null);
      JsonNode typeJson = new JsonObject { ["kind"] = "Type" };
      typeJson["name"] = ty.TypeName(options, null, true);
      return typeJson;
    }

    public void PrintType(string prefix, Type ty) {
      throw new NotImplementedException();
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
