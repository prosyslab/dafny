using System;
using System.Collections.Generic;
using System.Numerics;
using System.Reflection;

namespace Microsoft.Dafny;

internal sealed class HelperFunctionInterpreter {
  private const int MaxRecursionDepth = 10000;
  private const int MaxCollectionSize = 10000;

  private readonly PartialEvaluatorEngine engine;
  private readonly SystemModuleManager systemModuleManager;
  private readonly Dictionary<string, InterpreterHandler> handlers = new(StringComparer.Ordinal);
  private readonly HashSet<string> registeredModules = new(StringComparer.Ordinal);
  private static readonly MethodInfo AreLiteralExpressionsEqualMethod = typeof(PartialEvaluatorEngine).GetMethod(
    "AreLiteralExpressionsEqual",
    BindingFlags.NonPublic | BindingFlags.Static);
  private static readonly MethodInfo BuildMultisetCountsDictMethod = typeof(PartialEvaluatorEngine).GetMethod(
    "BuildMultisetCountsDict",
    BindingFlags.NonPublic | BindingFlags.Static);

  private delegate bool InterpreterHandler(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted);

  public HelperFunctionInterpreter(PartialEvaluatorEngine engine, SystemModuleManager systemModuleManager) {
    this.engine = engine;
    this.systemModuleManager = systemModuleManager;

    var moduleNames = GetRelevantModuleNames(engine, systemModuleManager);
    foreach (var moduleName in moduleNames) {
      RegisterAllHandlersForModule(moduleName);
    }

    RegisterAllHandlersForModule(string.Empty);
  }

  private static IReadOnlyCollection<string> GetRelevantModuleNames(PartialEvaluatorEngine engine, SystemModuleManager systemModuleManager) {
    var moduleNames = new HashSet<string>(StringComparer.Ordinal);
    var engineModuleName = GetEngineModuleFullName(engine);
    if (!string.IsNullOrEmpty(engineModuleName)) {
      moduleNames.Add(engineModuleName);
    }

    var systemModuleName = systemModuleManager?.SystemModule?.FullDafnyName;
    if (!string.IsNullOrEmpty(systemModuleName)) {
      moduleNames.Add(systemModuleName);
    }

    return moduleNames;
  }

  private static string GetEngineModuleFullName(PartialEvaluatorEngine engine) {
    if (engine == null) {
      return string.Empty;
    }

    var moduleField = typeof(PartialEvaluatorEngine).GetField("module", BindingFlags.Instance | BindingFlags.NonPublic);
    var moduleValue = moduleField?.GetValue(engine) as ModuleDefinition;
    return moduleValue?.FullDafnyName ?? string.Empty;
  }

  private void RegisterAllHandlersForModule(string moduleFullName) {
    moduleFullName ??= string.Empty;
    if (!registeredModules.Add(moduleFullName) && moduleFullName.Length > 0) {
      return;
    }

    RegisterHandler(moduleFullName, "Abs", TryInterpretAbs);
    RegisterHandler(moduleFullName, "Min", TryInterpretMin);
    RegisterHandler(moduleFullName, "Max", TryInterpretMax);
    RegisterHandler(moduleFullName, "Sum", TryInterpretSum);
    RegisterHandler(moduleFullName, "Product", TryInterpretProduct);
    RegisterHandler(moduleFullName, "Power", TryInterpretPower);
    RegisterHandler(moduleFullName, "Factorial", TryInterpretFactorial);
    RegisterHandler(moduleFullName, "GCD", TryInterpretGcd);
    RegisterHandler(moduleFullName, "LCM", TryInterpretLcm);
    RegisterHandler(moduleFullName, "IsPrime", TryInterpretIsPrime);
    RegisterHandler(moduleFullName, "DivisorCount", TryInterpretDivisorCount);
    RegisterHandler(moduleFullName, "Range", TryInterpretRange);
    RegisterHandler(moduleFullName, "PrefixSum", TryInterpretPrefixSum);
    RegisterHandler(moduleFullName, "Map", TryInterpretMap);
    RegisterHandler(moduleFullName, "MapIFrom", TryInterpretMapIFrom);
    RegisterHandler(moduleFullName, "MapI", TryInterpretMapI);
    RegisterHandler(moduleFullName, "Fold", TryInterpretFold);
    RegisterHandler(moduleFullName, "FoldIFrom", TryInterpretFoldIFrom);
    RegisterHandler(moduleFullName, "FoldI", TryInterpretFoldI);
    RegisterHandler(moduleFullName, "Filter", TryInterpretFilter);
    RegisterHandler(moduleFullName, "FilterIFrom", TryInterpretFilterIFrom);
    RegisterHandler(moduleFullName, "FilterI", TryInterpretFilterI);
    RegisterHandler(moduleFullName, "IsSorted", TryInterpretIsSorted);
    RegisterHandler(moduleFullName, "IsSortedDesc", TryInterpretIsSortedDesc);
    RegisterHandler(moduleFullName, "Count", TryInterpretCount);
    RegisterHandler(moduleFullName, "IsSubsequence", TryInterpretIsSubsequence);
    RegisterHandler(moduleFullName, "IsPermutation", TryInterpretIsPermutation);
    RegisterHandler(moduleFullName, "IsDigit", TryInterpretIsDigit);
    RegisterHandler(moduleFullName, "IsLower", TryInterpretIsLower);
    RegisterHandler(moduleFullName, "IsUpper", TryInterpretIsUpper);
    RegisterHandler(moduleFullName, "IsAlpha", TryInterpretIsAlpha);
    RegisterHandler(moduleFullName, "ToLower", TryInterpretToLower);
    RegisterHandler(moduleFullName, "ToUpper", TryInterpretToUpper);
    RegisterHandler(moduleFullName, "CharToNat", TryInterpretCharToNat);
    RegisterHandler(moduleFullName, "NatToChar", TryInterpretNatToChar);
    RegisterHandler(moduleFullName, "IntToString", TryInterpretIntToString);
    RegisterHandler(moduleFullName, "NatToString", TryInterpretNatToString);
    RegisterHandler(moduleFullName, "StringToNat", TryInterpretStringToNat);
    RegisterHandler(moduleFullName, "StringToInt", TryInterpretStringToInt);
  }

  private void RegisterHandler(string moduleFullName, string functionName, InterpreterHandler handler) {
    var key = $"{moduleFullName}::{functionName}";
    handlers[key] = handler;
  }

  public bool TryInterpret(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;

    if (callExpr?.Function == null || state == null) {
      return false;
    }

    if (engine == null || systemModuleManager == null) {
      return false;
    }

    if (!PartialEvaluatorEngine.AreAllInlineableArguments(callExpr.Args) &&
        !AreAllInterpreterInlineableArguments(callExpr.Args)) {
      return false;
    }

    if (!TryBuildHandlerKey(callExpr.Function, out var handlerKey)) {
      return false;
    }

    if (!handlers.TryGetValue(handlerKey, out var handler)) {
      var module = callExpr.Function.EnclosingClass?.EnclosingModuleDefinition?.FullDafnyName ?? string.Empty;
      RegisterAllHandlersForModule(module);
      if (!handlers.TryGetValue(handlerKey, out handler)) {
        return false;
      }
    }

    if (!handler(callExpr, simplifyExpression, state, out interpreted) || interpreted == null) {
      interpreted = null;
      return false;
    }

    return true;
  }


  private static bool ExtractIntArg(Expression arg, out BigInteger value) {
    value = default;
    if (Expression.IsIntLiteral(arg, out value)) {
      return true;
    }

    if (arg is NegationExpression negationExpression && ExtractIntArg(negationExpression.E, out var negatedValue)) {
      value = -negatedValue;
      return true;
    }

    if (arg is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Negate } unaryNegate && ExtractIntArg(unaryNegate.E, out var unaryNegatedValue)) {
      value = -unaryNegatedValue;
      return true;
    }

    if (arg is BinaryExpr { ResolvedOp: BinaryExpr.ResolvedOpcode.Sub } subtractionExpr &&
        Expression.IsIntLiteral(subtractionExpr.E0, out var leftValue) &&
        leftValue == 0 &&
        ExtractIntArg(subtractionExpr.E1, out var rightValue)) {
      value = -rightValue;
      return true;
    }

    if (arg is ConversionExpr conversionExpr && ExtractIntArg(conversionExpr.E, out var convertedValue)) {
      value = convertedValue;
      return true;
    }

    return false;
  }

  private static bool ExtractIntArg(
    Expression arg,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out BigInteger value) {
    if (ExtractIntArg(arg, out value)) {
      return true;
    }

    var simplified = simplifyExpression(arg, state);
    return simplified != null && ExtractIntArg(simplified, out value);
  }

  private static bool ExtractBoolArg(Expression arg, out bool value) {
    return Expression.IsBoolLiteral(arg, out value);
  }

  private static bool ExtractSeqArg(Expression arg, out SeqDisplayExpr sequence) {
    sequence = arg as SeqDisplayExpr;
    return sequence != null;
  }

  private static bool ExtractSeqArg(
    Expression arg,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out SeqDisplayExpr sequence) {
    if (ExtractSeqArg(arg, out sequence)) {
      return true;
    }

    var simplified = simplifyExpression(arg, state);
    return simplified != null && ExtractSeqArg(simplified, out sequence);
  }

  private static bool ExtractCharArg(Expression arg, out char value) {
    value = default;
    if (arg is not CharLiteralExpr charLiteral || charLiteral.Value is not string literal || literal.Length != 1) {
      return false;
    }

    value = literal[0];
    return true;
  }

  private static bool ExtractStringArg(Expression arg, out string value, out bool isVerbatim) {
    value = null;
    isVerbatim = false;
    if (arg is not StringLiteralExpr stringLiteral || stringLiteral.Value is not string stringValue) {
      return false;
    }

    value = stringValue;
    isVerbatim = stringLiteral.IsVerbatim;
    return true;
  }

  private static bool ExtractLambdaArg(Expression arg, out LambdaExpr lambda) {
    lambda = arg as LambdaExpr;
    return lambda != null;
  }

  private static bool ExtractLambdaArg(
    Expression arg,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out LambdaExpr lambda) {
    if (ExtractLambdaArg(arg, out lambda)) {
      return true;
    }

    var simplified = simplifyExpression(arg, state);
    return simplified != null && ExtractLambdaArg(simplified, out lambda);
  }

  private Expression CreateIntResult(IOrigin origin, BigInteger value) {
    return PartialEvaluatorEngine.CreateIntLiteral(origin, value);
  }

  private static Expression CreateBoolResult(IOrigin origin, bool value) {
    return Expression.CreateBoolLiteral(origin, value);
  }

  private Expression CreateSeqResult(IOrigin origin, List<Expression> elements, Type type) {
    return PartialEvaluatorEngine.CreateSeqDisplayLiteral(origin, elements, type);
  }

  private Expression CreateCharResult(IOrigin origin, string value, Type type) {
    return PartialEvaluatorEngine.CreateCharLiteral(origin, value, type);
  }

  private Expression CreateStringResult(IOrigin origin, string value, Type type, bool isVerbatim) {
    return PartialEvaluatorEngine.CreateStringLiteral(origin, value, type, isVerbatim);
  }

  private static bool TryBuildHandlerKey(Function function, out string key) {
    key = null;
    if (function == null) {
      return false;
    }

    var enclosingClass = function.EnclosingClass;
    if (enclosingClass == null) {
      return false;
    }

    var enclosingModule = enclosingClass.EnclosingModuleDefinition;
    if (enclosingModule == null) {
      return false;
    }

    if (enclosingClass is DefaultClassDecl) {
      key = $"{enclosingModule.FullDafnyName}::{function.Name}";
      return true;
    }

    key = function.FullDafnyName;
    return true;
  }

  private static bool AreLiteralExpressionsEqual(Expression left, Expression right) {
    if (AreLiteralExpressionsEqualMethod == null) {
      return false;
    }

    var result = AreLiteralExpressionsEqualMethod.Invoke(null, new object[] { left, right });
    return result is bool areEqual && areEqual;
  }

  private static bool TryBuildLiteralMultisetCounts(IEnumerable<Expression> elements, out Dictionary<Expression, int> counts) {
    counts = null;
    if (BuildMultisetCountsDictMethod == null) {
      return false;
    }

    var result = BuildMultisetCountsDictMethod.Invoke(null, new object[] { elements });
    counts = result as Dictionary<Expression, int>;
    return counts != null;
  }

  private static bool AreAllElementsLiteralComparable(IReadOnlyList<Expression> elements) {
    foreach (var element in elements) {
      if (!AreLiteralExpressionsEqual(element, element)) {
        return false;
      }
    }

    return true;
  }

  private static bool TryGetTupleLiteral(Expression expr, out DatatypeValue tuple) {
    tuple = expr as DatatypeValue;
    if (tuple == null) {
      return false;
    }

    if (tuple.Ctor?.EnclosingDatatype is TupleTypeDecl) {
      return true;
    }

    return tuple.MemberName.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix, StringComparison.Ordinal);
  }

  private static bool IsLiteralLike(Expression expr) {
    if (expr is LiteralExpr) {
      return true;
    }

    if (expr is SeqDisplayExpr seqDisplay) {
      foreach (var element in seqDisplay.Elements) {
        if (!IsLiteralLike(element)) {
          return false;
        }
      }

      return true;
    }

    if (expr is SetDisplayExpr setDisplay) {
      foreach (var element in setDisplay.Elements) {
        if (!IsLiteralLike(element)) {
          return false;
        }
      }

      return true;
    }

    if (expr is MultiSetDisplayExpr multiSetDisplay) {
      foreach (var element in multiSetDisplay.Elements) {
        if (!IsLiteralLike(element)) {
          return false;
        }
      }

      return true;
    }

    if (expr is MapDisplayExpr mapDisplay) {
      foreach (var entry in mapDisplay.Elements) {
        if (!IsLiteralLike(entry.A) || !IsLiteralLike(entry.B)) {
          return false;
        }
      }

      return true;
    }

    if (TryGetTupleLiteral(expr, out var tuple)) {
      foreach (var arg in tuple.Arguments) {
        if (!IsLiteralLike(arg)) {
          return false;
        }
      }

      return true;
    }

    return false;
  }

  private static bool IsInlineableArgument(Expression expr) {
    return IsLiteralLike(expr) || expr is LambdaExpr;
  }

  private static bool AreAllInterpreterInlineableArguments(IEnumerable<Expression> args) {
    foreach (var arg in args) {
      if (IsInterpreterInlineableArgument(arg)) {
        continue;
      }
      return false;
    }
    return true;
  }

  private static bool IsInterpreterInlineableArgument(Expression arg) {
    if (arg == null) {
      return false;
    }
    if (IsLiteralLike(arg) || arg is LambdaExpr) {
      return true;
    }
    if (arg is SeqDisplayExpr seqDisplay) {
      return AreCollectionElementsInterpreterInlineable(seqDisplay.Elements);
    }
    if (arg is SetDisplayExpr setDisplay) {
      return AreCollectionElementsInterpreterInlineable(setDisplay.Elements);
    }
    if (arg is MultiSetDisplayExpr multiSetDisplay) {
      return AreCollectionElementsInterpreterInlineable(multiSetDisplay.Elements);
    }
    if (arg is MapDisplayExpr mapDisplay) {
      foreach (var pair in mapDisplay.Elements) {
        if (!IsInterpreterInlineableArgument(pair.A) || !IsInterpreterInlineableArgument(pair.B)) {
          return false;
        }
      }
      return true;
    }
    if (TryGetTupleLiteral(arg, out var tuple)) {
      return AreCollectionElementsInterpreterInlineable(tuple.Arguments);
    }
    if (arg is ParensExpression parens) {
      return IsInterpreterInlineableArgument(parens.E);
    }
    if (arg is NegationExpression negationExpression) {
      return IsInterpreterInlineableArgument(negationExpression.E);
    }
    if (arg is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Negate } unaryNegate) {
      return IsInterpreterInlineableArgument(unaryNegate.E);
    }
    if (arg is ConversionExpr conversionExpr) {
      return IsInterpreterInlineableArgument(conversionExpr.E);
    }
    return false;
  }

  private static bool AreCollectionElementsInterpreterInlineable(IEnumerable<Expression> elements) {
    foreach (var element in elements) {
      if (!IsInterpreterInlineableArgument(element)) {
        return false;
      }
    }
    return true;
  }

  private bool TryEvaluateLambda(
    LambdaExpr lambda,
    IReadOnlyList<Expression> args,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression result) {
    result = null;
    if (lambda == null || lambda.Range != null || lambda.BoundVars.Count != args.Count) {
      return false;
    }

    foreach (var arg in args) {
      if (!IsInlineableArgument(arg)) {
        return false;
      }
    }

    var substMap = new Dictionary<IVariable, Expression>(lambda.BoundVars.Count);
    for (var i = 0; i < lambda.BoundVars.Count; i++) {
      substMap[lambda.BoundVars[i]] = args[i];
    }

    var substituter = new Substituter(null, substMap, null, null, systemModuleManager);
    var substituted = substituter.Substitute(lambda.Body);
    result = simplifyExpression(substituted, state);
    return result != null;
  }

  private bool TryExtractComparableLiteral(
    Expression arg,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression comparableLiteral) {
    comparableLiteral = simplifyExpression(arg, state) ?? arg;
    return AreLiteralExpressionsEqual(comparableLiteral, comparableLiteral);
  }

  private bool TryInterpretAbs(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var x)) {
      return false;
    }

    interpreted = CreateIntResult(callExpr.Origin, BigInteger.Abs(x));
    return true;
  }

  private bool TryInterpretMin(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 2 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var a) || !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var b)) {
      return false;
    }

    interpreted = CreateIntResult(callExpr.Origin, a <= b ? a : b);
    return true;
  }

  private bool TryInterpretMax(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 2 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var a) || !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var b)) {
      return false;
    }

    interpreted = CreateIntResult(callExpr.Origin, a >= b ? a : b);
    return true;
  }

  private bool TryInterpretSum(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractSeqArg(callExpr.Args[0], out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var sum = BigInteger.Zero;
    foreach (var element in sequence.Elements) {
      if (!ExtractIntArg(element, simplifyExpression, state, out var value)) {
        return false;
      }

      sum += value;
    }

    interpreted = CreateIntResult(callExpr.Origin, sum);
    return true;
  }

  private bool TryInterpretProduct(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractSeqArg(callExpr.Args[0], out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var product = BigInteger.One;
    foreach (var element in sequence.Elements) {
      if (!ExtractIntArg(element, simplifyExpression, state, out var value)) {
        return false;
      }

      product *= value;
    }

    interpreted = CreateIntResult(callExpr.Origin, product);
    return true;
  }

  private bool TryInterpretPower(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 2 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var baseValue) || !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var exp)) {
      return false;
    }

    if (exp <= 0) {
      interpreted = CreateIntResult(callExpr.Origin, BigInteger.One);
      return true;
    }

    if (exp > MaxRecursionDepth) {
      return false;
    }

    var power = BigInteger.One;
    for (var i = BigInteger.Zero; i < exp; i++) {
      power *= baseValue;
    }

    interpreted = CreateIntResult(callExpr.Origin, power);
    return true;
  }

  private bool TryInterpretFactorial(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    if (n <= 0) {
      interpreted = CreateIntResult(callExpr.Origin, BigInteger.One);
      return true;
    }

    if (n > MaxRecursionDepth) {
      return false;
    }

    var factorial = BigInteger.One;
    for (var i = BigInteger.One; i <= n; i++) {
      factorial *= i;
    }

    interpreted = CreateIntResult(callExpr.Origin, factorial);
    return true;
  }

  private bool TryInterpretGcd(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 2 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var a) || !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var b)) {
      return false;
    }

    var depth = 0;
    while (b != 0) {
      if (depth >= MaxRecursionDepth) {
        return false;
      }

      var remainder = ComputeDafnyModulo(a, b);
      a = b;
      b = remainder;
      depth++;
    }

    interpreted = CreateIntResult(callExpr.Origin, BigInteger.Abs(a));
    return true;
  }

  private bool TryInterpretLcm(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 2 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var a) || !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var b)) {
      return false;
    }

    if (a == 0 || b == 0) {
      interpreted = CreateIntResult(callExpr.Origin, BigInteger.Zero);
      return true;
    }

    if (!TryComputeGcd(a, b, out var gcd)) {
      return false;
    }

    var lcm = BigInteger.Abs(a * b) / gcd;
    interpreted = CreateIntResult(callExpr.Origin, lcm);
    return true;
  }

  private bool TryInterpretIsPrime(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    if (n < 2) {
      interpreted = CreateBoolResult(callExpr.Origin, false);
      return true;
    }

    if (n > MaxCollectionSize + 1) {
      return false;
    }

    for (var d = new BigInteger(2); d < n; d++) {
      if (ComputeDafnyModulo(n, d) == 0) {
        interpreted = CreateBoolResult(callExpr.Origin, false);
        return true;
      }
    }

    interpreted = CreateBoolResult(callExpr.Origin, true);
    return true;
  }

  private bool TryInterpretDivisorCount(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    if (n <= 0) {
      interpreted = CreateIntResult(callExpr.Origin, BigInteger.Zero);
      return true;
    }

    if (n > MaxCollectionSize) {
      return false;
    }

    var count = BigInteger.Zero;
    for (var d = BigInteger.One; d <= n; d++) {
      if (ComputeDafnyModulo(n, d) == 0) {
        count++;
      }
    }

    interpreted = CreateIntResult(callExpr.Origin, count);
    return true;
  }

  private bool TryInterpretRange(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var lo) ||
        !ExtractIntArg(callExpr.Args[1], simplifyExpression, state, out var hi)) {
      return false;
    }

    if (lo >= hi) {
      interpreted = CreateSeqResult(callExpr.Origin, [], callExpr.Type);
      return true;
    }

    var elementCount = hi - lo;
    if (elementCount > MaxCollectionSize) {
      return false;
    }

    var elements = new List<Expression>((int)elementCount);
    for (var value = lo; value < hi; value++) {
      elements.Add(CreateIntResult(callExpr.Origin, value));
    }

    interpreted = CreateSeqResult(callExpr.Origin, elements, callExpr.Type);
    return true;
  }

  private bool TryInterpretPrefixSum(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 1 || !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count >= MaxCollectionSize) {
      return false;
    }

    var prefix = new List<Expression>(sequence.Elements.Count + 1) {
      CreateIntResult(callExpr.Origin, BigInteger.Zero)
    };
    var runningSum = BigInteger.Zero;
    foreach (var element in sequence.Elements) {
      if (!ExtractIntArg(element, simplifyExpression, state, out var value)) {
        return false;
      }

      runningSum += value;
      prefix.Add(CreateIntResult(callExpr.Origin, runningSum));
    }

    interpreted = CreateSeqResult(callExpr.Origin, prefix, callExpr.Type);
    return true;
  }

  private bool TryInterpretMap(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[1], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var mapped = new List<Expression>(sequence.Elements.Count);
    foreach (var element in sequence.Elements) {
      var args = new List<Expression> { element };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      mapped.Add(value);
    }

    interpreted = CreateSeqResult(callExpr.Origin, mapped, callExpr.Type);
    return true;
  }

  private bool TryInterpretMapIFrom(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 3 ||
        !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var from) ||
        !ExtractSeqArg(callExpr.Args[1], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[2], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var mapped = new List<Expression>(sequence.Elements.Count);
    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, from + index);
      var args = new List<Expression> { indexExpr, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      mapped.Add(value);
    }

    interpreted = CreateSeqResult(callExpr.Origin, mapped, callExpr.Type);
    return true;
  }

  private bool TryInterpretMapI(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[1], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var mapped = new List<Expression>(sequence.Elements.Count);
    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, index);
      var args = new List<Expression> { indexExpr, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      mapped.Add(value);
    }

    interpreted = CreateSeqResult(callExpr.Origin, mapped, callExpr.Type);
    return true;
  }

  private bool TryInterpretFold(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 3 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[2], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var accumulator = simplifyExpression(callExpr.Args[1], state) ?? callExpr.Args[1];
    if (!IsLiteralLike(accumulator)) {
      return false;
    }

    foreach (var element in sequence.Elements) {
      var args = new List<Expression> { accumulator, element };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      accumulator = value;
    }

    interpreted = accumulator;
    return true;
  }

  private bool TryInterpretFoldIFrom(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 4 ||
        !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var from) ||
        !ExtractSeqArg(callExpr.Args[1], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[3], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var accumulator = simplifyExpression(callExpr.Args[2], state) ?? callExpr.Args[2];
    if (!IsLiteralLike(accumulator)) {
      return false;
    }

    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, from + index);
      var args = new List<Expression> { indexExpr, accumulator, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      accumulator = value;
    }

    interpreted = accumulator;
    return true;
  }

  private bool TryInterpretFoldI(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 3 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[2], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var accumulator = simplifyExpression(callExpr.Args[1], state) ?? callExpr.Args[1];
    if (!IsLiteralLike(accumulator)) {
      return false;
    }

    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, index);
      var args = new List<Expression> { indexExpr, accumulator, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var value) ||
          !IsLiteralLike(value)) {
        return false;
      }

      accumulator = value;
    }

    interpreted = accumulator;
    return true;
  }

  private bool TryInterpretFilter(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[1], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var filtered = new List<Expression>(sequence.Elements.Count);
    foreach (var element in sequence.Elements) {
      var args = new List<Expression> { element };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var predicateResult) ||
          !Expression.IsBoolLiteral(predicateResult, out var keep)) {
        return false;
      }

      if (keep) {
        filtered.Add(element);
      }
    }

    interpreted = CreateSeqResult(callExpr.Origin, filtered, callExpr.Type);
    return true;
  }

  private bool TryInterpretFilterIFrom(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 3 ||
        !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var from) ||
        !ExtractSeqArg(callExpr.Args[1], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[2], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var filtered = new List<Expression>(sequence.Elements.Count);
    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, from + index);
      var args = new List<Expression> { indexExpr, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var predicateResult) ||
          !Expression.IsBoolLiteral(predicateResult, out var keep)) {
        return false;
      }

      if (keep) {
        filtered.Add(sequence.Elements[index]);
      }
    }

    interpreted = CreateSeqResult(callExpr.Origin, filtered, callExpr.Type);
    return true;
  }

  private bool TryInterpretFilterI(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence) ||
        !ExtractLambdaArg(callExpr.Args[1], simplifyExpression, state, out var lambda)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    var filtered = new List<Expression>(sequence.Elements.Count);
    for (var index = 0; index < sequence.Elements.Count; index++) {
      var indexExpr = CreateIntResult(callExpr.Origin, index);
      var args = new List<Expression> { indexExpr, sequence.Elements[index] };
      if (!TryEvaluateLambda(lambda, args, simplifyExpression, state, out var predicateResult) ||
          !Expression.IsBoolLiteral(predicateResult, out var keep)) {
        return false;
      }

      if (keep) {
        filtered.Add(sequence.Elements[index]);
      }
    }

    interpreted = CreateSeqResult(callExpr.Origin, filtered, callExpr.Type);
    return true;
  }

  private bool TryInterpretIsSorted(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 1 || !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    for (var index = 1; index < sequence.Elements.Count; index++) {
      if (!ExtractIntArg(sequence.Elements[index - 1], simplifyExpression, state, out var previous) ||
          !ExtractIntArg(sequence.Elements[index], simplifyExpression, state, out var current)) {
        return false;
      }

      if (previous > current) {
        interpreted = CreateBoolResult(callExpr.Origin, false);
        return true;
      }
    }

    interpreted = CreateBoolResult(callExpr.Origin, true);
    return true;
  }

  private bool TryInterpretIsSortedDesc(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 1 || !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize) {
      return false;
    }

    for (var index = 1; index < sequence.Elements.Count; index++) {
      if (!ExtractIntArg(sequence.Elements[index - 1], simplifyExpression, state, out var previous) ||
          !ExtractIntArg(sequence.Elements[index], simplifyExpression, state, out var current)) {
        return false;
      }

      if (previous < current) {
        interpreted = CreateBoolResult(callExpr.Origin, false);
        return true;
      }
    }

    interpreted = CreateBoolResult(callExpr.Origin, true);
    return true;
  }

  private bool TryInterpretCount(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 || !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var sequence)) {
      return false;
    }

    if (sequence.Elements.Count > MaxCollectionSize ||
        !AreAllElementsLiteralComparable(sequence.Elements) ||
        !TryExtractComparableLiteral(callExpr.Args[1], simplifyExpression, state, out var target)) {
      return false;
    }

    var count = BigInteger.Zero;
    foreach (var element in sequence.Elements) {
      if (AreLiteralExpressionsEqual(element, target)) {
        count++;
      }
    }

    interpreted = CreateIntResult(callExpr.Origin, count);
    return true;
  }

  private bool TryInterpretIsSubsequence(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var subsequence) ||
        !ExtractSeqArg(callExpr.Args[1], simplifyExpression, state, out var mainSequence)) {
      return false;
    }

    if (subsequence.Elements.Count > MaxCollectionSize ||
        mainSequence.Elements.Count > MaxCollectionSize ||
        !AreAllElementsLiteralComparable(subsequence.Elements) ||
        !AreAllElementsLiteralComparable(mainSequence.Elements)) {
      return false;
    }

    var subIndex = 0;
    for (var mainIndex = 0; mainIndex < mainSequence.Elements.Count && subIndex < subsequence.Elements.Count; mainIndex++) {
      if (AreLiteralExpressionsEqual(subsequence.Elements[subIndex], mainSequence.Elements[mainIndex])) {
        subIndex++;
      }
    }

    interpreted = CreateBoolResult(callExpr.Origin, subIndex == subsequence.Elements.Count);
    return true;
  }

  private bool TryInterpretIsPermutation(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    if (callExpr.Args.Count != 2 ||
        !ExtractSeqArg(callExpr.Args[0], simplifyExpression, state, out var leftSequence) ||
        !ExtractSeqArg(callExpr.Args[1], simplifyExpression, state, out var rightSequence)) {
      return false;
    }

    if (leftSequence.Elements.Count > MaxCollectionSize ||
        rightSequence.Elements.Count > MaxCollectionSize ||
        !AreAllElementsLiteralComparable(leftSequence.Elements) ||
        !AreAllElementsLiteralComparable(rightSequence.Elements)) {
      return false;
    }

    if (!TryBuildLiteralMultisetCounts(leftSequence.Elements, out var leftCounts) ||
        !TryBuildLiteralMultisetCounts(rightSequence.Elements, out var rightCounts) ||
        leftCounts.Count != rightCounts.Count) {
      return false;
    }

    foreach (var entry in leftCounts) {
      if (!rightCounts.TryGetValue(entry.Key, out var rightCount) || rightCount != entry.Value) {
        interpreted = CreateBoolResult(callExpr.Origin, false);
        return true;
      }
    }

    interpreted = CreateBoolResult(callExpr.Origin, true);
    return true;
  }

  private bool TryInterpretIsDigit(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    interpreted = CreateBoolResult(callExpr.Origin, c is >= '0' and <= '9');
    return true;
  }

  private bool TryInterpretIsLower(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    interpreted = CreateBoolResult(callExpr.Origin, c is >= 'a' and <= 'z');
    return true;
  }

  private bool TryInterpretIsUpper(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    interpreted = CreateBoolResult(callExpr.Origin, c is >= 'A' and <= 'Z');
    return true;
  }

  private bool TryInterpretIsAlpha(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    var isAlpha = c is >= 'a' and <= 'z' || c is >= 'A' and <= 'Z';
    interpreted = CreateBoolResult(callExpr.Origin, isAlpha);
    return true;
  }

  private bool TryInterpretToLower(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    var lowered = c is >= 'A' and <= 'Z' ? (char)((c - 'A') + 'a') : c;
    interpreted = CreateCharResult(callExpr.Origin, lowered.ToString(), callExpr.Type);
    return true;
  }

  private bool TryInterpretToUpper(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    var uppered = c is >= 'a' and <= 'z' ? (char)((c - 'a') + 'A') : c;
    interpreted = CreateCharResult(callExpr.Origin, uppered.ToString(), callExpr.Type);
    return true;
  }

  private bool TryInterpretCharToNat(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractCharArg(callExpr.Args[0], out var c)) {
      return false;
    }

    interpreted = CreateIntResult(callExpr.Origin, c - '0');
    return true;
  }

  private bool TryInterpretNatToChar(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    var c = n >= 0 && n <= 9 ? (char)((int)n + '0') : '0';
    interpreted = CreateCharResult(callExpr.Origin, c.ToString(), callExpr.Type);
    return true;
  }

  private bool TryInterpretIntToString(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    if (!TryNatToStringValue(n < 0 ? -n : n, out var natString)) {
      return false;
    }

    var value = n < 0 ? "-" + natString : natString;
    interpreted = CreateStringResult(callExpr.Origin, value, callExpr.Type, false);
    return true;
  }

  private bool TryInterpretNatToString(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractIntArg(callExpr.Args[0], simplifyExpression, state, out var n)) {
      return false;
    }

    if (!TryNatToStringValue(n, out var value)) {
      return false;
    }

    interpreted = CreateStringResult(callExpr.Origin, value, callExpr.Type, false);
    return true;
  }

  private bool TryInterpretStringToNat(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractStringArg(callExpr.Args[0], out var value, out _)) {
      return false;
    }

    if (value.Length > MaxRecursionDepth) {
      return false;
    }

    BigInteger total = BigInteger.Zero;
    foreach (var c in value) {
      total = total * 10 + (c - '0');
    }

    interpreted = CreateIntResult(callExpr.Origin, total);
    return true;
  }

  private bool TryInterpretStringToInt(
    FunctionCallExpr callExpr,
    Func<Expression, PartialEvaluatorEngine.PartialEvalState, Expression> simplifyExpression,
    PartialEvaluatorEngine.PartialEvalState state,
    out Expression interpreted) {
    interpreted = null;
    _ = simplifyExpression;
    _ = state;
    if (callExpr.Args.Count != 1 || !ExtractStringArg(callExpr.Args[0], out var value, out _)) {
      return false;
    }

    if (value.Length > MaxRecursionDepth) {
      return false;
    }

    if (value.Length > 0 && value[0] == '-') {
      interpreted = CreateIntResult(callExpr.Origin, -StringToNatValue(value.AsSpan(1)));
      return true;
    }

    interpreted = CreateIntResult(callExpr.Origin, StringToNatValue(value.AsSpan()));
    return true;
  }

  private static bool TryComputeGcd(BigInteger a, BigInteger b, out BigInteger gcd) {
    gcd = BigInteger.Zero;
    var depth = 0;
    while (b != 0) {
      if (depth >= MaxRecursionDepth) {
        return false;
      }

      var remainder = ComputeDafnyModulo(a, b);
      a = b;
      b = remainder;
      depth++;
    }

    gcd = BigInteger.Abs(a);
    return true;
  }

  private static BigInteger ComputeDafnyModulo(BigInteger left, BigInteger right) {
    var divisor = BigInteger.Abs(right);
    var remainder = left % divisor;
    if (remainder < 0) {
      remainder += divisor;
    }

    return remainder;
  }

  private static bool TryNatToStringValue(BigInteger n, out string value) {
    value = null;
    if (n < 10) {
      value = NatToCharValue(n).ToString();
      return true;
    }

    var digits = new List<char>();
    var remaining = n;
    while (remaining >= 10) {
      digits.Add(NatToCharValue(ComputeDafnyModulo(remaining, 10)));
      remaining /= 10;
      if (digits.Count > MaxRecursionDepth) {
        return false;
      }
    }

    digits.Add(NatToCharValue(remaining));
    digits.Reverse();
    value = new string(digits.ToArray());
    return true;
  }

  private static char NatToCharValue(BigInteger n) {
    return n >= 0 && n <= 9 ? (char)((int)n + '0') : '0';
  }

  private static BigInteger StringToNatValue(ReadOnlySpan<char> chars) {
    BigInteger total = BigInteger.Zero;
    foreach (var c in chars) {
      total = total * 10 + (c - '0');
    }

    return total;
  }
}
