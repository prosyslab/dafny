#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace Microsoft.Dafny;

/// <summary>Clones contract expressions while observing a caller-supplied query boundary.</summary>
public sealed class ContractReductionCloner : Cloner {
  private readonly Action? cancellationCheck;

  /// <summary>Creates a contract cloner that checks the query boundary before each recursive clone.</summary>
  public ContractReductionCloner(Action? cancellationCheck, bool cloneResolvedFields = true)
    : base(cloneResolvedFields: cloneResolvedFields) {
    this.cancellationCheck = cancellationCheck;
  }

  public override Expression CloneExpr(Expression expr) {
    cancellationCheck?.Invoke();
    return base.CloneExpr(expr);
  }
}

/// <summary>Substitutes contract expressions while observing a caller-supplied query boundary.</summary>
public sealed class ContractReductionSubstituter : Substituter {
  private readonly Action? cancellationCheck;

  /// <summary>Creates a contract substituter that checks the query boundary before each recursive substitution.</summary>
  public ContractReductionSubstituter(Expression? receiverReplacement,
    Dictionary<IVariable, Expression> substitutionMap, Dictionary<TypeParameter, Type> typeMap,
    Label? oldHeapLabel, SystemModuleManager? systemModuleManager, Action? cancellationCheck)
    : base(receiverReplacement, substitutionMap, typeMap, oldHeapLabel, systemModuleManager) {
    this.cancellationCheck = cancellationCheck;
  }

  public override Expression Substitute(Expression expr) {
    cancellationCheck?.Invoke();
    return base.Substitute(expr);
  }
}

/// <summary>Traverses original logical AST nodes while observing a synchronous query boundary.</summary>
public static class ContractReductionTraversal {
  /// <summary>Prints a proof-key expression while checking native printer traversal and output boundaries.</summary>
  public static string PrintExpression(DafnyOptions options, Expression expression, Action? cancellationCheck = null) {
    cancellationCheck?.Invoke();
    using var writer = new BoundaryStringWriter(cancellationCheck);
    var printer = new Printer(writer, options, PrintModes.Everything, null, cancellationCheck);
    printer.PrintExpression(expression, false);
    var result = writer.ToString();
    cancellationCheck?.Invoke();
    return result;
  }

  private sealed class BoundaryStringWriter(Action? cancellationCheck) : StringWriter {
    public override void Write(char value) {
      cancellationCheck?.Invoke();
      base.Write(value);
      cancellationCheck?.Invoke();
    }

    public override void Write(string? value) {
      cancellationCheck?.Invoke();
      base.Write(value);
      cancellationCheck?.Invoke();
    }

    public override void Write(char[] buffer, int index, int count) {
      cancellationCheck?.Invoke();
      base.Write(buffer, index, count);
      cancellationCheck?.Invoke();
    }

    public override void Write(ReadOnlySpan<char> buffer) {
      cancellationCheck?.Invoke();
      base.Write(buffer);
      cancellationCheck?.Invoke();
    }

    public override void Write(StringBuilder? value) {
      cancellationCheck?.Invoke();
      base.Write(value);
      cancellationCheck?.Invoke();
    }

    public override void WriteLine(string? value) {
      cancellationCheck?.Invoke();
      base.WriteLine(value);
      cancellationCheck?.Invoke();
    }

    public override void WriteLine(ReadOnlySpan<char> buffer) {
      cancellationCheck?.Invoke();
      base.WriteLine(buffer);
      cancellationCheck?.Invoke();
    }

    public override void WriteLine(StringBuilder? value) {
      cancellationCheck?.Invoke();
      base.WriteLine(value);
      cancellationCheck?.Invoke();
    }

    public override void WriteLine() {
      cancellationCheck?.Invoke();
      base.WriteLine();
      cancellationCheck?.Invoke();
    }

    public override string ToString() {
      cancellationCheck?.Invoke();
      return base.ToString();
    }
  }

  /// <summary>Enumerates logical children lazily, excluding a function's compiled by-method body.</summary>
  public static IEnumerable<INode> LogicalNodes(INode root, Action? cancellationCheck = null) {
    var pending = new Stack<INode>();
    var seen = new HashSet<INode>(ReferenceEqualityComparer.Instance);
    pending.Push(root);
    while (pending.TryPop(out var node)) {
      cancellationCheck?.Invoke();
      if (!seen.Add(node)) { continue; }
      yield return node;
      foreach (var child in node.Children) {
        cancellationCheck?.Invoke();
        if (node is Function function && ReferenceEquals(child, function.ByMethodBody)) { continue; }
        pending.Push(child);
      }
    }
  }
}
