using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny {
  // DoTranslation is synchronous. Keep its names local even when the same AST is translated again.
  // Outside names use their original generators, so publishing assigned-state cannot cause collisions.
  internal sealed class VerificationNamingScope : IDisposable {
    [ThreadStatic] private static VerificationNamingScope current;
    internal static VerificationNamingScope Current => current;

    private readonly VerificationNamingScope previous = current;
    private readonly Dictionary<Declaration, VerificationIdGenerator> generators = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<VerificationIdGenerator, VerificationIdGenerator> legacyGenerators = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<IVariable, string> names = new(ReferenceEqualityComparer.Instance);

    internal VerificationNamingScope() {
      current = this;
    }

    internal VerificationIdGenerator Generator(Declaration declaration, VerificationIdGenerator legacy) {
      if (!generators.TryGetValue(declaration, out var generator)) {
        generator = new VerificationIdGenerator();
        generators.Add(declaration, generator);
        legacyGenerators.Add(generator, legacy);
      }
      return generator;
    }

    internal VerificationIdGenerator LegacyGenerator(VerificationIdGenerator generator) =>
      legacyGenerators.GetValueOrDefault(generator, generator);

    internal string Name(IVariable variable) => names.GetValueOrDefault(variable);

    internal string AssignName(IVariable variable, VerificationIdGenerator generator) {
      if (!names.TryGetValue(variable, out var name)) {
        name = generator.FreshId(variable.Name + "#");
        names.Add(variable, name);
      }
      return name;
    }

    public void Dispose() {
      current = previous;
    }
  }

  public abstract class FreshIdGenerator {
    string tipString;  // a string representation of Tip
    int tipChildrenCount = 0;
    readonly Stack<Dictionary<string, int>> prefixToCountStack = new();  // invariant PrefixToCount_Stack.Count == Tip.Count

    public /*spec public*/ readonly Stack<int> Tip = new();

    public void Push() {
      Tip.Push(tipChildrenCount);
      tipChildrenCount = 0;
      tipString = ComputeTipString();
      prefixToCountStack.Push(new());
    }

    public void Pop() {
      Contract.Requires(Tip.Count > 0);
      int k = Tip.Pop();
      tipChildrenCount = k + 1;
      tipString = ComputeTipString();
      prefixToCountStack.Pop();
    }

    string ComputeTipString() {
      return Tip.Any() ? string.Join('_', Tip.Reverse().Select(t => t.ToString())) : null;
    }

    readonly string commonPrefix = "";

    public FreshIdGenerator() {
      prefixToCountStack.Push(new());
    }

    protected FreshIdGenerator(string commonPrefix) : this() {
      this.commonPrefix = commonPrefix;
    }

    public void Reset() {
      var prefixToCount = prefixToCountStack.Peek();
      lock (prefixToCount) {
        prefixToCount.Clear();
      }
    }

    public string FreshId(string prefix) {
      return commonPrefix + prefix + FreshNumericId(prefix);
    }

    public virtual string FreshNumericId(string prefix = "") {
      var prefixToCount = prefixToCountStack.Peek();
      lock (prefixToCount) {
        if (!prefixToCount.TryGetValue(prefix, out var old)) {
          old = 0;
        }
        prefixToCount[prefix] = old + 1;
        return tipString == null ? old.ToString() : tipString + "_" + old.ToString();
      }
    }

    public override string ToString() {
      throw new InvalidOperationException("Did not expect to convert the fresh Id generator itself to a string");
    }
  }

  public class CodeGenIdGenerator : FreshIdGenerator {
  }

  public class VerificationIdGenerator : FreshIdGenerator {
    public VerificationIdGenerator() {
    }
    public VerificationIdGenerator(string commonPrefix) : base(commonPrefix) {
    }
    public VerificationIdGenerator NestedFreshIdGenerator(string prefix) {
      return new(FreshId(prefix));
    }
  }
}
