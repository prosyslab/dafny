using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using DafnyCore;
using DafnyCore.Options;
using Serilog.Events;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public class SimplifyOptionBag {
  public static readonly Option<bool> All = new("--all", "Apply all transformations.") {};
  public static readonly Option<bool> NoAttribute = new("--no-attribute", "Remove attributes.") {};
  public static readonly Option<bool> ExplicitEmptyBlock = new("--explicit-empty-block", "Explicitly add {} for empty block.") {};
  public static readonly Option<bool> ExplicitCardinality = new("--explicit-cardinality", "Explicitly add parentheses for cardinality expression.") {};
  public static readonly Option<bool> ExplicitTypeArgs = new("--explicit-type-args", "Explicitly add parentheses for cardinality expression.") {};

  static SimplifyOptionBag() {
    OptionRegistry.RegisterOption(All, OptionScope.Cli);
    OptionRegistry.RegisterOption(NoAttribute, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExplicitEmptyBlock, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExplicitCardinality, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExplicitTypeArgs, OptionScope.Cli);
  }
}

