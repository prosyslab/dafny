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
  public static readonly Option<bool> NoAttribute = new("--no-attribute", "Remove attributes.") {};
  public static readonly Option<bool> ExplicitEmptyBlock = new("--explicit-empty-block", "Explicitly add {} for empty block.") {};

  static SimplifyOptionBag() {
    OptionRegistry.RegisterOption(NoAttribute, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExplicitEmptyBlock, OptionScope.Cli);
  }
}

