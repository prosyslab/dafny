#nullable enable

using System;
using System.Collections.Generic;
using System.Numerics;
using Dafny;
using DafnyPbtRandom;
using Xunit;

namespace DafnyTestGeneration.Test;

public class PbtRandomSourceTests {
  // The suggested size grows every four samples and stays within the advertised bounds.
  [Theory]
  [InlineData(0, 2)]
  [InlineData(3, 2)]
  [InlineData(4, 3)]
  [InlineData(119, 31)]
  [InlineData(120, 32)]
  [InlineData(int.MaxValue, 32)]
  public void SizeFollowsTheCappedSchedule(int ordinal, int expected) {
    Assert.Equal(new BigInteger(expected), new Source(1, ordinal).Size());
  }

  // Negative sample ordinals cannot create a stream that violates the size contract.
  [Fact]
  public void NegativeOrdinalIsRejected() {
    Assert.Throws<ArgumentOutOfRangeException>(() => new Source(1, -1));
  }

  // Reading the suggested size leaves all subsequent random draws unchanged.
  [Fact]
  public void SizeDoesNotAdvanceTheStream() {
    var source = new Source(17, 9);
    var control = new Source(17, 9);
    for (var i = 0; i < 16; i++) {
      Assert.Equal(new BigInteger(4), source.Size());
      Assert.Equal(control.Int(-1000, 1000), source.Int(-1000, 1000));
    }
  }

  // The established integer, natural, boolean, index and unaffected character stream stays reproducible.
  [Fact]
  public void ExistingDrawSequenceIsPreserved() {
    var source = new Source(0x0123456789ABCDEF, 7);
    Assert.Equal(new BigInteger(66), source.Int(-100, 100));
    Assert.Equal(new BigInteger(746), source.Nat(1000));
    Assert.True(source.Bool());
    Assert.Equal(new BigInteger(3), source.Index(9));
    Assert.Equal(new Rune(35), source.Char(new Rune(32), new Rune(126)));
  }

  // Every inclusive character range returns scalar values without throwing at the surrogate gap.
  [Theory]
  [InlineData(0, 0x10FFFF)]
  [InlineData(0xD7FF, 0xE000)]
  [InlineData(0xD7FE, 0xE001)]
  [InlineData(0, 0xD7FF)]
  [InlineData(0xE000, 0x10FFFF)]
  [InlineData(0x10FFFF, 0x10FFFF)]
  public void CharacterDrawsStayWithinScalarBounds(int lo, int hi) {
    var source = new Source(1, 0);
    for (var i = 0; i < 256; i++) {
      var value = source.Char(new Rune(lo), new Rune(hi));
      Assert.InRange(value.Value, lo, hi);
      Assert.True(Rune.IsRune(value.Value));
    }
  }

  // The two scalars adjacent to the surrogate gap are both reachable as inclusive endpoints.
  [Fact]
  public void CharacterRangeAcrossTheGapReachesBothEndpoints() {
    var source = new Source(1, 0);
    var seen = new HashSet<int>();
    for (var i = 0; i < 16; i++) {
      seen.Add(source.Char(new Rune(0xD7FF), new Rune(0xE000)).Value);
    }
    Assert.True(seen.SetEquals(new[] { 0xD7FF, 0xE000 }));
  }

  // Character ranges wholly outside the surrogate gap consume exactly the original integer draws.
  [Theory]
  [InlineData(32, 126)]
  [InlineData(0xE000, 0xFFFF)]
  [InlineData(0x10000, 0x10FFFF)]
  public void UnaffectedCharacterRangesPreserveTheStream(int lo, int hi) {
    var source = new Source(23, 4);
    var control = new Source(23, 4);
    for (var i = 0; i < 32; i++) {
      Assert.Equal((int)control.Int(lo, hi), source.Char(new Rune(lo), new Rune(hi)).Value);
    }
    Assert.Equal(control.Bool(), source.Bool());
  }
}
