namespace DafnyPbtRandom {
  /// <summary>Deterministic generator random stream derived from the command-line seed and ordinal.</summary>
  public sealed class Source {
    private readonly ulong seed;
    private readonly int ordinal;
    private ulong counter;
    public Source() : this(System.Environment.GetCommandLineArgs()) {
    }
    private Source(string[] args) : this(
      ulong.Parse(args[System.Array.IndexOf(args, "--pbt-seed") + 1], System.Globalization.CultureInfo.InvariantCulture),
      int.Parse(args[System.Array.IndexOf(args, "--pbt-ordinal") + 1], System.Globalization.CultureInfo.InvariantCulture)) {
    }
    /// <summary>Creates a reproducible stream for a seed and nonnegative sample ordinal.</summary>
    public Source(ulong seed, int ordinal) {
      if (ordinal < 0) { throw new System.ArgumentOutOfRangeException(nameof(ordinal)); }
      this.seed = seed;
      this.ordinal = ordinal;
    }
    public static Source New() { return new Source(); }
    private byte[] Block() {
      var bytes = new byte[34];
      System.Buffers.Binary.BinaryPrimitives.WriteUInt64BigEndian(new System.Span<byte>(bytes, 0, 8), seed);
      System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian(new System.Span<byte>(bytes, 8, 4), ordinal);
      System.Buffers.Binary.BinaryPrimitives.WriteUInt64BigEndian(new System.Span<byte>(bytes, 12, 8), counter++);
      System.Buffers.Binary.BinaryPrimitives.WriteInt32BigEndian(new System.Span<byte>(bytes, 20, 4), 10);
      System.Text.Encoding.UTF8.GetBytes("pbt-random").CopyTo(bytes, 24);
      return System.Security.Cryptography.SHA256.HashData(bytes);
    }
    private System.Numerics.BigInteger Next(System.Numerics.BigInteger bound) {
      if (bound <= 0) { throw new System.ArgumentOutOfRangeException(nameof(bound)); }
      var bytes = new byte[bound.GetByteCount(isUnsigned: true)];
      for (var offset = 0; offset < bytes.Length; offset += 32) {
        var block = Block();
        System.Array.Copy(block, 0, bytes, offset, System.Math.Min(32, bytes.Length - offset));
      }
      return new System.Numerics.BigInteger(bytes, isUnsigned: true, isBigEndian: true) % bound;
    }
    public System.Numerics.BigInteger Int(System.Numerics.BigInteger lo, System.Numerics.BigInteger hi) { return lo + Next(hi - lo + 1); }
    public System.Numerics.BigInteger Nat(System.Numerics.BigInteger bound) { return Next(bound + 1); }
    public bool Bool() { return Next(2) == 1; }
    public Dafny.Rune Char(Dafny.Rune lo, Dafny.Rune hi) {
      if (lo.Value < 0xD800 && hi.Value >= 0xE000) {
        // Draw a scalar rank, then expand it past the UTF-16 surrogate gap.
        var value = (int)Int(lo.Value, hi.Value - 0x800);
        return new Dafny.Rune(value < 0xD800 ? value : value + 0x800);
      }
      return new Dafny.Rune((int)Int(lo.Value, hi.Value));
    }
    public System.Numerics.BigInteger Index(System.Numerics.BigInteger n) { return Next(n); }
    public System.Numerics.BigInteger Size() { return System.Math.Min(2 + ordinal / 4, 32); }
  }
}
