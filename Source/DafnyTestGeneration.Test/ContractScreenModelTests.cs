using System;
using System.Collections.Generic;
using System.Text.Json;
using DafnyTestGeneration.ContractTesting;
using Xunit;

namespace DafnyTestGeneration.Test;

public class ContractScreenModelTests {
  // Inspect accepts exact immutable sources without a generator, output guess or binding.
  [Fact]
  public void InspectAcceptsBodylessTypedRequest() {
    ContractScreenValidation.Validate(Request());
  }

  // Screen cannot reuse inspect's missing binding or silently screen zero inputs.
  [Fact]
  public void ScreenRequiresBindingAndCases() {
    Assert.Throws<ArgumentException>(() => ContractScreenValidation.Validate(Request() with { Action = ContractScreenAction.Screen }));
  }

  // A supplied source identity must match its actual snapshot bytes.
  [Fact]
  public void SnapshotDigestMismatchIsRejected() {
    Assert.Throws<ArgumentException>(() => ContractScreenValidation.Validate(Request() with {
      Sources = [new("input.dfy", "method Child()", "stale")]
    }));
  }

  // A dependency identity cannot turn an absent source into a trusted axiom source.
  [Fact]
  public void DependencyMustBelongToSnapshot() {
    Assert.Throws<ArgumentException>(() => ContractScreenValidation.Validate(Request() with {
      Dependencies = [new("other.dfy", "digest")]
    }));
  }

  // The separate strict family rejects user-authored assertions rather than forwarding them to native queries.
  [Fact]
  public void UnknownAssertionFieldIsRejected() {
    var json = JsonSerializer.Serialize(Request(), ContractJson.Options);
    Assert.Throws<JsonException>(() => JsonSerializer.Deserialize<ContractScreenRequest>(json[..^1] + ",\"assertion\":\"true\"}", ContractJson.Options));
  }

  // Integer enum encodings cannot bypass the question vocabulary.
  [Fact]
  public void NumericQuestionIsRejected() {
    var json = JsonSerializer.Serialize(Request(), ContractJson.Options).Replace("\"method_realizability\"", "0", StringComparison.Ordinal);
    Assert.Throws<JsonException>(() => JsonSerializer.Deserialize<ContractScreenRequest>(json, ContractJson.Options));
  }

  // Collection cases retain exact typed nested characters through the public JSON transport.
  [Fact]
  public void NestedStringValuesRoundTrip() {
    var value = new ContractValue(ContractValueKind.Sequence, Items: [
      new(ContractValueKind.Sequence, Items: [new(ContractValueKind.Character, "λ")])
    ]);
    var item = new ContractScreenCase("unicode", new Dictionary<string, ContractValue> { ["text"] = value });
    var json = JsonSerializer.Serialize(item, ContractJson.Options);
    var roundTrip = JsonSerializer.Deserialize<ContractScreenCase>(json, ContractJson.Options)!;
    Assert.Equal("λ", roundTrip.Inputs["text"].Items![0].Items![0].Value);
  }

  // Numerically equal map keys cannot evade duplicate rejection using different integer spellings.
  [Fact]
  public void EquivalentNumericMapKeysAreRejected() {
    var value = new ContractValue(ContractValueKind.Map, Entries: [
      new(new(ContractValueKind.Integer, "1"), new(ContractValueKind.Boolean, "true")),
      new(new(ContractValueKind.Integer, "+1"), new(ContractValueKind.Boolean, "false"))
    ]);
    Assert.Throws<ArgumentException>(() => ContractScreenValidation.ValidateConcreteValue(value));
    Assert.Equal("+1", value.Entries![1].Key.Value);
  }

  // Numeric aliases inside a set are checked semantically while the supplied payload stays unchanged.
  [Fact]
  public void EquivalentNumericSetElementsAreRejected() {
    var value = new ContractValue(ContractValueKind.Set, Items: [
      new(ContractValueKind.Integer, "1"), new(ContractValueKind.Integer, "+1")
    ]);
    Assert.Throws<ArgumentException>(() => ContractScreenValidation.ValidateConcreteValue(value));
    Assert.Equal("+1", value.Items![1].Value);
  }

  private static ContractScreenRequest Request() {
    const string source = "method Child(x: int) returns (y: int) ensures y == x";
    return new(1, ContractScreenAction.Inspect, [new("input.dfy", source, ContractHarnessBuilder.Hash(source))],
      new("Child"), [], ContractScreenQuestion.MethodRealizability);
  }
}
