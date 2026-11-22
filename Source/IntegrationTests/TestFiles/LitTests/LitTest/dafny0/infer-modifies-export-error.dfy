// RUN: %exits-with 2 %verify --cores 1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Hidden {
  export reveals Cell, Holder provides Holder.Set

  class Cell {
    var value: int
  }

  class Holder {
    const privateCell: Cell

    constructor(c: Cell) {
      privateCell := c;
    }

    // The inferred contract must pass the same export check as a source contract.
    method {:inferModifies} Set() {
      privateCell.value := 2;
    }
  }
}
