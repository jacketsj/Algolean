/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM

/-!
# Disclosed conventions of the sealed ordinary Word RAM

This profile records facts already enforced by `WordRAM.ops`; it does not provide extension
callbacks.  In particular, addresses and values are the same fixed-width words, arithmetic is
modular, comparison is unsigned, and every fetched core instruction has unit cost.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Machine-readable disclosure of the sealed core profile. -/
structure Profile (w : ℕ) where
  width : ℕ := w
  addressBits : ℕ := w
  addressableWords : ℕ := 2 ^ w
  valuesAreWords : Bool := true
  addressesAreWords : Bool := true
  arithmeticModuloTwoPow : Bool := true
  unsignedComparison : Bool := true
  signedComparisonPrimitive : Bool := false
  additionUnitCost : Bool := true
  subtractionUnitCost : Bool := true
  multiplicationUnitCost : Bool := true
  divisionUnitCost : Bool := true
  shiftPrimitive : Bool := false
  bitScanPrimitive : Bool := false
  invalidProgramCounterStuck : Bool := true
  outOfRangeAddressWraps : Bool := true
  layoutLayerForbidsRepresentedWrap : Bool := true
  haltInstructionCounted : Bool := true
  literalsUseFullWordBitsInDescription : Bool := true
  wordLoadedFromMemoryCanAddress : Bool := true
  wordAddressTransferUnitCost : Bool := true
  addressWordMultiplicationUnitCost : Bool := true

/-- The only preferred deterministic ordinary Word-RAM profile. -/
def standardProfile (w : ℕ) : Profile w := {}

/-- Human-readable profile disclosure used by audit tooling. -/
def Profile.summary (profile : Profile w) : String :=
  String.intercalate "\n" [
    "Machine: sealed fixed-width ordinary Word RAM",
    "Word width: " ++ toString profile.width,
    "Address type: BitVec " ++ toString profile.addressBits,
    "Addressable words: 2^" ++ toString profile.addressBits,
    "Arithmetic: unsigned modulo 2^w",
    "Comparison: unsigned three-way comparison",
    "Unit-cost operations: load/store, +, -, *, /, negation, compare",
    "Dynamic addressing: a loaded word transfers to an address register in one step",
    "Address arithmetic: +, -, and word multiplication are unit cost",
    "Unavailable primitives: shifts, bit scans, signed comparison",
    "Invalid program counter: stuck",
    "Raw address arithmetic: wraps; structured layouts prove no wrap",
    "Division: totalized BitVec division",
    "Halt instruction counted: yes",
    "Program literals/addresses: w bits each in description-size accounting",
    "Raw Nat/Int/Rat/Real canonical layout: none"
  ]

end Algolean.Algorithms.WordRAM
