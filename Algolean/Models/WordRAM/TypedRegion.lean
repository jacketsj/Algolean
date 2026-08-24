/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.WordRAM.Data.Physical

/-!
# Typed Word-RAM regions and first-order address plans

References retain the concrete closed layout selected at problem construction.  Fixed-stride
indexing requires a `FixedFootprint` witness.  Runtime address calculations are reified as closed
plans and lower to ordinary RAM instructions; they do not execute Lean callbacks on machine data.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- A typed region stores closed layout syntax and a machine base address. -/
structure TypedRegion (w : Nat) (alpha : Type) where
  layout : WordLayout w alpha
  region : Region w

/-- A typed reference into ordinary Word-RAM memory. -/
abbrev Ref (w : Nat) (alpha : Type) := TypedRegion w alpha

/-- Closed paths through structural layouts; no `alpha → beta` projection is accepted. -/
inductive Path (w : Nat) : WordLayout w alpha → WordLayout w beta → Type 1 where
  | prodFst (left : WordLayout w alpha) (right : WordLayout w beta) :
      Path w (.prod left right) left
  | rawProdSnd (left : WordLayout w alpha) (right : WordLayout w beta)
      (leftWords : Nat) : Path w (.prod left right) right
  | subtypeValue (predicate : alpha → Prop) (base : WordLayout w alpha) :
      Path w (.subtype predicate base) base
  | taggedValue (tag : DataTag) (base : WordLayout w alpha) :
      Path w (.tagged tag base) base
  | then (first : Path w source middle) (second : Path w middle target) :
      Path w source target

namespace Ref

def ofCanonical (w : Nat) (alpha : Type) [CanonicalLayout w alpha]
    (base : BitVec w) : Ref w alpha :=
  ⟨layoutOf w alpha, ⟨base⟩⟩

def Rep (reference : Ref w alpha) (value : alpha) (memory : Memory w) : Prop :=
  reference.layout.RepAt reference.region value memory

end Ref

/- Typed product projections.  The right projection requires a fixed left footprint. -/
namespace ProdRef

@[nolint unusedArguments]
def fst (left : WordLayout w alpha) (_right : WordLayout w beta)
    (reference : Ref w (alpha × beta)) : Ref w alpha :=
  ⟨left, reference.region⟩

/-- Unchecked low-level offset arithmetic; use `sndFixed` for a typed semantic projection. -/
@[nolint unusedArguments]
def rawSnd (_left : WordLayout w alpha) (right : WordLayout w beta)
    (leftWords : Nat) (reference : Ref w (alpha × beta)) : Ref w beta :=
  ⟨right, ⟨BitVec.ofNat w (reference.region.base.toNat + leftWords)⟩⟩

/-- Layout-derived right projection; no caller-provided offset is accepted. -/
def sndFixed [fixed : FixedFootprint w alpha] (right : WordLayout w beta)
    (reference : Ref w (alpha × beta)) : Ref w beta :=
  ⟨right, ⟨BitVec.ofNat w (reference.region.base.toNat + fixed.words)⟩⟩

/-- A layout-derived right-field reference represents the actual right component. -/
theorem sndFixed_rep [fixed : FixedFootprint w alpha]
    (right : WordLayout w beta) (region : Region w) (leftValue : alpha) (rightValue : beta)
    (memory : Memory w) (rightNonempty : 0 < right.footprintWords rightValue)
    (represented : (WordLayout.prod fixed.layout right).RepAt region
      (leftValue, rightValue) memory) :
    right.RepAt (sndFixed right ⟨.prod fixed.layout right, region⟩).region
      rightValue memory := by
  rcases represented with ⟨fits, words⟩
  have leftFootprint := fixed.footprint_eq leftValue
  have leftLength : (fixed.layout.encode leftValue).length = fixed.words := by
    simpa [WordLayout.footprintWords] using leftFootprint
  have baseOffsetBelow : region.base.toNat + fixed.words < 2 ^ w := by
    have total := fits.2
    simp only [WordLayout.footprintWords, WordLayout.encode,
      List.length_append] at total
    rw [leftLength] at total
    change 0 < (right.encode rightValue).length at rightNonempty
    omega
  have childBaseToNat :
      (BitVec.ofNat w (region.base.toNat + fixed.words)).toNat =
        region.base.toNat + fixed.words := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact baseOffsetBelow
  refine ⟨?_, ?_⟩
  · refine ⟨fits.1.2.1, ?_⟩
    simp only [sndFixed]
    rw [childBaseToNat]
    have total := fits.2
    simp only [WordLayout.footprintWords, WordLayout.encode,
      List.length_append] at total ⊢
    rw [leftLength] at total
    simpa [Nat.add_assoc] using total
  · intro index inRange
    simp only [sndFixed]
    have parentRange : (fixed.layout.encode leftValue).length + index <
        (WordLayout.prod fixed.layout right).footprintWords (leftValue, rightValue) := by
      simp only [WordLayout.footprintWords, WordLayout.encode, List.length_append]
      simpa [WordLayout.footprintWords] using
        Nat.add_lt_add_left inRange (fixed.layout.encode leftValue).length
    have parentWord := words ((fixed.layout.encode leftValue).length + index) parentRange
    rw [childBaseToNat]
    rw [← leftLength]
    convert parentWord using 1 <;>
      simp [WordLayout.encode, List.getElem_append_right, Nat.add_assoc]
    rfl

end ProdRef

/-- A typed length-prefixed array view. -/
structure ArrayRef (w : Nat) (alpha : Type) where
  elementLayout : WordLayout w alpha
  base : BitVec w

namespace ArrayRef

theorem fixedOffset_lt (index length offset stride : Nat)
    (indexInRange : index < length)
    (offsetInRange : offset < stride) :
    index * stride + offset < length * stride := by
  calc
    index * stride + offset < index * stride + stride :=
      Nat.add_lt_add_left offsetInRange _
    _ = (index + 1) * stride := by simp [Nat.add_mul]
    _ ≤ length * stride :=
      Nat.mul_le_mul_right stride (Nat.succ_le_iff.mpr indexInRange)

theorem encodeList_getElem?_fixed [fixed : FixedFootprint w alpha]
    (values : List alpha) (index : Nat) (indexInRange : index < values.length)
    (offset : Nat) (offsetInRange : offset < fixed.words) :
    (fixed.layout.encodeList values)[index * fixed.words + offset]? =
      some ((fixed.layout.encode values[index])[
        offset]'(by
          have lengthEq : (fixed.layout.encode values[index]).length = fixed.words := by
            simpa [WordLayout.footprintWords] using fixed.footprint_eq values[index]
          simpa [lengthEq] using offsetInRange)) := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => simp at indexInRange
      | cons head tail =>
          have headLength : (fixed.layout.encode head).length = fixed.words := by
            simpa [WordLayout.footprintWords] using fixed.footprint_eq head
          rw [WordLayout.encodeList, List.getElem?_append_left
            (by simpa [headLength] using offsetInRange)]
          simpa only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero] using
            List.getElem?_eq_getElem
              (l := fixed.layout.encode head) (i := offset)
              (by simpa [headLength] using offsetInRange)
  | succ index ih =>
      cases values with
      | nil => simp at indexInRange
      | cons head tail =>
        have headLength : (fixed.layout.encode head).length = fixed.words := by
          simpa [WordLayout.footprintWords] using fixed.footprint_eq head
        have tailRange : index < tail.length := by simpa using indexInRange
        have afterHead : (fixed.layout.encode head).length ≤
            (index + 1) * fixed.words + offset := by
          rw [headLength]
          simp only [Nat.add_mul, one_mul]
          omega
        have shifted : (index + 1) * fixed.words + offset -
            (fixed.layout.encode head).length = index * fixed.words + offset := by
          rw [headLength]
          simp only [Nat.add_mul, one_mul]
          omega
        rw [WordLayout.encodeList, List.getElem?_append_right afterHead, shifted]
        convert ih tail tailRange using 1 <;> simp

/-- The first represented word is the canonical array length header. -/
def lengthAddress (reference : ArrayRef w alpha) : BitVec w := reference.base

/-- Fixed-stride element address.  Variable-footprint arrays deliberately have no such operation. -/
def elementAddress (reference : ArrayRef w alpha) (stride index : Nat) : BitVec w :=
  BitVec.ofNat w (reference.base.toNat + 1 + index * stride)

/-- Unchecked low-level stride arithmetic; use `getFixed` for canonical typed indexing. -/
def getWithStride (reference : ArrayRef w alpha) (stride index : Nat) : Ref w alpha :=
  ⟨reference.elementLayout, ⟨reference.elementAddress stride index⟩⟩

/-- Canonical constant-time indexing is available only from a fixed-footprint witness. -/
@[nolint unusedArguments]
def getFixed [fixed : FixedFootprint w alpha]
    (reference : ArrayRef w alpha) (_layoutMatches : reference.elementLayout = fixed.layout)
    (index : Nat) : Ref w alpha :=
  ⟨fixed.layout, ⟨reference.elementAddress fixed.words index⟩⟩

/-- A layout-derived fixed-stride reference represents exactly the selected array element. -/
theorem getFixed_rep [fixed : FixedFootprint w alpha]
    (reference : ArrayRef w alpha)
    (layoutMatches : reference.elementLayout = fixed.layout)
    (values : Array alpha) (memory : Memory w) (index : Nat)
    (indexInRange : index < values.size) (positiveStride : 0 < fixed.words)
    (represented : (WordLayout.array fixed.layout).RepAt ⟨reference.base⟩ values memory) :
    fixed.layout.RepAt (getFixed reference layoutMatches index).region values[index] memory := by
  rcases represented with ⟨fits, words⟩
  have valueFit : fixed.layout.Fits values[index] :=
    fits.1.2.1 _ (Array.getElem_mem indexInRange)
  have encodedLength : (fixed.layout.encode values[index]).length = fixed.words := by
    simpa [WordLayout.footprintWords] using fixed.footprint_eq values[index]
  have listLength : values.toList.length = values.size := Array.length_toList
  have payloadLength : (fixed.layout.encodeList values.toList).length =
      values.size * fixed.words := by
    rw [FixedFootprint.encodeList_length fixed.layout fixed.words fixed.footprint_eq,
      listLength]
  have blockEnd : (index + 1) * fixed.words ≤ values.size * fixed.words :=
    Nat.mul_le_mul_right fixed.words (Nat.succ_le_iff.mpr indexInRange)
  have childEndBelow : reference.base.toNat + 1 + index * fixed.words + fixed.words ≤
      2 ^ w := by
    have total := fits.2
    simp only [WordLayout.footprintWords, WordLayout.encode, List.length_cons,
      payloadLength] at total
    calc
      reference.base.toNat + 1 + index * fixed.words + fixed.words =
          reference.base.toNat + 1 + (index + 1) * fixed.words := by
        simp [Nat.add_mul, Nat.add_assoc]
      _ ≤ reference.base.toNat + 1 + values.size * fixed.words :=
        Nat.add_le_add_left blockEnd _
      _ ≤ 2 ^ w := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using total
  have rawBaseBelow : reference.base.toNat + 1 + index * fixed.words < 2 ^ w := by
    exact (Nat.lt_add_of_pos_right positiveStride).trans_le childEndBelow
  have childBaseToNat :
      (reference.elementAddress fixed.words index).toNat =
        reference.base.toNat + 1 + index * fixed.words := by
    simp only [elementAddress, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt rawBaseBelow
  refine ⟨⟨valueFit, ?_⟩, ?_⟩
  · simp only [getFixed]
    rw [childBaseToNat, fixed.footprint_eq]
    exact childEndBelow
  · intro offset offsetInRange
    simp only [getFixed]
    rw [childBaseToNat]
    have parentIndexInRange : 1 + index * fixed.words + offset <
        (WordLayout.array fixed.layout).footprintWords values := by
      simp only [WordLayout.footprintWords, WordLayout.encode, List.length_cons,
        payloadLength]
      rw [fixed.footprint_eq] at offsetInRange
      have payloadIndex := fixedOffset_lt index values.size offset fixed.words
        indexInRange offsetInRange
      omega
    have parentWord := words (1 + index * fixed.words + offset) parentIndexInRange
    have listIndexInRange : index < values.toList.length := by simpa using indexInRange
    rw [show reference.base.toNat + 1 + index * fixed.words + offset =
      reference.base.toNat + (1 + index * fixed.words + offset) by omega]
    have parentPayload :
        ((WordLayout.array fixed.layout).encode values)[
            1 + index * fixed.words + offset] =
          (fixed.layout.encode values[index])[offset] := by
      have selected := encodeList_getElem?_fixed values.toList index listIndexInRange offset
        (by
          rw [← fixed.footprint_eq values[index]]
          exact offsetInRange)
      have arrayElement : values.toList[index] = values[index] :=
        Array.getElem_toList indexInRange
      have parentOption :
          ((WordLayout.array fixed.layout).encode values)[
              1 + index * fixed.words + offset]? =
            some ((fixed.layout.encode values[index])[offset]) := by
        rw [show 1 + index * fixed.words + offset =
          (index * fixed.words + offset) + 1 by omega]
        simp only [WordLayout.encode, List.getElem?_cons_succ]
        convert selected using 1 <;> simp [arrayElement]
        rfl
      rcases List.getElem?_eq_some_iff.mp parentOption with ⟨_, equality⟩
      exact equality
    exact parentWord.trans parentPayload

end ArrayRef

/-- A typed row-major runtime matrix view. -/
structure MatrixRef (w : Nat) (alpha : Type) where
  elementLayout : WordLayout w alpha
  base : BitVec w

namespace MatrixRef

/-- Header convention: rows, columns, array length, then row-major payload. -/
def dataBase (reference : MatrixRef w alpha) : Nat := reference.base.toNat + 3

@[nolint unusedArguments]
def elementAddress (reference : MatrixRef w alpha) (stride _rows cols row column : Nat) :
    BitVec w :=
  BitVec.ofNat w (reference.dataBase + (row * cols + column) * stride)

/-- Unchecked low-level shape arithmetic; use `getFixed` for a canonical typed reference. -/
def getWithShape (reference : MatrixRef w alpha)
    (stride rows cols row column : Nat) : Ref w alpha :=
  ⟨reference.elementLayout, ⟨reference.elementAddress stride rows cols row column⟩⟩

/-- Layout-derived row-major element reference for a runtime-shaped dense matrix. -/
@[nolint unusedArguments]
def getFixed [fixed : FixedFootprint w alpha]
    (reference : MatrixRef w alpha) (_layoutMatches : reference.elementLayout = fixed.layout)
    (runtimeCols row column : Nat) : Ref w alpha :=
  ⟨fixed.layout, ⟨reference.elementAddress fixed.words 0 runtimeCols row column⟩⟩

/--
Semantic row-major projection from a canonically represented three-header matrix payload.
`encoding` ties the runtime dimensions and payload to the closed parent layout; no unchecked
shape value can establish this theorem.
-/
theorem getFixed_rep_of_encoding [fixed : FixedFootprint w alpha]
    (parent : WordLayout w matrix) (reference : MatrixRef w alpha)
    (layoutMatches : reference.elementLayout = fixed.layout)
    (value : matrix) (rows cols : Nat) (values : Array alpha)
    (headerRows headerCols headerLength : BitVec w)
    (encoding : parent.encode value =
      headerRows :: headerCols :: headerLength :: fixed.layout.encodeList values.toList)
    (rowsHeader : headerRows.toNat = rows)
    (colsHeader : headerCols.toNat = cols)
    (lengthHeader : headerLength.toNat = values.size)
    (memory : Memory w) (row column : Nat)
    (rowInRange : row < rows) (columnInRange : column < cols)
    (shape : values.size = rows * cols)
    (indexInRange : row * cols + column < values.size)
    (positiveStride : 0 < fixed.words)
    (elementFits : fixed.layout.Fits values[row * cols + column])
    (represented : parent.RepAt ⟨reference.base⟩ value memory) :
    fixed.layout.RepAt
      (getFixed reference layoutMatches cols row column).region
      values[row * cols + column] memory := by
  rcases represented with ⟨parentFits, parentWords⟩
  have derivedIndexInRange : row * cols + column < values.size := by
    have rowHeaderBound : row < headerRows.toNat := by simpa [rowsHeader] using rowInRange
    have columnHeaderBound : column < headerCols.toNat := by
      simpa [colsHeader] using columnInRange
    have inHeaderLength : row * cols + column < headerLength.toNat := by
      rw [lengthHeader, shape]
      calc
        row * cols + column < row * cols + cols := by
          simpa [colsHeader] using Nat.add_lt_add_left columnHeaderBound (row * cols)
        _ = (row + 1) * cols := by simp [Nat.add_mul]
        _ ≤ rows * cols := by
          apply Nat.mul_le_mul_right cols
          exact Nat.succ_le_iff.mpr (by simpa [rowsHeader] using rowHeaderBound)
    simpa [lengthHeader] using inHeaderLength
  have payloadLength : (fixed.layout.encodeList values.toList).length =
      values.size * fixed.words := by
    rw [FixedFootprint.encodeList_length fixed.layout fixed.words fixed.footprint_eq,
      Array.length_toList]
  have blockEnd : (row * cols + column + 1) * fixed.words ≤
      values.size * fixed.words :=
    Nat.mul_le_mul_right fixed.words (Nat.succ_le_iff.mpr derivedIndexInRange)
  have childEndBelow : reference.base.toNat + 3 +
      (row * cols + column) * fixed.words + fixed.words ≤ 2 ^ w := by
    have total := parentFits.2
    simp only [WordLayout.footprintWords, encoding, List.length_cons, payloadLength] at total
    calc
      reference.base.toNat + 3 + (row * cols + column) * fixed.words + fixed.words =
          reference.base.toNat + 3 + (row * cols + column + 1) * fixed.words := by
        simp [Nat.add_mul, Nat.add_assoc]
      _ ≤ reference.base.toNat + 3 + values.size * fixed.words :=
        Nat.add_le_add_left blockEnd _
      _ ≤ 2 ^ w := by omega
  have rawBaseBelow : reference.dataBase +
      (row * cols + column) * fixed.words < 2 ^ w := by
    exact (Nat.lt_add_of_pos_right positiveStride).trans_le childEndBelow
  have childBaseToNat :
      (reference.elementAddress fixed.words 0 cols row column).toNat =
        reference.dataBase + (row * cols + column) * fixed.words := by
    simp only [elementAddress, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt rawBaseBelow
  refine ⟨⟨elementFits, ?_⟩, ?_⟩
  · simp only [getFixed]
    rw [childBaseToNat, fixed.footprint_eq]
    exact childEndBelow
  · intro offset offsetInRange
    simp only [getFixed]
    rw [childBaseToNat]
    have payloadOffset : (row * cols + column) * fixed.words + offset <
        values.size * fixed.words := by
      exact ArrayRef.fixedOffset_lt _ _ _ _ derivedIndexInRange
        (by simpa [fixed.footprint_eq] using offsetInRange)
    have parentIndexInRange : 3 + (row * cols + column) * fixed.words + offset <
        parent.footprintWords value := by
      simp only [WordLayout.footprintWords, encoding, List.length_cons, payloadLength]
      omega
    have parentWord := parentWords
      (3 + (row * cols + column) * fixed.words + offset) parentIndexInRange
    rw [show reference.dataBase + (row * cols + column) * fixed.words + offset =
      reference.base.toNat + (3 + (row * cols + column) * fixed.words + offset) by
        simp [dataBase]; omega]
    have listRange : row * cols + column < values.toList.length := by
      simpa using derivedIndexInRange
    have selected := ArrayRef.encodeList_getElem?_fixed values.toList
      (row * cols + column) listRange offset
      (by simpa [fixed.footprint_eq] using offsetInRange)
    have arrayElement : values.toList[row * cols + column] =
        values[row * cols + column] :=
      Array.getElem_toList derivedIndexInRange
    have encodedOffsetRange : offset <
        (fixed.layout.encode values[row * cols + column]).length := by
      simpa [WordLayout.footprintWords] using offsetInRange
    have parentOption :
        (parent.encode value)[3 + (row * cols + column) * fixed.words + offset]? =
          some ((fixed.layout.encode
            values[row * cols + column])[offset]'encodedOffsetRange) := by
      rw [encoding]
      rw [show 3 + (row * cols + column) * fixed.words + offset =
        (((row * cols + column) * fixed.words + offset + 1) + 1) + 1 by omega]
      simp only [List.getElem?_cons_succ]
      convert selected using 1 <;> simp [arrayElement]
    rcases List.getElem?_eq_some_iff.mp parentOption with ⟨_, equality⟩
    exact parentWord.trans equality

end MatrixRef

/-- Closed address calculations supported by the typed builder. -/
inductive AddressPlan (w : Nat) where
  | constant (address : BitVec w)
  | addConstant (base : BitVec w) (offset : Nat)
  | fixedIndex (base : BitVec w) (headerWords stride : Nat) (indexRegister : Nat)
  | registerFixedIndex (baseRegister headerWords stride indexRegister : Nat)
deriving DecidableEq, Repr

namespace AddressPlan

/-- Unbounded address calculation used to state the absence of modular wraparound. -/
def evalNat (plan : AddressPlan w) (memory : Memory w) : Nat :=
  match plan with
  | .constant address => address.toNat
  | .addConstant base offset => base.toNat + offset
  | .fixedIndex base headerWords stride indexRegister =>
      base.toNat + headerWords + (memory.address indexRegister).toNat * stride
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      (memory.address baseRegister).toNat + headerWords +
        (memory.address indexRegister).toNat * stride

/-- The calculated address is genuinely representable, rather than silently reduced modulo width. -/
def NoWrap (plan : AddressPlan w) (memory : Memory w) : Prop :=
  plan.evalNat memory < 2 ^ w

/-- Syntactic fragment which changes address registers but never the data bank. -/
def AddressOnly : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w) → Prop
  | .setAddress _ _ _ | .addAddress _ _ _ _ | .subAddress _ _ _ _ => True
  | .extra (.valueToAddress _ _) _ | .extra (.mulAddress _ _ _) _ => True
  | _ => False

/-- Mathematical modulo-`2^w` interpretation of a closed plan. -/
def eval (plan : AddressPlan w) (memory : Memory w) : BitVec w :=
  match plan with
  | .constant address => address
  | .addConstant base offset => BitVec.ofNat w (base.toNat + offset)
  | .fixedIndex base headerWords stride indexRegister =>
      BitVec.ofNat w
        (base.toNat + headerWords + (memory.address indexRegister).toNat * stride)
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      BitVec.ofNat w
        ((memory.address baseRegister).toNat + headerWords +
          (memory.address indexRegister).toNat * stride)

/-- Under the explicit fit obligation, the machine word denotes the unbounded address exactly. -/
theorem eval_toNat_eq (plan : AddressPlan w) (memory : Memory w)
    (noWrap : plan.NoWrap memory) :
    (plan.eval memory).toNat = plan.evalNat memory := by
  cases plan with
  | constant => rfl
  | addConstant | fixedIndex | registerFixedIndex =>
      simp only [NoWrap, evalNat] at noWrap
      simp only [eval, evalNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt noWrap

/-- Number of ordinary instructions emitted by the plan. -/
def cost : AddressPlan w → Nat
  | .constant _ => 1
  | .addConstant _ _ => 1
  | .fixedIndex _ _ _ _ => 2
  | .registerFixedIndex _ _ _ _ => 3

def repeatedAdds (indexRegister destination start : Nat) : Nat → Program w
  | 0 => []
  | count + 1 =>
      .addAddress (.reg destination) (.reg indexRegister) destination (start + 1) ::
        repeatedAdds indexRegister destination (start + 1) count

/-- Lower a plan to finite first-order core Word-RAM syntax. -/
def compile (plan : AddressPlan w) (destination start next : Nat) : Program w :=
  match plan with
  | .constant address => [.setAddress (.immediate address) destination next]
  | .addConstant base offset =>
      [.setAddress (.immediate (BitVec.ofNat w (base.toNat + offset))) destination next]
  | .fixedIndex base headerWords stride indexRegister =>
      [.extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
          destination) (start + 1),
        .addAddress (.reg destination)
          (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination next]
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      [.extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
          destination) (start + 1),
        .addAddress (.reg destination) (.reg baseRegister) destination (start + 2),
        .addAddress (.reg destination) (.immediate (BitVec.ofNat w headerWords))
          destination next]

theorem repeatedAdds_length (indexRegister destination start count : Nat) :
    (repeatedAdds (w := w) indexRegister destination start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [repeatedAdds, ih]

/-- Exact emitted instruction count; this is also the unit-cost address-computation charge. -/
theorem compile_length (plan : AddressPlan w) (destination start next : Nat) :
    (plan.compile destination start next).length = plan.cost := by
  cases plan <;> simp [compile, cost]

/-- Every emitted address-plan instruction belongs to the address-only fragment. -/
theorem repeatedAdds_addressOnly (indexRegister destination start count : Nat) :
    ∀ instruction ∈ repeatedAdds (w := w) indexRegister destination start count,
      AddressOnly instruction := by
  induction count generalizing start with
  | zero => simp [repeatedAdds]
  | succ count ih =>
      intro instruction member
      simp only [repeatedAdds, List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (start + 1) instruction member

/-- Every emitted accessor instruction preserves the complete data-memory bank. -/
theorem compile_addressOnly (plan : AddressPlan w) (destination start next : Nat) :
    ∀ instruction ∈ plan.compile destination start next, AddressOnly instruction := by
  cases plan <;> simp [compile, AddressOnly]

/-- Every emitted instruction is fixed first-order syntax and preserves the complete data bank. -/
theorem compile_firstOrder (plan : AddressPlan w) (destination start next : Nat) :
    ∀ instruction ∈ plan.compile destination start next, AddressOnly instruction :=
  plan.compile_addressOnly destination start next

/-- Executing one address-only instruction cannot alter any data cell. -/
theorem AddressOnly.execute_preservesData
    {instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w)}
    (addressOnly : AddressOnly instruction) (memory : Memory w)
    (next : Configuration w)
    (executes : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction memory = .running next) :
    next.memory.data = memory.data := by
  cases instruction with
  | set | add | sub | mul | div | neg | compare | compareAddress | halt =>
      simp [AddressOnly] at addressOnly
  | setAddress | addAddress | subAddress =>
      simp only [RAM.execute] at executes
      cases executes
      rfl
  | extra extra successor =>
      cases extra with
      | valueToAddress source destination =>
          simp only [RAM.execute] at executes
          cases executes
          rfl
      | addressToValue source destination => simp [AddressOnly] at addressOnly
      | mulAddress left right destination =>
          simp only [RAM.execute] at executes
          cases executes
          rfl

/-- Evaluation of a fixed-index plan exposes the exact modulo-word address formula. -/
theorem eval_fixedIndex (base : BitVec w) (headerWords stride indexRegister : Nat)
    (memory : Memory w) :
    (AddressPlan.fixedIndex base headerWords stride indexRegister).eval memory =
      BitVec.ofNat w
        (base.toNat + headerWords + (memory.address indexRegister).toNat * stride) := rfl

/--
Actual same-trace execution of a fixed-stride address accessor.  Both address operations and the
halt are charged, the data bank is preserved, and the destination contains the plan result.
-/
theorem fixedIndex_trace (memory : Memory w) (base : BitVec w)
    (headerWords stride indexRegister destination : Nat) :
    let plan := AddressPlan.fixedIndex base headerWords stride indexRegister
    let program := plan.compile destination 0 2 ++ [.halt (.immediate 0)]
    ∃ final,
      RAM.HaltingTrace (stepCosted program) ⟨0, memory⟩ final 0 3 3 ∧
      final.address destination =
        memory.address indexRegister * BitVec.ofNat w stride +
          BitVec.ofNat w (base.toNat + headerWords) ∧
      final.data = memory.data ∧
      (∀ register, register ≠ destination →
        final.address register = memory.address register) := by
  dsimp [AddressPlan.compile, AddressPlan.eval]
  let scaled := memory.writeAddress destination
    (memory.address indexRegister * BitVec.ofNat w stride)
  let finalMemory := scaled.writeAddress destination
    (memory.address indexRegister * BitVec.ofNat w stride +
      BitVec.ofNat w (base.toNat + headerWords))
  refine ⟨finalMemory, ?_, ?_, rfl, ?_⟩
  · have haltTrace : RAM.HaltingTrace
        (stepCosted [
          .extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
            destination) 1,
          .addAddress (.reg destination)
            (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination 2,
          .halt (.immediate 0)])
        ⟨2, finalMemory⟩ finalMemory 0 1 1 :=
      .halt (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, RAM.execute, RAM.Operand.eval, WordRAM.ops])
    have addTrace : RAM.HaltingTrace
        (stepCosted [
          .extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
            destination) 1,
          .addAddress (.reg destination)
            (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination 2,
          .halt (.immediate 0)])
        ⟨1, scaled⟩ finalMemory 0 2 2 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, RAM.execute, WordRAM.ops, RAM.AddressOperand.eval,
        scaled, finalMemory, RAM.Memory.writeAddress]) haltTrace
    exact .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
      RAM.CostedSemantics.unit, RAM.execute, WordRAM.evalExtra, RAM.AddressOperand.eval,
      scaled, RAM.Memory.writeAddress]) addTrace
  · simp [finalMemory, scaled, RAM.Memory.writeAddress]
  · intro register different
    simp [finalMemory, scaled, RAM.Memory.writeAddress, different]

/--
The trace-level fixed accessor computes the unbounded address exactly under its explicit
no-wrap obligation, preserves every unrelated address register, and preserves all data.
-/
theorem fixedIndex_trace_exact (memory : Memory w) (base : BitVec w)
    (headerWords stride indexRegister destination : Nat)
    (noWrap : (AddressPlan.fixedIndex base headerWords stride indexRegister).NoWrap memory) :
    let plan := AddressPlan.fixedIndex base headerWords stride indexRegister
    let program := plan.compile destination 0 2 ++ [.halt (.immediate 0)]
    ∃ final,
      RAM.HaltingTrace (stepCosted program) ⟨0, memory⟩ final 0 3 3 ∧
      (final.address destination).toNat = plan.evalNat memory ∧
      final.data = memory.data ∧
      (∀ register, register ≠ destination →
        final.address register = memory.address register) := by
  dsimp only
  rcases fixedIndex_trace memory base headerWords stride indexRegister destination with
    ⟨final, trace, destinationValue, dataFrame, registerFrame⟩
  refine ⟨final, trace, ?_, dataFrame, registerFrame⟩
  rw [destinationValue]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    AddressPlan.evalNat]
  have indexBelow : (memory.address indexRegister).toNat < 2 ^ w :=
    BitVec.isLt _
  have stridePartBelow : (memory.address indexRegister).toNat * stride < 2 ^ w := by
    simp only [AddressPlan.NoWrap, AddressPlan.evalNat] at noWrap
    omega
  have basePartBelow : base.toNat + headerWords < 2 ^ w := by
    simp only [AddressPlan.NoWrap, AddressPlan.evalNat] at noWrap
    omega
  have mulMod :
      (memory.address indexRegister).toNat * (stride % 2 ^ w) % 2 ^ w =
        ((memory.address indexRegister).toNat * stride) % 2 ^ w := by
    calc
      (memory.address indexRegister).toNat * (stride % 2 ^ w) % 2 ^ w =
          ((memory.address indexRegister).toNat % 2 ^ w) *
            (stride % 2 ^ w) % 2 ^ w := by rw [Nat.mod_eq_of_lt indexBelow]
      _ = ((memory.address indexRegister).toNat * stride) % 2 ^ w :=
        (Nat.mul_mod _ _ _).symm
  rw [mulMod, ← Nat.add_mod]
  have reorderedBelow :
      (memory.address indexRegister).toNat * stride + (base.toNat + headerWords) <
        2 ^ w := by
    simp only [AddressPlan.NoWrap, AddressPlan.evalNat] at noWrap
    omega
  rw [Nat.mod_eq_of_lt reorderedBelow]
  omega

end AddressPlan

namespace ArrayRef

/--
Runtime fixed-stride indexing joins the structural representation theorem to the actual
three-step machine trace.  The index is read from an address register, the no-wrap premise is
explicit, the resulting address is the canonical child region, and the represented payload is
unchanged.
-/
theorem getFixed_runtime_trace_rep [fixed : FixedFootprint w alpha]
    (reference : ArrayRef w alpha)
    (layoutMatches : reference.elementLayout = fixed.layout)
    (values : Array alpha) (memory : Memory w)
    (index indexRegister destination : Nat)
    (indexValue : (memory.address indexRegister).toNat = index)
    (indexInRange : index < values.size) (positiveStride : 0 < fixed.words)
    (noWrap : (AddressPlan.fixedIndex reference.base 1 fixed.words indexRegister).NoWrap memory)
    (represented : (WordLayout.array fixed.layout).RepAt ⟨reference.base⟩ values memory) :
    ∃ final,
      RAM.HaltingTrace
        (stepCosted
          ((AddressPlan.fixedIndex reference.base 1 fixed.words indexRegister).compile
            destination 0 2 ++ [.halt (.immediate 0)]))
        ⟨0, memory⟩ final 0 3 3 ∧
      final.address destination = (getFixed reference layoutMatches index).region.base ∧
      fixed.layout.RepAt ⟨final.address destination⟩ values[index] final ∧
      final.data = memory.data ∧
      (∀ register, register ≠ destination →
        final.address register = memory.address register) := by
  have childRep := getFixed_rep reference layoutMatches values memory index indexInRange
    positiveStride represented
  rcases AddressPlan.fixedIndex_trace_exact memory reference.base 1 fixed.words
      indexRegister destination noWrap with
    ⟨final, trace, destinationNat, dataFrame, registerFrame⟩
  have rawBelow : reference.base.toNat + 1 + index * fixed.words < 2 ^ w := by
    simpa [AddressPlan.NoWrap, AddressPlan.evalNat, indexValue] using noWrap
  have destinationEq :
      final.address destination = (getFixed reference layoutMatches index).region.base := by
    apply BitVec.eq_of_toNat_eq
    rw [destinationNat]
    simp only [AddressPlan.evalNat, indexValue, getFixed, elementAddress,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt rawBelow]
  have childRepFinal :
      fixed.layout.RepAt (getFixed reference layoutMatches index).region values[index] final := by
    rcases childRep with ⟨fits, words⟩
    refine ⟨fits, ?_⟩
    intro offset offsetInRange
    rw [dataFrame]
    exact words offset offsetInRange
  refine ⟨final, trace, destinationEq, ?_, dataFrame, registerFrame⟩
  rw [destinationEq]
  exact childRepFinal

end ArrayRef

namespace MatrixRef

/--
Runtime row-major indexing, after the caller has computed the linear index in an address
register.  The parent encoding fixes the runtime shape, and the emitted accessor trace reaches
the same canonical element region without modular wraparound.
-/
theorem getFixed_runtime_trace_rep_of_encoding [fixed : FixedFootprint w alpha]
    (parent : WordLayout w matrix) (reference : MatrixRef w alpha)
    (layoutMatches : reference.elementLayout = fixed.layout)
    (value : matrix) (rows cols : Nat) (values : Array alpha)
    (headerRows headerCols headerLength : BitVec w)
    (encoding : parent.encode value =
      headerRows :: headerCols :: headerLength :: fixed.layout.encodeList values.toList)
    (rowsHeader : headerRows.toNat = rows)
    (colsHeader : headerCols.toNat = cols)
    (lengthHeader : headerLength.toNat = values.size)
    (memory : Memory w) (row column linearIndexRegister destination : Nat)
    (linearIndexValue :
      (memory.address linearIndexRegister).toNat = row * cols + column)
    (rowInRange : row < rows) (columnInRange : column < cols)
    (shape : values.size = rows * cols)
    (indexInRange : row * cols + column < values.size)
    (positiveStride : 0 < fixed.words)
    (elementFits : fixed.layout.Fits values[row * cols + column])
    (noWrap :
      (AddressPlan.fixedIndex reference.base 3 fixed.words linearIndexRegister).NoWrap memory)
    (represented : parent.RepAt ⟨reference.base⟩ value memory) :
    ∃ final,
      RAM.HaltingTrace
        (stepCosted
          ((AddressPlan.fixedIndex reference.base 3 fixed.words linearIndexRegister).compile
            destination 0 2 ++ [.halt (.immediate 0)]))
        ⟨0, memory⟩ final 0 3 3 ∧
      final.address destination =
        (getFixed reference layoutMatches cols row column).region.base ∧
      fixed.layout.RepAt ⟨final.address destination⟩
        values[row * cols + column] final ∧
      final.data = memory.data ∧
      (∀ register, register ≠ destination →
        final.address register = memory.address register) := by
  have childRep := getFixed_rep_of_encoding parent reference layoutMatches value rows cols values
    headerRows headerCols headerLength encoding rowsHeader colsHeader lengthHeader memory row column
    rowInRange columnInRange shape indexInRange positiveStride elementFits represented
  rcases AddressPlan.fixedIndex_trace_exact memory reference.base 3 fixed.words
      linearIndexRegister destination noWrap with
    ⟨final, trace, destinationNat, dataFrame, registerFrame⟩
  have rawBelow :
      reference.base.toNat + 3 + (row * cols + column) * fixed.words < 2 ^ w := by
    simpa [AddressPlan.NoWrap, AddressPlan.evalNat, linearIndexValue] using noWrap
  have destinationEq :
      final.address destination =
        (getFixed reference layoutMatches cols row column).region.base := by
    apply BitVec.eq_of_toNat_eq
    rw [destinationNat]
    simp only [AddressPlan.evalNat, linearIndexValue, getFixed, elementAddress, dataBase,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt rawBelow]
  have childRepFinal :
      fixed.layout.RepAt (getFixed reference layoutMatches cols row column).region
        values[row * cols + column] final := by
    rcases childRep with ⟨fits, words⟩
    refine ⟨fits, ?_⟩
    intro offset offsetInRange
    rw [dataFrame]
    exact words offset offsetInRange
  refine ⟨final, trace, destinationEq, ?_, dataFrame, registerFrame⟩
  rw [destinationEq]
  exact childRepFinal

end MatrixRef

/-- A closed accessor bundles its plan, destination register, and exact unit cost. -/
structure CertifiedAccessor (w : Nat) where
  plan : AddressPlan w
  destinationRegister : Nat
  start : Nat
  next : Nat

namespace CertifiedAccessor

def code (accessor : CertifiedAccessor w) : Program w :=
  accessor.plan.compile accessor.destinationRegister accessor.start accessor.next

theorem cost (accessor : CertifiedAccessor w) :
    accessor.code.length = accessor.plan.cost := accessor.plan.compile_length _ _ _

theorem firstOrder (accessor : CertifiedAccessor w) :
    ∀ instruction ∈ accessor.code, AddressPlan.AddressOnly instruction :=
  accessor.plan.compile_firstOrder _ _ _

/-- `_cost`: the exact charge is the number of ordinary emitted instructions. -/
theorem _cost (accessor : CertifiedAccessor w) :
    accessor.code.length = accessor.plan.cost := accessor.cost

/-- `_lowering`: the accessor code is exactly the lowering of its closed address plan. -/
theorem _lowering (accessor : CertifiedAccessor w) :
    accessor.code = accessor.plan.compile accessor.destinationRegister accessor.start
      accessor.next := rfl

/-- `_preservesFrame`: every emitted step preserves all caller-owned data cells. -/
theorem _preservesFrame (accessor : CertifiedAccessor w)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w)}
    (member : instruction ∈ accessor.code) (memory : Memory w) (next : Configuration w)
    (executes : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction memory = .running next) :
    next.memory.data = memory.data :=
  (accessor.plan.compile_addressOnly _ _ _ instruction member).execute_preservesData
    memory next executes

end CertifiedAccessor

/-- Minimal closed program exercising data-dependent random access twice. -/
def indirectLookupProgram (indexAddress pointerBase valueBase : BitVec w)
    (indexRegister pointerAddressRegister pointerRegister valueAddressRegister : Nat) :
    Program w :=
  [.extra (.valueToAddress (.load (.immediate indexAddress)) indexRegister) 1,
    .addAddress (.immediate pointerBase) (.reg indexRegister) pointerAddressRegister 2,
    .extra (.valueToAddress (.load (.reg pointerAddressRegister)) pointerRegister) 3,
    .addAddress (.immediate valueBase) (.reg pointerRegister) valueAddressRegister 4,
    .halt (.load (.reg valueAddressRegister))]

/--
Actual same-trace indirect lookup: the word loaded from the pointer table becomes the address of
the value-table read.  The five fetched instructions are all charged.
-/
theorem indirectLookup_trace (memory : Memory w) (indexAddress pointerBase valueBase : BitVec w)
    (indexRegister pointerAddressRegister pointerRegister valueAddressRegister : Nat) :
    let index := memory.data indexAddress
    let pointerAddress := pointerBase + index
    let pointer := memory.data pointerAddress
    let valueAddress := valueBase + pointer
    ∃ final,
      RAM.HaltingTrace (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
        indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨0, memory⟩ final (memory.data valueAddress) 5 5 ∧
      final.data = memory.data ∧
      final.address valueAddressRegister = valueAddress := by
  dsimp
  let afterIndex := memory.writeAddress indexRegister (memory.data indexAddress)
  let afterPointerAddress := afterIndex.writeAddress pointerAddressRegister
    (pointerBase + memory.data indexAddress)
  let afterPointer := afterPointerAddress.writeAddress pointerRegister
    (memory.data (pointerBase + memory.data indexAddress))
  let finalMemory := afterPointer.writeAddress valueAddressRegister
    (valueBase + memory.data (pointerBase + memory.data indexAddress))
  refine ⟨finalMemory, ?_, rfl, ?_⟩
  · have haltTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨4, finalMemory⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 1 1 :=
      .halt (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops,
        finalMemory, afterPointer, afterPointerAddress, afterIndex, RAM.Memory.writeAddress])
    have valueAddressTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨3, afterPointer⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 2 2 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.ops,
        RAM.AddressOperand.eval, afterPointer, finalMemory,
        afterPointerAddress, afterIndex, RAM.Memory.writeAddress]) haltTrace
    have pointerTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨2, afterPointerAddress⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 3 3 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.evalExtra,
        WordRAM.ops, RAM.Operand.eval, RAM.AddressOperand.eval, afterPointer,
        afterPointerAddress, afterIndex, RAM.Memory.writeAddress]) valueAddressTrace
    have pointerAddressTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨1, afterIndex⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 4 4 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.ops,
        RAM.AddressOperand.eval, afterPointerAddress, afterIndex,
        RAM.Memory.writeAddress]) pointerTrace
    exact .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
      RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.evalExtra,
      WordRAM.ops, RAM.Operand.eval, RAM.AddressOperand.eval, afterIndex,
      RAM.Memory.writeAddress]) pointerAddressTrace
  · simp [finalMemory, afterPointer, afterPointerAddress, afterIndex, RAM.Memory.writeAddress]

/-- Runtime CSR view with explicitly maintained address registers for dynamic subregions. -/
structure CSRGraphRef (w : Nat) (edgeData : Type) where
  dataLayout : WordLayout w edgeData
  graphBaseRegister : Nat
  offsetsBaseRegister : Nat
  destinationsBaseRegister : Nat
  payloadBaseRegister : Nat

namespace CSRGraphRef

def vertexCountPlan (reference : CSRGraphRef w edgeData) : AddressPlan w :=
  .registerFixedIndex reference.graphBaseRegister 0 0 reference.graphBaseRegister

def edgeCountPlan (reference : CSRGraphRef w edgeData) : AddressPlan w :=
  .registerFixedIndex reference.graphBaseRegister 1 0 reference.graphBaseRegister

def neighborStartPlan (reference : CSRGraphRef w edgeData) (vertexRegister : Nat) :
    AddressPlan w :=
  .registerFixedIndex reference.offsetsBaseRegister 1 1 vertexRegister

def neighborEndPlan (reference : CSRGraphRef w edgeData) (vertexPlusOneRegister : Nat) :
    AddressPlan w :=
  .registerFixedIndex reference.offsetsBaseRegister 1 1 vertexPlusOneRegister

def destinationPlan (reference : CSRGraphRef w edgeData) (edgeRegister : Nat) : AddressPlan w :=
  .registerFixedIndex reference.destinationsBaseRegister 1 1 edgeRegister

def dataPlan (reference : CSRGraphRef w edgeData) (stride edgeRegister : Nat) : AddressPlan w :=
  .registerFixedIndex reference.payloadBaseRegister 1 stride edgeRegister

end CSRGraphRef

end Algolean.Algorithms.WordRAM
