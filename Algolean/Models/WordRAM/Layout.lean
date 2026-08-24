/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM.Costed
public import Algolean.Models.WordRAM.Data.Types

/-!
# Closed canonical layouts for the fixed-width Word RAM

`WordLayout w alpha` is closed indexed syntax.  There is no custom codec, equivalence, arbitrary
enumeration, or value-dependent layout constructor.  Encoding, decoding, footprint, fit,
initialization, and relational output interpretation are fixed recursive library definitions.

Raw `Nat`, `Int`, `Rat`, and `Real` deliberately have no canonical instances.  Native words are
`BitVec w`; bounded and multiword mathematical values use explicitly named wrappers.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- A base address in the `2^w`-word address space. -/
structure Region (w : ℕ) where
  /-- First represented word. -/
  base : BitVec w
deriving DecidableEq

/-- Closed syntax of canonical Word-RAM representations. -/
inductive WordLayout (w : ℕ) : (alpha : Type) → Type 1 where
  | unit : WordLayout w Unit
  | bool : WordLayout w Bool
  | ordering : WordLayout w Ordering
  | word : WordLayout w (BitVec w)
  | fin (n : ℕ) (valuesFit : n ≤ 2 ^ w) : WordLayout w (Fin n)
  | fixedPoint (fracBits : ℕ) : WordLayout w (FixedPoint w fracBits)
  | prod : WordLayout w alpha → WordLayout w beta → WordLayout w (alpha × beta)
  | sum : WordLayout w alpha → WordLayout w beta → WordLayout w (Sum alpha beta)
  | option : WordLayout w alpha → WordLayout w (Option alpha)
  | subtype (predicate : alpha → Prop) : WordLayout w alpha →
      WordLayout w {value : alpha // predicate value}
  | tagged (tag : DataTag) : WordLayout w alpha → WordLayout w (Tagged tag alpha)
  | list : WordLayout w alpha → WordLayout w (List alpha)
  | array : WordLayout w alpha → WordLayout w (Array alpha)
  | vector (length : ℕ) : WordLayout w alpha → WordLayout w (Vector alpha length)
  | finFun (size : ℕ) : WordLayout w alpha → WordLayout w (Fin size → alpha)

namespace WordLayout

/-- Compact kernel-derived syntax rendering for audits. -/
def syntaxName : WordLayout w alpha → String
  | .unit => "unit"
  | .bool => "bool[false=0,true=1]"
  | .ordering => "ordering[lt=0,eq=1,gt=2]"
  | .word => "word(" ++ toString w ++ ")"
  | .fin n _ => "fin(" ++ toString n ++ ")"
  | .fixedPoint fracBits => "fixedPoint(word=" ++ toString w ++
      ", fracBits=" ++ toString fracBits ++ ")"
  | .prod left right => "prod(" ++ left.syntaxName ++ ", " ++ right.syntaxName ++ ")"
  | .sum left right => "sum(tag, " ++ left.syntaxName ++ ", " ++ right.syntaxName ++ ")"
  | .option element => "option(tag, " ++ element.syntaxName ++ ")"
  | .subtype _ base => "subtype(" ++ base.syntaxName ++ ", proof-erased)"
  | .tagged tag base => "tagged(" ++ reprStr tag ++ ", " ++ base.syntaxName ++ ")"
  | .list element => "list(length-prefixed, " ++ element.syntaxName ++ ")"
  | .array element => "array(length-prefixed, " ++ element.syntaxName ++ ")"
  | .vector length element => "vector(" ++ toString length ++ ", " ++
      element.syntaxName ++ ")"
  | .finFun size element => "finFun(index-order, " ++ toString size ++ ", " ++
      element.syntaxName ++ ")"

/-- Syntactic fixed-footprint analysis used by accessors and audits. -/
def fixedFootprint? : WordLayout w alpha → Option Nat
  | .unit => some 0
  | .bool | .ordering | .word | .fin _ _ | .fixedPoint _ => some 1
  | .prod left right => return (← left.fixedFootprint?) + (← right.fixedFootprint?)
  | .sum left right => do
      let leftWords ← left.fixedFootprint?
      let rightWords ← right.fixedFootprint?
      if leftWords = rightWords then some (leftWords + 1) else none
  | .option element => do
      let words ← element.fixedFootprint?
      if words = 0 then some 1 else none
  | .subtype _ base | .tagged _ base => base.fixedFootprint?
  | .list _ | .array _ => none
  | .vector length element =>
      return length * (← element.fixedFootprint?)
  | .finFun length element =>
      return length * (← element.fixedFootprint?)

mutual

/-- Encode a sequence without adding a length header. -/
def encodeList (element : WordLayout w alpha) : List alpha → List (BitVec w)
  | [] => []
  | value :: values => element.encode value ++ encodeList element values

/-- Fixed structural encoder. -/
def encode : (layout : WordLayout w alpha) → alpha → List (BitVec w)
  | .unit, _ => []
  | .bool, value => [if value then 1 else 0]
  | .ordering, .lt => [0]
  | .ordering, .eq => [1]
  | .ordering, .gt => [2]
  | .word, value => [value]
  | .fin _ _, value => [BitVec.ofNat w value]
  | .fixedPoint _, value => [value.bits]
  | .prod left right, value => left.encode value.1 ++ right.encode value.2
  | .sum left _, .inl value => 0 :: left.encode value
  | .sum _ right, .inr value => 1 :: right.encode value
  | .option _, none => [0]
  | .option element, some value => 1 :: element.encode value
  | .subtype _ base, value => base.encode value.1
  | .tagged _ base, .mk value => base.encode value
  | .list element, values => BitVec.ofNat w values.length :: encodeList element values
  | .array element, values => BitVec.ofNat w values.size :: encodeList element values.toList
  | .vector _ element, values => encodeList element values.toArray.toList
  | .finFun _ element, values => encodeList element (List.ofFn values)

end

mutual

/-- Decode exactly `count` sequential values and return the unused suffix. -/
def decodeListPrefix (element : WordLayout w alpha) :
    (count : ℕ) → List (BitVec w) → Option (List alpha × List (BitVec w))
  | 0, words => some ([], words)
  | count + 1, words => do
      let (value, words) ← element.decodePrefix words
      let (values, rest) ← decodeListPrefix element count words
      pure (value :: values, rest)

/-- Fixed prefix decoder.  Noncanonical scalar tags fail. -/
def decodePrefix : (layout : WordLayout w alpha) →
    List (BitVec w) → Option (alpha × List (BitVec w))
  | .unit, words => some ((), words)
  | .bool, headWord :: words =>
      if headWord = 0 then some (false, words)
      else if headWord = 1 then some (true, words) else none
  | .bool, [] => none
  | .ordering, headWord :: words =>
      if headWord = 0 then some (.lt, words)
      else if headWord = 1 then some (.eq, words)
      else if headWord = 2 then some (.gt, words) else none
  | .ordering, [] => none
  | .word, headWord :: words => some (headWord, words)
  | .word, [] => none
  | .fin n _, headWord :: words =>
      if inRange : headWord.toNat < n then some (⟨headWord.toNat, inRange⟩, words) else none
  | .fin _ _, [] => none
  | .fixedPoint fracBits, headWord :: words => some (FixedPoint.ofBits headWord, words)
  | .fixedPoint _, [] => none
  | .prod left right, words => do
      let (leftValue, words) ← left.decodePrefix words
      let (rightValue, rest) ← right.decodePrefix words
      pure ((leftValue, rightValue), rest)
  | .sum left right, headWord :: words =>
      if headWord = 0 then
        (left.decodePrefix words).map fun (value, rest) => (.inl value, rest)
      else if headWord = 1 then
        (right.decodePrefix words).map fun (value, rest) => (.inr value, rest)
      else none
  | .sum _ _, [] => none
  | .option element, headWord :: words =>
      if headWord = 0 then some (none, words)
      else if headWord = 1 then
        (element.decodePrefix words).map fun (value, rest) => (some value, rest)
      else none
  | .option _, [] => none
  | .subtype predicate base, words => do
      let (value, rest) ← base.decodePrefix words
      if property : predicate value then pure (⟨value, property⟩, rest) else none
  | .tagged tag base, words => do
      let (value, rest) ← base.decodePrefix words
      pure (Tagged.mk value, rest)
  | .list element, headWord :: words => do
      let (values, rest) ← decodeListPrefix element headWord.toNat words
      pure (values, rest)
  | .list _, [] => none
  | .array element, headWord :: words => do
      let (values, rest) ← decodeListPrefix element headWord.toNat words
      pure (values.toArray, rest)
  | .array _, [] => none
  | .vector length element, words => do
      let (values, rest) ← decodeListPrefix element length words
      if hasLength : values.length = length then
        pure (⟨values.toArray, by simpa using hasLength⟩, rest)
      else none
  | .finFun size element, words => do
      let (values, rest) ← decodeListPrefix element size words
      if hasLength : values.length = size then
        pure ((fun index => values[index]), rest)
      else none

end

/-- Decode a complete representation, rejecting unused words. -/
def decode (layout : WordLayout w alpha) (words : List (BitVec w)) : Option alpha := do
  let (value, rest) ← layout.decodePrefix words
  if rest.isEmpty then some value else none

/-- Representation footprint in machine words. -/
def footprintWords (layout : WordLayout w alpha) (value : alpha) : ℕ :=
  (layout.encode value).length

/--
Addressability and recursive header safety.  Total footprint alone bounds every scalar header,
while recursive clauses retain the fit facts required by nested length-prefixed values.
-/
def Fits : (layout : WordLayout w alpha) → alpha → Prop
  | .unit, _ => True
  | .bool, _ => True
  | .ordering, _ => True
  | .word, _ => True
  | .fin _ _, _ => True
  | .fixedPoint _, _ => True
  | .prod left right, value => left.Fits value.1 ∧ right.Fits value.2 ∧
      (left.encode value.1 ++ right.encode value.2).length ≤ 2 ^ w
  | .sum left _, .inl value => left.Fits value ∧ (left.encode value).length + 1 ≤ 2 ^ w
  | .sum _ right, .inr value => right.Fits value ∧ (right.encode value).length + 1 ≤ 2 ^ w
  | .option _, none => True
  | .option element, some value =>
      element.Fits value ∧ (element.encode value).length + 1 ≤ 2 ^ w
  | .subtype _ base, value => base.Fits value.1
  | .tagged _ base, .mk value => base.Fits value
  | .list element, values =>
      values.length < 2 ^ w ∧ (∀ value ∈ values, element.Fits value) ∧
        (BitVec.ofNat w values.length :: encodeList element values).length ≤ 2 ^ w
  | .array element, values =>
      values.size < 2 ^ w ∧ (∀ value ∈ values, element.Fits value) ∧
        (BitVec.ofNat w values.size :: encodeList element values.toList).length ≤ 2 ^ w
  | .vector _ element, values =>
      (∀ value ∈ values.toArray, element.Fits value) ∧
        (encodeList element values.toArray.toList).length ≤ 2 ^ w
  | .finFun _ element, values =>
      (∀ index, element.Fits (values index)) ∧
        (encodeList element (List.ofFn values)).length ≤ 2 ^ w

/-- A value fits when placed at a specific base without address wraparound. -/
def FitsAt (layout : WordLayout w alpha) (region : Region w) (value : alpha) : Prop :=
  layout.Fits value ∧ region.base.toNat + layout.footprintWords value ≤ 2 ^ w

/-- Canonical input region begins at word address zero. -/
def inputRegion (w : ℕ) : Region w := ⟨0⟩

/-- A canonical input is addressable from word zero. -/
def FitsInput (layout : WordLayout w alpha) (value : alpha) : Prop :=
  layout.FitsAt (inputRegion w) value

/-- Relational representation in ordinary Word-RAM memory. -/
def RepAt (layout : WordLayout w alpha) (region : Region w)
    (value : alpha) (memory : WordRAM.Memory w) : Prop :=
  layout.FitsAt region value ∧
    ∀ (index : ℕ) (inRange : index < layout.footprintWords value),
      memory.data (BitVec.ofNat w (region.base.toNat + index)) =
        (layout.encode value)[index]

/-- Canonical zero-padded input memory.  The fit proof prevents address wraparound. -/
@[nolint unusedArguments]
def init (layout : WordLayout w alpha) (value : alpha)
    (_fits : layout.FitsInput value) : WordRAM.Memory w :=
  { data := fun address => (layout.encode value).getD address.toNat 0
    address := fun _ => 0 }

/-- Fixed structural overwrite used by typed procedures and relative calls. -/
def writeAt (layout : WordLayout w alpha) (region : Region w) (value : alpha)
    (memory : WordRAM.Memory w) : WordRAM.Memory w :=
  { memory with data := fun address =>
      let offset := address.toNat - region.base.toNat
      if region.base.toNat ≤ address.toNat ∧ offset < layout.footprintWords value then
        (layout.encode value).getD offset 0
      else memory.data address }

/-- Structural overwrite represents the supplied value whenever its region fits. -/
theorem writeAt_rep (layout : WordLayout w alpha) (region : Region w) (value : alpha)
    (memory : WordRAM.Memory w) (fits : layout.FitsAt region value) :
    layout.RepAt region value (layout.writeAt region value memory) := by
  refine ⟨fits, ?_⟩
  intro index inRange
  have addressBelow : region.base.toNat + index < 2 ^ w := by
    exact (Nat.add_lt_add_left inRange region.base.toNat).trans_le fits.2
  simp only [writeAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBelow]
  have baseBelow : region.base.toNat ≤ region.base.toNat + index := Nat.le_add_right _ _
  rw [if_pos ⟨baseBelow, by simpa using inRange⟩]
  rw [Nat.add_sub_cancel_left]
  have encodedRange : index < (layout.encode value).length := by
    simpa [WordLayout.footprintWords] using inRange
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem encodedRange]
  rfl

/-- Structural overwrite preserves cells outside the designated represented interval. -/
theorem writeAt_frame (layout : WordLayout w alpha) (region : Region w) (value : alpha)
    (memory : WordRAM.Memory w) (address : BitVec w)
    (outside : address.toNat < region.base.toNat ∨
      region.base.toNat + layout.footprintWords value ≤ address.toNat) :
    (layout.writeAt region value memory).data address = memory.data address := by
  simp only [writeAt]
  rw [if_neg]
  intro inside
  rcases inside with ⟨baseBelow, offsetBelow⟩
  rcases outside with before | after
  · omega
  · have : address.toNat < region.base.toNat + layout.footprintWords value := by
      omega
    omega

/-- Canonical initialization represents its input at word zero. -/
theorem init_rep (layout : WordLayout w alpha) (value : alpha)
    (fits : layout.FitsInput value) :
    layout.RepAt (inputRegion w) value (layout.init value fits) := by
  refine ⟨fits, ?_⟩
  intro index inRange
  have footprintBelowCapacity : layout.footprintWords value ≤ 2 ^ w := by
    simpa [FitsInput, FitsAt, inputRegion] using fits.2
  have indexBelowCapacity : index < 2 ^ w := by
    exact inRange.trans_le footprintBelowCapacity
  change index < (layout.encode value).length at inRange
  simp only [init, inputRegion]
  have zeroToNat : (0 : BitVec w).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  rw [zeroToNat, Nat.zero_add]
  rw [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt indexBelowCapacity]
  simp [List.getD, inRange]

/-- Every canonical address register starts at zero. -/
@[simp] theorem init_address (layout : WordLayout w alpha) (value : alpha)
    (fits : layout.FitsInput value) (register : ℕ) :
    (layout.init value fits).address register = 0 := rfl

/-- Every word outside the canonical input footprint is definitionally initialized to zero. -/
theorem init_zero_outside (layout : WordLayout w alpha) (value : alpha)
    (fits : layout.FitsInput value) (address : BitVec w)
    (outside : layout.footprintWords value ≤ address.toNat) :
    (layout.init value fits).data address = 0 := by
  apply List.getD_eq_default
  simpa only [WordLayout.footprintWords] using outside

/-- Footprint is definitionally the fixed encoder's output length. -/
theorem footprint_encode (layout : WordLayout w alpha) (value : alpha) :
    layout.footprintWords value = (layout.encode value).length := rfl

/-- Prefix decoding is a left inverse of structural sequence encoding. -/
private theorem decodeListPrefix_encodeList
    (element : WordLayout w alpha)
    (elementRoundTrip : ∀ value, element.Fits value → ∀ suffix,
      element.decodePrefix (element.encode value ++ suffix) = some (value, suffix))
    (values : List alpha) (valuesFit : ∀ value ∈ values, element.Fits value)
    (suffix : List (BitVec w)) :
    decodeListPrefix element values.length (encodeList element values ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => simp [encodeList, decodeListPrefix]
  | cons value values ih =>
      have valueFit := valuesFit value (by simp)
      have tailFit : ∀ item ∈ values, element.Fits item := by
        intro item member
        exact valuesFit item (by simp [member])
      simp [encodeList, decodeListPrefix, elementRoundTrip value valueFit,
        ih tailFit]

private theorem tagCapacity (widthAtLeastTwo : 2 ≤ w) : 3 < 2 ^ w := by
  have powerMonotone : 2 ^ 2 ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by decide) widthAtLeastTwo
  norm_num at powerMonotone ⊢
  omega

private theorem wordTag_ne (widthAtLeastTwo : 2 ≤ w) {left right : ℕ}
    (leftSmall : left < 3) (rightSmall : right < 3) (different : left ≠ right) :
    (BitVec.ofNat w left) ≠ BitVec.ofNat w right := by
  intro equal
  have equalNat := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at equalNat
  rw [Nat.mod_eq_of_lt (leftSmall.trans (tagCapacity widthAtLeastTwo)),
    Nat.mod_eq_of_lt (rightSmall.trans (tagCapacity widthAtLeastTwo))] at equalNat
  exact different equalNat

/-- Structural decoding is a left inverse of structural encoding. -/
theorem decodePrefix_encode (layout : WordLayout w alpha) (value : alpha)
    (suffix : List (BitVec w)) (widthAtLeastTwo : 2 ≤ w) (fits : layout.Fits value) :
    layout.decodePrefix (layout.encode value ++ suffix) = some (value, suffix) := by
  induction layout generalizing suffix with
  | unit => simp [encode, decodePrefix]
  | bool =>
      have widthNeZero : w ≠ 0 := by omega
      cases value
      · simp [encode, decodePrefix]
      · simp [encode, decodePrefix, widthNeZero]
  | ordering =>
      have widthNeZero : w ≠ 0 := by omega
      have widthNeOne : w ≠ 1 := by omega
      have twoNeZero : (2 : BitVec w) ≠ 0 :=
        wordTag_ne (w := w) widthAtLeastTwo (left := 2) (right := 0)
          (by omega) (by omega) (by omega)
      have twoNeOne : (2 : BitVec w) ≠ 1 :=
        wordTag_ne (w := w) widthAtLeastTwo (left := 2) (right := 1)
          (by omega) (by omega) (by omega)
      cases value with
      | lt => simp [encode, decodePrefix]
      | eq => simp [encode, decodePrefix, widthNeZero]
      | gt =>
          simp only [encode, decodePrefix, List.cons_append]
          rw [if_neg twoNeZero, if_neg twoNeOne]
          simp
  | word => simp [encode, decodePrefix]
  | fin n valuesFit =>
      have belowCapacity : value.val < 2 ^ w := value.isLt.trans_le valuesFit
      simp only [encode, decodePrefix, List.cons_append]
      rw [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt belowCapacity]
      simp [value.isLt, Fin.eta]
  | fixedPoint fracBits =>
      cases value with
      | mk bits => simp [encode, decodePrefix, FixedPoint.bits, FixedPoint.ofBits]
  | prod left right leftIH rightIH =>
      rcases value with ⟨leftValue, rightValue⟩
      rcases fits with ⟨leftFit, rightFit, totalFit⟩
      rw [encode, List.append_assoc, decodePrefix]
      rw [leftIH leftValue (right.encode rightValue ++ suffix) leftFit]
      simp [rightIH rightValue suffix rightFit]
  | sum left right leftIH rightIH =>
      cases value with
      | inl value =>
          have valueFit := fits.1
          simp [encode, decodePrefix, leftIH value suffix valueFit]
      | inr value =>
          have valueFit := fits.1
          have widthNeZero : w ≠ 0 := by omega
          simp [encode, decodePrefix, widthNeZero,
            rightIH value suffix valueFit]
  | option element ih =>
      cases value with
      | none => simp [encode, decodePrefix]
      | some value =>
          have widthNeZero : w ≠ 0 := by omega
          simp [encode, decodePrefix, widthNeZero,
            ih value suffix fits.1]
  | subtype predicate base ih =>
      rcases value with ⟨value, property⟩
      simp [encode, decodePrefix, ih value suffix fits, property]
  | tagged tag base ih =>
      rcases value with ⟨value⟩
      simp [encode, decodePrefix, ih value suffix fits]
  | list element ih =>
      rcases fits with ⟨lengthFit, elementsFit, totalFit⟩
      have lengthRoundTrip : value.length % 2 ^ w = value.length :=
        Nat.mod_eq_of_lt lengthFit
      simp [encode, decodePrefix,
        lengthRoundTrip,
        decodeListPrefix_encodeList element
          (fun item itemFit rest => ih item rest itemFit)
          value elementsFit suffix]
  | array element ih =>
      rcases fits with ⟨lengthFit, elementsFit, totalFit⟩
      have lengthRoundTrip : value.size % 2 ^ w = value.size :=
        Nat.mod_eq_of_lt lengthFit
      have listElementsFit : ∀ item ∈ value.toList, element.Fits item := by
        simpa using elementsFit
      have decoded := decodeListPrefix_encodeList element
        (fun item itemFit rest => ih item rest itemFit)
        value.toList listElementsFit suffix
      have decoded' : decodeListPrefix element value.size
          (encodeList element value.toList ++ suffix) = some (value.toList, suffix) := by
        simpa using decoded
      simp only [encode, decodePrefix, List.cons_append, BitVec.toNat_ofNat,
        lengthRoundTrip, decoded']
      simp
  | vector length element ih =>
      rcases fits with ⟨elementsFit, totalFit⟩
      have listElementsFit : ∀ item ∈ value.toArray.toList, element.Fits item := by
        simpa using elementsFit
      have decoded := decodeListPrefix_encodeList element
        (fun item itemFit rest => ih item rest itemFit)
        value.toArray.toList listElementsFit suffix
      have decoded' : decodeListPrefix element length
          (encodeList element value.toArray.toList ++ suffix) =
          some (value.toArray.toList, suffix) := by
        simpa using decoded
      rw [encode, decodePrefix, decoded']
      simp
  | finFun size element ih =>
      rcases fits with ⟨elementsFit, totalFit⟩
      have listElementsFit : ∀ item ∈ List.ofFn value, element.Fits item := by
        intro item member
        simp only [List.mem_ofFn] at member
        rcases member with ⟨index, rfl⟩
        exact elementsFit index
      have decoded := decodeListPrefix_encodeList element
        (fun item itemFit rest => ih item rest itemFit)
        (List.ofFn value) listElementsFit suffix
      have decoded' : decodeListPrefix element size
          (encodeList element (List.ofFn value) ++ suffix) =
          some (List.ofFn value, suffix) := by
        simpa using decoded
      rw [encode, decodePrefix, decoded']
      simp

/-- Complete structural decoding round trips every canonical encoding. -/
theorem decode_encode (layout : WordLayout w alpha) (value : alpha)
    (widthAtLeastTwo : 2 ≤ w) (fits : layout.Fits value) :
    layout.decode (layout.encode value) = some value := by
  unfold decode
  have prefixRoundTrip := decodePrefix_encode layout value [] widthAtLeastTwo fits
  simp only [List.append_nil] at prefixRoundTrip
  rw [prefixRoundTrip]
  rfl

/-- Canonical structural encodings are injective. -/
theorem encode_injective (layout : WordLayout w alpha) (widthAtLeastTwo : 2 ≤ w)
    {left right : alpha} (leftFits : layout.Fits left) (rightFits : layout.Fits right)
    (equal : layout.encode left = layout.encode right) : left = right := by
  have := congrArg layout.decode equal
  simpa [layout.decode_encode left widthAtLeastTwo leftFits,
    layout.decode_encode right widthAtLeastTwo rightFits] using this

/--
Same-region representations with the same footprint are functional.  Fixed-footprint layouts
discharge the footprint premise from their stride certificate; variable-footprint layouts expose
the premise explicitly until their length-header uniqueness lemma is used.
-/
theorem RepAt.functional_of_footprint_eq (layout : WordLayout w alpha)
    (widthAtLeastTwo : 2 ≤ w) (region : Region w) {left right : alpha}
    {memory : WordRAM.Memory w}
    (leftRep : layout.RepAt region left memory)
    (rightRep : layout.RepAt region right memory)
    (sameFootprint : layout.footprintWords left = layout.footprintWords right) :
    left = right := by
  have encodingEqual : layout.encode left = layout.encode right := by
    apply List.ext_get
    · exact sameFootprint
    · intro index leftInRange rightInRange
      have leftCell := leftRep.2 index leftInRange
      have rightCell := rightRep.2 index rightInRange
      exact leftCell.symm.trans rightCell
  exact layout.encode_injective widthAtLeastTwo leftRep.1.1 rightRep.1.1 encodingEqual

/--
Canonical representations are functional even when their footprints depend on the represented
value.  The proof first observes that the shorter encoding is a prefix of the longer one in the
shared memory, then uses the self-delimiting structural decoder to rule out a proper prefix.
-/
theorem RepAt.functional (layout : WordLayout w alpha)
    (widthAtLeastTwo : 2 ≤ w) (region : Region w) {left right : alpha}
    {memory : WordRAM.Memory w}
    (leftRep : layout.RepAt region left memory)
    (rightRep : layout.RepAt region right memory) :
    left = right := by
  wlog shorter : layout.footprintWords left ≤ layout.footprintWords right
      generalizing left right
  · exact (this rightRep leftRep (Nat.le_of_not_ge shorter)).symm
  have encodingIsPrefix : layout.encode left <+: layout.encode right := by
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem
    · simp only [List.length_take]
      rw [Nat.min_eq_left]
      simpa only [← layout.footprint_encode] using shorter
    · intro index leftInRange takeInRange
      rw [List.getElem_take]
      have rightInRange : index < layout.footprintWords right :=
        (show index < layout.footprintWords left by simpa [WordLayout.footprintWords] using
          leftInRange).trans_le shorter
      exact (leftRep.2 index (by simpa [WordLayout.footprintWords] using leftInRange)).symm.trans
        (rightRep.2 index rightInRange)
  rcases encodingIsPrefix with ⟨suffix, encodingPrefix⟩
  have leftDecoded := layout.decodePrefix_encode left suffix widthAtLeastTwo leftRep.1.1
  have rightDecoded := layout.decodePrefix_encode right [] widthAtLeastTwo rightRep.1.1
  rw [encodingPrefix] at leftDecoded
  simp only [List.append_nil] at rightDecoded
  rw [rightDecoded] at leftDecoded
  exact (congrArg Prod.fst (Option.some.inj leftDecoded)).symm

end WordLayout

/-- Model-specific canonical-layout selection.  The sole field is closed syntax. -/
class CanonicalLayout (w : ℕ) (alpha : Type) where
  /-- Resolved closed layout term. -/
  layout : WordLayout w alpha

/-- Resolve canonical syntax once during problem construction. -/
abbrev layoutOf (w : ℕ) (alpha : Type) [CanonicalLayout w alpha] : WordLayout w alpha :=
  CanonicalLayout.layout

namespace CanonicalLayout

instance unit : CanonicalLayout w Unit := ⟨.unit⟩
instance bool : CanonicalLayout w Bool := ⟨.bool⟩
instance ordering : CanonicalLayout w Ordering := ⟨.ordering⟩
instance word : CanonicalLayout w (BitVec w) := ⟨.word⟩
instance fin [Fact (n ≤ 2 ^ w)] : CanonicalLayout w (Fin n) := ⟨.fin n Fact.out⟩
instance fixedPoint : CanonicalLayout w (FixedPoint w fracBits) := ⟨.fixedPoint fracBits⟩

instance prod [CanonicalLayout w alpha] [CanonicalLayout w beta] :
    CanonicalLayout w (alpha × beta) := ⟨.prod (layoutOf w alpha) (layoutOf w beta)⟩

instance sum [CanonicalLayout w alpha] [CanonicalLayout w beta] :
    CanonicalLayout w (Sum alpha beta) := ⟨.sum (layoutOf w alpha) (layoutOf w beta)⟩

instance option [CanonicalLayout w alpha] : CanonicalLayout w (Option alpha) :=
  ⟨.option (layoutOf w alpha)⟩

instance subtype (predicate : alpha → Prop) [CanonicalLayout w alpha] :
    CanonicalLayout w {value : alpha // predicate value} :=
  ⟨.subtype predicate (layoutOf w alpha)⟩

instance tagged [CanonicalLayout w alpha] : CanonicalLayout w (Tagged tag alpha) :=
  ⟨.tagged tag (layoutOf w alpha)⟩

instance list [CanonicalLayout w alpha] : CanonicalLayout w (List alpha) :=
  ⟨.list (layoutOf w alpha)⟩

instance array [CanonicalLayout w alpha] : CanonicalLayout w (Array alpha) :=
  ⟨.array (layoutOf w alpha)⟩

instance vector [CanonicalLayout w alpha] : CanonicalLayout w (Vector alpha length) :=
  ⟨.vector length (layoutOf w alpha)⟩

instance finFun [CanonicalLayout w alpha] : CanonicalLayout w (Fin size → alpha) :=
  ⟨.finFun size (layoutOf w alpha)⟩

end CanonicalLayout

/--
A canonical closed layout together with a certified value-independent stride.  Extending
`CanonicalLayout` makes the selected syntax and its stride one coherent typeclass witness.
-/
class FixedFootprint (w : ℕ) (alpha : Type) extends CanonicalLayout w alpha where
  /-- Exact number of represented words. -/
  words : ℕ
  /-- Every value has exactly the advertised footprint. -/
  footprint_eq : ∀ value : alpha, layout.footprintWords value = words

attribute [instance 1100] FixedFootprint.toCanonicalLayout

namespace FixedFootprint

private theorem encodeList_length
    (layout : WordLayout w alpha)
    (words : Nat)
    (fixed : ∀ value : alpha, layout.footprintWords value = words)
    (values : List alpha) :
    (layout.encodeList values).length = values.length * words := by
  induction values with
  | nil => simp [WordLayout.encodeList]
  | cons head tail ih =>
      have headLength : (layout.encode head).length = words := by
        simpa [WordLayout.footprintWords] using fixed head
      simp only [WordLayout.encodeList, List.length_append, ih, headLength,
        List.length_cons, Nat.add_mul, one_mul]
      omega

instance unit : FixedFootprint w Unit where
  layout := .unit
  words := 0
  footprint_eq _ := by simp [WordLayout.footprintWords, WordLayout.encode]

instance bool : FixedFootprint w Bool where
  layout := .bool
  words := 1
  footprint_eq value := by
    cases value <;> simp [WordLayout.footprintWords, WordLayout.encode]

instance ordering : FixedFootprint w Ordering where
  layout := .ordering
  words := 1
  footprint_eq value := by
    cases value <;> simp [WordLayout.footprintWords, WordLayout.encode]

instance word : FixedFootprint w (BitVec w) where
  layout := .word
  words := 1
  footprint_eq _ := by simp [WordLayout.footprintWords, WordLayout.encode]

instance fin [fit : Fact (n ≤ 2 ^ w)] : FixedFootprint w (Fin n) where
  layout := .fin n fit.out
  words := 1
  footprint_eq _ := by simp [WordLayout.footprintWords, WordLayout.encode]

instance fixedPoint : FixedFootprint w (FixedPoint w fracBits) where
  layout := .fixedPoint fracBits
  words := 1
  footprint_eq _ := by simp [WordLayout.footprintWords, WordLayout.encode]

instance prod [leftFixed : FixedFootprint w alpha] [rightFixed : FixedFootprint w beta] :
    FixedFootprint w (alpha × beta) where
  layout := .prod leftFixed.layout rightFixed.layout
  words := leftFixed.words + rightFixed.words
  footprint_eq value := by
    have leftLength : (leftFixed.layout.encode value.1).length = leftFixed.words := by
      simpa [WordLayout.footprintWords] using leftFixed.footprint_eq value.1
    have rightLength : (rightFixed.layout.encode value.2).length = rightFixed.words := by
      simpa [WordLayout.footprintWords] using rightFixed.footprint_eq value.2
    simp [WordLayout.footprintWords, WordLayout.encode, List.length_append,
      leftLength, rightLength]

instance subtype (predicate : alpha → Prop) [baseFixed : FixedFootprint w alpha] :
    FixedFootprint w {value : alpha // predicate value} where
  layout := .subtype predicate baseFixed.layout
  words := baseFixed.words
  footprint_eq value := by
    simpa [WordLayout.footprintWords, WordLayout.encode] using
      baseFixed.footprint_eq value.1

instance tagged [baseFixed : FixedFootprint w alpha] : FixedFootprint w (Tagged tag alpha) where
  layout := .tagged tag baseFixed.layout
  words := baseFixed.words
  footprint_eq value := by
    rcases value with ⟨value⟩
    simpa [WordLayout.footprintWords, WordLayout.encode] using
      baseFixed.footprint_eq value

instance vector [baseFixed : FixedFootprint w alpha] : FixedFootprint w (Vector alpha length) where
  layout := .vector length baseFixed.layout
  words := length * baseFixed.words
  footprint_eq value := by
    simp only [WordLayout.footprintWords, WordLayout.encode]
    rw [encodeList_length baseFixed.layout baseFixed.words baseFixed.footprint_eq]
    simp

instance finFun [baseFixed : FixedFootprint w alpha] :
    FixedFootprint w (Fin size → alpha) where
  layout := .finFun size baseFixed.layout
  words := size * baseFixed.words
  footprint_eq value := by
    simp only [WordLayout.footprintWords, WordLayout.encode]
    rw [encodeList_length baseFixed.layout baseFixed.words baseFixed.footprint_eq]
    simp

/-- Extract the certified stride.  Absence of an instance prevents fixed-stride access. -/
def stride [FixedFootprint w alpha] : ℕ :=
  FixedFootprint.words (w := w) (alpha := alpha)

end FixedFootprint

end

end Algolean.Algorithms.WordRAM
