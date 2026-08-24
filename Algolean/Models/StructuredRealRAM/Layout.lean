/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Core

/-!
# Canonical structured layouts

`Layout` is closed indexed syntax.  Clients can compose only the structural constructors declared
by the inductive type; there is no custom encoder, decoder, map, or equivalence constructor.
Encoding and decoding are fixed interpreters defined by recursion over that syntax.  Thus the
kernel-visible shape of a layout, rather than declaration privacy, rules out input preprocessing.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Base addresses of the real and natural parts of a represented value. -/
structure Region where
  /-- Base address in exact-real memory. -/
  realBase : ℕ
  /-- Base address in natural memory. -/
  natBase : ℕ
deriving DecidableEq

/-- Numbers of real and natural cells occupied by a canonical representation. -/
structure Footprint where
  /-- Number of exact-real cells. -/
  realCells : ℕ
  /-- Number of natural cells, including layout headers. -/
  natCells : ℕ
deriving DecidableEq

namespace Footprint

/-- Total cell count used as the default scalar input size. -/
def total (footprint : Footprint) : ℕ := footprint.realCells + footprint.natCells

end Footprint

namespace Region

/-- Shift a region past a footprint in both banks. -/
def after (region : Region) (footprint : Footprint) : Region :=
  ⟨region.realBase + footprint.realCells, region.natBase + footprint.natCells⟩

end Region

/-- Closed diagnostic tags for named physical structured-data formats. -/
inductive DataTag where
  | realArray | natArray | fixedStrideArray | indexedArray
  | denseMatrix | denseTensor3 | denseTensor4
  | sparseVector | cooMatrix | csrMatrix | dynamicBitSet
  | permutation | labelPartition | parentPartition | parentForest
  | vertexTable | edgeTable | dartTable
  | directedEdgeList | undirectedDartList | csrGraph | adjacencyMatrixGraph
deriving DecidableEq, Repr

/-- Nominal wrapper whose tag is syntax-only and occupies no machine cells. -/
structure Tagged (tag : DataTag) (alpha : Type) where
  value : alpha

/-- The pair of finite streams underlying a canonical representation. -/
@[ext]
structure Encoding where
  /-- Canonical exact-real stream. -/
  reals : List ℝ
  /-- Canonical discrete stream. -/
  nats : List ℕ

/--
Closed syntax for canonical structured memory representations.

In particular, no constructor accepts a function `alpha → Encoding` or an equivalence to another
carrier.  The only function-valued field below is a subtype predicate in `Prop`; proof fields are
erased and the underlying value is represented structurally.
-/
inductive Layout : (alpha : Type) → Type 1 where
  | unit : Layout Unit
  | bool : Layout Bool
  | nat : Layout ℕ
  | int : Layout ℤ
  | rat : Layout ℚ
  | real : Layout ℝ
  | fin (size : ℕ) : Layout (Fin size)
  | bitVec (width : ℕ) : Layout (BitVec width)
  | prod : Layout alpha → Layout beta → Layout (alpha × beta)
  | sum : Layout alpha → Layout beta → Layout (Sum alpha beta)
  | option : Layout alpha → Layout (Option alpha)
  | list : Layout alpha → Layout (List alpha)
  | array : Layout alpha → Layout (Array alpha)
  | vector (length : ℕ) : Layout alpha → Layout (Vector alpha length)
  | finFun (size : ℕ) : Layout alpha → Layout (Fin size → alpha)
  | tagged (tag : DataTag) : Layout alpha → Layout (Tagged tag alpha)
  | realArray : Layout (Tagged .realArray (Array Real))
  | natArray : Layout (Tagged .natArray (Array Nat))
  | subtype (predicate : alpha → Prop) : Layout alpha → Layout {value : alpha // predicate value}

/--
A general round-trip serialization interface.  This is intentionally separate from `Layout` and
is never accepted by the strongest machine-problem APIs: a round-trip law alone does not rule out
arbitrary preprocessing in `encode`.
-/
structure CertifiedCodec (alpha : Type u) where
  /-- Arbitrary client serializer; this is why the type is excluded from strong claims. -/
  encode : alpha → Encoding
  /-- Claimed inverse of the arbitrary serializer. -/
  decode : Encoding → Option alpha
  /-- Round-trip guarantee, which does not prohibit preprocessing. -/
  decode_encode : ∀ value, decode (encode value) = some value

namespace Layout

/-- Compact structural rendering used by typed audit reports. -/
def syntaxName : (layout : Layout alpha) → String
  | .unit => "unit"
  | .bool => "bool"
  | .nat => "nat"
  | .int => "int"
  | .rat => "rat"
  | .real => "real"
  | .fin size => "fin(" ++ toString size ++ ")"
  | .bitVec width => "bitVec(" ++ toString width ++ ")"
  | .prod left right => "prod(" ++ left.syntaxName ++ ", " ++ right.syntaxName ++ ")"
  | .sum left right => "sum(" ++ left.syntaxName ++ ", " ++ right.syntaxName ++ ")"
  | .option element => "option(" ++ element.syntaxName ++ ")"
  | .list element => "list(length-delimited, " ++ element.syntaxName ++ ")"
  | .array element => "array(" ++ element.syntaxName ++ ")"
  | .vector length element => "vector(" ++ toString length ++ ", " ++
      element.syntaxName ++ ")"
  | .finFun size element => "finFun(index-order, " ++ toString size ++ ", " ++
      element.syntaxName ++ ")"
  | .tagged tag base => "tagged(" ++ reprStr tag ++ ", " ++ base.syntaxName ++ ")"
  | .realArray => "compactRealArray(length:nat,payload:real)"
  | .natArray => "compactNatArray(length:nat,payload:nat)"
  | .subtype _ underlying => "subtype(" ++ underlying.syntaxName ++ ", proof-erased)"

/-- Encode a list as length-delimited element chunks. -/
noncomputable def encodeListWith (encodeElement : alpha → Encoding) : List alpha → Encoding
  | [] => ⟨[], []⟩
  | value :: values =>
      let head := encodeElement value
      let tail := encodeListWith encodeElement values
      ⟨head.reals ++ tail.reals,
        head.reals.length :: head.nats.length :: (head.nats ++ tail.nats)⟩

/-- Decode exactly `count` length-delimited element chunks and return the unused streams. -/
noncomputable def decodeListWith (decodeElement : Encoding → Option alpha) :
    ℕ → Encoding → Option (List alpha × Encoding)
  | 0, encoding => some ([], encoding)
  | count + 1, encoding =>
      match encoding.nats with
      | realLength :: natLength :: nats =>
          match decodeElement ⟨encoding.reals.take realLength, nats.take natLength⟩,
            decodeListWith decodeElement count
              ⟨encoding.reals.drop realLength, nats.drop natLength⟩ with
          | some value, some (values, rest) => some (value :: values, rest)
          | _, _ => none
      | _ => none

theorem decodeListWith_encodeListWith (encodeElement : alpha → Encoding)
    (decodeElement : Encoding → Option alpha)
    (roundTrip : ∀ value, decodeElement (encodeElement value) = some value)
    (values : List alpha) :
    decodeListWith decodeElement values.length (encodeListWith encodeElement values) =
      some (values, ⟨[], []⟩) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [encodeListWith, decodeListWith, List.length_cons,
        List.take_left, List.drop_left]
      rw [roundTrip, induction]

/-- Fixed structural encoder, interpreted by recursion over closed `Layout` syntax. -/
noncomputable def encode : (layout : Layout alpha) → alpha → Encoding
  | .unit, _ => ⟨[], []⟩
  | .bool, value => ⟨[], [if value then 1 else 0]⟩
  | .nat, value => ⟨[], [value]⟩
  | .int, .ofNat value => ⟨[], [0, value]⟩
  | .int, .negSucc value => ⟨[], [1, value]⟩
  | .rat, value =>
      match value.num with
      | .ofNat numerator => ⟨[], [0, numerator, value.den]⟩
      | .negSucc numerator => ⟨[], [1, numerator, value.den]⟩
  | .real, value => ⟨[value], []⟩
  | .fin _, value => ⟨[], [value.val]⟩
  | .bitVec _, value => ⟨[], [value.toNat]⟩
  | .prod left right, value =>
      let leftEncoding := encode left value.1
      let rightEncoding := encode right value.2
      ⟨leftEncoding.reals ++ rightEncoding.reals,
        leftEncoding.reals.length :: leftEncoding.nats.length ::
          (leftEncoding.nats ++ rightEncoding.nats)⟩
  | .sum left _, .inl value =>
      let encoding := encode left value
      ⟨encoding.reals, 0 :: encoding.nats⟩
  | .sum _ right, .inr value =>
      let encoding := encode right value
      ⟨encoding.reals, 1 :: encoding.nats⟩
  | .option _, none => ⟨[], [0]⟩
  | .option element, some value =>
      let encoding := encode element value
      ⟨encoding.reals, 1 :: encoding.nats⟩
  | .list element, values =>
      let body := encodeListWith (encode element) values
      ⟨body.reals, values.length :: body.nats⟩
  | .array element, values =>
      let body := encodeListWith (encode element) values.toList
      ⟨body.reals, values.size :: body.nats⟩
  | .vector _ element, values =>
      encodeListWith (encode element) values.toArray.toList
  | .finFun _ element, values =>
      encodeListWith (encode element) (List.ofFn values)
  | .tagged _ base, value => base.encode value.value
  | .realArray, value => ⟨value.value.toList, [value.value.size]⟩
  | .natArray, value => ⟨[], value.value.size :: value.value.toList⟩
  | .subtype _ underlying, value => encode underlying value.1

/-- Fixed structural decoder, interpreted by recursion over closed `Layout` syntax. -/
noncomputable def decode : (layout : Layout alpha) → Encoding → Option alpha
  | .unit, ⟨[], []⟩ => some ()
  | .unit, _ => none
  | .bool, ⟨[], [0]⟩ => some false
  | .bool, ⟨[], [1]⟩ => some true
  | .bool, _ => none
  | .nat, ⟨[], [value]⟩ => some value
  | .nat, _ => none
  | .int, ⟨[], [0, value]⟩ => some (.ofNat value)
  | .int, ⟨[], [1, value]⟩ => some (.negSucc value)
  | .int, _ => none
  | .rat, ⟨[], [sign, magnitude, denominator]⟩ => by
      let numerator : ℤ := if sign = 0 then .ofNat magnitude else .negSucc magnitude
      exact if denominatorZero : denominator = 0 then none
        else some (Rat.normalize numerator denominator denominatorZero)
  | .rat, _ => none
  | .real, ⟨[value], []⟩ => some value
  | .real, _ => none
  | .fin size, ⟨[], [value]⟩ =>
      if inRange : value < size then some ⟨value, inRange⟩ else none
  | .fin _, _ => none
  | .bitVec width, ⟨[], [value]⟩ =>
      if inRange : value < 2 ^ width then some (BitVec.ofNat width value) else none
  | .bitVec _, _ => none
  | .prod left right, encoding =>
      match encoding.nats with
      | realLength :: natLength :: nats =>
          match decode left ⟨encoding.reals.take realLength, nats.take natLength⟩,
            decode right ⟨encoding.reals.drop realLength, nats.drop natLength⟩ with
          | some leftValue, some rightValue => some (leftValue, rightValue)
          | _, _ => none
      | _ => none
  | .sum left _, ⟨reals, 0 :: nats⟩ =>
      (decode left ⟨reals, nats⟩).map Sum.inl
  | .sum _ right, ⟨reals, 1 :: nats⟩ =>
      (decode right ⟨reals, nats⟩).map Sum.inr
  | .sum _ _, _ => none
  | .option _, ⟨[], [0]⟩ => some none
  | .option element, ⟨reals, 1 :: nats⟩ =>
      (decode element ⟨reals, nats⟩).map some
  | .option _, _ => none
  | .list element, encoding =>
      match encoding.nats with
      | count :: nats =>
          match decodeListWith (decode element) count ⟨encoding.reals, nats⟩ with
          | some (values, ⟨[], []⟩) => some values
          | _ => none
      | [] => none
  | .array element, encoding =>
      match encoding.nats with
      | count :: nats =>
          match decodeListWith (decode element) count ⟨encoding.reals, nats⟩ with
          | some (values, ⟨[], []⟩) => some values.toArray
          | _ => none
      | [] => none
  | .vector length element, encoding =>
      match decodeListWith (decode element) length encoding with
      | some (values, ⟨[], []⟩) =>
          if hasLength : values.length = length then
            some ⟨values.toArray, by simpa using hasLength⟩
          else none
      | _ => none
  | .finFun size element, encoding =>
      match decodeListWith (decode element) size encoding with
      | some (values, ⟨[], []⟩) =>
          if hasLength : values.length = size then
            some (fun index => values[index])
          else none
      | _ => none
  | .tagged tag base, encoding => (base.decode encoding).map Tagged.mk
  | .realArray, ⟨reals, [count]⟩ =>
      if reals.length = count then some ⟨reals.toArray⟩ else none
  | .realArray, _ => none
  | .natArray, ⟨[], count :: values⟩ =>
      if values.length = count then some ⟨values.toArray⟩ else none
  | .natArray, _ => none
  | .subtype predicate underlying, encoding => by
      classical
      exact match decode underlying encoding with
        | none => none
        | some value => dite (predicate value)
            (fun proof => some ⟨value, proof⟩) (fun _ => none)

/-- Every structural layout decoder is a left inverse of its fixed encoder. -/
theorem decode_encode (layout : Layout alpha) (value : alpha) :
    layout.decode (layout.encode value) = some value := by
  induction layout with
  | unit => cases value; rfl
  | bool => cases value <;> rfl
  | nat => rfl
  | int => cases value <;> rfl
  | rat =>
      simp only [encode]
      split <;> rename_i numerator <;> simp only [decode]
      · simp only [value.den_ne_zero, ↓reduceDIte, Rat.normalize_eq_mkRat,
          Option.some.injEq]
        rw [← numerator]
        exact value.mkRat_num_den'
      · simp only [value.den_ne_zero, ↓reduceDIte, Rat.normalize_eq_mkRat,
          Option.some.injEq]
        rw [← numerator]
        exact value.mkRat_num_den'
  | real => rfl
  | fin size => simp [encode, decode, value.isLt]
  | bitVec width =>
      simp only [encode, decode]
      have inRange : value.toNat < 2 ^ width := value.toFin.isLt
      simp only [inRange, ↓reduceDIte]
      exact congrArg some (by simp)
  | prod left right leftRoundTrip rightRoundTrip =>
      simp only [encode, decode, List.take_left, List.drop_left]
      rw [leftRoundTrip, rightRoundTrip]
  | sum left right leftRoundTrip rightRoundTrip =>
      cases value with
      | inl value => simp [encode, decode, leftRoundTrip]
      | inr value => simp [encode, decode, rightRoundTrip]
  | option element elementRoundTrip =>
      cases value with
      | none => rfl
      | some value => simp [encode, decode, elementRoundTrip]
  | list element elementRoundTrip =>
      simp only [encode, decode]
      rw [decodeListWith_encodeListWith _ _ elementRoundTrip]
  | array element elementRoundTrip =>
      simp only [encode, decode]
      rw [← Array.length_toList]
      change (match decodeListWith (decode element) value.toList.length
          (encodeListWith (encode element) value.toList) with
        | some (decoded, ⟨[], []⟩) => some decoded.toArray
        | _ => none) = some value
      rw [decodeListWith_encodeListWith _ _ elementRoundTrip]
  | vector length element elementRoundTrip =>
      simp only [encode, decode]
      have decoded : decodeListWith (decode element) length
          (encodeListWith (encode element) value.toArray.toList) =
          some (value.toArray.toList, ⟨[], []⟩) := by
        simpa using decodeListWith_encodeListWith _ _ elementRoundTrip value.toArray.toList
      rw [decoded]
      simp
  | finFun size element elementRoundTrip =>
      simp only [encode, decode]
      have decoded : decodeListWith (decode element) size
          (encodeListWith (encode element) (List.ofFn value)) =
          some (List.ofFn value, ⟨[], []⟩) := by
        simpa using decodeListWith_encodeListWith _ _ elementRoundTrip (List.ofFn value)
      rw [decoded]
      simp
  | tagged tag base baseRoundTrip =>
      rcases value with ⟨value⟩
      simp [encode, decode, baseRoundTrip]
  | realArray =>
      rcases value with ⟨values⟩
      simp [encode, decode]
  | natArray =>
      rcases value with ⟨values⟩
      simp [encode, decode]
  | subtype predicate underlying underlyingRoundTrip =>
      rcases value with ⟨value, property⟩
      simp only [encode, decode, underlyingRoundTrip]
      simp [property]

/-- The footprint of a value is derived from its canonical encoding. -/
noncomputable def footprint (layout : Layout alpha) (value : alpha) : Footprint :=
  let encoding := layout.encode value
  -- Two natural header cells store both stream lengths.
  ⟨encoding.reals.length, encoding.nats.length + 2⟩

/-- Read `length` consecutive real cells. -/
def readReals (memory : Memory) (base length : ℕ) : List ℝ :=
  List.ofFn fun index : Fin length => memory.realMem (base + index)

/-- Read `length` consecutive natural cells. -/
def readNats (memory : Memory) (base length : ℕ) : List ℕ :=
  List.ofFn fun index : Fin length => memory.natMem (base + index)

/--
Relational interpretation of a canonical value in designated cells.

The natural-bank header fixes both stream lengths, which makes two represented values comparable
without allowing an output decoder to perform computation.
-/
noncomputable def RepAt (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) : Prop :=
  let encoding := layout.encode value
  memory.natMem region.natBase = encoding.reals.length ∧
    memory.natMem (region.natBase + 1) = encoding.nats.length ∧
    readReals memory region.realBase encoding.reals.length = encoding.reals ∧
    readNats memory (region.natBase + 2) encoding.nats.length = encoding.nats

/-- Decode exactly the streams whose lengths are stored in a region's canonical headers. -/
noncomputable def readAt (layout : Layout alpha) (region : Region)
    (memory : Memory) : Option alpha :=
  layout.decode
    ⟨readReals memory region.realBase (memory.natMem region.natBase),
      readNats memory (region.natBase + 2) (memory.natMem (region.natBase + 1))⟩

/-- A relationally represented value is recovered by the fixed structural reader. -/
theorem readAt_eq_some (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) (rep : layout.RepAt region value memory) :
    layout.readAt region memory = some value := by
  simp only [RepAt] at rep
  simp only [readAt, rep.1, rep.2.1, rep.2.2.1, rep.2.2.2]
  exact layout.decode_encode value

/-- Place a finite list in otherwise-zero random-access memory. -/
def place (values : List alpha) [OfNat alpha 0] (base address : ℕ) : alpha :=
  if base ≤ address then values.getD (address - base) 0 else 0

/-- Replace exactly one finite interval of a random-access function. -/
def overwrite (values : List alpha) [OfNat alpha 0]
    (base : ℕ) (previous : ℕ → alpha) (address : ℕ) : alpha :=
  if base ≤ address ∧ address < base + values.length then
    place values base address
  else previous address

private theorem read_place (values : List alpha) [OfNat alpha 0] (base : ℕ) :
    List.ofFn (fun index : Fin values.length => place values base (base + index)) = values := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [List.get_ofFn]
    change place values base (base + index) = values[index]
    simp only [place, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left,
      List.getD_eq_getElem (l := values) (d := 0) rightBound]

private theorem read_overwrite (values : List alpha) [OfNat alpha 0]
    (base : ℕ) (previous : ℕ → alpha) :
    List.ofFn (fun index : Fin values.length ↦
      overwrite values base previous (base + index)) = values := by
  rw [show List.ofFn (fun index : Fin values.length ↦
      overwrite values base previous (base + index)) =
      List.ofFn (fun index : Fin values.length ↦ place values base (base + index)) by
    congr 1
    funext index
    simp [overwrite, index.isLt]]
  exact read_place values base

/--
Overwrite one canonical representation while preserving every ordinary memory cell outside its
two finite regions and preserving every register.  The operation is fixed by `Layout` syntax.
-/
noncomputable def writeAt (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) : Memory :=
  let encoding := layout.encode value
  { realMem := overwrite encoding.reals region.realBase memory.realMem
    natMem := fun address ↦
      if address = region.natBase then encoding.reals.length
      else if address = region.natBase + 1 then encoding.nats.length
      else overwrite encoding.nats (region.natBase + 2) memory.natMem address
    natReg := memory.natReg }

/-- The fixed region overwrite canonically represents the written value. -/
theorem writeAt_rep (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) :
    layout.RepAt region value (layout.writeAt region value memory) := by
  simp only [RepAt, writeAt]
  constructor
  · simp
  constructor
  · simp
  constructor
  · exact read_overwrite _ _ _
  · rw [show readNats
        { realMem := overwrite (layout.encode value).reals region.realBase memory.realMem
          natMem := fun address ↦
            if address = region.natBase then (layout.encode value).reals.length
            else if address = region.natBase + 1 then (layout.encode value).nats.length
            else overwrite (layout.encode value).nats (region.natBase + 2)
              memory.natMem address
          natReg := memory.natReg }
        (region.natBase + 2) (layout.encode value).nats.length =
        List.ofFn (fun index : Fin (layout.encode value).nats.length ↦
          overwrite (layout.encode value).nats (region.natBase + 2) memory.natMem
            (region.natBase + 2 + index)) by
          unfold readNats
          congr 1
          funext index
          have h0 : region.natBase + 2 + index ≠ region.natBase := by omega
          have h1 : region.natBase + 2 + index ≠ region.natBase + 1 := by omega
          simp [h0, h1]]
    exact read_overwrite _ _ _

/--
Canonical zero-initialized memory for a value.  Every cell outside the two finite representation
regions, and every natural register, is definitionally zero.
-/
noncomputable def initAt (layout : Layout alpha) (region : Region) (value : alpha) : Memory :=
  let encoding := layout.encode value
  { realMem := place encoding.reals region.realBase
    natMem := fun address =>
      if address = region.natBase then encoding.reals.length
      else if address = region.natBase + 1 then encoding.nats.length
      else place encoding.nats (region.natBase + 2) address
    natReg := fun _ => 0 }

/-- The conventional input region starts both banks at zero. -/
def inputRegion : Region := ⟨0, 0⟩

/-- Initialize a canonical input at `inputRegion`. -/
noncomputable def init (layout : Layout alpha) (value : alpha) : Memory :=
  initAt layout inputRegion value

/-- Canonical first work-memory region immediately after a represented input. -/
noncomputable def heapRegion (layout : Layout alpha) (value : alpha) : Region :=
  inputRegion.after (layout.footprint value)

/-- Canonical initialization represents the value it was built from. -/
theorem initAt_rep (layout : Layout alpha) (region : Region) (value : alpha) :
    layout.RepAt region value (layout.initAt region value) := by
  simp only [RepAt, initAt]
  constructor
  · simp
  constructor
  · simp
  constructor
  · exact read_place _ _
  · rw [show readNats
        { realMem := place (layout.encode value).reals region.realBase
          natMem := fun address =>
            if address = region.natBase then (layout.encode value).reals.length
            else if address = region.natBase + 1 then (layout.encode value).nats.length
            else place (layout.encode value).nats (region.natBase + 2) address
          natReg := fun _ => 0 }
        (region.natBase + 2) (layout.encode value).nats.length =
        List.ofFn (fun index : Fin (layout.encode value).nats.length =>
          place (layout.encode value).nats (region.natBase + 2)
            (region.natBase + 2 + index)) by
          unfold readNats
          congr 1
          funext index
          have h0 : region.natBase + 2 + index ≠ region.natBase := by omega
          have h1 : region.natBase + 2 + index ≠ region.natBase + 1 := by omega
          simp [h0, h1]]
    exact read_place _ _

/-- Canonical initialization at the default input region represents its input. -/
theorem init_rep (layout : Layout alpha) (value : alpha) :
    layout.RepAt inputRegion value (layout.init value) :=
  initAt_rep layout inputRegion value

/-- Exact-real cells outside the canonical representation region initialize to zero. -/
theorem initAt_real_zero_outside (layout : Layout alpha) (region : Region) (value : alpha)
    (address : ℕ)
    (outside : address < region.realBase ∨
      region.realBase + (layout.encode value).reals.length ≤ address) :
    (layout.initAt region value).realMem address = 0 := by
  simp only [initAt, place]
  split_ifs with inOrAfter
  · rw [List.getD_eq_default]
    omega
  · rfl

/-- Natural cells outside both length headers and the canonical payload initialize to zero. -/
theorem initAt_nat_zero_outside (layout : Layout alpha) (region : Region) (value : alpha)
    (address : ℕ)
    (outside : address < region.natBase ∨
      region.natBase + ((layout.encode value).nats.length + 2) ≤ address) :
    (layout.initAt region value).natMem address = 0 := by
  simp only [initAt]
  split_ifs with atRealLength atNatLength
  · subst address
    omega
  · subst address
    omega
  · simp only [place]
    split_ifs with inOrAfter
    · rw [List.getD_eq_default]
      omega
    · rfl

/-- Every natural register is zero in canonical initialization. -/
@[simp]
theorem initAt_natReg (layout : Layout alpha) (region : Region) (value : alpha)
    (register : ℕ) : (layout.initAt region value).natReg register = 0 := rfl

/-- A canonical representation denotes at most one structured value. -/
theorem rep_functional (layout : Layout alpha) (region : Region)
    {left right : alpha} {memory : Memory}
    (leftRep : layout.RepAt region left memory)
    (rightRep : layout.RepAt region right memory) : left = right := by
  simp only [RepAt] at leftRep rightRep
  let leftEncoding := layout.encode left
  let rightEncoding := layout.encode right
  have realLength : leftEncoding.reals.length = rightEncoding.reals.length :=
    leftRep.1.symm.trans rightRep.1
  have natLength : leftEncoding.nats.length = rightEncoding.nats.length :=
    leftRep.2.1.symm.trans rightRep.2.1
  have realStreams : leftEncoding.reals = rightEncoding.reals := by
    rw [← leftRep.2.2.1, ← rightRep.2.2.1, realLength]
  have natStreams : leftEncoding.nats = rightEncoding.nats := by
    rw [← leftRep.2.2.2, ← rightRep.2.2.2, natLength]
  have encodings : leftEncoding = rightEncoding :=
    Encoding.ext realStreams natStreams
  have decoded := congrArg layout.decode encodings
  rw [layout.decode_encode left, layout.decode_encode right] at decoded
  exact Option.some.inj decoded

end Layout

end Algolean.Algorithms.StructuredRealRAM
