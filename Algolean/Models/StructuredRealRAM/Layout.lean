/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Core

/-!
# Canonical structured layouts

`Layout` has a private constructor.  Clients can compose only the structural constructors in this
module; there is intentionally no public custom encoder, decoder, or equivalence constructor.
Every layout carries a kernel-checked round-trip certificate.  The implementation exposes its
canonical streams for auditing, but input initialization is fixed by `Layout.init`.
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

/-- The pair of finite streams underlying a canonical representation. -/
@[ext]
structure Encoding where
  /-- Canonical exact-real stream. -/
  reals : List ℝ
  /-- Canonical discrete stream. -/
  nats : List ℕ

/--
A certified canonical layout.

The constructor is private: only the closed structural combinators below can create layouts.
The decoder is library-defined metadata used to prove functionality; public algorithm statements
interpret output through `RepAt`, never through a user-supplied decoding function.
-/
structure Layout (alpha : Type u) where
  private mk ::
  /-- Auditable, structurally generated real and natural streams. -/
  encode : alpha → Encoding
  /-- The inverse used internally to certify information preservation. -/
  decode : Encoding → Option alpha
  /-- Kernel-checked left-inverse law. -/
  decode_encode : ∀ value, decode (encode value) = some value

namespace Layout

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Canonical layout for `Unit`. -/
def unit : Layout Unit := Layout.mk
  (fun _ => ⟨[], []⟩)
  (fun
    | ⟨[], []⟩ => some ()
    | _ => none)
  (by intro; rfl)

/-- Canonical layout for natural numbers. -/
def nat : Layout ℕ := Layout.mk
  (fun value => ⟨[], [value]⟩)
  (fun
    | ⟨[], [value]⟩ => some value
    | _ => none)
  (by intro; rfl)

/-- Canonical layout for exact real numbers. -/
noncomputable def real : Layout ℝ := Layout.mk
  (fun value => ⟨[value], []⟩)
  (fun
    | ⟨[value], []⟩ => some value
    | _ => none)
  (by intro; rfl)

/--
Canonical product layout.  Two natural header cells record the real and natural lengths of the
left component; the streams themselves are fieldwise concatenations.
-/
noncomputable def prod (left : Layout alpha) (right : Layout beta) : Layout (alpha × beta) :=
  Layout.mk (fun value =>
    let leftEncoding := left.encode value.1
    let rightEncoding := right.encode value.2
    ⟨leftEncoding.reals ++ rightEncoding.reals,
      leftEncoding.reals.length :: leftEncoding.nats.length ::
        (leftEncoding.nats ++ rightEncoding.nats)⟩)
  (fun encoding =>
    match encoding.nats with
    | realLength :: natLength :: nats =>
        match left.decode ⟨encoding.reals.take realLength, nats.take natLength⟩,
          right.decode ⟨encoding.reals.drop realLength, nats.drop natLength⟩ with
        | some leftValue, some rightValue => some (leftValue, rightValue)
        | _, _ => none
    | _ => none)
  (by
    intro value
    simp only [List.take_left, List.drop_left]
    rw [left.decode_encode, right.decode_encode])

/-- Encode a list as length-delimited element chunks. -/
private noncomputable def encodeList (layout : Layout alpha) : List alpha → Encoding
  | [] => ⟨[], []⟩
  | value :: values =>
      let head := layout.encode value
      let tail := encodeList layout values
      ⟨head.reals ++ tail.reals,
        head.reals.length :: head.nats.length :: (head.nats ++ tail.nats)⟩

/-- Decode exactly `count` length-delimited element chunks and return the unused streams. -/
private noncomputable def decodeList (layout : Layout alpha) :
    ℕ → Encoding → Option (List alpha × Encoding)
  | 0, encoding => some ([], encoding)
  | count + 1, encoding =>
      match encoding.nats with
      | realLength :: natLength :: nats =>
          match layout.decode ⟨encoding.reals.take realLength, nats.take natLength⟩,
            decodeList layout count
              ⟨encoding.reals.drop realLength, nats.drop natLength⟩ with
          | some value, some (values, rest) => some (value :: values, rest)
          | _, _ => none
      | _ => none

private theorem decodeList_encodeList (layout : Layout alpha) (values : List alpha) :
    decodeList layout values.length (encodeList layout values) =
      some (values, ⟨[], []⟩) := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [encodeList, decodeList, List.length_cons,
        List.take_left, List.drop_left]
      rw [layout.decode_encode, induction]

/--
Canonical array layout.  The stream begins with the array length, and every element is prefixed by
its two stream lengths.  This supports variable-footprint nested structural elements without an
arbitrary host-language codec.
-/
noncomputable def array (element : Layout alpha) : Layout (Array alpha) :=
  Layout.mk (fun values =>
    let body := encodeList element values.toList
    ⟨body.reals, values.size :: body.nats⟩)
  (fun encoding =>
    match encoding.nats with
    | count :: nats =>
        match decodeList element count ⟨encoding.reals, nats⟩ with
        | some (values, ⟨[], []⟩) => some values.toArray
        | _ => none
    | [] => none)
  (by
    intro values
    rw [← Array.length_toList]
    change (match decodeList element values.toList.length (encodeList element values.toList) with
      | some (decoded, ⟨[], []⟩) => some decoded.toArray
      | _ => none) = some values
    rw [decodeList_encodeList])

/--
Canonical proof-erasing subtype layout.  Only the underlying computational value is represented;
the proposition is re-established in Lean and no proof term is placed in machine memory.
-/
noncomputable def subtype (predicate : alpha → Prop) (underlying : Layout alpha) :
    Layout {value : alpha // predicate value} := Layout.mk
  (fun value => underlying.encode value.1)
  (by
    classical
    exact fun encoding =>
      match underlying.decode encoding with
      | none => none
      | some value => dite (predicate value)
          (fun proof => some ⟨value, proof⟩) (fun _ => none))
  (by
    classical
    rintro ⟨value, property⟩
    rw [underlying.decode_encode]
    simp [property])

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

/-- Place a finite list in otherwise-zero random-access memory. -/
def place (values : List alpha) [OfNat alpha 0] (base address : ℕ) : alpha :=
  if base ≤ address then values.getD (address - base) 0 else 0

private theorem read_place (values : List alpha) [OfNat alpha 0] (base : ℕ) :
    List.ofFn (fun index : Fin values.length => place values base (base + index)) = values := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [List.get_ofFn]
    change place values base (base + index) = values[index]
    simp only [place, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left,
      List.getD_eq_getElem (l := values) (d := 0) rightBound]

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
