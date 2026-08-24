/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.WordRAM.Layout

/-!
# Closed-layout indexed arrays for the Word RAM

The cached offset table is determined exclusively by the selected closed `WordLayout` footprint.
No caller-supplied sizing function can preload answer-dependent metadata.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Exact canonical-boundary invariant for a variable-footprint indexed array. -/
def IndexedArray.Valid [Inhabited alpha] (element : WordLayout w alpha)
    (payload : WordArray w (BitVec w) × WordArray w alpha) : Prop :=
  payload.1.size = payload.2.size + 1 ∧
    (payload.1.data.getD 0 0).toNat = 0 ∧
    (∀ i, i < payload.2.size →
      (payload.1.data.getD (i + 1) 0).toNat =
        (payload.1.data.getD i 0).toNat +
          element.footprintWords (payload.2.data.getD i default)) ∧
    (payload.1.data.getD payload.2.size 0).toNat =
      (payload.2.data.toList.map element.footprintWords).sum ∧
    (payload.1.data.getD payload.2.size 0).toNat < 2 ^ w

/-- Explicit-layout indexed physical representation. -/
abbrev IndexedArrayWithLayout (element : WordLayout w alpha) [Inhabited alpha] :=
  Tagged .indexedArray
    {payload : WordArray w (BitVec w) × WordArray w alpha //
      IndexedArray.Valid element payload}

/-- Canonical indexed representation obtained by resolving one closed layout term. -/
abbrev IndexedArray (w : Nat) (alpha : Type) [Inhabited alpha]
    [CanonicalLayout w alpha] :=
  IndexedArrayWithLayout (layoutOf w alpha)

/-- Closed explicit layout of an addressable array wrapper. -/
def wordArrayLayout (element : WordLayout w alpha) : WordLayout w (WordArray w alpha) :=
  .tagged .wordArray (.subtype (fun data : Array alpha ↦ data.size < 2 ^ w)
    (.array element))

/-- Closed layout of the cached-boundary indexed format, retaining the selected element syntax. -/
def indexedArrayLayout [Inhabited alpha] (element : WordLayout w alpha) :
    WordLayout w (IndexedArrayWithLayout element) :=
  .tagged .indexedArray (.subtype (IndexedArray.Valid element)
    (.prod (wordArrayLayout .word) (wordArrayLayout element)))

@[simp]
theorem wordArrayLayout_encode (element : WordLayout w alpha) (values : WordArray w alpha) :
    (wordArrayLayout element).encode values =
      BitVec.ofNat w values.size :: element.encodeList values.data.toList := by
  rcases values with ⟨⟨data, fits⟩⟩
  simp [wordArrayLayout, WordLayout.encode, WordArray.size, WordArray.data, Tagged.value]

@[simp]
theorem indexedArrayLayout_encode [Inhabited alpha] (element : WordLayout w alpha)
    (payload : WordArray w (BitVec w) × WordArray w alpha)
    (valid : IndexedArray.Valid element payload) :
    (indexedArrayLayout element).encode (Tagged.mk ⟨payload, valid⟩) =
      (BitVec.ofNat w payload.1.size :: payload.1.data.toList) ++
        (BitVec.ofNat w payload.2.size :: element.encodeList payload.2.data.toList) := by
  simp only [indexedArrayLayout, WordLayout.encode]
  rw [wordArrayLayout_encode, wordArrayLayout_encode]
  congr 1
  induction payload.1.data.toList with
  | nil => simp [WordLayout.encodeList, WordLayout.encode]
  | cons head tail induction =>
      have tailEncoding : (WordLayout.word : WordLayout w (BitVec w)).encodeList tail = tail :=
        List.cons.inj induction |>.2
      simp [WordLayout.encodeList, WordLayout.encode, tailEncoding]

/-- The next cached boundary is forced to use the closed layout's actual footprint. -/
theorem IndexedArray.Valid.nextBoundary [Inhabited alpha]
    {element : WordLayout w alpha}
    {payload : WordArray w (BitVec w) × WordArray w alpha}
    (valid : IndexedArray.Valid element payload) (index : Nat)
    (inRange : index < payload.2.size) :
    (payload.1.data.getD (index + 1) 0).toNat =
      (payload.1.data.getD index 0).toNat +
        element.footprintWords (payload.2.data.getD index default) :=
  valid.2.2.1 index inRange

end Algolean.Algorithms.WordRAM
