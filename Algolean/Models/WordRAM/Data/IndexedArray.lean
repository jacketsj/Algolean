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
