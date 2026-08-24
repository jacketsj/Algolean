/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Layout

/-!
# Canonical structured exact-real/natural layouts

Typeclass inference selects only a term of the closed `Layout` syntax.  It never selects an
encoder, decoder, equivalence, accessor, or cost function.  Problems and procedure contracts
resolve the instance once and retain the resulting syntax term.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Model-specific canonical-layout selection containing closed syntax and nothing else. -/
class CanonicalLayout (alpha : Type) where
  layout : Layout alpha

/-- Resolve the concrete closed layout selected for `alpha`. -/
abbrev layoutOf (alpha : Type) [CanonicalLayout alpha] : Layout alpha :=
  CanonicalLayout.layout

instance : CanonicalLayout Unit := ⟨.unit⟩
instance : CanonicalLayout Bool := ⟨.bool⟩
instance : CanonicalLayout Nat := ⟨.nat⟩
instance : CanonicalLayout Int := ⟨.int⟩
instance canonicalRat : CanonicalLayout Rat := ⟨.rat⟩
instance : CanonicalLayout Real := ⟨.real⟩
instance (size : Nat) : CanonicalLayout (Fin size) := ⟨.fin size⟩
instance (width : Nat) : CanonicalLayout (BitVec width) := ⟨.bitVec width⟩
instance [CanonicalLayout alpha] [CanonicalLayout beta] :
    CanonicalLayout (alpha × beta) := ⟨.prod (layoutOf alpha) (layoutOf beta)⟩
instance [CanonicalLayout alpha] [CanonicalLayout beta] :
    CanonicalLayout (Sum alpha beta) := ⟨.sum (layoutOf alpha) (layoutOf beta)⟩
instance [CanonicalLayout alpha] : CanonicalLayout (Option alpha) :=
  ⟨.option (layoutOf alpha)⟩
instance [CanonicalLayout alpha] : CanonicalLayout (List alpha) :=
  ⟨.list (layoutOf alpha)⟩
instance [CanonicalLayout alpha] : CanonicalLayout (Array alpha) :=
  ⟨.array (layoutOf alpha)⟩
instance (length : Nat) [CanonicalLayout alpha] : CanonicalLayout (Vector alpha length) :=
  ⟨.vector length (layoutOf alpha)⟩
instance (size : Nat) [CanonicalLayout alpha] : CanonicalLayout (Fin size → alpha) :=
  ⟨.finFun size (layoutOf alpha)⟩
instance (tag : DataTag) [CanonicalLayout alpha] : CanonicalLayout (Tagged tag alpha) :=
  ⟨.tagged tag (layoutOf alpha)⟩
instance (predicate : alpha → Prop) [CanonicalLayout alpha] :
    CanonicalLayout {value : alpha // predicate value} :=
  ⟨.subtype predicate (layoutOf alpha)⟩

/--
Capability for a layout whose two finite streams have value-independent sizes.  Array indexing
may use a constant stride only when this capability is available.
-/
class FixedFootprint (alpha : Type) [CanonicalLayout alpha] where
  footprint : Footprint
  footprint_eq : ∀ value : alpha, (layoutOf alpha).footprint value = footprint

/-- Full represented footprint, including the two universal stream-length headers. -/
def fixedFootprint (alpha : Type) [CanonicalLayout alpha]
    [fixed : FixedFootprint alpha] : Footprint :=
  fixed.footprint

/-- Every value has the advertised fixed two-bank footprint. -/
theorem fixedFootprint_eq (alpha : Type) [CanonicalLayout alpha]
    [fixed : FixedFootprint alpha] (value : alpha) :
    (layoutOf alpha).footprint value = fixedFootprint alpha := by
  exact fixed.footprint_eq value

instance : FixedFootprint Unit := ⟨⟨0, 2⟩, by intro value; cases value; rfl⟩
instance : FixedFootprint Bool := ⟨⟨0, 3⟩, by intro value; cases value <;> rfl⟩
instance : FixedFootprint Nat := ⟨⟨0, 3⟩, by intro; rfl⟩
instance : FixedFootprint Int := ⟨⟨0, 4⟩, by intro value; cases value <;> rfl⟩
instance : FixedFootprint Rat := ⟨⟨0, 5⟩, by
  intro value
  change (Layout.rat.footprint value = ⟨0, 5⟩)
  simp only [Layout.footprint, Layout.encode]
  split <;> rfl⟩
instance : FixedFootprint Real := ⟨⟨1, 2⟩, by intro; rfl⟩
instance (size : Nat) : FixedFootprint (Fin size) := ⟨⟨0, 3⟩, by intro; rfl⟩
instance (width : Nat) : FixedFootprint (BitVec width) := ⟨⟨0, 3⟩, by intro; rfl⟩

end Algolean.Algorithms.StructuredRealRAM
