/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.CFG

/-!
# Typed staged block authoring

This small builder manipulates only compile-time register and label handles.  Runtime naturals and
reals remain `NatOperand` and `RealOperand`; no builder action returns a Lean runtime value.
Control-flow combinators live in `CFG` and build shared labeled blocks.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.StructuredBuilder

open CFG

/-- Compile-time state for authoring one straight-line basic-block body. -/
structure State where
  /-- Next unused natural register number. -/
  nextRegister : ℕ := 0
  /-- Next unused source label number. -/
  nextLabel : ℕ := 0
  /-- Operations accumulated in reverse source order. -/
  operationsRev : List Operation := []

/-- Staged authoring monad; its state contains syntax handles, never runtime machine values. -/
abbrev BlockM := StateM State

/-- Allocate a natural register handle. -/
def freshN : BlockM NReg := fun state =>
  (⟨state.nextRegister⟩, { state with nextRegister := state.nextRegister + 1 })

/-- Allocate a real-cell address-register handle. -/
def freshR : BlockM RReg := fun state =>
  (⟨state.nextRegister⟩, { state with nextRegister := state.nextRegister + 1 })

/-- Allocate a fresh basic-block label. -/
def freshLabel : BlockM Label := fun state =>
  (⟨state.nextLabel⟩, { state with nextLabel := state.nextLabel + 1 })

/-- Emit one first-order operation. -/
def emit (operation : Operation) : BlockM Unit := fun state =>
  ((), { state with operationsRev := operation :: state.operationsRev })

/-- Allocate a real-cell handle and emit initialization of its address register. -/
def realCellAt (address : ℕ) : BlockM RReg := do
  let destination ← freshR
  emit (.nset (.literal address) ⟨destination.index⟩)
  pure destination

/-- Emit a natural literal assignment and return its destination handle. -/
def setN (value : ℕ) : BlockM NReg := do
  let destination ← freshN
  emit (.nset (.literal value) destination)
  pure destination

/-- Emit a natural-memory load and return its destination handle. -/
def loadN (address : NReg) : BlockM NReg := do
  let destination ← freshN
  emit (.nload address destination)
  pure destination

/-- Emit natural addition and return its destination handle. -/
def addN (left right : NatOperand) : BlockM NReg := do
  let destination ← freshN
  emit (.nadd left right destination)
  pure destination

/-- Emit exact-real addition into a previously addressed real cell. -/
def addR (left right : RealOperand) (destination : RReg) : BlockM Unit := do
  emit (.radd left right destination)

/-- Run a block builder and return source-order syntax plus the remaining fresh-name state. -/
def run (builder : BlockM alpha) (initial : State := {}) : alpha × List Operation × State :=
  let (result, finalState) := builder initial
  (result, finalState.operationsRev.reverse, { finalState with operationsRev := [] })

end Algolean.Algorithms.StructuredRealRAM.StructuredBuilder
