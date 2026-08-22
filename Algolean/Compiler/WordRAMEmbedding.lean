/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMStructured
public import Algolean.Models.WordRAM.Profile

/-!
# Certified Word-RAM model embeddings

Composition across unequal profiles is accepted only through a finite syntax translation with
step, trace, cost, and description-size simulation proofs.  An arbitrary program-lifting function
alone is not an embedding.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- A proof-carrying embedding between two explicitly disclosed Word-RAM profiles. -/
structure MachineEmbedding (sourceWidth targetWidth : Nat) where
  sourceProfile : Profile sourceWidth := standardProfile sourceWidth
  targetProfile : Profile targetWidth := standardProfile targetWidth
  liftInstruction : RAM.Instruction (BitVec sourceWidth) (BitVec sourceWidth) Empty →
    Program targetWidth
  liftProgram : Program sourceWidth → Program targetWidth
  liftProgram_eq : ∀ program,
    liftProgram program = program.flatMap liftInstruction
  valid : ∀ program, program.Valid → (liftProgram program).Valid
  configurationRelation :
    RAM.Configuration (BitVec sourceWidth) (BitVec sourceWidth) →
      RAM.Configuration (BitVec targetWidth) (BitVec targetWidth) → Prop
  memoryRelation : Memory sourceWidth → Memory targetWidth → Prop
  /-- Uniform target-cost overhead as a function of the observed source cost. -/
  costBound : Nat → Nat
  traceSimulation : ∀ program initial final result cost steps,
    RAM.HaltingTrace (stepCosted program) initial final result cost steps →
    ∀ targetInitial, configurationRelation initial targetInitial →
      ∃ targetFinal targetResult targetCost targetSteps,
        RAM.HaltingTrace (stepCosted (liftProgram program)) targetInitial
          targetFinal targetResult targetCost targetSteps ∧
        memoryRelation final targetFinal ∧
        targetCost ≤ costBound cost
  descriptionSizeBound : Nat → Nat
  descriptionSizeSimulation : ∀ program,
    WordRAM.descriptionSize (liftProgram program) ≤
      descriptionSizeBound (WordRAM.descriptionSize program)

/-- Same-width identity embedding; ordinary composition requires no hidden convention change. -/
def MachineEmbedding.identity (w : Nat) : MachineEmbedding w w where
  liftInstruction instruction := [instruction]
  liftProgram program := program
  liftProgram_eq program := by simp
  valid _ valid := valid
  configurationRelation := Eq
  memoryRelation := Eq
  costBound cost := cost
  traceSimulation _ _ final result cost steps trace targetInitial related := by
    subst targetInitial
    exact ⟨final, result, cost, steps, trace, rfl, le_rfl⟩
  descriptionSizeBound size := size
  descriptionSizeSimulation _ := le_rfl

end Algolean.Algorithms.WordRAM
