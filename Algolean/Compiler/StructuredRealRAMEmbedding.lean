/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Profile

/-!
# Certified embeddings between sealed structured exact-real/natural RAM profiles

The deterministic core embeds into either hidden-source profile by the fixed `.core` constructor.
The simulations below preserve ordinary memory, every deterministic cost coordinate, transition
count, and the hidden source cursor.  Thus composition never relies on an unproved instruction
lifting function.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

namespace RandomBit.CoreEmbedding

/-- Fixed syntax embedding of deterministic instructions. -/
def program (source : StructuredRealRAM.Program) : RandomBit.Program :=
  source.map .core

/-- Deterministic validity is preserved by the fixed syntax embedding. -/
theorem valid (source : StructuredRealRAM.Program) (sourceValid : source.Valid) :
    (program source).Valid := by
  intro pc instruction fetch target successor
  simp only [program, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨fetched, coreFetch, rfl⟩
  simpa [program] using sourceValid pc fetched coreFetch target successor

/-- One embedded core step preserves the hidden cursor and lifts only the cost type. -/
theorem step (source : StructuredRealRAM.Program) (randomSource : RandomBit.Source)
    (configuration : StructuredRealRAM.Configuration) (cursor : Nat) :
    RandomBit.step (program source) randomSource
      ⟨configuration.pc, configuration.memory, cursor⟩ =
    let observation := StructuredRealRAM.step source configuration
    ⟨RandomBit.liftCoreOutcome cursor observation.outcome,
      RandomBit.Cost.ofCore observation.cost⟩ := by
  cases fetched : source[configuration.pc]? with
  | none =>
      have zeroLift : RandomBit.Cost.ofCore 0 = 0 := rfl
      simp [RandomBit.step, program, StructuredRealRAM.step, fetched,
        RandomBit.liftCoreOutcome]
      exact zeroLift.symm
  | some instruction =>
      simp [RandomBit.step, program, StructuredRealRAM.step, fetched,
        RandomBit.execute]

/-- Whole deterministic traces lift with no draws and no hidden change of machine cost. -/
theorem trace (source : StructuredRealRAM.Program) (randomSource : RandomBit.Source)
    (cursor : Nat)
    (derivation : StructuredRealRAM.HaltingTrace source initial final result cost steps) :
    RandomBit.HaltingTrace (program source) randomSource
      ⟨initial.pc, initial.memory, cursor⟩ final result
      (RandomBit.Cost.ofCore cost) steps cursor := by
  induction derivation with
  | halt observes =>
      apply RandomBit.HaltingTrace.halt
      rw [step, observes]
      rfl
  | @next configuration nextConfiguration memory result headCost tailCost steps
      observes tail induction =>
      have embeddedStep := step source randomSource configuration cursor
      rw [observes] at embeddedStep
      have head : RandomBit.step (program source) randomSource
          ⟨configuration.pc, configuration.memory, cursor⟩ =
          ⟨.running ⟨nextConfiguration.pc, nextConfiguration.memory, cursor⟩,
            RandomBit.Cost.ofCore headCost⟩ := by
        simpa [RandomBit.liftCoreOutcome] using embeddedStep
      have lifted := RandomBit.HaltingTrace.next head induction
      have costEq : RandomBit.Cost.ofCore headCost + RandomBit.Cost.ofCore tailCost =
          RandomBit.Cost.ofCore (headCost + tailCost) := by
        apply RandomBit.Cost.ext <;> rfl
      rw [← costEq]
      exact lifted

private theorem encodeInstructions_length (source : StructuredRealRAM.Program) :
    (RandomBit.Program.encodeInstructions (program source)).length =
      (StructuredRealRAM.Program.encodeInstructions source).length + source.length := by
  induction source with
  | nil => rfl
  | cons instruction source ih =>
      simp only [program, List.map_cons, RandomBit.Program.encodeInstructions,
        RandomBit.Instruction.encode, StructuredRealRAM.Program.encodeInstructions,
        List.length_append, List.length_cons]
      have ih' :
          (RandomBit.Program.encodeInstructions (source.map .core)).length =
            (StructuredRealRAM.Program.encodeInstructions source).length + source.length := by
        simpa [program] using ih
      rw [ih']
      omega

/-- Each embedded instruction adds exactly one profile tag bit to the core description. -/
theorem descriptionSize (source : StructuredRealRAM.Program) :
    RandomBit.Program.descriptionSize (program source) =
      StructuredRealRAM.Program.descriptionSize source + source.length := by
  simp only [RandomBit.Program.descriptionSize, RandomBit.Program.encode,
    StructuredRealRAM.Program.descriptionSize, StructuredRealRAM.Program.encode,
    List.length_append]
  rw [encodeInstructions_length]
  simp [program, Nat.add_assoc]

end RandomBit.CoreEmbedding

namespace UniformReal.CoreEmbedding

/-- Fixed syntax embedding of deterministic instructions. -/
def program (source : StructuredRealRAM.Program) : UniformReal.Program :=
  source.map .core

/-- Deterministic validity is preserved by the exact-uniform profile embedding. -/
theorem valid (source : StructuredRealRAM.Program) (sourceValid : source.Valid) :
    (program source).Valid := by
  intro pc instruction fetch target successor
  simp only [program, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨fetched, coreFetch, rfl⟩
  simpa [program] using sourceValid pc fetched coreFetch target successor

/-- One embedded core step preserves the exact-uniform source cursor. -/
theorem step (source : StructuredRealRAM.Program) (randomSource : UniformReal.Source)
    (configuration : StructuredRealRAM.Configuration) (cursor : Nat) :
    UniformReal.step (program source) randomSource
      ⟨configuration.pc, configuration.memory, cursor⟩ =
    let observation := StructuredRealRAM.step source configuration
    ⟨UniformReal.liftCoreOutcome cursor observation.outcome,
      RandomBit.Cost.ofCore observation.cost⟩ := by
  cases fetched : source[configuration.pc]? with
  | none =>
      have zeroLift : RandomBit.Cost.ofCore 0 = 0 := rfl
      simp [UniformReal.step, program, StructuredRealRAM.step, fetched,
        UniformReal.liftCoreOutcome]
      exact zeroLift.symm
  | some instruction =>
      simp [UniformReal.step, program, StructuredRealRAM.step, fetched,
        UniformReal.execute]

/-- Deterministic traces lift to the continuous profile without consuming a sample. -/
theorem trace (source : StructuredRealRAM.Program) (randomSource : UniformReal.Source)
    (cursor : Nat)
    (derivation : StructuredRealRAM.HaltingTrace source initial final result cost steps) :
    UniformReal.HaltingTrace (program source) randomSource
      ⟨initial.pc, initial.memory, cursor⟩ final result
      (RandomBit.Cost.ofCore cost) steps cursor := by
  induction derivation with
  | halt observes =>
      apply UniformReal.HaltingTrace.halt
      rw [step, observes]
      rfl
  | @next configuration nextConfiguration memory result headCost tailCost steps
      observes tail induction =>
      have embeddedStep := step source randomSource configuration cursor
      rw [observes] at embeddedStep
      have head : UniformReal.step (program source) randomSource
          ⟨configuration.pc, configuration.memory, cursor⟩ =
          ⟨.running ⟨nextConfiguration.pc, nextConfiguration.memory, cursor⟩,
            RandomBit.Cost.ofCore headCost⟩ := by
        simpa [UniformReal.liftCoreOutcome] using embeddedStep
      have lifted := UniformReal.HaltingTrace.next head induction
      have costEq : RandomBit.Cost.ofCore headCost + RandomBit.Cost.ofCore tailCost =
          RandomBit.Cost.ofCore (headCost + tailCost) := by
        apply RandomBit.Cost.ext <;> rfl
      rw [← costEq]
      exact lifted

private theorem encodeInstructions_length (source : StructuredRealRAM.Program) :
    (UniformReal.Program.encodeInstructions (program source)).length =
      (StructuredRealRAM.Program.encodeInstructions source).length + source.length := by
  induction source with
  | nil => rfl
  | cons instruction source ih =>
      simp only [program, List.map_cons, UniformReal.Program.encodeInstructions,
        UniformReal.Instruction.encode, StructuredRealRAM.Program.encodeInstructions,
        List.length_append, List.length_cons]
      have ih' :
          (UniformReal.Program.encodeInstructions (source.map .core)).length =
            (StructuredRealRAM.Program.encodeInstructions source).length + source.length := by
        simpa [program] using ih
      rw [ih']
      omega

/-- Continuous-profile embedding likewise adds one sealed profile tag per instruction. -/
theorem descriptionSize (source : StructuredRealRAM.Program) :
    UniformReal.Program.descriptionSize (program source) =
      StructuredRealRAM.Program.descriptionSize source + source.length := by
  simp only [UniformReal.Program.descriptionSize, UniformReal.Program.encode,
    StructuredRealRAM.Program.descriptionSize, StructuredRealRAM.Program.encode,
    List.length_append]
  rw [encodeInstructions_length]
  simp [program, Nat.add_assoc]

end UniformReal.CoreEmbedding

end Algolean.Algorithms.StructuredRealRAM
