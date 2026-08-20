/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM.ContinuousRandom
public import Algolean.Models.StructuredRealRAM.Random

/-!
# A structured exact-real RAM with exact uniform `[0,1]` samples

This deliberately stronger profile is separate from the random-bit RAM.  Its source is a hidden,
lengthless sequence with the fixed product law of exact uniform values in `[0,1]`.  The only source
operation is the closed and charged `sampleUniform` instruction.  No arbitrary distribution or
sampling evaluator is accepted by an algorithm witness.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.UniformReal

/-- One realization of the fixed exact-uniform source. -/
abbrev Source := ContinuousRealSample.Oracle

/-- Canonical product law of independent exact uniform `[0,1]` coordinates. -/
noncomputable abbrev sourceLaw : MeasureTheory.Measure Source :=
  ContinuousRealSample.oracleLaw

/-- Closed instructions for the exact-uniform-real profile. -/
inductive Instruction where
  | core (instruction : StructuredRealRAM.Instruction)
  /-- Store one exact uniform sample at the real address held by `destinationRegister`. -/
  | sampleUniform (destinationRegister next : ℕ)
deriving DecidableEq, Repr

/-- One finite program in the exact-uniform profile. -/
abbrev Program := List Instruction
/-- Core state plus a hidden semantic source cursor. -/
abbrev Configuration := StructuredRealRAM.RandomBit.Configuration
/-- One-step operational outcome. -/
abbrev StepResult := StructuredRealRAM.RandomBit.StepResult
/-- Fuel-bounded operational outcome. -/
abbrev RunResult := StructuredRealRAM.RandomBit.RunResult
/-- Core resources plus the primitive sample count. -/
abbrev Cost := StructuredRealRAM.RandomBit.Cost

/-- Same-transition result and resource charge. -/
structure StepObservation where
  /-- Operational effect. -/
  outcome : StepResult
  /-- Charge returned by the same transition. -/
  cost : Cost

/-- Fuel-bounded result and charge. -/
structure RunObservation where
  /-- Halt, timeout, or stuck outcome. -/
  outcome : RunResult
  /-- Accumulated same-trace charge. -/
  cost : Cost
  /-- Number of fetched transitions. -/
  steps : ℕ

namespace Instruction

/-- Numeric successors stored by one instruction. -/
def successors : Instruction → List ℕ
  | .core instruction => instruction.successors
  | .sampleUniform _ next => [next]

/-- Canonical binary description of one instruction. -/
def encode : Instruction → List Bool
  | .core instruction => false :: StructuredRealRAM.Program.encodeInstruction instruction
  | .sampleUniform destination next =>
      true :: StructuredRealRAM.Program.encodeNat destination ++
        StructuredRealRAM.Program.encodeNat next

end Instruction

namespace Program

/-- Every numeric successor is a position in the same finite program. -/
def Valid (program : Program) : Prop :=
  ∀ (pc : ℕ) (instruction : Instruction), program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

/-- Concatenate canonical instruction descriptions. -/
def encodeInstructions : List Instruction → List Bool
  | [] => []
  | instruction :: instructions => instruction.encode ++ encodeInstructions instructions

/-- Canonical complete program description. -/
def encode (program : Program) : List Bool :=
  StructuredRealRAM.Program.encodeNat program.length ++ encodeInstructions program

/-- Number of instruction positions. -/
def instructionCount (program : Program) : ℕ := program.length

/-- Full canonical binary description size. -/
def descriptionSize (program : Program) : ℕ := program.encode.length

end Program

/-- Lift a deterministic outcome while preserving the hidden source cursor. -/
def liftCoreOutcome (cursor : ℕ) : StructuredRealRAM.StepResult → StepResult
  | .running configuration => .running ⟨configuration.pc, configuration.memory, cursor⟩
  | .halted memory result => .halted memory result cursor
  | .stuck configuration => .stuck ⟨configuration.pc, configuration.memory, cursor⟩

/-- One exact sample costs one fetched instruction, one real write, and one primitive draw. -/
def sampleCost : Cost :=
  ⟨StructuredRealRAM.Cost.ofFields 1 0 1 0 0 0 0 0 0, 1⟩

/-- Execute one fetched instruction against one fixed source realization. -/
noncomputable def execute (source : Source) (instruction : Instruction)
    (configuration : Configuration) : StepObservation :=
  match instruction with
  | .core coreInstruction =>
      let observation := StructuredRealRAM.execute coreInstruction configuration.memory
      ⟨liftCoreOutcome configuration.randomCursor observation.outcome,
        StructuredRealRAM.RandomBit.Cost.ofCore observation.cost⟩
  | .sampleUniform destination next =>
      let memory := configuration.memory.writeReal
        (configuration.memory.natReg destination) (source configuration.randomCursor)
      ⟨.running ⟨next, memory, configuration.randomCursor + 1⟩, sampleCost⟩

/-- Fetch and execute once. -/
noncomputable def step (program : Program) (source : Source)
    (configuration : Configuration) : StepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => execute source instruction configuration

/-- Run at most the supplied number of fetched instructions. -/
noncomputable def runFor (program : Program) (source : Source) :
    ℕ → Configuration → RunObservation
  | 0, configuration => ⟨.outOfFuel configuration, 0, 0⟩
  | fuel + 1, configuration =>
      let observation := step program source configuration
      match observation.outcome with
      | .running next =>
          let rest := runFor program source fuel next
          ⟨rest.outcome, observation.cost + rest.cost, rest.steps + 1⟩
      | .halted memory result draws =>
          ⟨.halted memory result draws, observation.cost, 1⟩
      | .stuck stuck => ⟨.stuck stuck, observation.cost, 1⟩

/-- Same-trace exact-uniform execution evidence. -/
inductive HaltingTrace (program : Program) (source : Source) :
    Configuration → Memory → ℝ → Cost → ℕ → ℕ → Prop where
  | halt {configuration memory result cost draws}
      (observes : step program source configuration =
        ⟨.halted memory result draws, cost⟩) :
      HaltingTrace program source configuration memory result cost 1 draws
  | next {configuration nextConfiguration memory result headCost tailCost steps draws}
      (observes : step program source configuration =
        ⟨.running nextConfiguration, headCost⟩)
      (tail : HaltingTrace program source nextConfiguration memory result tailCost steps draws) :
      HaltingTrace program source configuration memory result
        (headCost + tailCost) (steps + 1) draws

/-- Per-transition exact accounting of continuous primitive draws. -/
def StepObservation.CursorAccounting (observation : StepObservation)
    (initial : Configuration) : Prop :=
  match observation.outcome with
  | .running next => observation.cost.randomDraws + initial.randomCursor = next.randomCursor
  | .halted _ _ draws => observation.cost.randomDraws + initial.randomCursor = draws
  | .stuck _ => observation.cost.randomDraws = 0

theorem step_cursorAccounting (program : Program) (source : Source)
    (configuration : Configuration) :
    (step program source configuration).CursorAccounting configuration := by
  simp only [step]
  split
  · rfl
  · rename_i instruction fetch
    cases instruction with
    | core instruction =>
        simp only [execute]
        generalize hobs : StructuredRealRAM.execute instruction configuration.memory = observation
        cases observation with
        | mk outcome cost =>
          cases outcome <;>
            simp [StepObservation.CursorAccounting, liftCoreOutcome,
              StructuredRealRAM.RandomBit.Cost.ofCore]
    | sampleUniform destination next =>
        simp [execute, StepObservation.CursorAccounting, sampleCost, Nat.add_comm]

/-- The continuous-sample charge equals hidden cursor advancement on every halting trace. -/
theorem HaltingTrace.randomDraws_eq_cursorDifference
    {program : Program} {source : Source} {initial : Configuration}
    {memory : Memory} {result : ℝ} {cost : Cost} {steps draws : ℕ}
    (trace : HaltingTrace program source initial memory result cost steps draws) :
    cost.randomDraws + initial.randomCursor = draws := by
  induction trace with
  | @halt configuration memory result cost draws observes =>
      have accounting := step_cursorAccounting program source configuration
      rw [observes] at accounting
      exact accounting
  | @next configuration nextConfiguration memory result headCost tailCost steps draws
      observes tail induction =>
      have accounting := step_cursorAccounting program source configuration
      rw [observes] at accounting
      change headCost.randomDraws + configuration.randomCursor =
        nextConfiguration.randomCursor at accounting
      change headCost.randomDraws + tailCost.randomDraws +
        configuration.randomCursor = draws
      omega

/-- Stable metadata emphasizes that this is stronger than the fair-bit profile. -/
structure Profile where
  /-- Stable human-readable profile description. -/
  name : String

/-- Named sealed exact-uniform-real profile. -/
def profile : Profile :=
  ⟨"structured exact-real RAM with hidden lengthless exact-uniform-[0,1] source; " ++
    "one charged sampleUniform transition per sample; stronger than random-bit RAM"⟩

end Algolean.Algorithms.StructuredRealRAM.UniformReal
