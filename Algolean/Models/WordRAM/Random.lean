/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.WordRAM.Profile
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fixed-width Word RAM with a hidden lengthless iid bit source

The source cursor is semantic state and is never stored in ordinary RAM memory.  Programs can
only consume the next bit through one closed instruction, so neither a finite tape length nor an
input-dependent draw schedule can carry advice.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.RandomBit

open MeasureTheory

abbrev Source := Nat → Bool

noncomputable def coordinateLaw : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coordinateLaw := by
  unfold coordinateLaw
  infer_instance

noncomputable def sourceLaw : Measure Source :=
  Measure.infinitePi fun _ : Nat ↦ coordinateLaw

instance : IsProbabilityMeasure sourceLaw := by
  unfold sourceLaw
  infer_instance

/-- Closed randomized profile syntax. -/
inductive Instruction (w : Nat) where
  | core (instruction : RAM.Instruction (BitVec w) (BitVec w) Empty)
  | randBit (destination : RAM.AddressOperand (BitVec w)) (next : Nat)

abbrev Program (w : Nat) := List (Instruction w)

namespace Instruction

def successors : Instruction w → List Nat
  | .core instruction => instruction.successors
  | .randBit _ next => [next]

def descriptionSize : Instruction w → Nat
  | .core instruction => 1 + instruction.descriptionSize (fun _ ↦ w) (fun _ ↦ w)
      (fun impossible : Empty ↦ nomatch impossible)
  | .randBit destination next =>
      1 + destination.descriptionSize (fun _ ↦ w) + RAM.natDescriptionSize next

end Instruction

namespace Program

def Valid (program : Program w) : Prop :=
  ∀ (pc : Nat) (instruction : Instruction w), program[pc]? = some instruction →
    ∀ target ∈ Instruction.successors instruction, target < program.length

def descriptionSize (program : Program w) : Nat :=
  RAM.natDescriptionSize program.length + (program.map Instruction.descriptionSize).sum

end Program

structure Configuration (w : Nat) where
  pc : Nat
  memory : WordRAM.Memory w
  randomCursor : Nat

def Configuration.initial (memory : WordRAM.Memory w) : Configuration w := ⟨0, memory, 0⟩

inductive StepResult (w : Nat) where
  | running (configuration : Configuration w)
  | halted (memory : WordRAM.Memory w) (result : BitVec w) (randomDraws : Nat)
  | stuck (configuration : Configuration w)

@[ext]
structure Cost where
  steps : Nat
  randomDraws : Nat
deriving DecidableEq

namespace Cost

instance : Zero Cost := ⟨0, 0⟩
instance : Add Cost := ⟨fun left right ↦
  ⟨left.steps + right.steps, left.randomDraws + right.randomDraws⟩⟩

instance : LE Cost := ⟨fun left right ↦
  left.steps ≤ right.steps ∧ left.randomDraws ≤ right.randomDraws⟩

def core : Cost := ⟨1, 0⟩
def draw : Cost := ⟨1, 1⟩

end Cost

structure StepObservation (w : Nat) where
  outcome : StepResult w
  cost : Cost

/-- Execute one fetched closed instruction against one infinite source realization. -/
def execute (source : Source) (instruction : Instruction w)
    (configuration : Configuration w) : StepObservation w :=
  match instruction with
  | .core instruction =>
      match RAM.execute (WordRAM.ops w) RAM.noExtra instruction configuration.memory with
      | .running next => ⟨.running ⟨next.pc, next.memory, configuration.randomCursor⟩, .core⟩
      | .halted memory result =>
          ⟨.halted memory result configuration.randomCursor, .core⟩
      | .stuck _ => ⟨.stuck configuration, .core⟩
  | .randBit destination next =>
      let bit : BitVec w := if source configuration.randomCursor then 1 else 0
      let address := destination.eval configuration.memory
      ⟨.running ⟨next, configuration.memory.write address bit,
        configuration.randomCursor + 1⟩, .draw⟩

def step (program : Program w) (source : Source)
    (configuration : Configuration w) : StepObservation w :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => execute source instruction configuration

/-- Raw same-trace termination derivation. -/
inductive RawHaltingTrace (program : Program w) (source : Source) :
    Configuration w → WordRAM.Memory w → BitVec w → Nat → Cost → Prop where
  | halt {configuration memory result draws cost}
      (observed : step program source configuration =
        ⟨.halted memory result draws, cost⟩) :
      RawHaltingTrace program source configuration memory result draws cost
  | next {configuration nextConfiguration memory result draws headCost tailCost}
      (observed : step program source configuration =
        ⟨.running nextConfiguration, headCost⟩)
      (tail : RawHaltingTrace program source nextConfiguration memory result draws tailCost) :
      RawHaltingTrace program source configuration memory result draws (headCost + tailCost)

/--
Published traces package the raw operational derivation with its cursor-accounting invariant.
The invariant is proof data only; the cursor remains absent from program-visible memory.
-/
structure HaltingTrace (program : Program w) (source : Source)
    (initial : Configuration w) (final : WordRAM.Memory w)
    (result : BitVec w) (draws : Nat) (cost : Cost) where
  operational : RawHaltingTrace program source initial final result draws cost
  cursorAccounting : cost.randomDraws + initial.randomCursor = draws

/-- Every trace reports exactly the increase in the hidden cursor. -/
theorem HaltingTrace.randomDraws_eq_cursor
    (trace : HaltingTrace program source initial final result draws cost) :
    cost.randomDraws + initial.randomCursor = draws :=
  trace.cursorAccounting

end Algolean.Algorithms.WordRAM.RandomBit
