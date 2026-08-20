/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Core
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# A structured exact-real RAM with hidden iid fair bits

This is a sealed randomized profile.  A realization of the random source is an infinite Boolean
sequence with the fixed iid fair product law.  The source and its cursor are semantic machine
state: neither is represented in ordinary memory, and the instruction language has no operation
that can inspect a tape length or cursor.  The only observation is one charged `randBit` draw.

Core structured-real-RAM instructions are embedded as closed syntax.  No evaluator, distribution,
or source-length schedule is supplied by an algorithm certificate.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.RandomBit

open MeasureTheory

/-- One realization of the hidden, lengthless source. -/
abbrev Source := ℕ → Bool

/-- The fixed fair law of one Boolean coordinate. -/
noncomputable def coordinateLaw : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure coordinateLaw := by
  unfold coordinateLaw
  infer_instance

/-- The fixed law of countably many independent fair bits. -/
noncomputable def sourceLaw : Measure Source :=
  Measure.infinitePi fun _ : ℕ ↦ coordinateLaw

instance : IsProbabilityMeasure sourceLaw := by
  unfold sourceLaw
  infer_instance

/-- Closed instructions for the random-bit profile. -/
inductive Instruction where
  /-- Execute one deterministic structured-real-RAM instruction. -/
  | core (instruction : StructuredRealRAM.Instruction)
  /-- Draw one hidden source bit and store `0` or `1` at the address held by a Nat register. -/
  | randBit (destinationRegister next : ℕ)
deriving DecidableEq, Repr

/-- One finite random-bit program. -/
abbrev Program := List Instruction

/-- Program counter, ordinary memory, and the hidden next-source coordinate. -/
structure Configuration where
  /-- Current instruction position. -/
  pc : ℕ
  /-- Ordinary program-visible memory. -/
  memory : StructuredRealRAM.Memory
  /-- Semantic cursor; no instruction can read it as ordinary machine data. -/
  randomCursor : ℕ

namespace Configuration

/-- Canonical entry state.  Only the ordinary memory is client-visible. -/
def initial (memory : StructuredRealRAM.Memory) : Configuration := ⟨0, memory, 0⟩

/-- Number of primitive samples consumed so far, exposed only to trace metatheory. -/
def randomDraws (configuration : Configuration) : ℕ := configuration.randomCursor

end Configuration

/-- Halt, continuation, or invalid-program-counter result of one transition. -/
inductive StepResult where
  | running (configuration : Configuration)
  | halted (memory : StructuredRealRAM.Memory) (result : ℝ) (randomDraws : ℕ)
  | stuck (configuration : Configuration)

/-- Fuel-bounded execution result. -/
inductive RunResult where
  | halted (memory : StructuredRealRAM.Memory) (result : ℝ) (randomDraws : ℕ)
  | outOfFuel (configuration : Configuration)
  | stuck (configuration : Configuration)

/-- Machine resources plus the charged primitive-draw count. -/
@[ext]
structure Cost where
  /-- All deterministic structured-real-RAM resource coordinates. -/
  machine : StructuredRealRAM.Cost
  /-- Number of charged primitive bit draws. -/
  randomDraws : ℕ
deriving DecidableEq

namespace Cost

instance : Zero Cost := ⟨⟨0, 0⟩⟩

instance : Add Cost := ⟨fun left right ↦
  ⟨left.machine + right.machine, left.randomDraws + right.randomDraws⟩⟩

instance : PartialOrder Cost where
  le left right := left.machine ≤ right.machine ∧ left.randomDraws ≤ right.randomDraws
  le_refl cost := ⟨le_rfl, le_rfl⟩
  le_trans left middle right leftMiddle middleRight :=
    ⟨le_trans leftMiddle.1 middleRight.1, le_trans leftMiddle.2 middleRight.2⟩
  le_antisymm left right leftRight rightLeft := by
    apply Cost.ext
    · exact le_antisymm leftRight.1 rightLeft.1
    · exact le_antisymm leftRight.2 rightLeft.2

/-- Lift a deterministic charge without adding a random draw. -/
def ofCore (cost : StructuredRealRAM.Cost) : Cost := ⟨cost, 0⟩

/-- Charge one fetched instruction, one Nat write, and one primitive draw. -/
def draw : Cost :=
  ⟨StructuredRealRAM.Cost.ofFields 1 0 0 0 0 0 1 0 0, 1⟩

/-- Fetched-instruction coordinate. -/
def steps (cost : Cost) : ℕ := cost.machine.steps

end Cost

/-- Operational result and resource charge returned by the same transition. -/
structure StepObservation where
  /-- Operational outcome. -/
  outcome : StepResult
  /-- Charge returned by the same transition. -/
  cost : Cost

/-- Fuel-bounded result, accumulated cost, and actual fetched transitions. -/
structure RunObservation where
  /-- Halt, timeout, or stuck outcome. -/
  outcome : RunResult
  /-- Accumulated same-trace resource charge. -/
  cost : Cost
  /-- Number of fetched transitions. -/
  steps : ℕ

namespace Instruction

/-- Numeric successors appearing in one closed instruction. -/
def successors : Instruction → List ℕ
  | .core instruction => instruction.successors
  | .randBit _ next => [next]

/-- Canonical binary encoding of one random-profile instruction. -/
def encode : Instruction → List Bool
  | .core instruction => false :: StructuredRealRAM.Program.encodeInstruction instruction
  | .randBit destination next =>
      true :: StructuredRealRAM.Program.encodeNat destination ++
        StructuredRealRAM.Program.encodeNat next

/-- Decode one instruction and return the unused suffix. -/
def decode : List Bool → Option (Instruction × List Bool)
  | false :: bits => do
      let (instruction, rest) ← StructuredRealRAM.Program.decodeInstruction bits
      pure (.core instruction, rest)
  | true :: bits => do
      let (destination, bits) ← StructuredRealRAM.Program.decodeNat bits
      let (next, rest) ← StructuredRealRAM.Program.decodeNat bits
      pure (.randBit destination next, rest)
  | [] => none

@[simp]
theorem decode_encode (instruction : Instruction) (rest : List Bool) :
    decode (encode instruction ++ rest) = some (instruction, rest) := by
  cases instruction <;>
    simp [encode, decode, StructuredRealRAM.Program.decodeInstruction_encode,
      List.append_assoc]

end Instruction

namespace Program

/-- Every successor remains inside the same finite program. -/
def Valid (program : Program) : Prop :=
  ∀ (pc : ℕ) (instruction : Instruction), program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

/-- Concatenated canonical instruction encoding. -/
def encodeInstructions : List Instruction → List Bool
  | [] => []
  | instruction :: instructions =>
      instruction.encode ++ encodeInstructions instructions

/-- Canonical self-delimiting finite program encoding. -/
def encode (program : Program) : List Bool :=
  StructuredRealRAM.Program.encodeNat program.length ++ encodeInstructions program

/-- Decode exactly `count` instructions. -/
def decodeInstructions : ℕ → List Bool → Option (List Instruction × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (instruction, bits) ← Instruction.decode bits
      let (instructions, rest) ← decodeInstructions count bits
      pure (instruction :: instructions, rest)

@[simp]
theorem decodeInstructions_encode (instructions : List Instruction) (rest : List Bool) :
    decodeInstructions instructions.length (encodeInstructions instructions ++ rest) =
      some (instructions, rest) := by
  induction instructions with
  | nil => rfl
  | cons instruction instructions induction =>
      simp [encodeInstructions, decodeInstructions, List.append_assoc, induction]

/-- Decode a complete canonical random-profile program serialization. -/
def decode (bits : List Bool) : Option Program := do
  let (count, bits) ← StructuredRealRAM.Program.decodeNat bits
  let (program, rest) ← decodeInstructions count bits
  if rest.isEmpty then some program else none

@[simp]
theorem decode_encode (program : Program) : decode (encode program) = some program := by
  simp only [decode, encode,
    StructuredRealRAM.Program.decodeNat_encode, Option.bind_eq_bind, Option.bind_some]
  have decoded : decodeInstructions program.length (encodeInstructions program) =
      some (program, []) := by
    simpa using decodeInstructions_encode program []
  rw [decoded]
  rfl

/-- Number of instructions, distinct from full finite description size. -/
def instructionCount (program : Program) : ℕ := program.length

/-- Full canonical binary description size, including tags, operands, and successors. -/
def descriptionSize (program : Program) : ℕ := program.encode.length

end Program

/-- Translate a deterministic core outcome while preserving the hidden cursor. -/
def liftCoreOutcome (cursor : ℕ) : StructuredRealRAM.StepResult → StepResult
  | .running configuration => .running ⟨configuration.pc, configuration.memory, cursor⟩
  | .halted memory result => .halted memory result cursor
  | .stuck configuration => .stuck ⟨configuration.pc, configuration.memory, cursor⟩

/-- Execute one fetched instruction against one fixed source realization. -/
noncomputable def execute (source : Source) (instruction : Instruction)
    (configuration : Configuration) : StepObservation :=
  match instruction with
  | .core coreInstruction =>
      let observation := StructuredRealRAM.execute coreInstruction configuration.memory
      ⟨liftCoreOutcome configuration.randomCursor observation.outcome,
        Cost.ofCore observation.cost⟩
  | .randBit destination next =>
      let value := if source configuration.randomCursor then 1 else 0
      let memory := configuration.memory.writeNat
        (configuration.memory.natReg destination) value
      ⟨.running ⟨next, memory, configuration.randomCursor + 1⟩, Cost.draw⟩

/-- Fetch and execute once; the source has no length and therefore no end-of-tape behavior. -/
noncomputable def step (program : Program) (source : Source)
    (configuration : Configuration) : StepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => execute source instruction configuration

/-- Run for at most `fuel` fetched instructions. -/
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

/-- One derivation coupling output, all resource coordinates, and random draws. -/
inductive HaltingTrace (program : Program) (source : Source) :
    Configuration → StructuredRealRAM.Memory → ℝ → Cost → ℕ → ℕ → Prop where
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

/-- Per-transition statement that the draw charge exactly tracks cursor advancement. -/
def StepObservation.CursorAccounting (observation : StepObservation)
    (initial : Configuration) : Prop :=
  match observation.outcome with
  | .running next => observation.cost.randomDraws + initial.randomCursor = next.randomCursor
  | .halted _ _ draws => observation.cost.randomDraws + initial.randomCursor = draws
  | .stuck _ => observation.cost.randomDraws = 0

/-- Every sealed transition accounts exactly for its hidden-source consumption. -/
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
            simp [StepObservation.CursorAccounting, liftCoreOutcome, Cost.ofCore]
    | randBit destination next =>
        simp [execute, StepObservation.CursorAccounting, Cost.draw, Nat.add_comm]

/-- The trace's random-draw coordinate equals its final cursor minus its initial cursor. -/
theorem HaltingTrace.randomDraws_eq_cursorDifference
    {program : Program} {source : Source} {initial : Configuration}
    {memory : StructuredRealRAM.Memory} {result : ℝ} {cost : Cost} {steps draws : ℕ}
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

/-- Stable profile metadata for audit reports. -/
structure Profile where
  /-- Stable human-readable profile description. -/
  name : String

/-- Hidden lengthless iid fair bits, with one charged draw per `randBit`. -/
def profile : Profile :=
  ⟨"structured exact-real RAM with hidden lengthless iid fair bits; one charged randBit " ++
    "transition per sample; random draws and output share one halting trace"⟩

end Algolean.Algorithms.StructuredRealRAM.RandomBit
