/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM.Costed

/-!
# A structured exact-real RAM

This is a new profile rather than a change to the existing `RealRAM.Program`.  It has two
random-access banks: exact reals for continuous data and naturals for lengths, indices, tags, and
addresses.  Natural registers supply indirect addresses for both banks.  The instruction syntax
is closed; there is no arbitrary extension callback at the public algorithm-claim boundary.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Exact-real and natural random-access memory, plus a small natural register bank. -/
structure Memory where
  /-- Exact-real data cells. -/
  realMem : ℕ → ℝ
  /-- Discrete data cells: lengths, tags, endpoints, offsets, and indices. -/
  natMem : ℕ → ℕ
  /-- Natural registers used for addresses and loop indices. -/
  natReg : ℕ → ℕ

namespace Memory

/-- Canonical all-zero memory. -/
noncomputable def empty : Memory := ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0⟩

/-- Write one exact-real cell. -/
noncomputable def writeReal (memory : Memory) (address : ℕ) (value : ℝ) : Memory :=
  { memory with realMem := Function.update memory.realMem address value }

/-- Write one natural cell. -/
def writeNat (memory : Memory) (address value : ℕ) : Memory :=
  { memory with natMem := Function.update memory.natMem address value }

/-- Write one natural register. -/
def writeReg (memory : Memory) (register value : ℕ) : Memory :=
  { memory with natReg := Function.update memory.natReg register value }

@[simp] theorem empty_realMem (address : ℕ) : empty.realMem address = 0 := rfl
@[simp] theorem empty_natMem (address : ℕ) : empty.natMem address = 0 := rfl
@[simp] theorem empty_natReg (register : ℕ) : empty.natReg register = 0 := rfl

@[simp] theorem writeReal_same (memory : Memory) (address : ℕ) (value : ℝ) :
    (memory.writeReal address value).realMem address = value := by
  simp [writeReal]

@[simp] theorem writeNat_same (memory : Memory) (address value : ℕ) :
    (memory.writeNat address value).natMem address = value := by
  simp [writeNat]

@[simp] theorem writeReg_same (memory : Memory) (register value : ℕ) :
    (memory.writeReg register value).natReg register = value := by
  simp [writeReg]

end Memory

/-- A rational literal or an indirect exact-real memory read. -/
inductive RealOperand where
  | literal (value : ℚ)
  | load (addressRegister : ℕ)
deriving DecidableEq, Repr

/-- A natural literal, register read, or indirect natural-memory read. -/
inductive NatOperand where
  | literal (value : ℕ)
  | reg (register : ℕ)
  | load (addressRegister : ℕ)
deriving DecidableEq, Repr

namespace RealOperand

/-- Evaluate a real operand. -/
noncomputable def eval (memory : Memory) : RealOperand → ℝ
  | .literal value => value
  | .load register => memory.realMem (memory.natReg register)

/-- Number of random-access real reads performed by an operand. -/
def reads : RealOperand → ℕ
  | .literal _ => 0
  | .load _ => 1

end RealOperand

namespace NatOperand

/-- Evaluate a natural operand. -/
def eval (memory : Memory) : NatOperand → ℕ
  | .literal value => value
  | .reg register => memory.natReg register
  | .load register => memory.natMem (memory.natReg register)

/-- Number of random-access natural-memory reads performed by an operand. -/
def reads : NatOperand → ℕ
  | .literal _ | .reg _ => 0
  | .load _ => 1

end NatOperand

/--
Closed core instructions for the structured real RAM.

Every non-halting instruction contains its numeric successor.  Backward successors provide
runtime loops in one fixed finite program.
-/
inductive Instruction where
  | rset (source : RealOperand) (destinationRegister next : ℕ)
  | radd (left right : RealOperand) (destinationRegister next : ℕ)
  | rsub (left right : RealOperand) (destinationRegister next : ℕ)
  | rmul (left right : RealOperand) (destinationRegister next : ℕ)
  | rdiv (left right : RealOperand) (destinationRegister next : ℕ)
  | rneg (source : RealOperand) (destinationRegister next : ℕ)
  | nset (source : NatOperand) (destinationRegister next : ℕ)
  | nadd (left right : NatOperand) (destinationRegister next : ℕ)
  | nsub (left right : NatOperand) (destinationRegister next : ℕ)
  | nload (addressRegister destinationRegister next : ℕ)
  | nstore (source : NatOperand) (addressRegister next : ℕ)
  | rcompare (left right : RealOperand) (less equal greater : ℕ)
  | ncompare (left right : NatOperand) (less equal greater : ℕ)
  | jump (target : ℕ)
  | halt (result : RealOperand)
deriving DecidableEq, Repr

/-- One fixed structured-real-RAM program is an ordinary finite instruction list. -/
abbrev Program := List Instruction

/-- Program counter and private structured memory. -/
structure Configuration where
  /-- Numeric program counter. -/
  pc : ℕ
  /-- Current two-bank memory. -/
  memory : Memory

/-- Result of one structured-real-RAM transition. -/
inductive StepResult where
  | running (configuration : Configuration)
  | halted (memory : Memory) (result : ℝ)
  | stuck (configuration : Configuration)

/-- Result of observing at most a fixed number of transitions. -/
inductive RunResult where
  | halted (memory : Memory) (result : ℝ)
  | outOfFuel (configuration : Configuration)
  | stuck (configuration : Configuration)

/-- Return the scalar halt result of a completed run. -/
def RunResult.output? : RunResult → Option ℝ
  | .halted _ result => some result
  | .outOfFuel _ | .stuck _ => none

/-- A nine-coordinate resource vector.  The inherited order and addition are pointwise. -/
abbrev Cost := Fin 9 → ℕ

namespace Cost

/-- Construct a named structured-real-RAM resource vector. -/
def ofFields (steps realReads realWrites realArithmetic realComparisons
    natReads natWrites natArithmetic natComparisons : ℕ) : Cost :=
  ![steps, realReads, realWrites, realArithmetic, realComparisons,
    natReads, natWrites, natArithmetic, natComparisons]

/-- Fetched instruction count. -/
def steps (cost : Cost) : ℕ := cost 0
/-- Random-access exact-real reads. -/
def realReads (cost : Cost) : ℕ := cost 1
/-- Random-access exact-real writes. -/
def realWrites (cost : Cost) : ℕ := cost 2
/-- Exact-real arithmetic operations. -/
def realArithmetic (cost : Cost) : ℕ := cost 3
/-- Exact-real comparisons. -/
def realComparisons (cost : Cost) : ℕ := cost 4
/-- Random-access natural-memory reads. -/
def natReads (cost : Cost) : ℕ := cost 5
/-- Random-access natural-memory writes. -/
def natWrites (cost : Cost) : ℕ := cost 6
/-- Natural arithmetic operations. -/
def natArithmetic (cost : Cost) : ℕ := cost 7
/-- Natural comparisons. -/
def natComparisons (cost : Cost) : ℕ := cost 8

/-- A fetched control-flow instruction with no additional operation. -/
def control : Cost := ofFields 1 0 0 0 0 0 0 0 0

end Cost

/-- The result and charged resources of the same transition. -/
structure StepObservation where
  /-- Operational effect of the transition. -/
  outcome : StepResult
  /-- Resources charged by this transition. -/
  cost : Cost

/-- Result, accumulated resources, and actual transition count of a fuel-bounded execution. -/
structure RunObservation where
  /-- Halt, timeout, or stuck outcome. -/
  outcome : RunResult
  /-- Accumulated transition costs. -/
  cost : Cost
  /-- Number of transitions actually observed. -/
  steps : ℕ

namespace Instruction

/-- All numeric successors stored in an instruction. -/
def successors : Instruction → List ℕ
  | .rset _ _ next | .radd _ _ _ next | .rsub _ _ _ next | .rmul _ _ _ next
  | .rdiv _ _ _ next | .rneg _ _ next | .nset _ _ next | .nadd _ _ _ next
  | .nsub _ _ _ next | .nload _ _ next | .nstore _ _ next => [next]
  | .rcompare _ _ less equal greater | .ncompare _ _ less equal greater =>
      [less, equal, greater]
  | .jump target => [target]
  | .halt _ => []

/-- Resource charge of a fetched instruction. -/
def cost : Instruction → Cost
  | .rset source _ _ => Cost.ofFields 1 source.reads 1 0 0 0 0 0 0
  | .radd left right _ _ | .rsub left right _ _ | .rmul left right _ _
  | .rdiv left right _ _ =>
      Cost.ofFields 1 (left.reads + right.reads) 1 1 0 0 0 0 0
  | .rneg source _ _ => Cost.ofFields 1 source.reads 1 1 0 0 0 0 0
  | .nset source _ _ => Cost.ofFields 1 0 0 0 0 source.reads 0 0 0
  | .nadd left right _ _ | .nsub left right _ _ =>
      Cost.ofFields 1 0 0 0 0 (left.reads + right.reads) 0 1 0
  | .nload _ _ _ => Cost.ofFields 1 0 0 0 0 1 0 0 0
  | .nstore source _ _ => Cost.ofFields 1 0 0 0 0 source.reads 1 0 0
  | .rcompare left right _ _ _ =>
      Cost.ofFields 1 (left.reads + right.reads) 0 0 1 0 0 0 0
  | .ncompare left right _ _ _ =>
      Cost.ofFields 1 0 0 0 0 (left.reads + right.reads) 0 0 1
  | .jump _ => Cost.control
  | .halt result => Cost.ofFields 1 result.reads 0 0 0 0 0 0 0

end Instruction

namespace Program

/-- Every stored successor is a valid program counter. -/
def Valid (program : Program) : Prop :=
  ∀ (pc : ℕ) (instruction : Instruction), program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

end Program

/-- Select one of three numeric successors. -/
def branch (ordering : Ordering) (less equal greater : ℕ) : ℕ :=
  match ordering with
  | .lt => less
  | .eq => equal
  | .gt => greater

/-- Execute one already-fetched instruction and return its behavior and charge together. -/
noncomputable def execute (instruction : Instruction) (memory : Memory) : StepObservation :=
  let real := RealOperand.eval memory
  let nat := NatOperand.eval memory
  let run next memory := StepResult.running ⟨next, memory⟩
  let writeReal source destination next :=
    run next (memory.writeReal (memory.natReg destination) source)
  let writeReg source destination next := run next (memory.writeReg destination source)
  let outcome :=
    match instruction with
    | .rset source destination next => writeReal (real source) destination next
    | .radd left right destination next => writeReal (real left + real right) destination next
    | .rsub left right destination next => writeReal (real left - real right) destination next
    | .rmul left right destination next => writeReal (real left * real right) destination next
    | .rdiv left right destination next => writeReal (real left / real right) destination next
    | .rneg source destination next => writeReal (-real source) destination next
    | .nset source destination next => writeReg (nat source) destination next
    | .nadd left right destination next => writeReg (nat left + nat right) destination next
    | .nsub left right destination next => writeReg (nat left - nat right) destination next
    | .nload address destination next =>
        writeReg (memory.natMem (memory.natReg address)) destination next
    | .nstore source address next =>
        run next (memory.writeNat (memory.natReg address) (nat source))
    | .rcompare left right less equal greater =>
        run (branch (if real left < real right then .lt else if real left = real right then .eq
          else .gt) less equal greater) memory
    | .ncompare left right less equal greater =>
        run (branch (if nat left < nat right then .lt else if nat left = nat right then .eq
          else .gt) less equal greater) memory
    | .jump target => run target memory
    | .halt result => .halted memory (real result)
  ⟨outcome, instruction.cost⟩

/-- Fetch and execute once, getting stuck at an invalid program counter. -/
noncomputable def step (program : Program) (configuration : Configuration) : StepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => execute instruction configuration.memory

/-- Run at most `fuel` instructions, accumulating the costs returned by those instructions. -/
noncomputable def runFor (program : Program) : ℕ → Configuration → RunObservation
  | 0, configuration => ⟨.outOfFuel configuration, 0, 0⟩
  | fuel + 1, configuration =>
      let observation := step program configuration
      match observation.outcome with
      | .running next =>
          let rest := runFor program fuel next
          ⟨rest.outcome, observation.cost + rest.cost, rest.steps + 1⟩
      | .halted memory result => ⟨.halted memory result, observation.cost, 1⟩
      | .stuck stuck => ⟨.stuck stuck, observation.cost, 1⟩

/-- Run from program counter zero and a supplied initial memory. -/
noncomputable def runFromMemoryFor (program : Program) (fuel : ℕ)
    (memory : Memory) : RunObservation :=
  runFor program fuel ⟨0, memory⟩

/--
A halting trace coupling final memory, result, resource vector, and transition count.
-/
inductive HaltingTrace (program : Program) :
    Configuration → Memory → ℝ → Cost → ℕ → Prop where
  | halt {configuration memory result cost}
      (observes : step program configuration = ⟨.halted memory result, cost⟩) :
      HaltingTrace program configuration memory result cost 1
  | next {configuration nextConfiguration memory result headCost tailCost steps}
      (observes : step program configuration = ⟨.running nextConfiguration, headCost⟩)
      (tail : HaltingTrace program nextConfiguration memory result tailCost steps) :
      HaltingTrace program configuration memory result (headCost + tailCost) (steps + 1)

/-- The sealed public profile used by fixed structured real-RAM claims. -/
structure Profile where
  /-- Stable human-readable profile identifier. -/
  name : String

/-- Core exact-real arithmetic, two memory banks, and no extensions or oracles. -/
def coreProfile : Profile := ⟨"Algolean.StructuredRealRAM.Core"⟩

end Algolean.Algorithms.StructuredRealRAM
