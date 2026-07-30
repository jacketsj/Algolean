/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM

/-!
# Random-access machines

A RAM program is a finite list of instructions with numeric jump targets. Backward jumps give one
fixed program runtime-dependent loops. The same small semantics below instantiates integer RAM,
word RAM, and real RAM.

Data and addresses have separate types. This is immaterial for integer and word RAMs, and avoids
giving the real RAM an implicit floor or real-to-natural operation. Each instruction costs one
step. Inputs are pre-encoded memories. `Models.RealRAM.Extensions` supplies typed source
instructions for the existing optional real operations.
-/

@[expose] public section

namespace Algolean.Algorithms

namespace RAM

/-- The arithmetic needed to interpret RAM instructions. -/
structure Ops (Literal Value Address : Type*) where
  /-- Interpret a source literal. -/
  value : Literal → Value
  /-- Value addition. -/
  add : Value → Value → Value
  /-- Value subtraction. -/
  sub : Value → Value → Value
  /-- Value multiplication. -/
  mul : Value → Value → Value
  /-- Totalized value division. -/
  div : Value → Value → Value
  /-- Value negation. -/
  neg : Value → Value
  /-- Three-way value comparison. -/
  compare : Value → Value → Ordering
  /-- Address addition. -/
  addressAdd : Address → Address → Address
  /-- Address subtraction. -/
  addressSub : Address → Address → Address
  /-- Three-way address comparison. -/
  addressCompare : Address → Address → Ordering

/-- Data memory and a separate bank of address registers. -/
structure Memory (Value Address : Type*) where
  /-- Random-access data cells. -/
  data : Address → Value
  /-- Registers used for indirect addresses and loop indices. -/
  address : ℕ → Address

/-- A literal address or the contents of an address register. -/
inductive AddressOperand (Address : Type*) where
  | immediate (address : Address)
  | reg (register : ℕ)

/-- A literal value or a data-memory read. -/
inductive Operand (Literal Address : Type*) where
  | immediate (value : Literal)
  | load (address : AddressOperand Address)

/-- Uniform RAM instructions. Every non-halting instruction stores its successor counter. -/
inductive Instruction (Literal Address Extra : Type*) where
  | set (source : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | add (left right : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | sub (left right : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | mul (left right : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | div (left right : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | neg (source : Operand Literal Address) (destination : AddressOperand Address) (next : ℕ)
  | setAddress (source : AddressOperand Address) (destination next : ℕ)
  | addAddress (left right : AddressOperand Address) (destination next : ℕ)
  | subAddress (left right : AddressOperand Address) (destination next : ℕ)
  | compare (left right : Operand Literal Address) (less equal greater : ℕ)
  | compareAddress (left right : AddressOperand Address) (less equal greater : ℕ)
  | extra (instruction : Extra) (next : ℕ)
  | halt (result : Operand Literal Address)

/-- A RAM program is ordinary finite code; jumps, including backward jumps, are program counters. -/
abbrev Program (Literal Address Extra : Type*) := List (Instruction Literal Address Extra)

/-- Program counter and private memory. -/
structure Configuration (Value Address : Type*) where
  /-- Program counter. -/
  pc : ℕ
  /-- Current memory. -/
  memory : Memory Value Address

/-- The result of one machine step. -/
inductive StepResult (Value Address : Type*) where
  | running (configuration : Configuration Value Address)
  | halted (memory : Memory Value Address) (result : Value)
  | stuck (configuration : Configuration Value Address)

/-- The result of observing at most a fixed number of steps. -/
inductive RunResult (Value Address : Type*) where
  | halted (memory : Memory Value Address) (result : Value)
  | outOfFuel (configuration : Configuration Value Address)
  | stuck (configuration : Configuration Value Address)

/-- Return the output of a halted run. -/
def RunResult.output? : RunResult Value Address → Option Value
  | .halted _ result => some result
  | .outOfFuel _ | .stuck _ => none

/-- Evaluate an immediate address or address-register read. -/
def AddressOperand.eval (memory : Memory Value Address) : AddressOperand Address → Address
  | .immediate address => address
  | .reg register => memory.address register

/-- Evaluate a literal or data-memory read. -/
def Operand.eval (ops : Ops Literal Value Address) (memory : Memory Value Address) :
    Operand Literal Address → Value
  | .immediate value => ops.value value
  | .load address => memory.data (address.eval memory)

/-- Write one data cell. -/
def Memory.write [DecidableEq Address]
    (memory : Memory Value Address) (address : Address) (value : Value) :
    Memory Value Address :=
  { memory with data := Function.update memory.data address value }

/-- Write one address register. -/
def Memory.writeAddress (memory : Memory Value Address) (register : ℕ) (address : Address) :
    Memory Value Address :=
  { memory with address := Function.update memory.address register address }

/-- Select a comparison successor. -/
def branch (ordering : Ordering) (less equal greater : ℕ) : ℕ :=
  match ordering with
  | .lt => less
  | .eq => equal
  | .gt => greater

/-- Execute one fetched instruction. -/
def execute [DecidableEq Address] (ops : Ops Literal Value Address)
    (extra : Extra → Memory Value Address → Memory Value Address)
    (instruction : Instruction Literal Address Extra) (memory : Memory Value Address) :
    StepResult Value Address :=
  let value := Operand.eval ops memory
  let address := AddressOperand.eval memory
  let write source destination next :=
    .running ⟨next, memory.write (address destination) source⟩
  match instruction with
  | .set source destination next => write (value source) destination next
  | .add left right destination next => write (ops.add (value left) (value right)) destination next
  | .sub left right destination next => write (ops.sub (value left) (value right)) destination next
  | .mul left right destination next => write (ops.mul (value left) (value right)) destination next
  | .div left right destination next => write (ops.div (value left) (value right)) destination next
  | .neg source destination next => write (ops.neg (value source)) destination next
  | .setAddress source destination next =>
      .running ⟨next, memory.writeAddress destination (address source)⟩
  | .addAddress left right destination next =>
      .running ⟨next, memory.writeAddress destination
        (ops.addressAdd (address left) (address right))⟩
  | .subAddress left right destination next =>
      .running ⟨next, memory.writeAddress destination
        (ops.addressSub (address left) (address right))⟩
  | .compare left right less equal greater =>
      .running ⟨branch (ops.compare (value left) (value right)) less equal greater, memory⟩
  | .compareAddress left right less equal greater =>
      .running ⟨branch (ops.addressCompare (address left) (address right))
        less equal greater, memory⟩
  | .extra instruction next => .running ⟨next, extra instruction memory⟩
  | .halt result => .halted memory (value result)

/-- Fetch and execute one instruction, getting stuck at an invalid program counter. -/
def step [DecidableEq Address]
    (ops : Ops Literal Value Address) (extra : Extra → Memory Value Address → Memory Value Address)
    (program : Program Literal Address Extra)
    (configuration : Configuration Value Address) : StepResult Value Address :=
  match program[configuration.pc]? with
  | none => .stuck configuration
  | some instruction => execute ops extra instruction configuration.memory

/-- Run at most `fuel` instructions. Fuel observes a program; it is not part of the program. -/
def runFor [DecidableEq Address]
    (ops : Ops Literal Value Address) (extra : Extra → Memory Value Address → Memory Value Address)
    (program : Program Literal Address Extra) :
    ℕ → Configuration Value Address → RunResult Value Address
  | 0, configuration => .outOfFuel configuration
  | fuel + 1, configuration =>
      match step ops extra program configuration with
      | .running configuration => runFor ops extra program fuel configuration
      | .halted memory result => .halted memory result
      | .stuck configuration => .stuck configuration

/-- Unbounded, reflexive-transitive execution semantics. -/
inductive Reaches [DecidableEq Address]
    (ops : Ops Literal Value Address) (extra : Extra → Memory Value Address → Memory Value Address)
    (program : Program Literal Address Extra) :
    StepResult Value Address → StepResult Value Address → Prop where
  | refl (result) : Reaches ops extra program result result
  | tail {configuration result final}
      (step : RAM.step ops extra program configuration = result)
      (rest : Reaches ops extra program result final) :
      Reaches ops extra program (.running configuration) final

/-- The unique interpreter for a machine with no extension instructions. -/
def noExtra (instruction : Empty) : Memory Value Address → Memory Value Address :=
  nomatch instruction

/-- Combine two independently selected extension instruction sets. -/
def sumExtra
    (left : E₁ → Memory Value Address → Memory Value Address)
    (right : E₂ → Memory Value Address → Memory Value Address) :
    E₁ ⊕ E₂ → Memory Value Address → Memory Value Address
  | .inl instruction => left instruction
  | .inr instruction => right instruction

end RAM

namespace IntegerRAM

/-- Integer-RAM programs use signed literals and data, with natural addresses. -/
abbrev Program := RAM.Program ℤ ℕ Empty
/-- Integer-RAM memory. -/
abbrev Memory := RAM.Memory ℤ ℕ
/-- Integer-RAM runtime configuration. -/
abbrev Configuration := RAM.Configuration ℤ ℕ
/-- Integer-RAM execution result. -/
abbrev RunResult := RAM.RunResult ℤ ℕ

/-- Unit-cost unbounded signed-integer arithmetic. -/
def ops : RAM.Ops ℤ ℤ ℕ where
  value := id
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := (- ·)
  compare x y := if x < y then .lt else if x = y then .eq else .gt
  addressAdd := (· + ·)
  addressSub := (· - ·)
  addressCompare x y := if x < y then .lt else if x = y then .eq else .gt

/-- Run an integer-RAM program for at most `fuel` instructions. -/
def runFor (program : Program) (fuel : ℕ) (memory : Memory) : RunResult :=
  RAM.runFor ops RAM.noExtra program fuel ⟨0, memory⟩

end IntegerRAM

namespace WordRAM

/-- `w`-bit word-RAM programs. Data, literals, and addresses all wrap at `w` bits. -/
abbrev Program (w : ℕ) := RAM.Program (BitVec w) (BitVec w) Empty
/-- `w`-bit word-RAM memory. -/
abbrev Memory (w : ℕ) := RAM.Memory (BitVec w) (BitVec w)
/-- `w`-bit word-RAM runtime configuration. -/
abbrev Configuration (w : ℕ) := RAM.Configuration (BitVec w) (BitVec w)
/-- `w`-bit word-RAM execution result. -/
abbrev RunResult (w : ℕ) := RAM.RunResult (BitVec w) (BitVec w)

/-- Unit-cost unsigned modular word operations. -/
def ops (w : ℕ) : RAM.Ops (BitVec w) (BitVec w) (BitVec w) where
  value := id
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg x := 0 - x
  compare x y := if x.toNat < y.toNat then .lt else if x = y then .eq else .gt
  addressAdd := (· + ·)
  addressSub := (· - ·)
  addressCompare x y := if x.toNat < y.toNat then .lt else if x = y then .eq else .gt

/-- Run a word-RAM program for at most `fuel` instructions. -/
def runFor (program : Program w) (fuel : ℕ) (memory : Memory w) : RunResult w :=
  RAM.runFor (ops w) RAM.noExtra program fuel ⟨0, memory⟩

end WordRAM

namespace RealRAM

/-- Real-RAM programs have rational literals, exact-real data, and natural addresses. -/
abbrev Program (Extra : Type := Empty) := RAM.Program ℚ ℕ Extra
/-- Exact-real data memory with natural address registers. -/
abbrev MachineMemory := RAM.Memory ℝ ℕ
/-- Real-RAM runtime configuration. -/
abbrev Configuration := RAM.Configuration ℝ ℕ
/-- Real-RAM execution result. -/
abbrev RunResult := RAM.RunResult ℝ ℕ

/-- Source syntax for a unary real-RAM extension instruction, distinguished by `Tag`. -/
structure UnaryInstruction (Tag : Type → Type) where
  /-- Source operand. -/
  source : RAM.Operand ℚ ℕ
  /-- Destination data address. -/
  destination : RAM.AddressOperand ℕ

/-- Source syntax for a binary real-RAM extension instruction, distinguished by `Tag`. -/
structure BinaryInstruction (Tag : Type → Type) where
  /-- Left source operand. -/
  left : RAM.Operand ℚ ℕ
  /-- Right source operand. -/
  right : RAM.Operand ℚ ℕ
  /-- Destination data address. -/
  destination : RAM.AddressOperand ℕ

/-- Source syntax for an arbitrary-degree root instruction, distinguished by `Tag`. -/
structure NthRootInstruction (Tag : Type → Type) where
  /-- Root degree stored in source code. -/
  degree : ℕ
  /-- Radicand operand. -/
  source : RAM.Operand ℚ ℕ
  /-- Destination data address. -/
  destination : RAM.AddressOperand ℕ

/-- Unit-cost exact-real arithmetic with no real-to-natural conversion. -/
noncomputable def ops : RAM.Ops ℚ ℝ ℕ where
  value := (↑)
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := (- ·)
  compare x y := if x < y then .lt else if x = y then .eq else .gt
  addressAdd := (· + ·)
  addressSub := (· - ·)
  addressCompare x y := if x < y then .lt else if x = y then .eq else .gt

/-- Interpret a unary extension instruction. -/
noncomputable def evalUnary (operation : ℝ → ℝ) :
    UnaryInstruction Tag → MachineMemory → MachineMemory
  | ⟨source, destination⟩, memory =>
      memory.write (destination.eval memory) (operation (source.eval ops memory))

/-- Interpret a binary extension instruction. -/
noncomputable def evalBinary (operation : ℝ → ℝ → ℝ) :
    BinaryInstruction Tag → MachineMemory → MachineMemory
  | ⟨left, right, destination⟩, memory =>
      memory.write (destination.eval memory)
        (operation (left.eval ops memory) (right.eval ops memory))

/-- Interpret an arbitrary-degree root instruction. -/
noncomputable def evalNthRoot (operation : ℕ → ℝ → ℝ) :
    NthRootInstruction Tag → MachineMemory → MachineMemory
  | ⟨degree, source, destination⟩, memory =>
      memory.write (destination.eval memory) (operation degree (source.eval ops memory))

/-- Run a real-RAM program for at most `fuel` instructions. -/
noncomputable def runForExtra
    (extra : Extra → MachineMemory → MachineMemory)
    (program : Program Extra) (fuel : ℕ) (memory : MachineMemory) : RunResult :=
  RAM.runFor ops extra program fuel ⟨0, memory⟩

/-- Run a real RAM extended by one unary operation. -/
noncomputable def runUnaryFor (operation : ℝ → ℝ)
    (program : Program (UnaryInstruction Tag)) (fuel : ℕ)
    (memory : MachineMemory) : RunResult :=
  runForExtra (evalUnary operation) program fuel memory

/-- Run a real RAM extended by one binary operation. -/
noncomputable def runBinaryFor (operation : ℝ → ℝ → ℝ)
    (program : Program (BinaryInstruction Tag)) (fuel : ℕ)
    (memory : MachineMemory) : RunResult :=
  runForExtra (evalBinary operation) program fuel memory

/-- Run a real RAM extended by an arbitrary-degree root operation. -/
noncomputable def runNthRootFor (operation : ℕ → ℝ → ℝ)
    (program : Program (NthRootInstruction Tag)) (fuel : ℕ)
    (memory : MachineMemory) : RunResult :=
  runForExtra (evalNthRoot operation) program fuel memory

/-- Run a core real-RAM program for at most `fuel` instructions. -/
noncomputable def runFor (program : Program) (fuel : ℕ) (memory : MachineMemory) : RunResult :=
  runForExtra RAM.noExtra program fuel memory

end RealRAM

end Algolean.Algorithms
