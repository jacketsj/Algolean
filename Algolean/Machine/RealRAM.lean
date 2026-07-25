/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Machine
public import Algolean.Models.RealRAM

/-!
# Address-level real-RAM machine code

`RealRAM` queries carry runtime real values. This module supplies the corresponding first-order
address language: source instructions contain only register addresses and rational literals.
Lowering emits every memory access and arithmetic operation as an ordinary `RealRAM` query.

The standard `Query` takes an already encoded `RealRAM.Memory` as input. Its initialization query
therefore has zero cost; constructing that memory is outside this machine's cost contract. Clients
whose input has another representation should define their own `Machine.Query` and charged
initializer while reusing `lowerInstruction`, `lowerCompare`, and `lowerFinish`.

One source instruction need not have unit cost. For example, `add` lowers to two reads, one
addition, and one write.
-/

@[expose] public section

namespace Algolean.Algorithms.RealRAMMachine

open Cslib Machine

/-- Address-level instructions with one successor. -/
inductive Instruction where
  /-- Store an audited rational literal in one register. -/
  | constant (value : ℚ) (destination : ℕ)
  | copy (source destination : ℕ)
  | add (left right destination : ℕ)
  | sub (left right destination : ℕ)
  | mul (left right destination : ℕ)
  | div (left right destination : ℕ)
  | neg (source destination : ℕ)

/-- Address-level three-way comparison. -/
inductive Compare where
  | compare (left right : ℕ)

/-- Core deterministic real-RAM source language. -/
abbrev language : Machine.Language where
  Next := Instruction
  Choose2 := Empty
  Choose3 := Compare

/-- Core real-RAM programs return the contents of one statically named address. -/
abbrev Program := Machine.Program language ℕ

/-- Recorded operations for a core real-RAM program with pre-encoded memory input. -/
abbrev Query : Type → Type :=
  Machine.Query language RealRAM.Memory ℕ RealRAM.Memory ℝ

/-- Lift one primitive query into a real-RAM program. -/
def liftReal (query : RealRAM α) : Prog RealRAM α :=
  FreeM.lift query

/-- Lower one address-level instruction to primitive real-RAM queries. -/
def lowerInstruction : Instruction → RealRAM.Memory → Prog RealRAM RealRAM.Memory
  | .constant value destination, memory =>
      liftReal (.write memory destination value)
  | .copy source destination, memory => do
      let value ← liftReal (.read memory source)
      liftReal (.write memory destination value)
  | .add left right destination, memory => do
      let x ← liftReal (.read memory left)
      let y ← liftReal (.read memory right)
      let value ← liftReal (.add x y)
      liftReal (.write memory destination value)
  | .sub left right destination, memory => do
      let x ← liftReal (.read memory left)
      let y ← liftReal (.read memory right)
      let value ← liftReal (.sub x y)
      liftReal (.write memory destination value)
  | .mul left right destination, memory => do
      let x ← liftReal (.read memory left)
      let y ← liftReal (.read memory right)
      let value ← liftReal (.mul x y)
      liftReal (.write memory destination value)
  | .div left right destination, memory => do
      let x ← liftReal (.read memory left)
      let y ← liftReal (.read memory right)
      let value ← liftReal (.div x y)
      liftReal (.write memory destination value)
  | .neg source destination, memory => do
      let x ← liftReal (.read memory source)
      let value ← liftReal (.neg x)
      liftReal (.write memory destination value)

/-- Convert the primitive comparison result to a source branch status. -/
def choiceOfOrdering : Ordering → Machine.Choice3
  | Ordering.lt => .first
  | Ordering.eq => .second
  | Ordering.gt => .third

/-- Lower an address-level comparison, exposing only its three-way status. -/
def lowerCompare : Compare → RealRAM.Memory →
    Prog RealRAM (RealRAM.Memory × Machine.Choice3)
  | .compare left right, memory => do
      let x ← liftReal (.read memory left)
      let y ← liftReal (.read memory right)
      let ordering ← liftReal (.compare x y)
      pure (memory, choiceOfOrdering ordering)

/-- Decode the result by performing one charged read. -/
def lowerFinish (address : ℕ) (memory : RealRAM.Memory) : Prog RealRAM ℝ :=
  liftReal (.read memory address)

/-- Standard lowering of the complete core source language to `RealRAM`. -/
def implementation : Reduction Query RealRAM where
  reduce
    | .init memory => pure memory
    | .execute instruction memory => lowerInstruction instruction memory
    | .choose2 instruction _ => nomatch instruction
    | .choose3 instruction memory => lowerCompare instruction memory
    | .finish address memory => lowerFinish address memory

/-- Compile and lower a core real-RAM source program. -/
def run (program : Program) (input : RealRAM.Memory) : Prog RealRAM ℝ :=
  (program.compile (State := RealRAM.Memory) (Result := ℝ) input).reduceProg implementation

/-- Direct mathematical meaning of one address-level instruction. -/
noncomputable def evalInstruction : Instruction → RealRAM.Memory → RealRAM.Memory
  | .constant value destination, memory =>
      RealRAM.Memory.write memory destination value
  | .copy source destination, memory =>
      RealRAM.Memory.write memory destination (RealRAM.Memory.read memory source)
  | .add left right destination, memory =>
      RealRAM.Memory.write memory destination
        (RealRAM.Memory.read memory left + RealRAM.Memory.read memory right)
  | .sub left right destination, memory =>
      RealRAM.Memory.write memory destination
        (RealRAM.Memory.read memory left - RealRAM.Memory.read memory right)
  | .mul left right destination, memory =>
      RealRAM.Memory.write memory destination
        (RealRAM.Memory.read memory left * RealRAM.Memory.read memory right)
  | .div left right destination, memory =>
      RealRAM.Memory.write memory destination
        (RealRAM.Memory.read memory left / RealRAM.Memory.read memory right)
  | .neg source destination, memory =>
      RealRAM.Memory.write memory destination (-RealRAM.Memory.read memory source)

/-- Direct mathematical meaning of one address-level comparison. -/
noncomputable def evalCompare : Compare → RealRAM.Memory → RealRAM.Memory × Machine.Choice3
  | .compare left right, memory =>
      let x := RealRAM.Memory.read memory left
      let y := RealRAM.Memory.read memory right
      (memory, if x < y then .first else if x = y then .second else .third)

@[simp]
theorem choiceOfOrdering_comparison (x y : ℝ) :
    choiceOfOrdering (if x < y then Ordering.lt else if x = y then Ordering.eq else Ordering.gt) =
      if x < y then .first else if x = y then .second else .third := by
  by_cases less : x < y <;> by_cases equal : x = y <;>
    simp [less, equal, choiceOfOrdering]

/-- Number of primitive real-RAM queries emitted by one address-level instruction. -/
def instructionCost : Instruction → ℕ
  | .constant _ _ => 1
  | .copy _ _ => 2
  | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .div _ _ _ => 4
  | .neg _ _ => 3

/--
Independent source-level semantics and exact natural cost for the standard lowering.

The costs displayed here are per address instruction, rather than per primitive `RealRAM` query.
-/
noncomputable def natModel : Model Query ℕ where
  evalQuery
    | .init memory => memory
    | .execute instruction memory => evalInstruction instruction memory
    | .choose2 instruction _ => nomatch instruction
    | .choose3 instruction memory => evalCompare instruction memory
    | .finish address memory => RealRAM.Memory.read memory address
  cost
    | .init _ => 0
    | .execute instruction _ => instructionCost instruction
    | .choose2 instruction _ => nomatch instruction
    | .choose3 _ _ => 3
    | .finish _ _ => 1

/-- The standard lowering has exactly the independently specified result and natural cost. -/
theorem implementation_isExact :
    Reduction.IsExact implementation natModel RealRAM.natCost := by
  constructor
  · intro result query
    cases query with
    | init memory => rfl
    | execute instruction memory =>
        cases instruction <;>
          simp [implementation, lowerInstruction, liftReal, natModel, evalInstruction,
            RealRAM.natCost]
    | choose2 instruction memory => nomatch instruction
    | choose3 instruction memory =>
        cases instruction
        simp [implementation, lowerCompare, liftReal, natModel, evalCompare, RealRAM.natCost]
    | finish address memory =>
        simp [implementation, lowerFinish, liftReal, natModel, RealRAM.natCost]
  · intro result query
    cases query with
    | init memory => rfl
    | execute instruction memory =>
        cases instruction <;>
          simp [implementation, lowerInstruction, liftReal, natModel, instructionCost,
            RealRAM.natCost]
    | choose2 instruction memory => nomatch instruction
    | choose3 instruction memory =>
        cases instruction
        simp [implementation, lowerCompare, liftReal, natModel, RealRAM.natCost]
    | finish address memory =>
        simp [implementation, lowerFinish, liftReal, natModel, RealRAM.natCost]

end Algolean.Algorithms.RealRAMMachine
