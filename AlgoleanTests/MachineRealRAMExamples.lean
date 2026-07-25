/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Machine.RealRAM

/-!
# Address-level real-RAM machine examples

These finite programs exercise arithmetic, all three comparison successors, natural cost, and
detailed operation cost. Their input is explicitly the pre-encoded memory required by
`RealRAMMachine.run`.
-/

@[expose] public section

namespace AlgoleanTests.MachineRealRAMExamples

open Algolean Algorithms Machine

noncomputable section

def input (x y : ℝ) : RealRAM.Memory :=
  RealRAM.Memory.write (RealRAM.Memory.write RealRAM.Memory.empty 0 x) 1 y

def addCode : RealRAMMachine.Program :=
  .next (.add 0 1 2) (.halt 2)

@[simp]
theorem addCode_eval (x y : ℝ) :
    (RealRAMMachine.run addCode (input x y)).eval RealRAM.natCost = x + y := by
  change
    (((addCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x y)).reduceProg
      RealRAMMachine.implementation).eval RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_eval]
  simp [addCode, input, RealRAMMachine.natModel, RealRAMMachine.evalInstruction,
    RealRAM.Memory.read]

@[simp]
theorem addCode_time (x y : ℝ) :
    (RealRAMMachine.run addCode (input x y)).time RealRAM.natCost = 5 := by
  change
    (((addCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x y)).reduceProg
      RealRAMMachine.implementation).time RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_time]
  simp [addCode, RealRAMMachine.natModel, RealRAMMachine.instructionCost]

/-- `compileFrom` uses the caller-supplied memory and omits the initialization query. -/
@[simp]
theorem addCode_compileFrom_eval (x y : ℝ) :
    ((addCode.compileFrom (Input := RealRAM.Memory) (input x y)).reduceProg
      RealRAMMachine.implementation).eval RealRAM.natCost = x + y := by
  rw [RealRAMMachine.implementation_isExact.reduceProg_eval]
  simp [addCode, input, RealRAMMachine.natModel, RealRAMMachine.evalInstruction,
    RealRAM.Memory.read]

/-- Exactness applies to the direct `compileFrom` route as well. -/
@[simp]
theorem addCode_compileFrom_time (x y : ℝ) :
    ((addCode.compileFrom (Input := RealRAM.Memory) (input x y)).reduceProg
      RealRAMMachine.implementation).time RealRAM.natCost = 5 := by
  rw [RealRAMMachine.implementation_isExact.reduceProg_time]
  simp [addCode, RealRAMMachine.natModel, RealRAMMachine.instructionCost]

@[simp]
theorem addCode_operationCost (x y : ℝ) :
    (RealRAMMachine.run addCode (input x y)).time RealRAM.operationCost =
      ⟨3, 1, 1, 0, 0⟩ := by
  rfl

def maximumCode : RealRAMMachine.Program :=
  .choose3 (.compare 0 1) (.halt 1) (.halt 0) (.halt 0)

theorem maximumCode_eval_of_lt (x y : ℝ) (less : x < y) :
    (RealRAMMachine.run maximumCode (input x y)).eval RealRAM.natCost = y := by
  change
    (((maximumCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x y)).reduceProg
      RealRAMMachine.implementation).eval RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_eval]
  simp [maximumCode, input, RealRAMMachine.natModel, RealRAMMachine.evalCompare,
    RealRAM.Memory.read, less]

theorem maximumCode_eval_of_eq (x y : ℝ) (equal : x = y) :
    (RealRAMMachine.run maximumCode (input x y)).eval RealRAM.natCost = x := by
  subst y
  change
    (((maximumCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x x)).reduceProg
      RealRAMMachine.implementation).eval RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_eval]
  simp [maximumCode, input, RealRAMMachine.natModel, RealRAMMachine.evalCompare,
    RealRAM.Memory.read]

theorem maximumCode_eval_of_gt (x y : ℝ) (greater : y < x) :
    (RealRAMMachine.run maximumCode (input x y)).eval RealRAM.natCost = x := by
  change
    (((maximumCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x y)).reduceProg
      RealRAMMachine.implementation).eval RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_eval]
  have notLess : ¬x < y := not_lt.mpr (le_of_lt greater)
  have notEqual : ¬x = y := ne_of_gt greater
  simp [maximumCode, input, RealRAMMachine.natModel, RealRAMMachine.evalCompare,
    RealRAM.Memory.read, notLess, notEqual]

@[simp]
theorem maximumCode_time (x y : ℝ) :
    (RealRAMMachine.run maximumCode (input x y)).time RealRAM.natCost = 4 := by
  change
    (((maximumCode.compile (State := RealRAM.Memory) (Result := ℝ) (input x y)).reduceProg
      RealRAMMachine.implementation).time RealRAM.natCost) = _
  rw [RealRAMMachine.implementation_isExact.reduceProg_time]
  generalize hchoice :
    (RealRAMMachine.evalCompare (.compare 0 1) (input x y)).2 = choice
  cases choice <;> simp [maximumCode, RealRAMMachine.natModel, hchoice]

end

end AlgoleanTests.MachineRealRAMExamples
