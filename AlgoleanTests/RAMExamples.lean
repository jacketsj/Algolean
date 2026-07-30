/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM.Extensions

/-! # RAM examples -/

@[expose] public section

namespace AlgoleanTests.RAMExamples

open Algolean Algorithms RAM

def integerMemory : IntegerRAM.Memory :=
  ⟨fun | 0 => 3 | _ => 0, fun _ => 0⟩

/-- One fixed program decrements data cell zero until it reaches zero. -/
def integerCountdown : IntegerRAM.Program := [
  .compare (.load (.immediate 0)) (.immediate 0) 2 2 1,
  .sub (.load (.immediate 0)) (.immediate 1) (.immediate 0) 0,
  .halt (.load (.immediate 0))
]

example : (IntegerRAM.runFor integerCountdown 8 integerMemory).output? = some 0 := by
  decide

abbrev width := 8

def wordMemory : WordRAM.Memory width :=
  ⟨fun | 0 => 3 | _ => 0, fun _ => 0⟩

def wordCountdown : WordRAM.Program width := [
  .compare (.load (.immediate 0)) (.immediate 0) 2 2 1,
  .sub (.load (.immediate 0)) (.immediate 1) (.immediate 0) 0,
  .halt (.load (.immediate 0))
]

example : (WordRAM.runFor wordCountdown 8 wordMemory).output? = some 0 := by
  decide

noncomputable def realMemory (x : ℝ) : RealRAM.MachineMemory :=
  ⟨fun | 10 => x | _ => 0, fun | 0 => 10 | _ => 0⟩

/-- Real RAM reads data indirectly through address register zero. -/
def realRead : RealRAM.Program := [
  .halt (.load (.reg 0))
]

example (x : ℝ) : RealRAM.runFor realRead 1 (realMemory x) =
    .halted (realMemory x) x := by
  simp [RealRAM.runFor, RealRAM.runForExtra, RAM.runFor, RAM.step, RAM.execute,
    realRead, realMemory,
    RAM.Operand.eval, RAM.AddressOperand.eval]

noncomputable def sqrtMemory : RealRAM.MachineMemory :=
  ⟨fun | 0 => 9 | _ => 0, fun _ => 0⟩

def sqrtProgram : RealRAM.Sqrt.MachineProgram := [
  .extra ⟨.load (.immediate 0), .immediate 1⟩ 1,
  .halt (.load (.immediate 1))
]

example : (RealRAM.Sqrt.runMachineFor sqrtProgram 2 sqrtMemory).output? = some 3 := by
  change some (Real.sqrt 9) = some 3
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

end AlgoleanTests.RAMExamples
