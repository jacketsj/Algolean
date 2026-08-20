/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.Algorithm

/-! # Acceptance examples for auditable existential algorithm statements -/

@[expose] public section

namespace AlgoleanTests.ExistentialAlgorithms

open Algolean Algorithms
open StructuredRealRAM

/--
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Layout.mk

noncomputable def pairArrayLayout : Layout (Array (ℕ × ℝ)) :=
  .array (.prod .nat .real)

example (values : Array (ℕ × ℝ)) :
    pairArrayLayout.decode (pairArrayLayout.encode values) = some values :=
  pairArrayLayout.decode_encode values

example (values : Array (ℕ × ℝ)) :
    pairArrayLayout.RepAt Layout.inputRegion values (pairArrayLayout.init values) :=
  pairArrayLayout.init_rep values

example (values other : Array (ℕ × ℝ)) (memory : Memory)
    (left : pairArrayLayout.RepAt Layout.inputRegion values memory)
    (right : pairArrayLayout.RepAt Layout.inputRegion other memory) : values = other :=
  pairArrayLayout.rep_functional Layout.inputRegion left right

namespace FixedStructured

def identityProblem : MachineProblem where
  Input := ℕ
  Output := ℕ
  inputLayout := .nat
  outputLayout := .nat
  outputRegion := Layout.inputRegion
  pre _ := True
  post input output := output = input

def haltProgram : StructuredRealRAM.Program := [
  .halt (.literal 0)
]

def haltCost : StructuredRealRAM.Cost :=
  StructuredRealRAM.Cost.ofFields 1 0 0 0 0 0 0 0 0

theorem haltProgram_hasAlgorithm :
    identityProblem.HasFixedMachineAlgorithm (fun _ => haltCost) := by
  refine ⟨haltProgram, ?_, ?_⟩
  · intro pc instruction fetch target successor
    cases pc with
    | zero =>
        simp [haltProgram] at fetch
        subst instruction
        simp [StructuredRealRAM.Instruction.successors] at successor
    | succ pc => simp [haltProgram] at fetch
  · intro input _
    refine ⟨input, {
      final := Layout.nat.init input
      result := 0
      cost := haltCost
      steps := 1
      trace := StructuredRealRAM.HaltingTrace.halt ?_
    }, Layout.nat.init_rep input, rfl, le_rfl⟩
    simp [StructuredRealRAM.step, StructuredRealRAM.execute, haltProgram, haltCost,
      StructuredRealRAM.Instruction.cost, StructuredRealRAM.RealOperand.eval,
      StructuredRealRAM.RealOperand.reads, MachineProblem.initialMemory, identityProblem]

end FixedStructured

namespace SharedJoin

open StructuredRealRAM.CFG

def entry : Label := ⟨0⟩
def yes : Label := ⟨1⟩
def no : Label := ⟨2⟩
def join : Label := ⟨3⟩

/-- Both runtime arms target one materialized join block. -/
def source : CFG.Program :=
  ⟨entry, [
    ⟨entry, [], .nbranch (.reg 0) (.literal 0) no join yes⟩,
    ⟨yes, [.nset (.literal 1) ⟨1⟩], .jump join⟩,
    ⟨no, [.nset (.literal 2) ⟨1⟩], .jump join⟩,
    ⟨join, [.nset (.literal 3) ⟨2⟩], .halt (.literal 0)⟩
  ]⟩

example : source.codeSize = 7 := by decide
example : (compile source).length = 7 := by
  rw [compile_length]
  decide

end SharedJoin

namespace NativeRAMs

def integerReadFirst : IntegerRAM.Program := [
  .halt (.load (.immediate 1))
]

def integerFirstProblem : IntegerRAM.Problem where
  pre cells := cells.length = 1
  post cells result := result = cells.getD 0 0

theorem integerReadFirst_hasAlgorithm :
    integerFirstProblem.HasFixedMachineAlgorithm (fun _ => 1) := by
  refine ⟨integerReadFirst, ?_, ?_⟩
  · intro pc instruction fetch target successor
    cases pc with
    | zero =>
        simp [integerReadFirst] at fetch
        subst instruction
        simp [RAM.Instruction.successors] at successor
    | succ pc => simp [integerReadFirst] at fetch
  · intro input _
    refine ⟨{
      final := IntegerRAM.canonicalMemory input
      result := input.getD 0 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt ?_
    }, rfl, le_rfl⟩
    simp [IntegerRAM.stepCosted, IntegerRAM.costedSemantics,
      RAM.CostedSemantics.step, integerReadFirst, RAM.execute, RAM.Operand.eval,
      RAM.AddressOperand.eval, IntegerRAM.canonicalMemory,
      RAM.CostedSemantics.unit]

example :
    ((IntegerRAM.costedSemantics.runFor integerReadFirst 1
      ⟨0, IntegerRAM.canonicalMemory [37]⟩).outcome).output? = some 37 := by
  decide

def wordReadFirst : WordRAM.Program 8 := [
  .halt (.load (.immediate 1))
]

def wordInput : WordRAM.Input 8 := ⟨[37], by decide⟩

def wordFirstProblem : WordRAM.Problem 8 where
  pre _ := True
  post input result := result = input.cells.getD 0 0

theorem wordReadFirst_hasAlgorithm :
    wordFirstProblem.HasFixedMachineAlgorithm (fun _ => 1) := by
  refine ⟨wordReadFirst, ?_, ?_⟩
  · intro pc instruction fetch target successor
    cases pc with
    | zero =>
        simp [wordReadFirst] at fetch
        subst instruction
        simp [RAM.Instruction.successors] at successor
    | succ pc => simp [wordReadFirst] at fetch
  · intro input _
    refine ⟨{
      final := WordRAM.canonicalMemory input
      result := input.cells.getD 0 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt ?_
    }, rfl, le_rfl⟩
    simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
      wordReadFirst, RAM.execute, RAM.Operand.eval, RAM.AddressOperand.eval,
      WordRAM.canonicalMemory, RAM.CostedSemantics.unit]

example :
    ((WordRAM.costedSemantics 8).runFor wordReadFirst 1
      ⟨0, WordRAM.canonicalMemory wordInput⟩).outcome.output? = some 37 := by
  decide

end NativeRAMs

end AlgoleanTests.ExistentialAlgorithms
