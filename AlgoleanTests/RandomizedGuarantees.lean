/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMRandomized

/-!
# Behavioral regression tests for randomized guarantee categories

These examples distinguish bounded success, every-source Monte Carlo, one-sided error,
zero-error termination, and distributional output using the same sealed fair-bit trace semantics.
-/

@[expose] public section

namespace AlgoleanTests.RandomizedGuarantees

open MeasureTheory
open Algolean.Algorithms
open Algolean.Algorithms.WordRAM

noncomputable section

def boolProblem : StructuredProblem 8 where
  widthAtLeastTwo := by omega
  Input := Unit
  Output := Bool
  inputLayout := .unit
  outputLayout := .bool
  outputRegion := ⟨0⟩
  pre := fun _ ↦ True
  post := fun _ output ↦ output = false
  inputFits := by
    intro input valid
    simp [WordLayout.FitsInput, WordLayout.FitsAt, WordLayout.Fits,
      WordLayout.footprintWords, WordLayout.encode, WordLayout.inputRegion]

def initial : Memory 8 := boolProblem.initialMemory () trivial

def afterBit (source : RandomBit.Source) : Memory 8 :=
  initial.write 0 (if source 0 then 1 else 0)

/-- False halts correctly; true enters the self-loop at pc 3. -/
def divergentProgram : RandomBit.Program 8 := [
  .randBit (.immediate 0) 1,
  .core (.compare (.load (.immediate 0)) (.immediate 0) 2 2 3),
  .core (.halt (.load (.immediate 0))),
  .core (.compare (.immediate 0) (.immediate 0) 3 3 3)
]

theorem divergentProgram_valid : divergentProgram.Valid := by
  intro pc instruction fetch target successor
  rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
  have pcBelow' : pc < 4 := by simpa [divergentProgram] using pcBelow
  interval_cases pc <;>
    simp [divergentProgram, RandomBit.Instruction.successors,
      RAM.Instruction.successors] at successor ⊢ <;> omega

theorem false_trace (source : RandomBit.Source) (bit : source 0 = false) :
    RandomBit.HaltingTrace divergentProgram source
      (RandomBit.Configuration.initial initial) (afterBit source) 0 1 ⟨3, 1⟩ := by
  have drawStep : RandomBit.step divergentProgram source
      (RandomBit.Configuration.initial initial) =
      ⟨RandomBit.StepResult.running ⟨1, afterBit source, 1⟩, RandomBit.Cost.draw⟩ := by
    simp [RandomBit.step, divergentProgram, RandomBit.execute,
      RandomBit.Configuration.initial, afterBit, bit, RandomBit.Cost.draw,
      RAM.AddressOperand.eval]
  have branchStep : RandomBit.step divergentProgram source ⟨1, afterBit source, 1⟩ =
      ⟨RandomBit.StepResult.running ⟨2, afterBit source, 1⟩,
        RandomBit.Cost.core⟩ := by
    simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute,
      RAM.Operand.eval, RAM.AddressOperand.eval, afterBit, initial, bit,
      WordRAM.ops, RAM.Memory.write, RAM.branch, RandomBit.Cost.core]
  have haltStep : RandomBit.step divergentProgram source ⟨2, afterBit source, 1⟩ =
      ⟨RandomBit.StepResult.halted (afterBit source) 0 1, RandomBit.Cost.core⟩ := by
    simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute,
      RAM.Operand.eval, RAM.AddressOperand.eval, afterBit, initial, bit,
      WordRAM.ops, RAM.Memory.write, RandomBit.Cost.core]
  refine ⟨RandomBit.RawHaltingTrace.next drawStep
      (RandomBit.RawHaltingTrace.next branchStep
        (RandomBit.RawHaltingTrace.halt haltStep)), ?_⟩
  simp [RandomBit.Configuration.initial, RandomBit.Cost.draw, RandomBit.Cost.core]

theorem false_output_rep (source : RandomBit.Source) (bit : source 0 = false) :
    boolProblem.OutputRep false (afterBit source) := by
  change WordLayout.bool.RepAt ⟨0⟩ false (afterBit source)
  constructor
  · simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
      WordLayout.encode]
  · intro index inRange
    have indexZero : index = 0 := by
      simpa [WordLayout.footprintWords, WordLayout.encode] using inRange
    subst index
    simp [afterBit, bit, RAM.Memory.write, WordLayout.encode]

theorem no_raw_trace_from_loop
    {source : RandomBit.Source} {configuration : RandomBit.Configuration 8}
    {final : Memory 8} {result : BitVec 8} {draws : Nat} {cost : RandomBit.Cost}
    (trace : RandomBit.RawHaltingTrace divergentProgram source configuration
      final result draws cost)
    (atLoop : configuration.pc = 3) : False := by
  induction trace with
  | halt observed =>
      simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute,
        RAM.Operand.eval, WordRAM.ops, RAM.branch, atLoop] at observed
  | @next configuration nextConfiguration final result draws headCost tailCost observed tail induction =>
      have nextAtLoop : nextConfiguration.pc = 3 := by
        simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, WordRAM.ops, RAM.branch, atLoop] at observed
        simpa using congrArg RandomBit.Configuration.pc observed.1.symm
      exact induction nextAtLoop

theorem no_raw_trace_when_true (source : RandomBit.Source) (bit : source 0 = true)
    {final : Memory 8} {result : BitVec 8} {draws : Nat} {cost : RandomBit.Cost}
    (operational : RandomBit.RawHaltingTrace divergentProgram source
      (RandomBit.Configuration.initial initial) final result draws cost) : False := by
  cases operational with
  | halt observed =>
      simp [RandomBit.step, divergentProgram, RandomBit.execute,
        RandomBit.Configuration.initial] at observed
  | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
      have firstConfiguration : nextConfiguration =
          (RandomBit.Configuration.mk 1 (afterBit source) 1) := by
        simp [RandomBit.step, divergentProgram, RandomBit.execute,
          RandomBit.Configuration.initial, afterBit, bit, RAM.AddressOperand.eval] at observed
        simpa [afterBit, bit] using observed.1.symm
      subst nextConfiguration
      cases tail with
      | halt observed =>
          simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute] at observed
      | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
          have atLoop : nextConfiguration.pc = 3 := by
            simp [RandomBit.step, divergentProgram, RandomBit.execute, RAM.execute,
              RAM.Operand.eval, RAM.AddressOperand.eval, afterBit, initial, bit,
              RAM.Memory.write, WordRAM.ops, RAM.branch] at observed
            simpa using congrArg RandomBit.Configuration.pc observed.1.symm
          exact no_raw_trace_from_loop tail atLoop

theorem no_trace_when_true (source : RandomBit.Source) (bit : source 0 = true) :
    ¬ Nonempty (boolProblem.RandomSuccessfulRun divergentProgram source () trivial) := by
  rintro ⟨run⟩
  exact no_raw_trace_when_true source bit run.trace.operational

def threeSteps : boolProblem.Input → Nat := fun _ ↦ 3
def oneDraw : boolProblem.Input → Nat := fun _ ↦ 1

def halfFailure : boolProblem.Input → Probability := fun _ ↦
  ⟨(2 : ENNReal)⁻¹, by norm_num⟩

theorem divergent_success_event :
    boolProblem.RandomSuccessEvent divergentProgram threeSteps oneDraw () trivial =
      {source | source 0 = false} := by
  ext source
  constructor
  · rintro ⟨run, output, represented, correct, stepCost, drawCost⟩
    by_cases bitFalse : source 0 = false
    · exact bitFalse
    · have bitTrue : source 0 = true := by simpa using bitFalse
      exact (no_trace_when_true source bitTrue ⟨run⟩).elim
  · intro bitFalse
    let run : boolProblem.RandomSuccessfulRun divergentProgram source () trivial := {
      final := afterBit source
      result := 0
      draws := 1
      cost := ⟨3, 1⟩
      trace := false_trace source bitFalse }
    exact ⟨run, false, false_output_rep source bitFalse, rfl,
      (show (3 : Nat) ≤ threeSteps () by decide),
      (show (1 : Nat) ≤ oneDraw () by decide)⟩

/-- A concrete program which may diverge is accepted by bounded-success semantics at failure 1/2. -/
noncomputable def divergentBoundedSuccessCertificate :
    boolProblem.HighProbabilityBoundedSuccessCertificate
      threeSteps oneDraw halfFailure where
  program := divergentProgram
  valid := divergentProgram_valid
  measurableSuccess input validInput := by
    cases input
    rw [divergent_success_event]
    change MeasurableSet ((fun source : RandomBit.Source ↦ source 0) ⁻¹' {false})
    exact (measurable_pi_apply 0) (MeasurableSet.singleton false)
  successProbability input validInput := by
    cases input
    rw [divergent_success_event, RandomBit.sourceLaw_eval_false]
    norm_num [halfFailure]

/-- The same program cannot satisfy an every-source bounded-time premise. -/
theorem divergentProgram_not_every_source_bounded :
    ¬ (∀ source,
      source ∈ boolProblem.RandomTerminationWithinEvent divergentProgram
        threeSteps oneDraw () trivial) := by
  intro everySource
  let allTrue : RandomBit.Source := fun _ ↦ true
  rcases everySource allTrue with ⟨run, output, represented, stepCost, drawCost⟩
  exact no_trace_when_true allTrue rfl ⟨run⟩

/-! ## Every-source bounded time with two-sided error -/

def alwaysHaltingProgram : RandomBit.Program 8 := [
  .randBit (.immediate 0) 1,
  .core (.halt (.load (.immediate 0)))
]

theorem alwaysHaltingProgram_valid : alwaysHaltingProgram.Valid := by
  intro pc instruction fetch target successor
  rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
  have pcBelow' : pc < 2 := by simpa [alwaysHaltingProgram] using pcBelow
  interval_cases pc <;>
    simp [alwaysHaltingProgram, RandomBit.Instruction.successors,
      RAM.Instruction.successors] at successor ⊢ <;> omega

theorem source_output_rep (source : RandomBit.Source) :
    boolProblem.OutputRep (source 0) (afterBit source) := by
  cases bit : source 0
  · exact false_output_rep source bit
  · change WordLayout.bool.RepAt ⟨0⟩ true (afterBit source)
    constructor
    · simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode]
    · intro index inRange
      have indexZero : index = 0 := by
        simpa [WordLayout.footprintWords, WordLayout.encode] using inRange
      subst index
      simp [afterBit, bit, RAM.Memory.write, WordLayout.encode]

theorem always_halting_trace (source : RandomBit.Source) :
    RandomBit.HaltingTrace alwaysHaltingProgram source
      (RandomBit.Configuration.initial initial) (afterBit source)
      (if source 0 then 1 else 0) 1 ⟨2, 1⟩ := by
  have drawStep : RandomBit.step alwaysHaltingProgram source
      (RandomBit.Configuration.initial initial) =
      ⟨RandomBit.StepResult.running ⟨1, afterBit source, 1⟩,
        RandomBit.Cost.draw⟩ := by
    simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute,
      RandomBit.Configuration.initial, afterBit, RAM.AddressOperand.eval]
  have haltStep : RandomBit.step alwaysHaltingProgram source ⟨1, afterBit source, 1⟩ =
      ⟨RandomBit.StepResult.halted (afterBit source)
        (if source 0 then 1 else 0) 1, RandomBit.Cost.core⟩ := by
    simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute, RAM.execute,
      RAM.Operand.eval, RAM.AddressOperand.eval, afterBit, RAM.Memory.write,
      RandomBit.Cost.core]
  refine ⟨RandomBit.RawHaltingTrace.next drawStep
      (RandomBit.RawHaltingTrace.halt haltStep), ?_⟩
  simp [RandomBit.Configuration.initial]

theorem always_raw_final (source : RandomBit.Source)
    {final : Memory 8} {result : BitVec 8} {draws : Nat} {cost : RandomBit.Cost}
    (trace : RandomBit.RawHaltingTrace alwaysHaltingProgram source
      (RandomBit.Configuration.initial initial) final result draws cost) :
    final = afterBit source := by
  cases trace with
  | halt observed =>
      simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute,
        RandomBit.Configuration.initial] at observed
  | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
      have firstConfiguration : nextConfiguration =
          (RandomBit.Configuration.mk 1 (afterBit source) 1) := by
        simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute,
          RandomBit.Configuration.initial, afterBit, RAM.AddressOperand.eval] at observed
        exact observed.1.symm
      subst firstConfiguration
      cases tail with
      | halt haltObserved =>
          simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute, RAM.execute,
            RAM.Operand.eval, RAM.AddressOperand.eval, afterBit, RAM.Memory.write] at haltObserved
          simpa [afterBit, RAM.Memory.write] using haltObserved.1.1.symm
      | next tailObserved tailTail =>
          simp [RandomBit.step, alwaysHaltingProgram, RandomBit.execute,
            RAM.execute] at tailObserved

def twoSteps : boolProblem.Input → Nat := fun _ ↦ 2

theorem always_termination (source : RandomBit.Source) :
    source ∈ boolProblem.RandomTerminationWithinEvent alwaysHaltingProgram
      twoSteps oneDraw () trivial := by
  let run : boolProblem.RandomSuccessfulRun alwaysHaltingProgram source () trivial := {
    final := afterBit source
    result := if source 0 then 1 else 0
    draws := 1
    cost := ⟨2, 1⟩
    trace := always_halting_trace source }
  exact ⟨run, source 0, source_output_rep source,
    (show (2 : Nat) ≤ twoSteps () by decide),
    (show (1 : Nat) ≤ oneDraw () by decide)⟩

theorem always_correct_event :
    boolProblem.RandomCorrectEvent alwaysHaltingProgram () trivial =
      {source | source 0 = false} := by
  ext source
  constructor
  · rintro ⟨run, output, represented, correct⟩
    by_cases bitFalse : source 0 = false
    · exact bitFalse
    · have bitTrue : source 0 = true := by simpa using bitFalse
      have finalEq := always_raw_final source run.trace.operational
      rw [finalEq] at represented
      have trueRep : boolProblem.OutputRep true (afterBit source) := by
        simpa [bitTrue] using source_output_rep source
      have outputFalse : output = false := correct
      subst output
      have impossible : true = false := WordLayout.RepAt.functional
        boolProblem.outputLayout boolProblem.widthAtLeastTwo
        boolProblem.outputRegion trueRep represented
      exact Bool.noConfusion impossible
  · intro bitFalse
    let run : boolProblem.RandomSuccessfulRun alwaysHaltingProgram source () trivial := {
      final := afterBit source
      result := if source 0 then 1 else 0
      draws := 1
      cost := ⟨2, 1⟩
      trace := always_halting_trace source }
    exact ⟨run, false, false_output_rep source bitFalse, rfl⟩

/-- Every source halts, while correctness is exactly one fair-bit event. -/
noncomputable def boundedTimeTwoSidedCertificate :
    boolProblem.BoundedTimeMonteCarloCertificate twoSteps oneDraw halfFailure where
  program := alwaysHaltingProgram
  valid := alwaysHaltingProgram_valid
  terminatesWithin source input validInput := by
    cases input
    exact always_termination source
  correctMeasurable input validInput := by
    cases input
    rw [always_correct_event]
    change MeasurableSet ((fun source : RandomBit.Source ↦ source 0) ⁻¹' {false})
    exact (measurable_pi_apply 0) (MeasurableSet.singleton false)
  correctProbability input validInput := by
    cases input
    rw [always_correct_event, RandomBit.sourceLaw_eval_false]
    norm_num [halfFailure]

/-- The same two-sided program is not zero error, so it cannot be Las Vegas. -/
theorem alwaysHaltingProgram_not_lasVegas :
    ¬ boolProblem.CorrectOnEveryHaltingRun alwaysHaltingProgram := by
  intro zeroError
  let allTrue : RandomBit.Source := fun _ ↦ true
  let run : boolProblem.RandomSuccessfulRun alwaysHaltingProgram allTrue () trivial := {
    final := afterBit allTrue
    result := 1
    draws := 1
    cost := ⟨2, 1⟩
    trace := always_halting_trace allTrue }
  rcases zeroError () trivial allTrue run with ⟨output, represented, correct⟩
  have outputFalse : output = false := correct
  subst output
  have trueRep : boolProblem.OutputRep true (afterBit allTrue) := source_output_rep allTrue
  have impossible : true = false := WordLayout.RepAt.functional boolProblem.outputLayout
    boolProblem.widthAtLeastTwo boolProblem.outputRegion trueRep represented
  exact Bool.noConfusion impossible

/-! ## Distributional and expected-quality output are not Boolean success predicates -/

local instance : MeasurableSpace boolProblem.Output := ⊤

def fairBitTarget (_ : boolProblem.Input) : Measure boolProblem.Output :=
  Measure.map (fun source : RandomBit.Source ↦ source 0) RandomBit.sourceLaw

/-- The same trace is an exact fair-bit sampler when given a distributional specification. -/
noncomputable def fairBitSampler :
    boolProblem.SamplerCertificate fairBitTarget where
  program := alwaysHaltingProgram
  valid := alwaysHaltingProgram_valid
  output := fun _ source ↦ source 0
  realizes input validInput source := by
    cases input
    let run : boolProblem.RandomSuccessfulRun alwaysHaltingProgram source () trivial := {
      final := afterBit source
      result := if source 0 then 1 else 0
      draws := 1
      cost := ⟨2, 1⟩
      trace := always_halting_trace source }
    exact ⟨run, source_output_rep source⟩
  outputMeasurable input := measurable_pi_apply 0
  distribution input validInput := by
    cases input
    rfl

def zeroLoss (_ : boolProblem.Input) (_ : boolProblem.Output) : ENNReal := 0
def zeroExpectedLoss (_ : boolProblem.Input) : ENNReal := 0

/-- Expected-quality certificates retain an actual same-source output realization. -/
noncomputable def zeroLossApproximation :
    boolProblem.ExpectedApproximationCertificate zeroLoss zeroExpectedLoss where
  program := alwaysHaltingProgram
  valid := alwaysHaltingProgram_valid
  output := fun _ source ↦ source 0
  realizes input validInput source := by
    cases input
    let run : boolProblem.RandomSuccessfulRun alwaysHaltingProgram source () trivial := {
      final := afterBit source
      result := if source 0 then 1 else 0
      draws := 1
      cost := ⟨2, 1⟩
      trace := always_halting_trace source }
    exact ⟨run, source_output_rep source⟩
  lossMeasurable input := by simp [zeroLoss]
  expectedLoss input validInput := by simp [zeroLoss, zeroExpectedLoss]

/-- A bounded one-bit factor has finite output support, unlike exact continuous uniform output. -/
theorem fairBitSampler_finite_support :
    Set.Finite (Set.range (fun source : RandomBit.Source ↦ source 0)) := by
  apply StructuredProblem.finite_output_support_of_prefix_factor 1
      (fun source : RandomBit.Source ↦ source 0)
      (fun bits ↦ bits ⟨0, by decide⟩)
  intro source
  rfl

/-! ## RP-oriented one-sided error -/

def decisionProblem : StructuredProblem 8 where
  widthAtLeastTwo := by omega
  Input := Bool
  Output := Bool
  inputLayout := .bool
  outputLayout := .bool
  outputRegion := ⟨1⟩
  pre := fun _ ↦ True
  post := fun input output ↦ output = input
  inputFits := by
    intro input valid
    simp [WordLayout.FitsInput, WordLayout.FitsAt, WordLayout.Fits,
      WordLayout.footprintWords, WordLayout.encode, WordLayout.inputRegion]

def decisionSpec : StructuredProblem.OneSidedDecisionSpec decisionProblem where
  isYes := fun input ↦ input = true
  isNo := fun input ↦ input = false
  accepts := fun output ↦ output = true
  classified input valid := by cases input <;> simp
  disjoint input := by cases input <;> simp

def decisionInitial (input : Bool) : Memory 8 := decisionProblem.initialMemory input trivial

def decisionFinal (input : Bool) (source : RandomBit.Source) : Memory 8 :=
  (decisionInitial input).write 1 (if input then (if source 0 then 1 else 0) else 0)

/-- No inputs deterministically reject; yes inputs accept exactly when the first bit is true. -/
def rpProgram : RandomBit.Program 8 := [
  .core (.compare (.load (.immediate 0)) (.immediate 0) 1 1 2),
  .core (.set (.immediate 0) (.immediate 1) 3),
  .randBit (.immediate 1) 3,
  .core (.halt (.load (.immediate 1)))
]

theorem rpProgram_valid : rpProgram.Valid := by
  intro pc instruction fetch target successor
  rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
  have pcBelow' : pc < 4 := by simpa [rpProgram] using pcBelow
  interval_cases pc <;>
    simp [rpProgram, RandomBit.Instruction.successors,
      RAM.Instruction.successors] at successor ⊢ <;> omega

theorem rp_output_rep (input : Bool) (source : RandomBit.Source) :
    decisionProblem.OutputRep (if input then source 0 else false)
      (decisionFinal input source) := by
  change WordLayout.bool.RepAt ⟨1⟩ _ _
  constructor
  · simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
      WordLayout.encode]
  · intro index inRange
    have indexZero : index = 0 := by
      simpa [WordLayout.footprintWords, WordLayout.encode] using inRange
    subst index
    cases input with
    | false => simp [decisionFinal, RAM.Memory.write, WordLayout.encode]
    | true =>
        by_cases bit : source 0 = true
        · simp [decisionFinal, RAM.Memory.write, WordLayout.encode, bit]
        · have bitFalse : source 0 = false := by simpa using bit
          simp [decisionFinal, RAM.Memory.write, WordLayout.encode, bitFalse]

theorem rp_trace (input : Bool) (source : RandomBit.Source) :
    RandomBit.HaltingTrace rpProgram source
      (RandomBit.Configuration.initial (decisionInitial input))
      (decisionFinal input source)
      (if input then (if source 0 then 1 else 0) else 0)
      (if input then 1 else 0) ⟨3, if input then 1 else 0⟩ := by
  cases input with
  | false =>
      have branchStep : RandomBit.step rpProgram source
          (RandomBit.Configuration.initial (decisionInitial false)) =
          ⟨RandomBit.StepResult.running ⟨1, decisionInitial false, 0⟩,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, RandomBit.Configuration.initial,
          decisionInitial, decisionProblem, StructuredProblem.initialMemory,
          WordLayout.init, WordLayout.encode, WordRAM.ops, RAM.branch,
          RandomBit.Cost.core]
      have setStep : RandomBit.step rpProgram source ⟨1, decisionInitial false, 0⟩ =
          ⟨RandomBit.StepResult.running ⟨3, decisionFinal false source, 0⟩,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal, RAM.Memory.write,
          WordRAM.ops, RandomBit.Cost.core]
      have haltStep : RandomBit.step rpProgram source ⟨3, decisionFinal false source, 0⟩ =
          ⟨RandomBit.StepResult.halted (decisionFinal false source) 0 0,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal, RAM.Memory.write,
          RandomBit.Cost.core]
      refine ⟨RandomBit.RawHaltingTrace.next branchStep
        (RandomBit.RawHaltingTrace.next setStep
          (RandomBit.RawHaltingTrace.halt haltStep)), ?_⟩
      simp [RandomBit.Configuration.initial]
  | true =>
      have branchStep : RandomBit.step rpProgram source
          (RandomBit.Configuration.initial (decisionInitial true)) =
          ⟨RandomBit.StepResult.running ⟨2, decisionInitial true, 0⟩,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, RandomBit.Configuration.initial,
          decisionInitial, decisionProblem, StructuredProblem.initialMemory,
          WordLayout.init, WordLayout.encode, WordRAM.ops, RAM.branch,
          RandomBit.Cost.core]
      have drawStep : RandomBit.step rpProgram source ⟨2, decisionInitial true, 0⟩ =
          ⟨RandomBit.StepResult.running ⟨3, decisionFinal true source, 1⟩,
            RandomBit.Cost.draw⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.AddressOperand.eval,
          decisionFinal, RandomBit.Cost.draw]
      have haltStep : RandomBit.step rpProgram source ⟨3, decisionFinal true source, 1⟩ =
          ⟨RandomBit.StepResult.halted (decisionFinal true source)
            (if source 0 then 1 else 0) 1, RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal, RAM.Memory.write,
          RandomBit.Cost.core]
      refine ⟨RandomBit.RawHaltingTrace.next branchStep
        (RandomBit.RawHaltingTrace.next drawStep
          (RandomBit.RawHaltingTrace.halt haltStep)), ?_⟩
      simp [RandomBit.Configuration.initial]

def decisionStepBound (_ : decisionProblem.Input) : Nat := 3
def decisionDrawBound (_ : decisionProblem.Input) : Nat := 1
def decisionFailure (_ : decisionProblem.Input) : Probability :=
  ⟨(2 : ENNReal)⁻¹, by norm_num⟩

theorem rp_termination (input : Bool) (source : RandomBit.Source) :
    source ∈ decisionProblem.RandomTerminationWithinEvent rpProgram
      decisionStepBound decisionDrawBound input trivial := by
  let run : decisionProblem.RandomSuccessfulRun rpProgram source input trivial := {
    final := decisionFinal input source
    result := if input then (if source 0 then 1 else 0) else 0
    draws := if input then 1 else 0
    cost := ⟨3, if input then 1 else 0⟩
    trace := rp_trace input source }
  exact ⟨run, if input then source 0 else false, rp_output_rep input source,
    (show (3 : Nat) ≤ decisionStepBound input by simp [decisionStepBound]),
    (by change (if input then 1 else 0) ≤ decisionDrawBound input
        cases input <;> simp [decisionDrawBound])⟩

theorem rp_raw_final (input : Bool) (source : RandomBit.Source)
    {final : Memory 8} {result : BitVec 8} {draws : Nat} {cost : RandomBit.Cost}
    (trace : RandomBit.RawHaltingTrace rpProgram source
      (RandomBit.Configuration.initial (decisionInitial input)) final result draws cost) :
    final = decisionFinal input source := by
  cases input with
  | false =>
      cases trace with
      | halt observed =>
          simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
            RandomBit.Configuration.initial, decisionInitial, decisionProblem,
            StructuredProblem.initialMemory, WordLayout.init, WordLayout.encode,
            RAM.Operand.eval, RAM.AddressOperand.eval, WordRAM.ops, RAM.branch] at observed
      | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
          have firstEq : nextConfiguration = ⟨1, decisionInitial false, 0⟩ := by
            simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
              RandomBit.Configuration.initial, decisionInitial, decisionProblem,
              StructuredProblem.initialMemory, WordLayout.init, WordLayout.encode,
              RAM.Operand.eval, RAM.AddressOperand.eval, WordRAM.ops, RAM.branch] at observed
            simpa [decisionInitial, decisionProblem, StructuredProblem.initialMemory,
              WordLayout.init, WordLayout.encode] using observed.1.symm
          subst nextConfiguration
          cases tail with
          | halt observed =>
              simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute] at observed
          | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
              have secondEq : nextConfiguration = ⟨3, decisionFinal false source, 0⟩ := by
                simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
                  RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal,
                  RAM.Memory.write, WordRAM.ops] at observed
                exact observed.1.symm
              subst nextConfiguration
              cases tail with
              | halt observed =>
                  simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
                    RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal,
                    RAM.Memory.write] at observed
                  exact observed.1.1.symm
              | next observed tail =>
                  simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute] at observed
  | true =>
      cases trace with
      | halt observed =>
          simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
            RandomBit.Configuration.initial, decisionInitial, decisionProblem,
            StructuredProblem.initialMemory, WordLayout.init, WordLayout.encode,
            RAM.Operand.eval, RAM.AddressOperand.eval, WordRAM.ops, RAM.branch] at observed
      | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
          have firstEq : nextConfiguration = ⟨2, decisionInitial true, 0⟩ := by
            simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
              RandomBit.Configuration.initial, decisionInitial, decisionProblem,
              StructuredProblem.initialMemory, WordLayout.init, WordLayout.encode,
              RAM.Operand.eval, RAM.AddressOperand.eval, WordRAM.ops, RAM.branch] at observed
            simpa [decisionInitial, decisionProblem, StructuredProblem.initialMemory,
              WordLayout.init, WordLayout.encode] using observed.1.symm
          subst nextConfiguration
          cases tail with
          | halt observed =>
              simp [RandomBit.step, rpProgram, RandomBit.execute] at observed
          | @next configuration nextConfiguration final result draws headCost tailCost observed tail =>
              have secondEq : nextConfiguration = ⟨3, decisionFinal true source, 1⟩ := by
                simp [RandomBit.step, rpProgram, RandomBit.execute,
                  RAM.AddressOperand.eval, decisionFinal] at observed
                exact observed.1.symm
              subst nextConfiguration
              cases tail with
              | halt observed =>
                  simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute,
                    RAM.Operand.eval, RAM.AddressOperand.eval, decisionFinal,
                    RAM.Memory.write] at observed
                  exact observed.1.1.symm
              | next observed tail =>
                  simp [RandomBit.step, rpProgram, RandomBit.execute, RAM.execute] at observed

theorem rp_accept_event (input : Bool) :
    decisionSpec.AcceptEvent rpProgram input trivial =
      if input then {source | source 0 = true} else ∅ := by
  ext source
  cases input with
  | false =>
      simp only [Bool.false_eq_true, if_false, Set.mem_empty_iff_false, iff_false]
      rintro ⟨run, output, represented, accepts⟩
      have outputTrue : output = true := accepts
      subst output
      have finalEq : run.final = decisionFinal false source :=
        rp_raw_final false source run.trace.operational
      rw [finalEq] at represented
      have falseRep := rp_output_rep false source
      have impossible : false = true := WordLayout.RepAt.functional
        decisionProblem.outputLayout decisionProblem.widthAtLeastTwo
        decisionProblem.outputRegion falseRep represented
      exact Bool.noConfusion impossible
  | true =>
      simp only [if_true]
      constructor
      · rintro ⟨run, output, represented, accepts⟩
        by_cases bitTrue : source 0 = true
        · exact bitTrue
        · have bitFalse : source 0 = false := by simpa using bitTrue
          have finalEq : run.final = decisionFinal true source :=
            rp_raw_final true source run.trace.operational
          rw [finalEq] at represented
          have falseRep : decisionProblem.OutputRep false (decisionFinal true source) := by
            simpa [bitFalse] using rp_output_rep true source
          have outputTrue : output = true := accepts
          subst output
          have impossible : false = true := WordLayout.RepAt.functional
            decisionProblem.outputLayout decisionProblem.widthAtLeastTwo
            decisionProblem.outputRegion falseRep represented
          exact Bool.noConfusion impossible
      · intro bitTrue
        let run : decisionProblem.RandomSuccessfulRun rpProgram source true trivial := {
          final := decisionFinal true source
          result := if source 0 then 1 else 0
          draws := 1
          cost := ⟨3, 1⟩
          trace := rp_trace true source }
        have trueRep := rp_output_rep true source
        rw [bitTrue] at trueRep
        exact ⟨run, true, trueRep, rfl⟩

/-- No-instances never accept, while yes-instances accept with probability exactly one half. -/
noncomputable def rpCertificate :
    decisionProblem.OneSidedBoundedTimeMonteCarloCertificate decisionSpec
      decisionStepBound decisionDrawBound decisionFailure where
  program := rpProgram
  valid := rpProgram_valid
  terminatesWithin source input validInput := rp_termination input source
  neverAcceptsNo input validInput isNo source run output represented accepts := by
    have noInput : input = false := isNo
    subst input
    have noAccept : source ∉ decisionSpec.AcceptEvent rpProgram false trivial := by
      rw [rp_accept_event false]
      simp
    exact noAccept ⟨run, output, represented, accepts⟩
  acceptMeasurable input validInput := by
    rw [rp_accept_event input]
    split
    · change MeasurableSet ((fun source : RandomBit.Source ↦ source 0) ⁻¹' {true})
      exact (measurable_pi_apply 0) (MeasurableSet.singleton true)
    · exact MeasurableSet.empty
  acceptsYesWithHighProbability input validInput isYes := by
    have yesInput : input = true := isYes
    subst input
    have proofEq : validInput = trivial := Subsingleton.elim _ _
    subst validInput
    have setEq : decisionSpec.AcceptEvent rpProgram true trivial =
        {source | source 0 = true} := by
      simpa using rp_accept_event true
    rw [setEq, RandomBit.sourceLaw_eval_true]
    norm_num [decisionFailure]

/-! ## Rejection sampling: finite expectation without an every-source bound -/

/-- Draw until the first false bit, then return the unique correct Boolean output. -/
def rejectionProgram : RandomBit.Program 8 := [
  .randBit (.immediate 0) 1,
  .core (.compare (.load (.immediate 0)) (.immediate 0) 2 2 0),
  .core (.halt (.load (.immediate 0)))
]

theorem rejectionProgram_valid : rejectionProgram.Valid := by
  intro pc instruction fetch target successor
  rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
  have pcBelow' : pc < 3 := by simpa [rejectionProgram] using pcBelow
  interval_cases pc <;>
    simp [rejectionProgram, RandomBit.Instruction.successors,
      RAM.Instruction.successors] at successor ⊢ <;> omega

def rejectionAfterDraw (memory : Memory 8) (source : RandomBit.Source) (cursor : Nat) :
    Memory 8 :=
  memory.write 0 (if source cursor then 1 else 0)

theorem rejection_raw_trace_from (source : RandomBit.Source) (memory : Memory 8)
    (cursor attempts : Nat)
    (survives : ∀ offset < attempts, source (cursor + offset) = true)
    (accepts : source (cursor + attempts) = false) :
    ∃ final,
      RandomBit.RawHaltingTrace rejectionProgram source
        ⟨0, memory, cursor⟩ final 0 (cursor + attempts + 1) ⟨2 * attempts + 3, attempts + 1⟩ ∧
      final.data (0 : BitVec 8) = (0 : BitVec 8) := by
  induction attempts generalizing memory cursor with
  | zero =>
      let final := rejectionAfterDraw memory source cursor
      have accepts' : source cursor = false := by simpa using accepts
      have finalZero : final.data (0 : BitVec 8) = (0 : BitVec 8) := by
        simp [final, rejectionAfterDraw, accepts', RAM.Memory.write]
      have drawStep : RandomBit.step rejectionProgram source ⟨0, memory, cursor⟩ =
          ⟨RandomBit.StepResult.running ⟨1, final, cursor + 1⟩,
            RandomBit.Cost.draw⟩ := by
        simp [RandomBit.step, rejectionProgram, RandomBit.execute,
          final, rejectionAfterDraw, accepts', RAM.AddressOperand.eval, RandomBit.Cost.draw]
      have branchStep : RandomBit.step rejectionProgram source ⟨1, final, cursor + 1⟩ =
          ⟨RandomBit.StepResult.running ⟨2, final, cursor + 1⟩,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rejectionProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, finalZero,
          WordRAM.ops, RAM.branch, RandomBit.Cost.core]
        simp [final, rejectionAfterDraw, accepts', RAM.Memory.write]
      have haltStep : RandomBit.step rejectionProgram source ⟨2, final, cursor + 1⟩ =
          ⟨RandomBit.StepResult.halted final 0 (cursor + 1),
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rejectionProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, finalZero,
          RandomBit.Cost.core]
        simp [final, rejectionAfterDraw, accepts', RAM.Memory.write]
      refine ⟨final, ?_, ?_⟩
      · have raw := RandomBit.RawHaltingTrace.next drawStep
          (RandomBit.RawHaltingTrace.next branchStep
            (RandomBit.RawHaltingTrace.halt haltStep))
        have costEq : RandomBit.Cost.draw +
            (RandomBit.Cost.core + RandomBit.Cost.core) = ⟨3, 1⟩ := by
          apply RandomBit.Cost.ext <;> rfl
        rw [← costEq]
        exact raw
      · exact finalZero
  | succ attempts induction =>
      have firstTrue : source cursor = true := by
        simpa using survives 0 (Nat.zero_lt_succ attempts)
      let nextMemory := rejectionAfterDraw memory source cursor
      have tailSurvives : ∀ offset < attempts,
          source ((cursor + 1) + offset) = true := by
        intro offset below
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          survives (offset + 1) (Nat.succ_lt_succ below)
      have tailAccepts : source ((cursor + 1) + attempts) = false := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using accepts
      obtain ⟨final, tail, finalZero⟩ :=
        induction nextMemory (cursor + 1) tailSurvives tailAccepts
      have drawStep : RandomBit.step rejectionProgram source ⟨0, memory, cursor⟩ =
          ⟨RandomBit.StepResult.running ⟨1, nextMemory, cursor + 1⟩,
            RandomBit.Cost.draw⟩ := by
        simp [RandomBit.step, rejectionProgram, RandomBit.execute,
          nextMemory, rejectionAfterDraw, firstTrue, RAM.AddressOperand.eval,
          RandomBit.Cost.draw]
      have branchStep : RandomBit.step rejectionProgram source
          ⟨1, nextMemory, cursor + 1⟩ =
          ⟨RandomBit.StepResult.running ⟨0, nextMemory, cursor + 1⟩,
            RandomBit.Cost.core⟩ := by
        simp [RandomBit.step, rejectionProgram, RandomBit.execute, RAM.execute,
          RAM.Operand.eval, RAM.AddressOperand.eval, nextMemory, rejectionAfterDraw,
          firstTrue, RAM.Memory.write, WordRAM.ops, RAM.branch, RandomBit.Cost.core]
      refine ⟨final, ?_, finalZero⟩
      have raw := RandomBit.RawHaltingTrace.next drawStep
        (RandomBit.RawHaltingTrace.next branchStep tail)
      have costEq : RandomBit.Cost.draw +
          (RandomBit.Cost.core + ⟨2 * attempts + 3, attempts + 1⟩) =
          ⟨2 * Nat.succ attempts + 3, Nat.succ attempts + 1⟩ := by
        apply RandomBit.Cost.ext
        · change 1 + (1 + (2 * attempts + 3)) = 2 * Nat.succ attempts + 3
          omega
        · change 1 + (0 + (attempts + 1)) = Nat.succ attempts + 1
          omega
      rw [← costEq]
      convert raw using 1 <;> omega

theorem rejection_run_of_first_false (source : RandomBit.Source) (attempts : Nat)
    (survives : ∀ offset < attempts, source offset = true)
    (accepts : source attempts = false) :
    ∃ run : boolProblem.RandomSuccessfulRun rejectionProgram source () trivial,
      run.cost.steps = 2 * attempts + 3 ∧ run.draws = attempts + 1 ∧
      boolProblem.OutputRep false run.final := by
  obtain ⟨final, rawTrace, finalZero⟩ := rejection_raw_trace_from source initial 0 attempts
    (by simpa using survives) (by simpa using accepts)
  have rawTrace' : RandomBit.RawHaltingTrace rejectionProgram source
      (RandomBit.Configuration.initial (boolProblem.initialMemory () trivial)) final 0
      (attempts + 1) ⟨2 * attempts + 3, attempts + 1⟩ := by
    simpa [initial, RandomBit.Configuration.initial] using rawTrace
  let run : boolProblem.RandomSuccessfulRun rejectionProgram source () trivial := {
    final := final
    result := 0
    draws := attempts + 1
    cost := ⟨2 * attempts + 3, attempts + 1⟩
    trace := ⟨rawTrace', rawTrace'.cursorAccounting⟩ }
  refine ⟨run, rfl, rfl, ?_⟩
  change WordLayout.bool.RepAt ⟨0⟩ false final
  constructor
  · simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
      WordLayout.encode]
  · intro index inRange
    have indexZero : index = 0 := by
      simpa [WordLayout.footprintWords, WordLayout.encode] using inRange
    subst index
    simpa [WordLayout.encode] using finalZero

/-- The two reachable loop states when every unread source bit is true. -/
def rejectionLoopInvariant (source : RandomBit.Source)
    (configuration : RandomBit.Configuration 8) : Prop :=
  (configuration.pc = 0 ∧
      ∀ index, configuration.randomCursor ≤ index → source index = true) ∨
  (configuration.pc = 1 ∧ configuration.memory.data 0#8 = 1#8 ∧
      ∀ index, configuration.randomCursor ≤ index → source index = true)

theorem rejectionLoopInvariant.running
    (invariant : rejectionLoopInvariant source configuration)
    (observed : RandomBit.step rejectionProgram source configuration =
      ⟨RandomBit.StepResult.running next, cost⟩) :
    rejectionLoopInvariant source next := by
  rcases invariant with ⟨atDraw, allTrue⟩ | ⟨atBranch, memoryOne, allTrue⟩
  · have bitTrue := allTrue configuration.randomCursor le_rfl
    simp [RandomBit.step, rejectionProgram, RandomBit.execute, atDraw,
      bitTrue, RAM.AddressOperand.eval] at observed
    rcases observed with ⟨rfl, rfl⟩
    right
    refine ⟨rfl, ?_, ?_⟩
    · simp [RAM.Memory.write]
    · intro index lower
      change configuration.randomCursor + 1 ≤ index at lower
      exact allTrue index ((Nat.le_succ configuration.randomCursor).trans lower)
  · simp [RandomBit.step, rejectionProgram, RandomBit.execute, RAM.execute,
      atBranch, memoryOne, RAM.Operand.eval, RAM.AddressOperand.eval,
      WordRAM.ops, RAM.branch] at observed
    rcases observed with ⟨rfl, rfl⟩
    left
    exact ⟨rfl, allTrue⟩

theorem rejectionLoopInvariant.not_halted
    (invariant : rejectionLoopInvariant source configuration) :
    RandomBit.step rejectionProgram source configuration ≠
      ⟨RandomBit.StepResult.halted final result draws, cost⟩ := by
  rcases invariant with ⟨atDraw, allTrue⟩ | ⟨atBranch, memoryOne, allTrue⟩
  · simp [RandomBit.step, rejectionProgram, RandomBit.execute, atDraw]
  · simp [RandomBit.step, rejectionProgram, RandomBit.execute, RAM.execute,
      atBranch, memoryOne, RAM.Operand.eval, RAM.AddressOperand.eval,
      WordRAM.ops, RAM.branch]

theorem no_rejection_trace_of_loop_invariant
    (invariant : rejectionLoopInvariant source configuration)
    (trace : RandomBit.RawHaltingTrace rejectionProgram source configuration
      final result draws cost) : False := by
  induction trace with
  | halt observed => exact invariant.not_halted observed
  | next observed tail induction =>
      exact induction (invariant.running observed)

theorem rejectionProgram_diverges_on_all_true :
    ¬ Nonempty (boolProblem.RandomSuccessfulRun rejectionProgram
      (fun _ ↦ true) () trivial) := by
  rintro ⟨run⟩
  apply no_rejection_trace_of_loop_invariant
    (source := fun _ ↦ true) (trace := run.trace.operational)
  left
  exact ⟨rfl, by simp⟩

/-- No finite worst-case step/draw pair can cover the rejection loop. -/
theorem rejectionProgram_not_every_source_bounded
    (stepBound drawBound : boolProblem.Input → Nat) :
    ¬ (∀ source,
      source ∈ boolProblem.RandomTerminationWithinEvent rejectionProgram
        stepBound drawBound () trivial) := by
  intro everySource
  rcases everySource (fun _ ↦ true) with ⟨run, output, represented, steps, draws⟩
  exact rejectionProgram_diverges_on_all_true ⟨run⟩

/-- The source survives the first `attempts` rejection tests. -/
def rejectionSurvivalEvent (attempts : Nat) : Set RandomBit.Source :=
  {source | ∀ index < attempts, source index = true}

theorem rejectionSurvivalEvent_eq_pi (attempts : Nat) :
    rejectionSurvivalEvent attempts =
      Set.pi (Finset.range attempts) (fun _ ↦ {true}) := by
  ext source
  simp [rejectionSurvivalEvent]

theorem rejectionSurvivalEvent_measurable (attempts : Nat) :
    MeasurableSet (rejectionSurvivalEvent attempts) := by
  rw [rejectionSurvivalEvent_eq_pi]
  exact MeasurableSet.pi (Finset.range attempts).countable_toSet
    (fun _ _ ↦ MeasurableSet.singleton true)

theorem rejectionSurvivalEvent_probability (attempts : Nat) :
    RandomBit.sourceLaw (rejectionSurvivalEvent attempts) =
      ((2 : ENNReal)⁻¹) ^ attempts := by
  rw [rejectionSurvivalEvent_eq_pi]
  change (Measure.infinitePi fun _ : Nat ↦ RandomBit.coordinateLaw)
      (Set.pi (Finset.range attempts) (fun _ ↦ {true})) = _
  calc
    _ = ∏ _index ∈ Finset.range attempts,
        RandomBit.coordinateLaw {true} :=
      Measure.infinitePi_pi (fun _ : Nat ↦ RandomBit.coordinateLaw)
        (fun _ _ ↦ MeasurableSet.singleton true)
    _ = ((2 : ENNReal)⁻¹) ^ attempts := by
      simp [RandomBit.coordinateLaw, Finset.prod_const]

/-- Number of draws before acceptance, with the all-true source assigned infinity. -/
noncomputable def rejectionDrawEnvelope (source : RandomBit.Source) : ENNReal :=
  ∑' attempts : Nat,
    (rejectionSurvivalEvent attempts).indicator (fun _ ↦ (1 : ENNReal)) source

theorem rejectionDrawEnvelope_measurable : Measurable rejectionDrawEnvelope := by
  apply Measurable.tsum
  intro attempts
  exact measurable_const.indicator (rejectionSurvivalEvent_measurable attempts)

theorem rejectionDrawEnvelope_expected :
    ∫⁻ source, rejectionDrawEnvelope source ∂RandomBit.sourceLaw = 2 := by
  unfold rejectionDrawEnvelope
  rw [lintegral_tsum]
  · simp [lintegral_indicator (rejectionSurvivalEvent_measurable _),
      lintegral_const, Measure.restrict_apply_univ,
      rejectionSurvivalEvent_probability]
  · intro attempts
    exact (measurable_const.indicator
      (rejectionSurvivalEvent_measurable attempts)).aemeasurable

theorem rejectionDrawEnvelope_of_first_false (source : RandomBit.Source) (attempts : Nat)
    (survives : ∀ index < attempts, source index = true)
    (accepts : source attempts = false) :
    rejectionDrawEnvelope source = attempts + 1 := by
  unfold rejectionDrawEnvelope
  rw [tsum_eq_sum (s := Finset.range (attempts + 1))]
  ·
    have everyIncluded : ∀ index ∈ Finset.range (attempts + 1),
        source ∈ rejectionSurvivalEvent index := by
      intro index included offset below
      exact survives offset (lt_of_lt_of_le below (Nat.le_of_lt_succ (Finset.mem_range.mp included)))
    calc
      ∑ index ∈ Finset.range (attempts + 1),
          (rejectionSurvivalEvent index).indicator (fun _ ↦ (1 : ENNReal)) source =
          ∑ _index ∈ Finset.range (attempts + 1), (1 : ENNReal) := by
            apply Finset.sum_congr rfl
            intro index included
            simp [everyIncluded index included]
      _ = attempts + 1 := by simp
  · intro index outside
    have above : attempts + 1 ≤ index := by
      simpa [Finset.mem_range] using outside
    have notSurvives : source ∉ rejectionSurvivalEvent index := by
      intro survivesIndex
      have := survivesIndex attempts (lt_of_lt_of_le (Nat.lt_succ_self attempts) above)
      simp [accepts] at this
    simp [notSurvives]

theorem rejectionDrawEnvelope_all_true :
    rejectionDrawEnvelope (fun _ ↦ true) = ⊤ := by
  unfold rejectionDrawEnvelope
  have eachTerm : ∀ attempts,
      (rejectionSurvivalEvent attempts).indicator (fun _ ↦ (1 : ENNReal))
        (fun _ ↦ true) = 1 := by
    intro attempts
    simp [rejectionSurvivalEvent]
  simp_rw [eachTerm]
  simp

theorem rejectionRuntime_eq_envelope (source : RandomBit.Source) :
    boolProblem.randomRuntimeENNReal rejectionProgram () trivial source =
      1 + 2 * rejectionDrawEnvelope source := by
  classical
  by_cases hasFalse : ∃ attempts, source attempts = false
  · let attempts := Nat.find hasFalse
    have accepts : source attempts = false := Nat.find_spec hasFalse
    have survives : ∀ index < attempts, source index = true := by
      intro index below
      have notFalse : source index ≠ false := by
        intro isFalse
        exact (not_lt_of_ge (Nat.find_min' hasFalse isFalse)) below
      cases bit : source index
      · exact (notFalse bit).elim
      · rfl
    obtain ⟨run, steps, draws, represented⟩ :=
      rejection_run_of_first_false source attempts survives accepts
    rw [boolProblem.randomRuntimeENNReal_eq_run rejectionProgram () trivial source run,
      steps, rejectionDrawEnvelope_of_first_false source attempts survives accepts]
    rw [mul_add]
    norm_num
    have three : (3 : ENNReal) = 1 + 2 := by norm_num
    rw [three]
    ac_rfl
  · have sourceEq : source = fun _ ↦ true := by
      funext index
      cases bit : source index
      · exact (hasFalse ⟨index, bit⟩).elim
      · rfl
    subst source
    have noRun := rejectionProgram_diverges_on_all_true
    let Run := boolProblem.RandomSuccessfulRun rejectionProgram (fun _ ↦ true) () trivial
    haveI : IsEmpty Run := not_nonempty_iff.mp noRun
    simp [StructuredProblem.randomRuntimeENNReal, rejectionDrawEnvelope_all_true, Run]

theorem rejectionRuntime_measurable :
    Measurable (boolProblem.randomRuntimeENNReal rejectionProgram () trivial) := by
  rw [funext rejectionRuntime_eq_envelope]
  exact measurable_const.add (measurable_const.mul rejectionDrawEnvelope_measurable)

theorem rejectionRuntime_expected :
    ∫⁻ source,
      boolProblem.randomRuntimeENNReal rejectionProgram () trivial source
        ∂RandomBit.sourceLaw = 5 := by
  simp_rw [rejectionRuntime_eq_envelope]
  rw [lintegral_add_left measurable_const,
    lintegral_const_mul 2 rejectionDrawEnvelope_measurable,
    rejectionDrawEnvelope_expected]
  rw [lintegral_const]
  norm_num

theorem rejectionTerminationEvent_eq :
    boolProblem.RandomTerminationEvent rejectionProgram () trivial =
      {source | boolProblem.randomRuntimeENNReal rejectionProgram () trivial source < ⊤} := by
  ext source
  constructor
  · rintro ⟨run⟩
    change boolProblem.randomRuntimeENNReal rejectionProgram () trivial source < ⊤
    rw [boolProblem.randomRuntimeENNReal_eq_run rejectionProgram () trivial source run]
    exact ENNReal.coe_lt_top
  · intro finiteRuntime
    change boolProblem.randomRuntimeENNReal rejectionProgram () trivial source < ⊤ at finiteRuntime
    by_contra noRun
    let Run := boolProblem.RandomSuccessfulRun rejectionProgram source () trivial
    haveI : IsEmpty Run := not_nonempty_iff.mp noRun
    have runtimeTop :
        boolProblem.randomRuntimeENNReal rejectionProgram () trivial source = ⊤ := by
      simp [StructuredProblem.randomRuntimeENNReal, Run]
    rw [runtimeTop] at finiteRuntime
    exact (lt_irrefl ⊤ finiteRuntime).elim

theorem rejectionTerminationEvent_measurable :
    MeasurableSet (boolProblem.RandomTerminationEvent rejectionProgram () trivial) := by
  rw [rejectionTerminationEvent_eq]
  exact rejectionRuntime_measurable measurableSet_Iio

theorem rejectionProgram_correct_on_every_halting_run :
    boolProblem.CorrectOnEveryHaltingRun rejectionProgram := by
  intro input validInput source run
  cases input
  classical
  have hasFalse : ∃ attempts, source attempts = false := by
    by_contra noFalse
    have sourceEq : source = fun _ ↦ true := by
      funext index
      cases bit : source index
      · exact (noFalse ⟨index, bit⟩).elim
      · rfl
    subst source
    exact rejectionProgram_diverges_on_all_true ⟨run⟩
  let attempts := Nat.find hasFalse
  have accepts : source attempts = false := Nat.find_spec hasFalse
  have survives : ∀ index < attempts, source index = true := by
    intro index below
    have notFalse : source index ≠ false := by
      intro isFalse
      exact (not_lt_of_ge (Nat.find_min' hasFalse isFalse)) below
    cases bit : source index
    · exact (notFalse bit).elim
    · rfl
  obtain ⟨canonical, steps, draws, represented⟩ :=
    rejection_run_of_first_false source attempts survives accepts
  have finalEq := (run.trace.operational.deterministic canonical.trace.operational).1
  rw [← finalEq] at represented
  exact ⟨false, represented, rfl⟩

def rejectionExpectedBound (_ : boolProblem.Input) : ENNReal := 5

/-- Genuine Las Vegas rejection sampling: zero error and expectation five fetched steps. -/
noncomputable def rejectionExpectedTimeCertificate :
    boolProblem.LasVegasExpectedTimeCertificate rejectionExpectedBound where
  program := rejectionProgram
  valid := rejectionProgram_valid
  correctOnEveryHaltingRun := rejectionProgram_correct_on_every_halting_run
  terminationMeasurable input validInput := by
    cases input
    exact rejectionTerminationEvent_measurable
  terminatesAlmostSurely input validInput := by
    cases input
    have almostEverywhereFinite : ∀ᵐ source ∂RandomBit.sourceLaw,
        boolProblem.randomRuntimeENNReal rejectionProgram () trivial source < ⊤ :=
      ae_lt_top rejectionRuntime_measurable (by rw [rejectionRuntime_expected]; norm_num)
    rw [rejectionTerminationEvent_eq]
    have measureFull := (ae_mem_iff_measure_eq
      (rejectionRuntime_measurable measurableSet_Iio).nullMeasurableSet).mp
      almostEverywhereFinite
    have setEq :
        boolProblem.randomRuntimeENNReal rejectionProgram () trivial ⁻¹' Set.Iio ⊤ =
          {source | boolProblem.randomRuntimeENNReal rejectionProgram () trivial source < ⊤} :=
      rfl
    rw [setEq] at measureFull
    simpa using measureFull
  runtimeMeasurable input validInput := by
    cases input
    exact rejectionRuntime_measurable
  expectedRuntime input validInput := by
    cases input
    rw [rejectionRuntime_expected]
    change (5 : ENNReal) ≤ 5
    exact le_rfl
  expectedStepBound_finite input validInput := by
    cases input
    norm_num [rejectionExpectedBound]


end

end AlgoleanTests.RandomizedGuarantees
