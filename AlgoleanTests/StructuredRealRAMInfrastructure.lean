/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.StructuredRealRAM
public meta import Algolean.Audit.StructuredRealRAM
public import Algolean.Complexity.Basic

/-! # Semantic regressions for the two-bank structured exact-real/natural RAM -/

@[expose] public section

namespace AlgoleanTests.StructuredRealRAMInfrastructure

open Algolean Algorithms
open Algorithms.StructuredRealRAM

#synth CanonicalLayout (Array (Nat × Real))
#synth CanonicalLayout (Vector Bool 4)
#synth CanonicalLayout (Fin 3 → Rat)
#synth CanonicalLayout (DirectedEdgeList Real)

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Layout.custom

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Layout.viaEquiv

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check CanonicalLayout.ofEquiv

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.extra

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.realToNat

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.natToReal

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.floor

/- Query algorithms and finite-machine algorithms retain visibly different theorem types. -/
#check QueryProblem.HasQueryAlgorithm
#check MachineProblem.HasFixedMachineAlgorithm
#check MachineProblem.HasAlgorithmBy

/- Natural-table contents can drive exact-real random access in the actual machine trace. -/
#check indirectRealLookup_trace
#check fixedIndex_trace

def compactValues : RealArray := ⟨#[1, 3, 5]⟩

/-- Compact real arrays expose contiguous real-bank cells without scanning structural headers. -/
example :
    let memory := Layout.realArray.init compactValues
    memory.realMem 1 = 3 := by
  have represented := Layout.realArray.init_rep compactValues
  exact RealArrayRef.represented_get ⟨Layout.inputRegion⟩ compactValues.value
    (Layout.realArray.init compactValues) represented 1 (by decide)

/-- Every standard output representation remains functional. -/
example (memory : Memory) (region : Region) (left right : DenseMatrix Real)
    (leftRep : (layoutOf (DenseMatrix Real)).RepAt region left memory)
    (rightRep : (layoutOf (DenseMatrix Real)).RepAt region right memory) :
    left = right :=
  (layoutOf (DenseMatrix Real)).rep_functional region leftRep rightRep

namespace ExactInputBound

def problem : MachineProblem :=
  MachineProblem.ofCanonical Unit Unit Layout.inputRegion (fun _ ↦ True) (fun _ _ ↦ True)

def bound : problem.Input → Cost := fun _ ↦ (Instruction.halt (.literal 0)).cost

def certificate : MachineProblem.FixedAlgorithmCertificateBy problem bound where
  program := [.halt (.literal 0)]
  valid := by
    intro pc instruction fetch target successor
    cases pc with
    | zero =>
        simp at fetch
        subst instruction
        simp [Instruction.successors] at successor
    | succ pc => simp at fetch
  solves input validInput := by
    cases input
    refine ⟨(), {
      final := problem.initialMemory ()
      result := 0
      cost := (Instruction.halt (.literal 0)).cost
      steps := 1
      trace := .halt ?_ }, ?_, trivial, le_rfl⟩
    · simp [step, execute, RealOperand.eval, MachineProblem.initialMemory, problem]
    · exact Layout.unit.init_rep ()

theorem exists_algorithm : problem.HasAlgorithmBy bound := ⟨certificate⟩

def publication : Audit.FixedByPublication problem bound where
  certificate := certificate
  certificateName := ``certificate
  problemName := ``problem
  boundName := ``bound
  correctnessTheorem := ``exists_algorithm

#algorithm_audit publication

end ExactInputBound

namespace ProcedureKinds

def contract : ProcedureContract :=
  ProcedureContract.ofCanonical Unit Unit (fun _ ↦ True) (fun _ _ ↦ True)

#check ProcedureCertificate contract
#check RestoringProcedureCertificate contract
#check HasProcedure contract
#check HasRestoringProcedure contract

end ProcedureKinds

/- Exact continuous-randomness certificates cannot omit success-event measurability. -/
#check UniformRealRandomizedMachineProblem.MonteCarloAlgorithmCertificate.measurableSuccess
#check BitRandomizedMachineProblem.MonteCarloAlgorithmCertificate.measurableSuccess

namespace ContinuousMeasurability

open MeasureTheory

def problem : UniformRealRandomizedMachineProblem where
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := Layout.inputRegion
  pre _ := True
  post _ _ := True

def program : StructuredRealRAM.UniformReal.Program := [.core (.halt (.literal 0))]

def bound : Nat → StructuredRealRAM.UniformReal.Cost := fun _ ↦
  StructuredRealRAM.RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost

def failure : problem.Input → Probability := fun _ ↦ ⟨0, by simp⟩

theorem succeeds (source : StructuredRealRAM.UniformReal.Source) :
    problem.SucceedsWithin program () source (bound (problem.inputSize ())) := by
  let initial := problem.initialMemory ()
  let run : UniformRealRandomizedMachineProblem.SuccessfulRun problem program () source := {
    final := initial
    result := 0
    cost := StructuredRealRAM.RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost
    steps := 1
    randomDraws := 0
    trace := .halt (by
      simp [StructuredRealRAM.UniformReal.step, StructuredRealRAM.UniformReal.execute,
        StructuredRealRAM.UniformReal.liftCoreOutcome, program, StructuredRealRAM.execute,
        RealOperand.eval,
        StructuredRealRAM.RandomBit.Configuration.initial, initial]) }
  exact ⟨(), run, Layout.unit.init_rep (), trivial, le_rfl⟩

theorem successEvent_eq_univ :
    problem.SuccessEvent program () (bound (problem.inputSize ())) = Set.univ := by
  ext source
  simp only [UniformRealRandomizedMachineProblem.SuccessEvent, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  exact succeeds source

def certificate : problem.MonteCarloAlgorithmCertificate bound failure where
  program := program
  valid := by
    intro pc instruction fetch target member
    cases pc with
    | zero =>
        simp [program] at fetch
        subst instruction
        simp [StructuredRealRAM.UniformReal.Instruction.successors,
          StructuredRealRAM.Instruction.successors] at member
    | succ pc => simp [program] at fetch
  measurableSuccess input validInput := by
    cases input
    rw [successEvent_eq_univ]
    exact MeasurableSet.univ
  solves input validInput := by
    cases input
    constructor
    · intro source
      rcases succeeds source with ⟨output, run, represented, _, cost⟩
      exact ⟨output, run, represented, cost⟩
    · rw [successEvent_eq_univ]
      change StructuredRealRAM.UniformReal.sourceLaw Set.univ ≥ 1 - 0
      simp

theorem exists_algorithm : problem.HasMonteCarloAlgorithm bound failure := ⟨certificate⟩

end ContinuousMeasurability

/- External oracle certificates remain separately typed and visibly non-vacuous. -/
#check OracleMachineProblem.OracleAlgorithmCertificate.interfaceNonvacuous
#check StructuredRealRAM.OracleMachine.Instruction.oracleCall

#layout_audit StructuredRealRAM (Array (Nat × Real))
#machine_profile_audit Audit.coreProfileAudit
#machine_profile_audit Audit.randomBitProfileAudit
#machine_profile_audit Audit.uniformRealProfileAudit

#check Linker.link
#check Linker.link_length
#check Linker.LinkableRelativeAlgorithmCertificate.hasAlgorithm

#print axioms ExactInputBound.exists_algorithm

end AlgoleanTests.StructuredRealRAMInfrastructure
