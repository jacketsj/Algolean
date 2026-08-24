/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.StructuredRealRAM
public meta import Algolean.Audit.StructuredRealRAM
public import Algolean.Complexity.Basic
public import Algolean.Models.StructuredRealRAM.Physical

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
#check UniformRealRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate.measurableSuccess
#check BitRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate.measurableSuccess

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

def certificate : problem.BoundedTimeMonteCarloAlgorithmCertificate bound failure where
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

theorem exists_algorithm : problem.HasBoundedTimeMonteCarloAlgorithm bound failure :=
  ⟨certificate⟩

end ContinuousMeasurability

/- External oracle certificates remain separately typed and visibly non-vacuous. -/
#check OracleMachineProblem.OracleAlgorithmCertificate.interfaceNonvacuous
#check StructuredRealRAM.OracleMachine.Instruction.oracleCall

#layout_audit StructuredRealRAM (Array (Nat × Real))
#machine_profile_audit Audit.coreProfileAudit
#machine_profile_audit Audit.randomBitProfileAudit
#machine_profile_audit Audit.uniformRealProfileAudit

namespace ArithmeticProfiles

def squareRootInstruction :
    ArithmeticInstruction AlgebraicSqrtExactRealNatRAM :=
  .unary .sqrt (by simp [ArithmeticProfile.AllowsUnary]) (.literal 4) 0 1

/-- The algebraic core excludes square root as a kernel-reduced proposition. -/
example : ¬ ArithmeticProfile.algebraic.AllowsUnary .sqrt := by
  simp [ArithmeticProfile.AllowsUnary]

/-- Square root is admitted only after selecting the named square-root profile. -/
example : AlgebraicSqrtExactRealNatRAM.AllowsUnary .sqrt := by
  simp [ArithmeticProfile.AllowsUnary]

/-- Floor is absent from the algebraic profile and present in the separately named profile. -/
example : ¬ AlgebraicExactRealNatRAM.AllowsFloorToNat ∧
    FloorExactRealNatRAM.AllowsFloorToNat := by
  simp [ArithmeticProfile.AllowsFloorToNat]

/-- Optional primitive charges occupy their own resource coordinate. -/
example : squareRootInstruction.cost.count (.unary .sqrt) = 1 := by
  simp [squareRootInstruction, ArithmeticInstruction.cost, ArithmeticCost.count,
    ArithmeticCost.ofPrimitive]

/-- Three emitted square-root instructions contribute exactly three square-root charges. -/
def rootZero (next : Nat) : ArithmeticInstruction AlgebraicSqrtExactRealNatRAM :=
  .unary .sqrt (by simp [ArithmeticProfile.AllowsUnary]) (.literal 0) 0 next

def haltZero : Instruction := .halt (.literal 0)

def threeRootProgram : ArithmeticProgram AlgebraicSqrtExactRealNatRAM :=
  [rootZero 1, rootZero 2, rootZero 3, .core haltZero]

theorem writeZero_empty : Memory.empty.writeReal 0 0 = Memory.empty := by
  unfold Memory.writeReal Memory.empty
  congr
  funext address
  simp

/-- Three roots really execute in one same-trace derivation, rather than merely being summed. -/
noncomputable def threeRootTrace :
    ArithmeticHaltingTrace threeRootProgram ⟨0, Memory.empty⟩ Memory.empty 0
      ((rootZero 1).cost + ((rootZero 2).cost +
        ((rootZero 3).cost + ArithmeticCost.ofCore haltZero.cost))) 4 := by
  apply ArithmeticHaltingTrace.next (nextConfiguration := ⟨1, Memory.empty⟩)
  · simp [arithmeticStep, threeRootProgram, rootZero, executeArithmetic,
      RealUnaryPrimitive.eval, RealOperand.eval, writeZero_empty]
  · apply ArithmeticHaltingTrace.next (nextConfiguration := ⟨2, Memory.empty⟩)
    · simp [arithmeticStep, threeRootProgram, rootZero, executeArithmetic,
        RealUnaryPrimitive.eval, RealOperand.eval, writeZero_empty]
    · apply ArithmeticHaltingTrace.next (nextConfiguration := ⟨3, Memory.empty⟩)
      · simp [arithmeticStep, threeRootProgram, rootZero, executeArithmetic,
          RealUnaryPrimitive.eval, RealOperand.eval, writeZero_empty]
      · apply ArithmeticHaltingTrace.halt
        simp [arithmeticStep, threeRootProgram, haltZero, executeArithmetic, execute,
          RealOperand.eval]

/-- The operation-sensitive coordinate of the actual trace is exactly three. -/
example :
    let charge := (rootZero 1).cost + ((rootZero 2).cost +
      ((rootZero 3).cost + ArithmeticCost.ofCore haltZero.cost))
    charge.count (.unary .sqrt) = 3 := by
  change (if RealPrimitive.unary .sqrt = RealPrimitive.unary .sqrt then 1 else 0) +
    ((if RealPrimitive.unary .sqrt = RealPrimitive.unary .sqrt then 1 else 0) +
      ((if RealPrimitive.unary .sqrt = RealPrimitive.unary .sqrt then 1 else 0) + 0)) = 3
  decide

/-- The closed core embedding works for every selected arithmetic profile. -/
example (program : Program) (valid : program.Valid) :
    ArithmeticProgram.Valid
      (liftCoreArithmetic (profile := AlgebraicSqrtExactRealNatRAM) program) :=
  liftCoreArithmetic_valid program valid

#arithmetic_profile_audit AlgebraicExactRealNatRAM
#arithmetic_profile_audit AlgebraicSqrtExactRealNatRAM
#arithmetic_profile_audit TrigExactRealNatRAM

end ArithmeticProfiles

namespace ExactGraphRelations

def edgeListPayload : Nat × Array Nat × Array Nat × Array Unit :=
  (3, #[0], #[1], #[()])

def edgeList : DirectedEdgeList Unit :=
  Tagged.mk ⟨edgeListPayload, by
    simp [edgeListPayload, DirectedEdgeList.Valid]⟩

def intendedAdjacency (tail head : Nat) : Prop :=
  (tail = 0 ∧ head = 1) ∨ (tail = 1 ∧ head = 2)

/-- The one stored edge is semantically valid. -/
theorem everyStoredEdge : DirectedEdgeList.EveryStoredEdgeSatisfies edgeList
    (fun tail head _ ↦ intendedAdjacency tail head) := by
  intro index indexInRange
  have indexZero : index = 0 := by
    change index < 1 at indexInRange
    omega
  subst index
  exact ⟨0, 1, (), by decide, by decide, by decide, Or.inl ⟨rfl, rfl⟩⟩

/-- Exact representation rejects the omitted mathematical edge `(1,2)`. -/
theorem notExact : ¬ DirectedEdgeList.RepresentsExactly edgeList intendedAdjacency := by
  intro exact
  rcases exact.2 1 2 (Or.inr ⟨rfl, rfl⟩) with ⟨index, inRange, tail, head⟩
  have indexZero : index = 0 := by
    change index < 1 at inRange
    omega
  subst index
  norm_num [edgeList, edgeListPayload, DirectedEdgeList.tail,
    DirectedEdgeList.payload] at tail

end ExactGraphRelations

#check Linker.link
#check Linker.link_length
#check Linker.LinkableRelativeAlgorithmCertificate.hasAlgorithm

#print axioms ExactInputBound.exists_algorithm

end AlgoleanTests.StructuredRealRAMInfrastructure
