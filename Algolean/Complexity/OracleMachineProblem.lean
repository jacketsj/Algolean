/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem
public import Algolean.Models.StructuredRealRAM.Oracle

/-!
# Same-trace oracle-machine algorithm claims

The preferred claim fixes a typed `OracleInterface` before choosing one finite program, requires
the interface to be non-vacuous, and proves correctness for every admissible responder.  One
responder is fixed throughout each execution.  Oracle queries, answer validity, canonical answer
transfer, and their costs are integrated into the same operational trace as the final output.
-/

@[expose] public section

namespace Algolean.Algorithms

open StructuredRealRAM

/-- A structured problem relative to one explicitly fixed typed oracle interface. -/
structure OracleMachineProblem where
  /-- Oracle profile fixed independently of the program witness. -/
  interface : OracleInterface StructuredRealRAM.Cost
  /-- Mathematical input carrier. -/
  Input : Type
  /-- Computational output carrier. -/
  Output : Type
  /-- Closed canonical input layout. -/
  inputLayout : Layout Input
  /-- Closed canonical output layout. -/
  outputLayout : Layout Output
  /-- Designated final-memory output region. -/
  outputRegion : Region
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical correctness relation. -/
  post : Input → Output → Prop

namespace OracleMachineProblem

/-- Represented input-cell count. -/
noncomputable def inputSize (problem : OracleMachineProblem) (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Canonical otherwise-zero input memory. -/
noncomputable def initialMemory (problem : OracleMachineProblem)
    (input : problem.Input) : Memory :=
  problem.inputLayout.init input

/-- Closed relational output interpretation. -/
noncomputable def OutputRep (problem : OracleMachineProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- Canonical oracle-machine output is functional. -/
theorem OutputRep.functional (problem : OracleMachineProblem)
    {left right : problem.Output} {memory : Memory}
    (leftRep : problem.OutputRep left memory) (rightRep : problem.OutputRep right memory) :
    left = right :=
  problem.outputLayout.rep_functional problem.outputRegion leftRep rightRep

/-- One halting run with one responder fixed throughout the same cost/output trace. -/
structure SuccessfulRun (problem : OracleMachineProblem)
    (oracle : AdmissibleOracle problem.interface)
    (program : StructuredRealRAM.OracleMachine.Program) (input : problem.Input) where
  /-- Final ordinary memory. -/
  final : Memory
  /-- Scalar halt result. -/
  result : ℝ
  /-- Same-trace resource vector, including oracle transfer. -/
  cost : StructuredRealRAM.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Coupled behavior and resource derivation. -/
  trace : StructuredRealRAM.OracleMachine.HaltingTrace problem.interface oracle program
    ⟨0, problem.initialMemory input⟩ final result cost steps

/-- One program solves one input for one admissible responder within the same-trace bound. -/
noncomputable def SolvesInputWithin (problem : OracleMachineProblem)
    (oracle : AdmissibleOracle problem.interface)
    (program : StructuredRealRAM.OracleMachine.Program) (input : problem.Input)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output) (run : SuccessfulRun problem oracle program input),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/-- The same fixed program and bound work for every admissible responder and valid input. -/
noncomputable def SolvesWithinEveryOracle (problem : OracleMachineProblem)
    (program : StructuredRealRAM.OracleMachine.Program)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  ∀ oracle : AdmissibleOracle problem.interface,
    ∀ input, problem.pre input →
      problem.SolvesInputWithin oracle program input (bound (problem.inputSize input))

/--
Typed robust oracle certificate.  Non-vacuity is a proof field, not an optional audit annotation;
the responder quantifier is universal and occurs after the concrete program.
-/
structure OracleAlgorithmCertificate (problem : OracleMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- Proof that universal responder quantification is not vacuous. -/
  interfaceNonvacuous : problem.interface.Nonvacuous
  /-- Concrete finite first-order program. -/
  program : StructuredRealRAM.OracleMachine.Program
  /-- All successors stay within the program. -/
  valid : program.Valid
  /-- Correctness and cost for every valid input and admissible responder. -/
  solvesEveryOracle : problem.SolvesWithinEveryOracle program bound

/-- Preferred oracle-algorithm existence claim: non-vacuous and robust to every valid answerer. -/
noncomputable def HasOracleAlgorithm (problem : OracleMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  Nonempty (OracleAlgorithmCertificate problem bound)

/-- Explicit synonym emphasizing universal responder quantification. -/
abbrev HasRobustOracleAlgorithm := HasOracleAlgorithm

end OracleMachineProblem

end Algolean.Algorithms
