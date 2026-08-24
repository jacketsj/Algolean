/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.StructuredRealRAMProcedure

/-! # Contract-relative structured exact-real/natural programs -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

noncomputable section

/-- Finite typed dependency interface with no implementation fields. -/
structure DependencySignature where
  Op : Type
  finiteOp : Fintype Op
  decEqOp : DecidableEq Op
  contract : Op → ProcedureContract
  bound : (op : Op) → ProcedureBound (contract op)

attribute [instance] DependencySignature.finiteOp DependencySignature.decEqOp

/-- One coherent answer source for a complete relative execution. -/
structure AdmissibleResponder (signature : DependencySignature) where
  answer : (op : signature.Op) →
    (input : (signature.contract op).Input) → (signature.contract op).Output
  correct : ∀ op input, (signature.contract op).pre input →
    (signature.contract op).post input (answer op input)

/-- Typed record of one actual dynamic dependency call. -/
structure DependencyCallRecord (signature : DependencySignature) where
  callSite : Nat
  op : signature.Op
  input : (signature.contract op).Input
  output : (signature.contract op).Output
  outputCorrect : (signature.contract op).post input output
  chargedCost : Cost
  chargedCost_eq : chargedCost = signature.bound op input

/-- Exact dependency charge recorded by a dynamic relative trace. -/
def totalDependencyCost (calls : List (DependencyCallRecord signature)) : Cost :=
  (calls.map DependencyCallRecord.chargedCost).sum

/-- Closed first-order relative instruction syntax. -/
inductive OpenInstruction (signature : DependencySignature) where
  | core (instruction : Instruction)
  | call (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)

abbrev OpenProgram (signature : DependencySignature) := List (OpenInstruction signature)

def OpenInstruction.successors : OpenInstruction signature → List Nat
  | .core instruction => instruction.successors
  | .call _ _ _ next => [next]

def OpenProgram.Valid (program : OpenProgram signature) : Prop :=
  ∀ (pc : Nat) (instruction : OpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ OpenInstruction.successors instruction, target < program.length

/-- One relational relative transition and its optional typed call record. -/
inductive OpenStep (signature : DependencySignature) (responder : AdmissibleResponder signature)
    (program : OpenProgram signature) :
    Configuration → StepResult → Cost → Option (DependencyCallRecord signature) → Prop where
  | core {configuration instruction outcome cost}
      (fetch : program[configuration.pc]? = some (.core instruction))
      (executes : execute instruction configuration.memory = ⟨outcome, cost⟩) :
      OpenStep signature responder program configuration outcome cost none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      OpenStep signature responder program configuration
        (.running ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (responder.answer op input) configuration.memory⟩)
        (signature.bound op input)
        (some {
          callSite := configuration.pc
          op := op
          input := input
          output := responder.answer op input
          outputCorrect := responder.correct op input validInput
          chargedCost := signature.bound op input
          chargedCost_eq := rfl })

/-- A call transition's charged cost is exactly the cost stored in its typed record. -/
theorem OpenStep.call_cost
    {signature : DependencySignature} {responder : AdmissibleResponder signature}
    {program : OpenProgram signature} {configuration : Configuration}
    {outcome : StepResult} {cost : Cost} {call : DependencyCallRecord signature}
    (step : OpenStep signature responder program configuration outcome cost (some call)) :
    cost = call.chargedCost := by
  cases step
  rfl

/-- Same-trace relative termination with the exact dynamic call sequence. -/
inductive OpenHaltingTrace (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : OpenProgram signature) :
    Configuration → Memory → Real → Cost → Nat → List (DependencyCallRecord signature) → Prop where
  | halt {configuration memory result cost}
      (step : OpenStep signature responder program configuration
        (.halted memory result) cost none) :
      OpenHaltingTrace signature responder program configuration memory result cost 1 []
  | core {configuration next final result headCost tailCost steps calls}
      (step : OpenStep signature responder program configuration (.running next) headCost none)
      (tail : OpenHaltingTrace signature responder program next final result tailCost steps calls) :
      OpenHaltingTrace signature responder program configuration final result
        (headCost + tailCost) (steps + 1) calls
  | call {configuration next final result headCost tailCost steps call calls}
      (step : OpenStep signature responder program configuration
        (.running next) headCost (some call))
      (tail : OpenHaltingTrace signature responder program next final result tailCost steps calls) :
      OpenHaltingTrace signature responder program configuration final result
        (headCost + tailCost) (steps + 1) (call :: calls)

/-- The trace cost splits into ordinary core cost and the exact sum of recorded call charges. -/
theorem OpenHaltingTrace.cost_decomposition
    (trace : OpenHaltingTrace signature responder program initial final result cost steps calls) :
    ∃ coreCost : Cost, cost = coreCost + totalDependencyCost calls := by
  induction trace with
  | @halt configuration memory result haltCost step =>
      exact ⟨haltCost, by simp [totalDependencyCost]⟩
  | @core configuration next final result headCost tailCost steps calls step tail induction =>
      rcases induction with ⟨coreCost, equal⟩
      refine ⟨headCost + coreCost, ?_⟩
      rw [equal]
      exact (add_assoc headCost coreCost (totalDependencyCost calls)).symm
  | @call configuration next final result headCost tailCost steps call calls
      step tail induction =>
      rcases induction with ⟨coreCost, equal⟩
      refine ⟨coreCost, ?_⟩
      rw [step.call_cost, equal]
      simp only [totalDependencyCost, List.map_cons, List.sum_cons]
      ac_rfl

/-- Dynamic call count is exposed rather than collapsed into an opaque counter. -/
@[nolint unusedArguments]
def OpenHaltingTrace.callCount
    (_trace : OpenHaltingTrace signature responder program initial final result cost steps calls) :
    Nat := calls.length

/-- Relative problem execution against one coherent responder. -/
def RelativeSolvesWithinBy (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : OpenProgram signature)
    (problem : MachineProblem) (bound : problem.Input → Cost) : Prop :=
  ∀ input, problem.pre input →
    ∃ output final result cost steps calls,
      OpenHaltingTrace signature responder program ⟨0, problem.initialMemory input⟩
        final result cost steps calls ∧
      problem.OutputRep output final ∧ problem.post input output ∧ cost ≤ bound input

/-- Explicitly relative certificate, never coerced to an unconditional algorithm. -/
structure RelativeAlgorithmCertificate (signature : DependencySignature)
    (problem : MachineProblem) (bound : problem.Input → Cost) where
  module : OpenProgram signature
  valid : module.Valid
  solvesAgainstContracts : ∀ responder,
    RelativeSolvesWithinBy signature responder module problem bound

/-- Concrete restoring implementations used by the shared-body exact-state linker. -/
structure ImplementationEnvironment (signature : DependencySignature) where
  implementation : (op : signature.Op) →
    RestoringProcedureCertificate (signature.contract op) (signature.bound op)

def ImplementationEnvironment.responder (environment : ImplementationEnvironment signature) :
    AdmissibleResponder signature where
  answer op input := (environment.implementation op).output input
  correct op input valid := (environment.implementation op).outputCorrect input valid

def HasImplementations (signature : DependencySignature) : Prop :=
  Nonempty (ImplementationEnvironment signature)

end

end Algolean.Algorithms.StructuredRealRAM
