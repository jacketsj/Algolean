/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.StructuredRealRAMProfiledProcedure

/-! # Contract-relative programs in one closed structured exact-real profile -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

open MeasureTheory
noncomputable section

/-- Finite typed dependency signature for a fixed final machine profile. -/
structure ProfiledDependencySignature (profile : ClosedMachineProfile) where
  Op : Type
  finiteOp : Fintype Op
  decEqOp : DecidableEq Op
  contract : Op → ProcedureContract
  bound : (op : Op) → ProfiledProcedureBound (contract op)

attribute [instance] ProfiledDependencySignature.finiteOp ProfiledDependencySignature.decEqOp

structure ProfiledAdmissibleResponder (signature : ProfiledDependencySignature profile) where
  answer : (op : signature.Op) →
    (input : (signature.contract op).Input) → (signature.contract op).Output
  correct : ∀ op input, (signature.contract op).pre input →
    (signature.contract op).post input (answer op input)

structure ProfiledDependencyCallRecord (signature : ProfiledDependencySignature profile) where
  callSite : Nat
  op : signature.Op
  input : (signature.contract op).Input
  output : (signature.contract op).Output
  outputCorrect : (signature.contract op).post input output
  chargedCost : ProfiledCost
  chargedCost_eq : chargedCost = signature.bound op input

def profiledTotalDependencyCost
    (calls : List (ProfiledDependencyCallRecord signature)) : ProfiledCost :=
  (calls.map ProfiledDependencyCallRecord.chargedCost).sum

/-- Closed first-order syntax: a profiled machine instruction or a typed abstract call. -/
inductive ProfiledOpenInstruction (signature : ProfiledDependencySignature profile) where
  | machine (instruction : ProfiledInstruction profile)
  | call (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)

abbrev ProfiledOpenProgram (signature : ProfiledDependencySignature profile) :=
  List (ProfiledOpenInstruction signature)

def ProfiledOpenInstruction.successors : ProfiledOpenInstruction signature → List Nat
  | .machine instruction => instruction.successors
  | .call _ _ _ next => [next]

def ProfiledOpenProgram.Valid (program : ProfiledOpenProgram signature) : Prop :=
  ∀ (pc : Nat) instruction, program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

inductive ProfiledOpenStep (signature : ProfiledDependencySignature profile)
    (responder : ProfiledAdmissibleResponder signature)
    (program : ProfiledOpenProgram signature) (source : profile.randomness.Source) :
    ProfiledConfiguration → ProfiledStepResult → ProfiledCost →
      Option (ProfiledDependencyCallRecord signature) → Prop where
  | machine {configuration instruction outcome cost}
      (fetch : program[configuration.pc]? = some (.machine instruction))
      (executes : executeProfiled source instruction configuration = ⟨outcome, cost⟩) :
      ProfiledOpenStep signature responder program source configuration outcome cost none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      ProfiledOpenStep signature responder program source configuration
        (.running ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (responder.answer op input) configuration.memory, configuration.randomCursor⟩)
        (signature.bound op input)
        (some {
          callSite := configuration.pc
          op := op
          input := input
          output := responder.answer op input
          outputCorrect := responder.correct op input validInput
          chargedCost := signature.bound op input
          chargedCost_eq := rfl })

inductive ProfiledOpenHaltingTrace (signature : ProfiledDependencySignature profile)
    (responder : ProfiledAdmissibleResponder signature)
    (program : ProfiledOpenProgram signature) (source : profile.randomness.Source) :
    ProfiledConfiguration → Memory → Real → ProfiledCost → Nat → Nat →
      List (ProfiledDependencyCallRecord signature) → Prop where
  | halt {configuration memory result cost draws}
      (step : ProfiledOpenStep signature responder program source configuration
        (.halted memory result draws) cost none) :
      ProfiledOpenHaltingTrace signature responder program source configuration
        memory result cost 1 draws []
  | machine {configuration next final result headCost tailCost steps draws calls}
      (step : ProfiledOpenStep signature responder program source configuration
        (.running next) headCost none)
      (tail : ProfiledOpenHaltingTrace signature responder program source next
        final result tailCost steps draws calls) :
      ProfiledOpenHaltingTrace signature responder program source configuration
        final result (headCost + tailCost) (steps + 1) draws calls
  | call {configuration next final result headCost tailCost steps draws call calls}
      (step : ProfiledOpenStep signature responder program source configuration
        (.running next) headCost (some call))
      (tail : ProfiledOpenHaltingTrace signature responder program source next
        final result tailCost steps draws calls) :
      ProfiledOpenHaltingTrace signature responder program source configuration
        final result (headCost + tailCost) (steps + 1) draws (call :: calls)

def ProfiledRelativeSolvesWithinBy (signature : ProfiledDependencySignature profile)
    (responder : ProfiledAdmissibleResponder signature)
    (program : ProfiledOpenProgram signature) (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) : Prop :=
  ∀ input, problem.pre input → ∀ source,
    ∃ output final result cost steps draws calls,
      ProfiledOpenHaltingTrace signature responder program source
        (RandomBit.Configuration.initial (problem.initialMemory input))
        final result cost steps draws calls ∧
      problem.OutputRep output final ∧ problem.post input output ∧ cost ≤ bound input

structure ProfiledRelativeAlgorithmCertificate
    (signature : ProfiledDependencySignature profile)
    (problem : ProfiledMachineProblem profile) (bound : problem.Input → ProfiledCost) where
  module : ProfiledOpenProgram signature
  valid : module.Valid
  solvesAgainstContracts : ∀ responder,
    ProfiledRelativeSolvesWithinBy signature responder module problem bound

structure ProfiledImplementationEnvironment
    (signature : ProfiledDependencySignature profile) where
  implementation : (op : signature.Op) →
    ProfiledRestoringProcedureCertificate profile
      (signature.contract op) (signature.bound op)

def ProfiledImplementationEnvironment.responder
    (environment : ProfiledImplementationEnvironment signature) :
    ProfiledAdmissibleResponder signature where
  answer op input := (environment.implementation op).output input
  correct op input valid := (environment.implementation op).outputCorrect input valid

/-- Relative success event for probability transfer through the same-source linker. -/
def ProfiledRelativeSuccessEvent (signature : ProfiledDependencySignature profile)
    (responder : ProfiledAdmissibleResponder signature)
    (problem : ProfiledMachineProblem profile) (program : ProfiledOpenProgram signature)
    (bound : problem.Input → ProfiledCost) (input : problem.Input) :
    Set profile.randomness.Source :=
  {source | ∃ output final result cost steps draws calls,
    ProfiledOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls ∧
    problem.OutputRep output final ∧ problem.post input output ∧ cost ≤ bound input}

/-- Contract-relative bounded-time Monte Carlo in an explicitly selected source profile. -/
structure ProfiledBoundedTimeMonteCarloRelativeCertificate
    (signature : ProfiledDependencySignature profile)
    (problem : ProfiledMachineProblem profile) (bound : problem.Input → ProfiledCost)
    (failure : problem.Input → Probability) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledOpenProgram signature
  valid : program.Valid
  terminates : ∀ responder input, problem.pre input → ∀ source,
    ∃ final result cost steps draws calls,
      ProfiledOpenHaltingTrace signature responder program source
        (RandomBit.Configuration.initial (problem.initialMemory input))
        final result cost steps draws calls ∧ cost ≤ bound input
  successMeasurable : ∀ responder input, problem.pre input →
    MeasurableSet (ProfiledRelativeSuccessEvent signature responder problem program bound input)
  successProbability : ∀ responder input, problem.pre input →
    profile.randomness.sourceLaw
      (ProfiledRelativeSuccessEvent signature responder problem program bound input) ≥
        1 - (failure input : ENNReal)

end

end Algolean.Algorithms.StructuredRealRAM
