/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.RandomizedMachineProblem
public import Algolean.Complexity.StructuredRealRAMRelative

/-!
# Randomized structured-real clients with deterministic procedure dependencies

Calls are finite typed syntax and preserve the hidden lengthless source cursor.  This layer is
explicitly relative; the automatic linker produces ordinary sealed `UniformReal.Program` syntax.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

open MeasureTheory

noncomputable section

inductive UniformOpenInstruction (signature : DependencySignature) where
  | machine (instruction : UniformReal.Instruction)
  | call (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)

abbrev UniformOpenProgram (signature : DependencySignature) :=
  List (UniformOpenInstruction signature)

def UniformOpenInstruction.successors : UniformOpenInstruction signature → List Nat
  | .machine instruction => instruction.successors
  | .call _ _ _ next => [next]

def UniformOpenProgram.Valid (program : UniformOpenProgram signature) : Prop :=
  ∀ (pc : Nat) (instruction : UniformOpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ UniformOpenInstruction.successors instruction, target < program.length

inductive UniformOpenStep (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : UniformOpenProgram signature)
    (source : UniformReal.Source) :
    UniformReal.Configuration → UniformReal.StepResult → UniformReal.Cost →
      Option (DependencyCallRecord signature) → Prop where
  | machine {configuration instruction outcome cost}
      (fetch : program[configuration.pc]? = some (.machine instruction))
      (executes : UniformReal.execute source instruction configuration = ⟨outcome, cost⟩) :
      UniformOpenStep signature responder program source configuration outcome cost none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      UniformOpenStep signature responder program source configuration
        (.running ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (responder.answer op input) configuration.memory, configuration.randomCursor⟩)
        (RandomBit.Cost.ofCore (signature.bound op input))
        (some {
          callSite := configuration.pc
          op := op
          input := input
          output := responder.answer op input
          outputCorrect := responder.correct op input validInput
          chargedCost := signature.bound op input
          chargedCost_eq := rfl })

inductive UniformOpenHaltingTrace (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : UniformOpenProgram signature)
    (source : UniformReal.Source) :
    UniformReal.Configuration → Memory → Real → UniformReal.Cost → Nat → Nat →
      List (DependencyCallRecord signature) → Prop where
  | halt {configuration memory result cost draws}
      (step : UniformOpenStep signature responder program source configuration
        (.halted memory result draws) cost none) :
      UniformOpenHaltingTrace signature responder program source configuration memory result
        cost 1 draws []
  | machine {configuration next final result headCost tailCost steps draws calls}
      (step : UniformOpenStep signature responder program source configuration
        (.running next) headCost none)
      (tail : UniformOpenHaltingTrace signature responder program source next final result
        tailCost steps draws calls) :
      UniformOpenHaltingTrace signature responder program source configuration final result
        (headCost + tailCost) (steps + 1) draws calls
  | call {configuration next final result headCost tailCost steps draws call calls}
      (step : UniformOpenStep signature responder program source configuration
        (.running next) headCost (some call))
      (tail : UniformOpenHaltingTrace signature responder program source next final result
        tailCost steps draws calls) :
      UniformOpenHaltingTrace signature responder program source configuration final result
        (headCost + tailCost) (steps + 1) draws (call :: calls)

def UniformRelativeSuccessEvent (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (problem : UniformRealRandomizedMachineProblem)
    (program : UniformOpenProgram signature) (bound : Nat → UniformReal.Cost)
    (input : problem.Input) : Set UniformReal.Source :=
  {source | ∃ output final result cost steps draws calls,
    UniformOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls ∧
    problem.OutputRep output final ∧ problem.post input output ∧
    cost ≤ bound (problem.inputSize input)}

def UniformRelativeTermination (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (problem : UniformRealRandomizedMachineProblem)
    (program : UniformOpenProgram signature) (bound : Nat → UniformReal.Cost)
    (input : problem.Input) (source : UniformReal.Source) : Prop :=
  ∃ output final result cost steps draws calls,
    UniformOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls ∧
    problem.OutputRep output final ∧ cost ≤ bound (problem.inputSize input)

/-- Relative every-source-time Monte Carlo proof against every coherent contract responder. -/
structure UniformRealBoundedTimeMonteCarloRelativeCertificate
    (signature : DependencySignature)
    (problem : UniformRealRandomizedMachineProblem) (bound : Nat → UniformReal.Cost)
    (failure : problem.Input → Probability) where
  program : UniformOpenProgram signature
  valid : program.Valid
  measurableSuccess : ∀ responder input, problem.pre input →
    MeasurableSet (UniformRelativeSuccessEvent signature responder problem program bound input)
  terminates : ∀ responder input, problem.pre input → ∀ source,
    UniformRelativeTermination signature responder problem program bound input source
  successProbability : ∀ responder input, problem.pre input →
    UniformReal.sourceLaw
      (UniformRelativeSuccessEvent signature responder problem program bound input) ≥
      1 - (failure input : ENNReal)

/-- Compatibility name; the guarantee is every-source bounded-time Monte Carlo. -/
abbrev UniformRelativeAlgorithmCertificate :=
  UniformRealBoundedTimeMonteCarloRelativeCertificate

end

end Algolean.Algorithms.StructuredRealRAM
