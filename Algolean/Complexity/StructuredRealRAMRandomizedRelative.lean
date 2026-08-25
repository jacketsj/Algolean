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
explicitly relative; the automatic linker produces ordinary sealed `RandomBit.Program` syntax.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

open MeasureTheory

noncomputable section

inductive RandomOpenInstruction (signature : DependencySignature) where
  | machine (instruction : RandomBit.Instruction)
  | call (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)

abbrev RandomOpenProgram (signature : DependencySignature) :=
  List (RandomOpenInstruction signature)

def RandomOpenInstruction.successors : RandomOpenInstruction signature → List Nat
  | .machine instruction => instruction.successors
  | .call _ _ _ next => [next]

def RandomOpenProgram.Valid (program : RandomOpenProgram signature) : Prop :=
  ∀ (pc : Nat) (instruction : RandomOpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ RandomOpenInstruction.successors instruction, target < program.length

inductive RandomOpenStep (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : RandomOpenProgram signature)
    (source : RandomBit.Source) :
    RandomBit.Configuration → RandomBit.StepResult → RandomBit.Cost →
      Option (DependencyCallRecord signature) → Prop where
  | machine {configuration instruction outcome cost}
      (fetch : program[configuration.pc]? = some (.machine instruction))
      (executes : RandomBit.execute source instruction configuration = ⟨outcome, cost⟩) :
      RandomOpenStep signature responder program source configuration outcome cost none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      RandomOpenStep signature responder program source configuration
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

inductive RandomOpenHaltingTrace (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (program : RandomOpenProgram signature)
    (source : RandomBit.Source) :
    RandomBit.Configuration → Memory → Real → RandomBit.Cost → Nat → Nat →
      List (DependencyCallRecord signature) → Prop where
  | halt {configuration memory result cost draws}
      (step : RandomOpenStep signature responder program source configuration
        (.halted memory result draws) cost none) :
      RandomOpenHaltingTrace signature responder program source configuration memory result
        cost 1 draws []
  | machine {configuration next final result headCost tailCost steps draws calls}
      (step : RandomOpenStep signature responder program source configuration
        (.running next) headCost none)
      (tail : RandomOpenHaltingTrace signature responder program source next final result
        tailCost steps draws calls) :
      RandomOpenHaltingTrace signature responder program source configuration final result
        (headCost + tailCost) (steps + 1) draws calls
  | call {configuration next final result headCost tailCost steps draws call calls}
      (step : RandomOpenStep signature responder program source configuration
        (.running next) headCost (some call))
      (tail : RandomOpenHaltingTrace signature responder program source next final result
        tailCost steps draws calls) :
      RandomOpenHaltingTrace signature responder program source configuration final result
        (headCost + tailCost) (steps + 1) draws (call :: calls)

def RandomRelativeSuccessEvent (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (problem : BitRandomizedMachineProblem)
    (program : RandomOpenProgram signature) (bound : Nat → RandomBit.Cost)
    (input : problem.Input) : Set RandomBit.Source :=
  {source | ∃ output final result cost steps draws calls,
    RandomOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls ∧
    problem.OutputRep output final ∧ problem.post input output ∧
    cost ≤ bound (problem.inputSize input)}

def RandomRelativeTermination (signature : DependencySignature)
    (responder : AdmissibleResponder signature) (problem : BitRandomizedMachineProblem)
    (program : RandomOpenProgram signature) (bound : Nat → RandomBit.Cost)
    (input : problem.Input) (source : RandomBit.Source) : Prop :=
  ∃ output final result cost steps draws calls,
    RandomOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls ∧
    problem.OutputRep output final ∧ cost ≤ bound (problem.inputSize input)

/-- Relative bounded-time Monte Carlo proof against every coherent contract responder. -/
structure BoundedTimeMonteCarloRelativeCertificate (signature : DependencySignature)
    (problem : BitRandomizedMachineProblem) (bound : Nat → RandomBit.Cost)
    (failure : problem.Input → Probability) where
  program : RandomOpenProgram signature
  valid : program.Valid
  measurableSuccess : ∀ responder input, problem.pre input →
    MeasurableSet (RandomRelativeSuccessEvent signature responder problem program bound input)
  terminates : ∀ responder input, problem.pre input → ∀ source,
    RandomRelativeTermination signature responder problem program bound input source
  successProbability : ∀ responder input, problem.pre input →
    RandomBit.sourceLaw
      (RandomRelativeSuccessEvent signature responder problem program bound input) ≥
      1 - (failure input : ENNReal)

/-! Ambiguous pre-taxonomy name isolated from the preferred public namespace. -/
namespace Legacy

abbrev RandomRelativeAlgorithmCertificate := BoundedTimeMonteCarloRelativeCertificate

end Legacy

end

end Algolean.Algorithms.StructuredRealRAM
