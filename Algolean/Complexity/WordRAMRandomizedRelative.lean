/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMRandomized
public import Algolean.Complexity.WordRAMRelative

/-!
# Randomized Word-RAM clients with deterministic typed dependencies

Relative calls preserve the hidden source cursor and record exact structured call data.  A
discharge artifact must expose an ordinary finite `RandomBit.Program`; because that syntax has
only core instructions and `randBit`, it cannot hide a whole procedure in one callback.  Its
same-source refinement theorem transfers the relative success event to the concrete program.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open MeasureTheory

noncomputable section

/-- First-order randomized client syntax with typed abstract deterministic calls. -/
inductive RandomOpenInstruction (signature : DependencySignature w) where
  | machine (instruction : RandomBit.Instruction w)
  | call (op : signature.Op) (inputRegion outputRegion : Region w) (next : Nat)

abbrev RandomOpenProgram (signature : DependencySignature w) :=
  List (RandomOpenInstruction signature)

namespace RandomOpenInstruction

def successors : RandomOpenInstruction signature → List Nat
  | .machine instruction => instruction.successors
  | .call _ _ _ next => [next]

end RandomOpenInstruction

def RandomOpenProgram.Valid (program : RandomOpenProgram signature) : Prop :=
  ∀ (pc : Nat) (instruction : RandomOpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

/-- One relative randomized transition; calls leave the hidden source and cursor untouched. -/
inductive RandomOpenStep (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (program : RandomOpenProgram signature)
    (source : RandomBit.Source) :
    RandomBit.Configuration w → RandomBit.StepResult w → RandomBit.Cost →
      Option (DependencyCallRecord signature) → Prop where
  | machine {configuration instruction outcome cost}
      (fetch : program[configuration.pc]? = some (.machine instruction))
      (observed : RandomBit.execute source instruction configuration = ⟨outcome, cost⟩) :
      RandomOpenStep signature responder program source configuration
        outcome cost none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      RandomOpenStep signature responder program source configuration
        (.running {
          pc := next
          memory := (signature.contract op).outputLayout.writeAt outputRegion
            (responder.answer op input) configuration.memory
          randomCursor := configuration.randomCursor })
        { steps := signature.bound op input + 1, randomDraws := 0 }
        (some {
          callSite := configuration.pc
          op := op
          input := input
          output := responder.answer op input
          outputCorrect := responder.correct op input validInput
          chargedCost := signature.bound op input + 1
          chargedCost_eq := rfl })

/-- One same-source trace accumulating machine cost and typed dependency calls together. -/
inductive RandomOpenHaltingTrace (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (program : RandomOpenProgram signature)
    (source : RandomBit.Source) :
    RandomBit.Configuration w → Memory w → BitVec w → Nat → RandomBit.Cost →
      List (DependencyCallRecord signature) → Prop where
  | halt {configuration memory result draws cost call}
      (step : RandomOpenStep signature responder program source configuration
        (.halted memory result draws) cost call) :
      RandomOpenHaltingTrace signature responder program source configuration memory result draws
        cost call.toList
  | next {configuration nextConfiguration memory result draws headCost tailCost headCall calls}
      (step : RandomOpenStep signature responder program source configuration
        (.running nextConfiguration) headCost headCall)
      (tail : RandomOpenHaltingTrace signature responder program source nextConfiguration
        memory result draws tailCost calls) :
      RandomOpenHaltingTrace signature responder program source configuration memory result draws
        (headCost + tailCost) (headCall.toList ++ calls)

/-- Each recorded randomized relative call contributes its explicit dispatch transition. -/
theorem RandomOpenHaltingTrace.calls_length_le_steps
    (trace : RandomOpenHaltingTrace signature responder program source initial final result draws
      cost calls) :
    calls.length ≤ cost.steps := by
  induction trace with
  | halt step =>
      cases step with
      | machine => simp
  | @next configuration nextConfiguration memory result draws headCost tailCost headCall calls
      step tail ih =>
      cases step with
      | machine =>
          simp only [Option.toList_none, List.nil_append]
          change calls.length ≤ headCost.steps + tailCost.steps
          omega
      | call fetch inputRep validInput =>
          simp only [Option.toList_some, List.singleton_append, List.length_cons]
          change calls.length + 1 ≤ signature.bound _ _ + 1 + tailCost.steps
          omega

/-- Every randomized dynamic call record names an actual in-range call instruction. -/
theorem RandomOpenHaltingTrace.callSite_lt
    (trace : RandomOpenHaltingTrace signature responder program source initial final result draws
      cost calls)
    (call : DependencyCallRecord signature) (member : call ∈ calls) :
    call.callSite < program.length := by
  induction trace with
  | halt step =>
      cases step with
      | machine => simp at member
  | next step tail ih =>
      cases step with
      | machine => simpa using ih member
      | call fetch inputRep validInput =>
          simp only [Option.toList_some, List.singleton_append, List.mem_cons] at member
          rcases member with rfl | member
          · exact List.getElem?_eq_some_iff.mp fetch |>.1
          · exact ih member

/-- Relative source event, including exact call records and both same-trace resource coordinates. -/
def RandomRelativeSuccessEvent (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (problem : StructuredProblem w)
    (program : RandomOpenProgram signature) (stepBound drawBound : problem.Input → Nat)
    (input : problem.Input) (validInput : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ final result draws cost calls output,
    RandomOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input validInput))
      final result draws cost calls ∧
    problem.OutputRep output final ∧ problem.post input output ∧
    cost.steps ≤ stepBound input ∧ draws ≤ drawBound input}

/-- Relative termination inside explicit step/draw bounds, without a correctness requirement. -/
def RandomRelativeTerminationWithin (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (problem : StructuredProblem w)
    (program : RandomOpenProgram signature) (stepBound drawBound : problem.Input → Nat)
    (source : RandomBit.Source) (input : problem.Input) (validInput : problem.pre input) : Prop :=
  ∃ final result draws cost calls output,
    RandomOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input validInput))
      final result draws cost calls ∧
    problem.OutputRep output final ∧
    cost.steps ≤ stepBound input ∧ draws ≤ drawBound input

/-- Relative correctness event without folding timeout into the correctness failure event. -/
def RandomRelativeCorrectEvent (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (problem : StructuredProblem w)
    (program : RandomOpenProgram signature)
    (input : problem.Input) (validInput : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ final result draws cost calls output,
    RandomOpenHaltingTrace signature responder program source
      (RandomBit.Configuration.initial (problem.initialMemory input validInput))
      final result draws cost calls ∧
    problem.OutputRep output final ∧ problem.post input output}

/-- High-probability bounded success uniformly against every valid deterministic responder. -/
structure HighProbabilityBoundedSuccessRelativeCertificate (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomOpenProgram signature
  valid : program.Valid
  measurableSuccess : ∀ responder input validInput,
    MeasurableSet (RandomRelativeSuccessEvent signature responder problem program
      stepBound drawBound input validInput)
  successProbability : ∀ responder input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw
      (RandomRelativeSuccessEvent signature responder problem program
        stepBound drawBound input validInput) ≥
      1 - (failure input : ENNReal)

/-- Relative every-source-time Monte Carlo, preserving the selected guarantee through linking. -/
structure BoundedTimeMonteCarloRelativeCertificate (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomOpenProgram signature
  valid : program.Valid
  terminatesWithin : ∀ responder source input, ∀ validInput : problem.pre input,
    RandomRelativeTerminationWithin signature responder problem program stepBound drawBound
      source input validInput
  correctMeasurable : ∀ responder input validInput,
    MeasurableSet
      (RandomRelativeCorrectEvent signature responder problem program input validInput)
  correctProbability : ∀ responder input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw
      (RandomRelativeCorrectEvent signature responder problem program input validInput) ≥
        1 - (failure input : ENNReal)

/-! Ambiguous pre-taxonomy relative name, isolated from the preferred public namespace. -/
namespace Legacy

abbrev RandomRelativeAlgorithmCertificate (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) :=
  HighProbabilityBoundedSuccessRelativeCertificate signature problem stepBound drawBound failure

end Legacy

/--
Proof-carrying concrete randomized link.  `program` is ordinary sealed randomized syntax, while
`refines` is pointwise in the same infinite source.  The body-presence theorem makes code
materialization explicit for audits; no dependency implementation is a machine instruction.
-/
structure RandomizedConcreteLink
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (implementations : ImplementationEnvironment signature)
    (linkedStepBound linkedDrawBound : problem.Input → Nat) where
  program : RandomBit.Program w
  valid : program.Valid
  /-- One shared contiguous concrete body range for each deterministic dependency. -/
  bodyBase : signature.Op → Nat
  bodyMaterialized : ∀ op pc instruction,
    (implementations.implementation op).module.code[pc]? = some instruction →
      ∃ linkedInstruction,
        program[bodyBase op + pc]? = some (.core linkedInstruction)
  bodyRangesDisjoint : ∀ left right, left ≠ right →
    bodyBase left + (implementations.implementation left).module.code.length ≤ bodyBase right ∨
    bodyBase right + (implementations.implementation right).module.code.length ≤ bodyBase left
  refines : ∀ source input, ∀ validInput : problem.pre input,
    source ∈ RandomRelativeSuccessEvent signature implementations.responder problem client.program
      relativeStepBound relativeDrawBound input validInput →
    source ∈ problem.RandomSuccessEvent program linkedStepBound linkedDrawBound input validInput
  measurableSuccess : ∀ input validInput,
    MeasurableSet (problem.RandomSuccessEvent program linkedStepBound linkedDrawBound
      input validInput)

namespace RandomizedConcreteLink

/-- Transfer the relative probability theorem to the concrete closed randomized program. -/
def certificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound linkedStepBound linkedDrawBound :
      problem.Input → Nat}
    {failure : problem.Input → Probability}
    {client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure}
    {implementations : ImplementationEnvironment signature}
    (link : RandomizedConcreteLink client implementations linkedStepBound linkedDrawBound) :
    problem.HighProbabilityBoundedSuccessCertificate
      linkedStepBound linkedDrawBound failure where
  program := link.program
  valid := link.valid
  measurableSuccess := link.measurableSuccess
  successProbability input validInput := by
    have relativeProbability :=
      client.successProbability implementations.responder input validInput
    exact relativeProbability.trans
      (measure_mono fun source member ↦ link.refines source input validInput member)

/-- Existential randomized discharge retains the fixed fair source and concrete linked syntax. -/
theorem hasAlgorithm
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound linkedStepBound linkedDrawBound :
      problem.Input → Nat}
    {failure : problem.Input → Probability}
    {client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure}
    {implementations : ImplementationEnvironment signature}
    (link : RandomizedConcreteLink client implementations linkedStepBound linkedDrawBound) :
    problem.HasHighProbabilityBoundedSuccessAlgorithm
      linkedStepBound linkedDrawBound failure :=
  ⟨link.certificate⟩

end RandomizedConcreteLink

end

end Algolean.Algorithms.WordRAM
