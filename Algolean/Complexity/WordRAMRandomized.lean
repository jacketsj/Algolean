/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMStructured
public import Algolean.Models.WordRAM.Random

/-!
# Structured randomized Word-RAM certificates

Randomness is the sealed hidden infinite iid source from `WordRAM.RandomBit`.  Bounds constrain
draws observed in the same trace; no tape, length field, or input-dependent distribution is part
of the problem or certificate.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open MeasureTheory

/-- A probability value with the range invariant enforced in its type. -/
abbrev Probability := {probability : ENNReal // probability ≤ 1}

namespace StructuredProblem

/-- The first `draws` hidden bits, exposed only to metatheory rather than machine syntax. -/
def sourcePrefix (source : RandomBit.Source) (draws : Nat) : Fin draws → Bool :=
  fun index ↦ source index

/--
Any theorem-side output which factors through a bounded fair-bit prefix has finite support.  This
is the basic separation from exact continuous sampling; no coercion to a uniform-real sampler is
provided.
-/
theorem finite_output_support_of_prefix_factor
    (draws : Nat) (output : RandomBit.Source → alpha)
    (factor : (Fin draws → Bool) → alpha)
    (factors : ∀ source, output source = factor (sourcePrefix source draws)) :
    Set.Finite (Set.range output) := by
  apply (Set.finite_range factor).subset
  rintro value ⟨source, rfl⟩
  exact ⟨sourcePrefix source draws, (factors source).symm⟩

/-- One source-specific randomized run whose output, cost, and draw count share one trace. -/
structure RandomSuccessfulRun (problem : StructuredProblem w)
    (program : RandomBit.Program w) (source : RandomBit.Source)
    (input : problem.Input) (valid : problem.pre input) where
  final : Memory w
  result : BitVec w
  draws : Nat
  cost : RandomBit.Cost
  trace : RandomBit.HaltingTrace program source
    (RandomBit.Configuration.initial (problem.initialMemory input valid))
    final result draws cost

/-- The source event on which a run is correct and within both resource bounds. -/
def RandomSuccessEvent (problem : StructuredProblem w) (program : RandomBit.Program w)
    (stepBound drawBound : problem.Input → Nat)
    (input : problem.Input) (valid : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧
      run.cost.steps ≤ stepBound input ∧ run.draws ≤ drawBound input}

/-- A source terminates with some canonically represented output inside both resource bounds. -/
def RandomTerminationWithinEvent (problem : StructuredProblem w)
    (program : RandomBit.Program w) (stepBound drawBound : problem.Input → Nat)
    (input : problem.Input) (valid : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧
      run.cost.steps ≤ stepBound input ∧ run.draws ≤ drawBound input}

/-- A source terminates with a represented output satisfying the mathematical postcondition. -/
def RandomCorrectEvent (problem : StructuredProblem w) (program : RandomBit.Program w)
    (input : problem.Input) (valid : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output}

/-- The source set on which the concrete program has any halting trace. -/
def RandomTerminationEvent (problem : StructuredProblem w) (program : RandomBit.Program w)
    (input : problem.Input) (valid : problem.pre input) : Set RandomBit.Source :=
  {source | Nonempty (problem.RandomSuccessfulRun program source input valid)}

/--
Exact extended runtime: the least fetched-step count of a halting trace, or `⊤` when no trace
exists.  Determinism makes the infimum a singleton on terminating sources; using `iInf` fixes
nontermination as infinite rather than allowing a certificate author to choose a runtime.
-/
noncomputable def randomRuntimeENNReal (problem : StructuredProblem w)
    (program : RandomBit.Program w) (input : problem.Input) (valid : problem.pre input)
    (source : RandomBit.Source) : ENNReal :=
  ⨅ run : problem.RandomSuccessfulRun program source input valid,
    (run.cost.steps : ENNReal)

/-- Exact extended draw count, with nontermination interpreted as infinite. -/
noncomputable def randomDrawsENNReal (problem : StructuredProblem w)
    (program : RandomBit.Program w) (input : problem.Input) (valid : problem.pre input)
    (source : RandomBit.Source) : ENNReal :=
  ⨅ run : problem.RandomSuccessfulRun program source input valid,
    (run.draws : ENNReal)

/-- A concrete same-source trace computes the exact infimum-based runtime. -/
theorem randomRuntimeENNReal_eq_run (problem : StructuredProblem w)
    (program : RandomBit.Program w) (input : problem.Input) (valid : problem.pre input)
    (source : RandomBit.Source)
    (run : problem.RandomSuccessfulRun program source input valid) :
    problem.randomRuntimeENNReal program input valid source = run.cost.steps := by
  apply le_antisymm
  · exact iInf_le_of_le run le_rfl
  · apply le_iInf
    intro other
    have costEq := (run.trace.operational.deterministic other.trace.operational).2.2.2
    rw [← costEq]

/--
High-probability bounded success.  Timeout, divergence, stuckness, or an incorrect output are all
permitted outside the measured success event.  This is the exact semantics of the former
unqualified `RandomizedAlgorithmCertificate`.
-/
structure HighProbabilityBoundedSuccessCertificate (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomBit.Program w
  valid : program.Valid
  measurableSuccess : ∀ input validInput,
    MeasurableSet (problem.RandomSuccessEvent program stepBound drawBound input validInput)
  successProbability : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw
      (problem.RandomSuccessEvent program stepBound drawBound input validInput) ≥
      1 - (failure input : ENNReal)

/-- Existence of one high-probability bounded-success Word-RAM program. -/
def HasHighProbabilityBoundedSuccessAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (HighProbabilityBoundedSuccessCertificate problem stepBound drawBound failure)

/--
Conventional bounded-time Monte Carlo: every source halts within the resource bounds, while
correctness holds with probability at least `1 - failure`.
-/
structure BoundedTimeMonteCarloCertificate (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomBit.Program w
  valid : program.Valid
  terminatesWithin : ∀ source input, ∀ validInput : problem.pre input,
    source ∈ problem.RandomTerminationWithinEvent program stepBound drawBound input validInput
  correctMeasurable : ∀ input validInput,
    MeasurableSet (problem.RandomCorrectEvent program input validInput)
  correctProbability : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw (problem.RandomCorrectEvent program input validInput) ≥
      1 - (failure input : ENNReal)

/-- Preferred ordinary worst-case-time bounded-error randomized Word-RAM claim. -/
def HasBoundedTimeMonteCarloAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (BoundedTimeMonteCarloCertificate problem stepBound drawBound failure)

/-- Explicit yes/no partition and accepted-output predicate for one-sided error. -/
structure OneSidedDecisionSpec (problem : StructuredProblem w) where
  isYes : problem.Input → Prop
  isNo : problem.Input → Prop
  accepts : problem.Output → Prop
  classified : ∀ input, problem.pre input → isYes input ∨ isNo input
  disjoint : ∀ input, ¬ (isYes input ∧ isNo input)
  /-- The decision view is the published problem semantics, not an unrelated classifier. -/
  post_consistent : ∀ input output, problem.pre input →
    (problem.post input output ↔ (isYes input ↔ accepts output))

namespace OneSidedDecisionSpec

/-- Sources on which a represented accepting output is returned. -/
def AcceptEvent {w : Nat} {problem : StructuredProblem w}
    (specification : OneSidedDecisionSpec problem)
    (program : RandomBit.Program w) (input : problem.Input) (valid : problem.pre input) :
    Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ specification.accepts output}

/-- Sources on which a represented rejecting output is returned. -/
def RejectEvent {w : Nat} {problem : StructuredProblem w}
    (specification : OneSidedDecisionSpec problem)
    (program : RandomBit.Program w) (input : problem.Input) (valid : problem.pre input) :
    Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ ¬ specification.accepts output}

end OneSidedDecisionSpec

/-- Every source is bounded; no-instance acceptance is impossible and yes acceptance is likely. -/
structure OneSidedBoundedTimeMonteCarloCertificate (problem : StructuredProblem w)
    (specification : OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomBit.Program w
  valid : program.Valid
  terminatesWithin : ∀ source input, ∀ validInput : problem.pre input,
    source ∈ problem.RandomTerminationWithinEvent program stepBound drawBound input validInput
  neverAcceptsNo : ∀ input, ∀ validInput : problem.pre input,
    specification.isNo input → ∀ source,
    ∀ run : problem.RandomSuccessfulRun program source input validInput, ∀ output,
      problem.OutputRep output run.final →
      ¬ specification.accepts output
  acceptMeasurable : ∀ input validInput,
    MeasurableSet (specification.AcceptEvent program input validInput)
  acceptsYesWithHighProbability : ∀ input, ∀ validInput : problem.pre input,
    specification.isYes input →
    RandomBit.sourceLaw (specification.AcceptEvent program input validInput) ≥
      1 - (failure input : ENNReal)

/-- Existence of one RP-oriented bounded-time one-sided-error program. -/
def HasOneSidedBoundedTimeMonteCarloAlgorithm (problem : StructuredProblem w)
    (specification : OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (OneSidedBoundedTimeMonteCarloCertificate problem specification
    stepBound drawBound failure)

/-- Dual coRP-oriented contract: yes instances are always accepted and no instances reject likely. -/
structure CoOneSidedBoundedTimeMonteCarloCertificate (problem : StructuredProblem w)
    (specification : OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  program : RandomBit.Program w
  valid : program.Valid
  terminatesWithin : ∀ source input, ∀ validInput : problem.pre input,
    source ∈ problem.RandomTerminationWithinEvent program stepBound drawBound input validInput
  alwaysAcceptsYes : ∀ input, ∀ validInput : problem.pre input,
    specification.isYes input → ∀ source,
    ∀ run : problem.RandomSuccessfulRun program source input validInput, ∀ output,
      problem.OutputRep output run.final → specification.accepts output
  rejectMeasurable : ∀ input validInput,
    MeasurableSet (specification.RejectEvent program input validInput)
  rejectsNoWithHighProbability : ∀ input, ∀ validInput : problem.pre input,
    specification.isNo input →
    RandomBit.sourceLaw (specification.RejectEvent program input validInput) ≥
      1 - (failure input : ENNReal)

/-- Existence of one coRP-oriented bounded-time one-sided-error program. -/
def HasCoOneSidedBoundedTimeMonteCarloAlgorithm (problem : StructuredProblem w)
    (specification : OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (CoOneSidedBoundedTimeMonteCarloCertificate problem specification
    stepBound drawBound failure)

/-- Every halting execution has a represented mathematically correct output. -/
def CorrectOnEveryHaltingRun (problem : StructuredProblem w)
    (program : RandomBit.Program w) : Prop :=
  ∀ input, ∀ validInput : problem.pre input, ∀ source,
    ∀ run : problem.RandomSuccessfulRun program source input validInput,
      ∃ output : problem.Output,
        problem.OutputRep output run.final ∧ problem.post input output

/-- Zero-error correctness with almost-sure, but not necessarily expected-time, termination. -/
structure AlmostSureLasVegasCertificate (problem : StructuredProblem w) where
  program : RandomBit.Program w
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input validInput,
    MeasurableSet (problem.RandomTerminationEvent program input validInput)
  terminatesAlmostSurely : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw (problem.RandomTerminationEvent program input validInput) = 1

/-- Existence of one zero-error, almost-surely terminating program. -/
def HasAlmostSureLasVegasAlgorithm (problem : StructuredProblem w) : Prop :=
  Nonempty (AlmostSureLasVegasCertificate problem)

/-- Zero-error almost-sure termination with a measurable finite expected fetched-step bound. -/
structure LasVegasExpectedTimeCertificate (problem : StructuredProblem w)
    (expectedStepBound : problem.Input → ENNReal) where
  program : RandomBit.Program w
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input validInput,
    MeasurableSet (problem.RandomTerminationEvent program input validInput)
  terminatesAlmostSurely : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw (problem.RandomTerminationEvent program input validInput) = 1
  runtimeMeasurable : ∀ input validInput,
    Measurable (problem.randomRuntimeENNReal program input validInput)
  expectedRuntime : ∀ input, ∀ validInput : problem.pre input,
    ∫⁻ source, problem.randomRuntimeENNReal program input validInput source
      ∂RandomBit.sourceLaw ≤ expectedStepBound input
  expectedStepBound_finite : ∀ input, problem.pre input → expectedStepBound input ≠ ⊤

/-- Existence of one finite-expected-time zero-error program. -/
def HasLasVegasExpectedTimeAlgorithm (problem : StructuredProblem w)
    (expectedStepBound : problem.Input → ENNReal) : Prop :=
  Nonempty (LasVegasExpectedTimeCertificate problem expectedStepBound)

/-- Zero-error correctness with a high-probability time/draw bound. -/
structure LasVegasHighProbabilityTimeCertificate (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (timeout : problem.Input → Probability) where
  program : RandomBit.Program w
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input validInput,
    MeasurableSet (problem.RandomTerminationEvent program input validInput)
  terminatesAlmostSurely : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw (problem.RandomTerminationEvent program input validInput) = 1
  withinMeasurable : ∀ input validInput,
    MeasurableSet
      (problem.RandomTerminationWithinEvent program stepBound drawBound input validInput)
  withinProbability : ∀ input, ∀ validInput : problem.pre input,
    RandomBit.sourceLaw
      (problem.RandomTerminationWithinEvent program stepBound drawBound input validInput) ≥
        1 - (timeout input : ENNReal)

/-- Existence of one zero-error program with an almost-sure and high-probability time claim. -/
def HasLasVegasHighProbabilityTimeAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (timeout : problem.Input → Probability) : Prop :=
  Nonempty (LasVegasHighProbabilityTimeCertificate problem stepBound drawBound timeout)

/--
Expected-loss approximation certificate.  The theorem-side output selector is harmless because
every selected value is tied to a concrete same-source halting trace.
-/
structure ExpectedApproximationCertificate (problem : StructuredProblem w)
    (loss : problem.Input → problem.Output → ENNReal)
    (expectedLossBound : problem.Input → ENNReal) where
  program : RandomBit.Program w
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, ∀ validInput : problem.pre input, ∀ source,
    ∃ run : problem.RandomSuccessfulRun program source input validInput,
      problem.OutputRep (output input source) run.final
  lossMeasurable : ∀ input, Measurable (fun source ↦ loss input (output input source))
  expectedLoss : ∀ input, ∀ _validInput : problem.pre input,
    ∫⁻ source, loss input (output input source) ∂RandomBit.sourceLaw ≤
      expectedLossBound input

/-- Existence of one every-source terminating expected-quality algorithm. -/
def HasExpectedApproximationAlgorithm (problem : StructuredProblem w)
    (loss : problem.Input → problem.Output → ENNReal)
    (expectedLossBound : problem.Input → ENNReal) : Prop :=
  Nonempty (ExpectedApproximationCertificate problem loss expectedLossBound)

/-- Exact distributional sampler certificate, separate from relational postconditions. -/
structure SamplerCertificate (problem : StructuredProblem w)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) where
  program : RandomBit.Program w
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, ∀ validInput : problem.pre input, ∀ source,
    ∃ run : problem.RandomSuccessfulRun program source input validInput,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  distribution : ∀ input, problem.pre input →
    Measure.map (output input) RandomBit.sourceLaw = target input

/-- Approximate distributional sampler with the selected distance and error in its type. -/
structure ApproximateSamplerCertificate (problem : StructuredProblem w)
    [MeasurableSpace problem.Output]
    (distance : Measure problem.Output → Measure problem.Output → ENNReal)
    (target : problem.Input → Measure problem.Output)
    (error : problem.Input → ENNReal) where
  program : RandomBit.Program w
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, ∀ validInput : problem.pre input, ∀ source,
    ∃ run : problem.RandomSuccessfulRun program source input validInput,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  approximate : ∀ input, problem.pre input →
    distance (Measure.map (output input) RandomBit.sourceLaw) (target input) ≤ error input

/-- Existence of one every-source terminating exact distributional sampler. -/
def HasSamplerAlgorithm (problem : StructuredProblem w)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) : Prop :=
  Nonempty (SamplerCertificate problem target)

/-- Existence of one approximate sampler for an explicitly selected distribution distance. -/
def HasApproximateSamplerAlgorithm (problem : StructuredProblem w)
    [MeasurableSpace problem.Output]
    (distance : Measure problem.Output → Measure problem.Output → ENNReal)
    (target : problem.Input → Measure problem.Output)
    (error : problem.Input → ENNReal) : Prop :=
  Nonempty (ApproximateSamplerCertificate problem distance target error)

/-- Strong every-source Las Vegas certificate; almost-sure termination is intentionally separate. -/
structure EverySourceLasVegasCertificate (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat) where
  program : RandomBit.Program w
  valid : program.Valid
  solvesEverySource : ∀ source input, ∀ validInput : problem.pre input,
    ∃ run : problem.RandomSuccessfulRun program source input validInput,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧
      run.cost.steps ≤ stepBound input ∧ run.draws ≤ drawBound input

/-- Existence of one bounded every-source zero-error program. -/
def HasEverySourceLasVegasAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat) : Prop :=
  Nonempty (EverySourceLasVegasCertificate problem stepBound drawBound)

/-! Ambiguous pre-taxonomy names are isolated from the preferred public namespace. -/
namespace Legacy

abbrev RandomizedAlgorithmCertificate (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) :=
  HighProbabilityBoundedSuccessCertificate problem stepBound drawBound failure

abbrev HasRandomizedWordRAMAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) :=
  HasHighProbabilityBoundedSuccessAlgorithm problem stepBound drawBound failure

end Legacy

end StructuredProblem

end Algolean.Algorithms.WordRAM
