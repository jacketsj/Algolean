/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.RandomizedMachineProblem

/-!
# Guarantee-specific structured exact-real/natural randomized certificates

These declarations classify runtime, correctness, and distributional guarantees independently.
They reuse the sealed hidden-source operational traces; no certificate accepts a caller-defined
source law, event semantics, or machine evaluator.
-/

@[expose] public section

namespace Algolean.Algorithms

open MeasureTheory StructuredRealRAM

namespace BitRandomizedMachineProblem

/-- Correct termination without a resource condition. -/
def CorrectEvent (problem : BitRandomizedMachineProblem)
    (program : RandomBit.Program) (input : problem.Input) : Set RandomBit.Source :=
  {source | ∃ output : problem.Output, ∃ run : SuccessfulRun problem program input source,
    problem.OutputRep output run.final ∧ problem.post input output}

/-- Any halting source, whether or not its represented output is correct. -/
def TerminationEvent (problem : BitRandomizedMachineProblem)
    (program : RandomBit.Program) (input : problem.Input) : Set RandomBit.Source :=
  {source | Nonempty (SuccessfulRun problem program input source)}

/-- Exact extended fetched-step runtime; nontermination is `⊤`. -/
noncomputable def runtimeENNReal (problem : BitRandomizedMachineProblem)
    (program : RandomBit.Program) (input : problem.Input) (source : RandomBit.Source) : ENNReal :=
  ⨅ run : SuccessfulRun problem program input source, (run.steps : ENNReal)

/-- Exact extended primitive-draw count; nontermination is `⊤`. -/
noncomputable def drawsENNReal (problem : BitRandomizedMachineProblem)
    (program : RandomBit.Program) (input : problem.Input) (source : RandomBit.Source) : ENNReal :=
  ⨅ run : SuccessfulRun problem program input source, (run.randomDraws : ENNReal)

/-- Correct bounded execution has high probability; behavior outside that event is unrestricted. -/
structure HighProbabilityBoundedSuccessCertificate (problem : BitRandomizedMachineProblem)
    (bound : Nat → RandomBit.Cost) (failure : problem.Input → Probability) where
  program : RandomBit.Program
  valid : program.Valid
  successMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.SuccessEvent program input (bound (problem.inputSize input)))
  successProbability : ∀ input, problem.pre input →
    RandomBit.sourceLaw (problem.SuccessEvent program input (bound (problem.inputSize input))) ≥
      1 - (failure input : ENNReal)

/-- Every halting source produces a represented output satisfying the postcondition. -/
def CorrectOnEveryHaltingRun (problem : BitRandomizedMachineProblem)
    (program : RandomBit.Program) : Prop :=
  ∀ input, problem.pre input → ∀ source,
    ∀ run : SuccessfulRun problem program input source,
      ∃ output : problem.Output,
        problem.OutputRep output run.final ∧ problem.post input output

/-- Zero-error correctness and almost-sure termination, with no expected-time claim. -/
structure AlmostSureLasVegasCertificate (problem : BitRandomizedMachineProblem) where
  program : RandomBit.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    RandomBit.sourceLaw (problem.TerminationEvent program input) = 1

/-- Almost-sure zero-error execution with a measurable finite expected fetched-step bound. -/
structure LasVegasExpectedTimeCertificate (problem : BitRandomizedMachineProblem)
    (expectedBound : Nat → ENNReal) where
  program : RandomBit.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    RandomBit.sourceLaw (problem.TerminationEvent program input) = 1
  runtimeMeasurable : ∀ input, problem.pre input →
    Measurable (problem.runtimeENNReal program input)
  expectedRuntime : ∀ input, problem.pre input →
    ∫⁻ source, problem.runtimeENNReal program input source ∂RandomBit.sourceLaw ≤
      expectedBound (problem.inputSize input)
  expectedBound_finite : ∀ input, problem.pre input →
    expectedBound (problem.inputSize input) ≠ ⊤

/-- Zero-error correctness with a high-probability resource bound. -/
structure LasVegasHighProbabilityTimeCertificate (problem : BitRandomizedMachineProblem)
    (bound : Nat → RandomBit.Cost) (timeout : problem.Input → Probability) where
  program : RandomBit.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    RandomBit.sourceLaw (problem.TerminationEvent program input) = 1
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))}
  withinProbability : ∀ input, problem.pre input →
    RandomBit.sourceLaw {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))} ≥ 1 - (timeout input : ENNReal)

/--
Weaker zero-error bounded-termination theorem.  Positive-probability divergence is explicitly
permitted outside the measured event; this is not called Las Vegas high-probability time.
-/
structure ZeroErrorHighProbabilityBoundedTerminationCertificate
    (problem : BitRandomizedMachineProblem)
    (bound : Nat → RandomBit.Cost) (timeout : problem.Input → Probability) where
  program : RandomBit.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))}
  withinProbability : ∀ input, problem.pre input →
    RandomBit.sourceLaw {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))} ≥ 1 - (timeout input : ENNReal)

/-- Explicit one-sided decision semantics over a structured output carrier. -/
structure OneSidedDecisionSpec (problem : BitRandomizedMachineProblem) where
  isYes : problem.Input → Prop
  isNo : problem.Input → Prop
  accepts : problem.Output → Prop
  classified : ∀ input, problem.pre input → isYes input ∨ isNo input
  disjoint : ∀ input, ¬ (isYes input ∧ isNo input)
  /-- The decision view is explicitly tied to the problem's mathematical postcondition. -/
  post_consistent : ∀ input output, problem.pre input →
    (problem.post input output ↔ (isYes input ↔ accepts output))

namespace OneSidedDecisionSpec

/-- Source event returning a represented accepting output. -/
def AcceptEvent (specification : OneSidedDecisionSpec problem)
    (program : RandomBit.Program) (input : problem.Input) : Set RandomBit.Source :=
  {source | ∃ output : problem.Output, ∃ run : SuccessfulRun problem program input source,
    problem.OutputRep output run.final ∧ specification.accepts output}

end OneSidedDecisionSpec

/-- Every source is bounded, no input is never accepted, and yes inputs are accepted likely. -/
structure OneSidedBoundedTimeMonteCarloCertificate (problem : BitRandomizedMachineProblem)
    (specification : OneSidedDecisionSpec problem)
    (bound : Nat → RandomBit.Cost) (failure : problem.Input → Probability) where
  program : RandomBit.Program
  valid : program.Valid
  terminatesWithin : ∀ input, problem.pre input → ∀ source,
    problem.TerminatesWithin program input source (bound (problem.inputSize input))
  neverAcceptsNo : ∀ input, problem.pre input → specification.isNo input → ∀ source,
    ∀ run : SuccessfulRun problem program input source, ∀ output,
      problem.OutputRep output run.final → ¬ specification.accepts output
  acceptMeasurable : ∀ input, problem.pre input →
    MeasurableSet (specification.AcceptEvent program input)
  acceptsYesWithHighProbability : ∀ input, problem.pre input →
    specification.isYes input →
    RandomBit.sourceLaw (specification.AcceptEvent program input) ≥
      1 - (failure input : ENNReal)

/-- Expected-loss guarantee tied pointwise to actual same-source terminating traces. -/
structure ExpectedApproximationCertificate (problem : BitRandomizedMachineProblem)
    (loss : problem.Input → problem.Output → ENNReal)
    (expectedLossBound : Nat → ENNReal) where
  program : RandomBit.Program
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : SuccessfulRun problem program input source,
      problem.OutputRep (output input source) run.final
  lossMeasurable : ∀ input, Measurable (fun source ↦ loss input (output input source))
  expectedLoss : ∀ input, problem.pre input →
    ∫⁻ source, loss input (output input source) ∂RandomBit.sourceLaw ≤
      expectedLossBound (problem.inputSize input)

/-- Exact distributional output specification, independent of relational success predicates. -/
structure SamplerCertificate (problem : BitRandomizedMachineProblem)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) where
  program : RandomBit.Program
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : SuccessfulRun problem program input source,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  distribution : ∀ input, problem.pre input →
    Measure.map (output input) RandomBit.sourceLaw = target input

/-- Approximate fair-bit sampler with an explicit distribution distance and error function. -/
structure ApproximateSamplerCertificate (problem : BitRandomizedMachineProblem)
    [MeasurableSpace problem.Output]
    (distance : Measure problem.Output → Measure problem.Output → ENNReal)
    (target : problem.Input → Measure problem.Output)
    (error : problem.Input → ENNReal) where
  program : RandomBit.Program
  valid : program.Valid
  output : problem.Input → RandomBit.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : SuccessfulRun problem program input source,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  approximate : ∀ input, problem.pre input →
    distance (Measure.map (output input) RandomBit.sourceLaw) (target input) ≤ error input

end BitRandomizedMachineProblem

namespace UniformRealRandomizedMachineProblem

/-- Correct termination event for the exact-uniform-real profile. -/
def CorrectEvent (problem : UniformRealRandomizedMachineProblem)
    (program : UniformReal.Program) (input : problem.Input) : Set UniformReal.Source :=
  {source | ∃ output : problem.Output, ∃ run : SuccessfulRun problem program input source,
    problem.OutputRep output run.final ∧ problem.post input output}

/-- Any terminating exact-uniform source. -/
def TerminationEvent (problem : UniformRealRandomizedMachineProblem)
    (program : UniformReal.Program) (input : problem.Input) : Set UniformReal.Source :=
  {source | Nonempty (SuccessfulRun problem program input source)}

/-- Exact extended fetched-step runtime; nontermination is `⊤`. -/
noncomputable def runtimeENNReal (problem : UniformRealRandomizedMachineProblem)
    (program : UniformReal.Program) (input : problem.Input) (source : UniformReal.Source) :
    ENNReal :=
  ⨅ run : SuccessfulRun problem program input source, (run.steps : ENNReal)

/-- Bounded correct execution has high probability; timeout may occur outside the event. -/
structure HighProbabilityBoundedSuccessCertificate
    (problem : UniformRealRandomizedMachineProblem)
    (bound : Nat → UniformReal.Cost) (failure : problem.Input → Probability) where
  program : UniformReal.Program
  valid : program.Valid
  successMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.SuccessEvent program input (bound (problem.inputSize input)))
  successProbability : ∀ input, problem.pre input →
    UniformReal.sourceLaw (problem.SuccessEvent program input (bound (problem.inputSize input))) ≥
      1 - (failure input : ENNReal)

/-- Every halting continuous-source execution is mathematically correct. -/
def CorrectOnEveryHaltingRun (problem : UniformRealRandomizedMachineProblem)
    (program : UniformReal.Program) : Prop :=
  ∀ input, problem.pre input → ∀ source,
    ∀ run : SuccessfulRun problem program input source,
      ∃ output : problem.Output,
        problem.OutputRep output run.final ∧ problem.post input output

/-- Almost-sure zero-error exact-uniform-real algorithm. -/
structure AlmostSureLasVegasCertificate (problem : UniformRealRandomizedMachineProblem) where
  program : UniformReal.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    UniformReal.sourceLaw (problem.TerminationEvent program input) = 1

/-- Expected-time zero-error exact-uniform-real algorithm. -/
structure LasVegasExpectedTimeCertificate (problem : UniformRealRandomizedMachineProblem)
    (expectedBound : Nat → ENNReal) where
  program : UniformReal.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    UniformReal.sourceLaw (problem.TerminationEvent program input) = 1
  runtimeMeasurable : ∀ input, problem.pre input →
    Measurable (problem.runtimeENNReal program input)
  expectedRuntime : ∀ input, problem.pre input →
    ∫⁻ source, problem.runtimeENNReal program input source ∂UniformReal.sourceLaw ≤
      expectedBound (problem.inputSize input)
  expectedBound_finite : ∀ input, problem.pre input →
    expectedBound (problem.inputSize input) ≠ ⊤

/-- Strong high-probability-time Las Vegas theorem, aligned with the Word-RAM convention. -/
structure LasVegasHighProbabilityTimeCertificate
    (problem : UniformRealRandomizedMachineProblem)
    (bound : Nat → UniformReal.Cost) (timeout : problem.Input → Probability) where
  program : UniformReal.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    UniformReal.sourceLaw (problem.TerminationEvent program input) = 1
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))}
  withinProbability : ∀ input, problem.pre input →
    UniformReal.sourceLaw {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))} ≥ 1 - (timeout input : ENNReal)

/-- Weaker exact-uniform zero-error theorem permitting divergence outside the bounded event. -/
structure ZeroErrorHighProbabilityBoundedTerminationCertificate
    (problem : UniformRealRandomizedMachineProblem)
    (bound : Nat → UniformReal.Cost) (timeout : problem.Input → Probability) where
  program : UniformReal.Program
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))}
  withinProbability : ∀ input, problem.pre input →
    UniformReal.sourceLaw {source | problem.TerminatesWithin program input source
      (bound (problem.inputSize input))} ≥ 1 - (timeout input : ENNReal)

/-- Exact output-distribution theorem for a continuous-source sampler. -/
structure SamplerCertificate (problem : UniformRealRandomizedMachineProblem)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) where
  program : UniformReal.Program
  valid : program.Valid
  output : problem.Input → UniformReal.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : SuccessfulRun problem program input source,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  distribution : ∀ input, problem.pre input →
    Measure.map (output input) UniformReal.sourceLaw = target input

/-- Approximate exact-uniform-source sampler with an explicit metric and error parameter. -/
structure ApproximateSamplerCertificate (problem : UniformRealRandomizedMachineProblem)
    [MeasurableSpace problem.Output]
    (distance : Measure problem.Output → Measure problem.Output → ENNReal)
    (target : problem.Input → Measure problem.Output)
    (error : problem.Input → ENNReal) where
  program : UniformReal.Program
  valid : program.Valid
  output : problem.Input → UniformReal.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : SuccessfulRun problem program input source,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  approximate : ∀ input, problem.pre input →
    distance (Measure.map (output input) UniformReal.sourceLaw) (target input) ≤ error input

end UniformRealRandomizedMachineProblem

end Algolean.Algorithms
