/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Profiled
public import Algolean.Models.StructuredRealRAM.CanonicalLayout
public import Algolean.Complexity.RandomizedMachineProblem

/-!
# Structured algorithm certificates indexed by a closed exact-real machine profile

The profile is part of every problem and certificate.  Input/output representation remains closed
layout syntax, while arithmetic and randomness are independent closed capability axes.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

open MeasureTheory

/-- Worst-case-valid-input structured problem in one closed machine profile. -/
structure ProfiledMachineProblem (profile : ClosedMachineProfile) where
  Input : Type
  Output : Type
  inputLayout : Layout Input
  outputLayout : Layout Output
  outputRegion : Region
  pre : Input → Prop
  post : Input → Output → Prop

namespace ProfiledMachineProblem

def ofCanonical (profile : ClosedMachineProfile) (Input Output : Type)
    [CanonicalLayout Input] [CanonicalLayout Output]
    (outputRegion : Region) (pre : Input → Prop) (post : Input → Output → Prop) :
    ProfiledMachineProblem profile where
  Input := Input
  Output := Output
  inputLayout := layoutOf Input
  outputLayout := layoutOf Output
  outputRegion := outputRegion
  pre := pre
  post := post

noncomputable def initialMemory (problem : ProfiledMachineProblem profile)
    (input : problem.Input) : Memory := problem.inputLayout.init input

noncomputable def inputSize (problem : ProfiledMachineProblem profile)
    (input : problem.Input) : Nat := (problem.inputLayout.footprint input).total

noncomputable def OutputRep (problem : ProfiledMachineProblem profile)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- Same-trace run for one fixed source realization. -/
structure SuccessfulRun (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (source : profile.randomness.Source)
    (input : problem.Input) where
  final : Memory
  result : Real
  cost : ProfiledCost
  steps : Nat
  draws : Nat
  trace : ProfiledHaltingTrace program source
    (RandomBit.Configuration.initial (problem.initialMemory input))
    final result cost steps draws

/-- Exact input-dependent correctness and resource bound for every source. -/
def SolvesWithinBy (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (bound : problem.Input → ProfiledCost) : Prop :=
  ∀ input, problem.pre input → ∀ source,
    ∃ run : problem.SuccessfulRun program source input,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound input

/-- One finite fixed program selected before all inputs and sources. -/
structure FixedAlgorithmCertificateBy (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) where
  program : ProfiledProgram profile
  valid : program.Valid
  solves : problem.SolvesWithinBy program bound

def HasAlgorithmBy (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) : Prop :=
  Nonempty (FixedAlgorithmCertificateBy problem bound)

/-- Correct bounded execution event. -/
def SuccessEvent (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (bound : problem.Input → ProfiledCost)
    (input : problem.Input) : Set profile.randomness.Source :=
  {source | ∃ run : problem.SuccessfulRun program source input,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound input}

/-- Any halting source. -/
def TerminationEvent (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (input : problem.Input) :
    Set profile.randomness.Source :=
  {source | Nonempty (problem.SuccessfulRun program source input)}

/-- Termination within the full operation-sensitive resource vector. -/
def TerminationWithinEvent (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (bound : problem.Input → ProfiledCost)
    (input : problem.Input) : Set profile.randomness.Source :=
  {source | ∃ run : problem.SuccessfulRun program source input, run.cost ≤ bound input}

/-- Exact extended runtime, assigning `⊤` to sources without a halting trace. -/
noncomputable def runtimeENNReal (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) (input : problem.Input)
    (source : profile.randomness.Source) : ENNReal :=
  ⨅ run : problem.SuccessfulRun program source input, (run.steps : ENNReal)

def CorrectOnEveryHaltingRun (problem : ProfiledMachineProblem profile)
    (program : ProfiledProgram profile) : Prop :=
  ∀ input, problem.pre input → ∀ source,
    ∀ run : problem.SuccessfulRun program source input,
      ∃ output : problem.Output,
        problem.OutputRep output run.final ∧ problem.post input output

/-- Bounded-time Monte Carlo in any non-deterministic closed source profile. -/
structure BoundedTimeMonteCarloCertificate (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (failure : problem.Input → Probability) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  terminatesWithin : ∀ input, problem.pre input → ∀ source,
    source ∈ problem.TerminationWithinEvent program bound input
  successMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.SuccessEvent program bound input)
  successProbability : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.SuccessEvent program bound input) ≥
      1 - (failure input : ENNReal)

/-- High-probability bounded success; divergence is included in failure. -/
structure HighProbabilityBoundedSuccessCertificate
    (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (failure : problem.Input → Probability) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  successMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.SuccessEvent program bound input)
  successProbability : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.SuccessEvent program bound input) ≥
      1 - (failure input : ENNReal)

/-- Strong finite-expected-time Las Vegas theorem. -/
structure LasVegasExpectedTimeCertificate (problem : ProfiledMachineProblem profile)
    (expectedBound : problem.Input → ENNReal) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.TerminationEvent program input) = 1
  runtimeMeasurable : ∀ input, problem.pre input →
    Measurable (problem.runtimeENNReal program input)
  expectedRuntime : ∀ input, problem.pre input →
    ∫⁻ source, problem.runtimeENNReal program input source
      ∂profile.randomness.sourceLaw ≤ expectedBound input
  expectedBound_finite : ∀ input, problem.pre input → expectedBound input ≠ ⊤

/-- Strong Las Vegas convention: zero error, a.s. termination, and a high-probability bound. -/
structure LasVegasHighProbabilityTimeCertificate
    (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (timeout : problem.Input → Probability) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  terminationMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationEvent program input)
  terminatesAlmostSurely : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.TerminationEvent program input) = 1
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationWithinEvent program bound input)
  withinProbability : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.TerminationWithinEvent program bound input) ≥
      1 - (timeout input : ENNReal)

/--
Weaker zero-error bounded-termination theorem.  Unlike the Las Vegas certificate above, this
category deliberately permits divergence outside the measured bounded-termination event.
-/
structure ZeroErrorHighProbabilityBoundedTerminationCertificate
    (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (timeout : problem.Input → Probability) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  correctOnEveryHaltingRun : problem.CorrectOnEveryHaltingRun program
  withinMeasurable : ∀ input, problem.pre input →
    MeasurableSet (problem.TerminationWithinEvent program bound input)
  withinProbability : ∀ input, problem.pre input →
    profile.randomness.sourceLaw (problem.TerminationWithinEvent program bound input) ≥
      1 - (timeout input : ENNReal)

/-- Exact distributional sampler in the selected closed source profile. -/
structure SamplerCertificate (problem : ProfiledMachineProblem profile)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  output : problem.Input → profile.randomness.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : problem.SuccessfulRun program source input,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  distribution : ∀ input, problem.pre input →
    Measure.map (output input) profile.randomness.sourceLaw = target input

/-- Approximate sampling keeps its distance, target, and error visible in the theorem type. -/
structure ApproximateSamplerCertificate (problem : ProfiledMachineProblem profile)
    [MeasurableSpace problem.Output]
    (distance : Measure problem.Output → Measure problem.Output → ENNReal)
    (target : problem.Input → Measure problem.Output)
    (error : problem.Input → ENNReal) where
  hasRandomness : profile.randomness ≠ .none
  program : ProfiledProgram profile
  valid : program.Valid
  output : problem.Input → profile.randomness.Source → problem.Output
  realizes : ∀ input, problem.pre input → ∀ source,
    ∃ run : problem.SuccessfulRun program source input,
      problem.OutputRep (output input source) run.final
  outputMeasurable : ∀ input, Measurable (output input)
  approximate : ∀ input, problem.pre input →
    distance (Measure.map (output input) profile.randomness.sourceLaw) (target input) ≤
      error input

/-!
Input randomness is a separate theorem-side axis.  It is never projected into the machine source
or canonical initialization, so average-case, random-order, and smoothed analyses cannot silently
change an internal-randomness claim.
-/

/-- A named external distribution on mathematical inputs, separate from machine randomness. -/
structure InputDistributionModel (problem : ProfiledMachineProblem profile)
    [MeasurableSpace problem.Input] where
  name : String
  law : Measure problem.Input
  validAlmostEverywhere : ∀ᵐ input ∂law, problem.pre input

end ProfiledMachineProblem

end Algolean.Algorithms.StructuredRealRAM
