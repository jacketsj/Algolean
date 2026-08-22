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

/-- The measurable source event on which a run is correct and within both resource bounds. -/
def RandomSuccessEvent (problem : StructuredProblem w) (program : RandomBit.Program w)
    (stepBound drawBound : problem.Input → Nat)
    (input : problem.Input) (valid : problem.pre input) : Set RandomBit.Source :=
  {source | ∃ run : problem.RandomSuccessfulRun program source input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧
      run.cost.steps ≤ stepBound input ∧ run.draws ≤ drawBound input}

/-- Typed Monte Carlo certificate over the fixed fair product measure. -/
structure RandomizedAlgorithmCertificate (problem : StructuredProblem w)
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

/-- Preferred unqualified uniform randomized Word-RAM existence claim. -/
def HasRandomizedWordRAMAlgorithm (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (RandomizedAlgorithmCertificate problem stepBound drawBound failure)

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

end StructuredProblem

end Algolean.Algorithms.WordRAM
