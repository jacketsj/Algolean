/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem

/-!
# Randomized fixed-machine claims

A random tape is canonically represented alongside the input.  The fixed program is quantified
before inputs and tapes.  Monte Carlo claims bound cost for every tape and state success
probability separately.  Las Vegas expected-time claims require a successful same-trace run for
every tape and explicitly scalarize the machine resource vector before taking expectation.
-/

@[expose] public section

namespace Algolean.Algorithms

open StructuredRealRAM

/-- A structured randomized problem with a discrete input-dependent tape distribution. -/
@[nolint checkUnivs]
structure RandomizedMachineProblem where
  /-- Mathematical input carrier. -/
  Input : Type u
  /-- Computational output carrier. -/
  Output : Type v
  /-- Complete realized random-tape carrier. -/
  Tape : Type w
  /-- Closed canonical input layout. -/
  inputLayout : Layout Input
  /-- Closed canonical tape layout. -/
  tapeLayout : Layout Tape
  /-- Closed canonical output layout. -/
  outputLayout : Layout Output
  /-- Designated final-memory output region. -/
  outputRegion : Region
  /-- Discrete random-tape law for each input. -/
  tapeDistribution : Input → PMF Tape
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical success relation. -/
  post : Input → Output → Prop

namespace RandomizedMachineProblem

/-- Closed product layout used for the actual machine input. -/
noncomputable def combinedLayout (problem : RandomizedMachineProblem) :
    Layout (problem.Input × problem.Tape) :=
  .prod problem.inputLayout problem.tapeLayout

/-- Canonical input-and-tape memory. -/
noncomputable def initialMemory (problem : RandomizedMachineProblem)
    (input : problem.Input) (tape : problem.Tape) : Memory :=
  problem.combinedLayout.init (input, tape)

/-- Input size excludes the random tape and is derived from the canonical input layout. -/
noncomputable def inputSize (problem : RandomizedMachineProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Relational output interpretation in the designated output region. -/
noncomputable def OutputRep (problem : RandomizedMachineProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- Probability mass of a tape predicate under a PMF. -/
noncomputable def tapeProbability {TapeType : Type x}
    (distribution : PMF TapeType) (event : TapeType → Prop) : ENNReal :=
  by
    classical
    exact ∑' tape, if event tape then distribution tape else 0

end RandomizedMachineProblem

/-- A terminating randomized execution for one input and one realized tape. -/
structure RandomizedSuccessfulRun (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape) where
  /-- Final structured machine memory. -/
  final : Memory
  /-- Scalar halt result. -/
  result : ℝ
  /-- Resource vector accumulated by this tape's trace. -/
  cost : StructuredRealRAM.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Coupled behavior/resource evidence for this realized tape. -/
  trace : StructuredRealRAM.HaltingTrace program
    ⟨0, problem.initialMemory input tape⟩ final result cost steps

/-- Every-tape termination/output/cost obligation used by Monte Carlo claims. -/
noncomputable def RandomizedTerminatesWithin (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output) (run : RandomizedSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ run.cost ≤ bound

/-- Successful output event for a realized tape. -/
noncomputable def RandomizedSucceeds (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape) : Prop :=
  ∃ (output : problem.Output) (run : RandomizedSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ problem.post input output

/-- Successful represented output whose producing trace also satisfies the resource bound. -/
noncomputable def RandomizedSucceedsWithin (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output) (run : RandomizedSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/--
Monte Carlo semantics: worst-case-over-tapes cost, and success mass at least `1 - failure`.
-/
noncomputable def MonteCarloSolvesWithin (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → ENNReal) : Prop :=
  ∀ input, problem.pre input →
    (∀ tape, RandomizedTerminatesWithin problem program input tape
      (bound (problem.inputSize input))) ∧
    RandomizedMachineProblem.tapeProbability (problem.tapeDistribution input)
      (fun tape => RandomizedSucceedsWithin problem program input tape
        (bound (problem.inputSize input))) ≥ 1 - failure input

/-- One fixed Monte Carlo program, quantified before every input and tape. -/
noncomputable def RandomizedMachineProblem.HasMonteCarloAlgorithm
    (problem : RandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → ENNReal) : Prop :=
  ∃ program : StructuredRealRAM.Program,
    program.Valid ∧ MonteCarloSolvesWithin problem program bound failure

/--
Las Vegas expected-time semantics.  `scalarize` names the resource coordinate or aggregate being
averaged; the tape-indexed costs are witnessed by successful runs of the same program.
-/
noncomputable def LasVegasSolvesInExpectation (problem : RandomizedMachineProblem)
    (program : StructuredRealRAM.Program) (scalarize : StructuredRealRAM.Cost → ℕ)
    (bound : ℕ → ENNReal) : Prop :=
  ∀ input, problem.pre input →
    ∃ costOf : problem.Tape → StructuredRealRAM.Cost,
      (∀ tape, ∃ (output : problem.Output)
          (run : RandomizedSuccessfulRun problem program input tape),
        run.cost = costOf tape ∧ problem.OutputRep output run.final ∧
          problem.post input output) ∧
      (∑' tape, (problem.tapeDistribution input tape) * (scalarize (costOf tape) : ENNReal)) ≤
        bound (problem.inputSize input)

/-- One fixed Las Vegas program with an explicit expected scalar resource bound. -/
noncomputable def RandomizedMachineProblem.HasLasVegasAlgorithmFor
    (problem : RandomizedMachineProblem) (scalarize : StructuredRealRAM.Cost → ℕ)
    (bound : ℕ → ENNReal) : Prop :=
  ∃ program : StructuredRealRAM.Program,
    program.Valid ∧ LasVegasSolvesInExpectation problem program scalarize bound

/-- Standard Las Vegas expected-time claim using the fetched-instruction coordinate. -/
noncomputable def RandomizedMachineProblem.HasLasVegasStepAlgorithm
    (problem : RandomizedMachineProblem) (bound : ℕ → ENNReal) : Prop :=
  problem.HasLasVegasAlgorithmFor StructuredRealRAM.Cost.steps bound

end Algolean.Algorithms
