/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem

/-!
# Randomized fixed-machine claims

The preferred `BitRandomizedMachineProblem` has a library-fixed iid fair-bit law whose tape length
depends only on represented input size.  Problem authors cannot provide `Input → PMF Tape` and
therefore cannot preload answers as input-dependent random advice.  Tapes are canonically
represented and every tape access is an ordinary charged machine-memory read.

The fully generic legacy abstraction remains available as `InputDependentTapeProblem`, but all of
its claims are explicitly named relative to the supplied tape law and are not ordinary randomized
algorithm claims.
-/

@[expose] public section

namespace Algolean.Algorithms

open StructuredRealRAM

/-- A problem relative to an arbitrary, potentially advice-bearing, input-dependent tape law. -/
structure InputDependentTapeProblem where
  /-- Mathematical input carrier. -/
  Input : Type
  /-- Computational output carrier. -/
  Output : Type
  /-- Complete realized random-tape carrier. -/
  Tape : Type
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

namespace InputDependentTapeProblem

/-- Closed product layout used for the actual machine input. -/
noncomputable def combinedLayout (problem : InputDependentTapeProblem) :
    Layout (problem.Input × problem.Tape) :=
  .prod problem.inputLayout problem.tapeLayout

/-- Canonical input-and-tape memory. -/
noncomputable def initialMemory (problem : InputDependentTapeProblem)
    (input : problem.Input) (tape : problem.Tape) : Memory :=
  problem.combinedLayout.init (input, tape)

/-- Input size excludes the random tape and is derived from the canonical input layout. -/
noncomputable def inputSize (problem : InputDependentTapeProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Relational output interpretation in the designated output region. -/
noncomputable def OutputRep (problem : InputDependentTapeProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- Probability mass of a tape predicate under a PMF. -/
noncomputable def tapeProbability {TapeType : Type x}
    (distribution : PMF TapeType) (event : TapeType → Prop) : ENNReal :=
  by
    classical
    exact ∑' tape, if event tape then distribution tape else 0

end InputDependentTapeProblem

/-- A terminating execution for one input and one realized tape. -/
structure TapeLawSuccessfulRun (problem : InputDependentTapeProblem)
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
noncomputable def TapeLawTerminatesWithin (problem : InputDependentTapeProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output) (run : TapeLawSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ run.cost ≤ bound

/-- Successful output event for a realized tape. -/
noncomputable def TapeLawSucceeds (problem : InputDependentTapeProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape) : Prop :=
  ∃ (output : problem.Output) (run : TapeLawSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ problem.post input output

/-- Successful represented output whose producing trace also satisfies the resource bound. -/
noncomputable def TapeLawSucceedsWithin (problem : InputDependentTapeProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input) (tape : problem.Tape)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output) (run : TapeLawSuccessfulRun problem program input tape),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/--
Monte Carlo semantics: worst-case-over-tapes cost, and success mass at least `1 - failure`.
-/
structure Probability where
  /-- Underlying extended nonnegative real. -/
  val : ENNReal
  /-- Probability values lie in the unit interval. -/
  valid : val ≤ 1

instance : Coe Probability ENNReal := ⟨Probability.val⟩

/-- Monte Carlo semantics relative to the problem's caller-supplied tape law. -/
noncomputable def MonteCarloSolvesWithinRelativeToTapeLaw
    (problem : InputDependentTapeProblem)
    (program : StructuredRealRAM.Program)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) : Prop :=
  ∀ input, problem.pre input →
    (∀ tape, TapeLawTerminatesWithin problem program input tape
      (bound (problem.inputSize input))) ∧
    InputDependentTapeProblem.tapeProbability (problem.tapeDistribution input)
      (fun tape => TapeLawSucceedsWithin problem program input tape
        (bound (problem.inputSize input))) ≥ 1 - (failure input : ENNReal)

/-- One fixed program, with probability interpreted relative to the supplied tape law. -/
noncomputable def InputDependentTapeProblem.HasMonteCarloAlgorithmRelativeToTapeLaw
    (problem : InputDependentTapeProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) : Prop :=
  ∃ program : StructuredRealRAM.Program,
    program.Valid ∧ MonteCarloSolvesWithinRelativeToTapeLaw problem program bound failure

/--
Las Vegas expected-time semantics.  `scalarize` names the resource coordinate or aggregate being
averaged; the tape-indexed costs are witnessed by successful runs of the same program.
-/
noncomputable def LasVegasSolvesInExpectationRelativeToTapeLaw
    (problem : InputDependentTapeProblem)
    (program : StructuredRealRAM.Program) (scalarize : StructuredRealRAM.Cost → ℕ)
    (bound : ℕ → ENNReal) : Prop :=
  ∀ input, problem.pre input →
    ∃ costOf : problem.Tape → StructuredRealRAM.Cost,
      (∀ tape, ∃ (output : problem.Output)
          (run : TapeLawSuccessfulRun problem program input tape),
        run.cost = costOf tape ∧ problem.OutputRep output run.final ∧
          problem.post input output) ∧
      (∑' tape, (problem.tapeDistribution input tape) * (scalarize (costOf tape) : ENNReal)) ≤
        bound (problem.inputSize input)

/-- One fixed Las Vegas program with an explicit expected scalar resource bound. -/
noncomputable def InputDependentTapeProblem.HasLasVegasAlgorithmRelativeToTapeLawFor
    (problem : InputDependentTapeProblem) (scalarize : StructuredRealRAM.Cost → ℕ)
    (bound : ℕ → ENNReal) : Prop :=
  ∃ program : StructuredRealRAM.Program,
    program.Valid ∧
      LasVegasSolvesInExpectationRelativeToTapeLaw problem program scalarize bound

/-- Relative tape-law claim using the fixed fetched-instruction cost projection. -/
noncomputable def InputDependentTapeProblem.HasLasVegasStepAlgorithmRelativeToTapeLaw
    (problem : InputDependentTapeProblem) (bound : ℕ → ENNReal) : Prop :=
  problem.HasLasVegasAlgorithmRelativeToTapeLawFor StructuredRealRAM.Cost.steps bound

/-- The fixed fair distribution on one bit. -/
noncomputable def fairBit : PMF Bool := PMF.uniformOfFintype Bool

/-- Library-defined iid fair-bit tapes.  No caller controls their joint law. -/
noncomputable def iidBitArray : ℕ → PMF (Array Bool)
  | 0 => PMF.pure #[]
  | count + 1 => fairBit.bind fun bit =>
      (iidBitArray count).map fun tape => tape.push bit

/-- A randomized problem whose only randomness parameter is a size-indexed bit-count bound. -/
structure BitRandomizedMachineProblem where
  /-- Mathematical input carrier. -/
  Input : Type
  /-- Computational output carrier. -/
  Output : Type
  /-- Closed canonical input layout. -/
  inputLayout : Layout Input
  /-- Closed canonical output layout. -/
  outputLayout : Layout Output
  /-- Designated final-memory output region. -/
  outputRegion : Region
  /-- Number of iid fair bits supplied at each represented input size. -/
  randomBitCount : ℕ → ℕ
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical success relation. -/
  post : Input → Output → Prop

namespace BitRandomizedMachineProblem

/-- Represented input-cell count; tape length and contents are excluded. -/
noncomputable def inputSize (problem : BitRandomizedMachineProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/--
Forget to the relative interface using the one library-defined iid fair-bit law.  Dependence is
only through represented size, not input contents.
-/
noncomputable def asTapeLaw (problem : BitRandomizedMachineProblem) :
    InputDependentTapeProblem where
  Input := problem.Input
  Output := problem.Output
  Tape := Array Bool
  inputLayout := problem.inputLayout
  tapeLayout := .array .bool
  outputLayout := problem.outputLayout
  outputRegion := problem.outputRegion
  tapeDistribution input := iidBitArray (problem.randomBitCount (problem.inputSize input))
  pre := problem.pre
  post := problem.post

/-- Typed Monte Carlo certificate over the sealed iid fair-bit tape profile. -/
structure MonteCarloAlgorithmCertificate (problem : BitRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) where
  /-- Concrete fixed first-order program. -/
  program : StructuredRealRAM.Program
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Worst-tape resource bound and success probability under the fixed law. -/
  solves : MonteCarloSolvesWithinRelativeToTapeLaw problem.asTapeLaw program bound failure

/-- Preferred fixed-program Monte Carlo claim over a sealed iid fair-bit tape profile. -/
noncomputable def HasMonteCarloAlgorithm (problem : BitRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) : Prop :=
  Nonempty (MonteCarloAlgorithmCertificate problem bound failure)

/-- Typed total-tape Las Vegas step certificate over the sealed iid fair-bit tape profile. -/
structure TotalTapeLasVegasStepAlgorithmCertificate (problem : BitRandomizedMachineProblem)
    (bound : ℕ → ENNReal) where
  /-- Concrete fixed first-order program. -/
  program : StructuredRealRAM.Program
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Every-tape correctness and expected fetched-instruction bound. -/
  solves : LasVegasSolvesInExpectationRelativeToTapeLaw problem.asTapeLaw program
    StructuredRealRAM.Cost.steps bound

/-- Preferred total-tape Las Vegas step claim over a sealed iid fair-bit tape profile. -/
noncomputable def HasTotalTapeLasVegasStepAlgorithm (problem : BitRandomizedMachineProblem)
    (bound : ℕ → ENNReal) : Prop :=
  Nonempty (TotalTapeLasVegasStepAlgorithmCertificate problem bound)

end BitRandomizedMachineProblem

end Algolean.Algorithms
