/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem
public import Algolean.Models.StructuredRealRAM.UniformReal

/-!
# Randomized fixed-machine claims

The preferred `BitRandomizedMachineProblem` runs a sealed first-order machine against a hidden,
lengthless source with the library-fixed iid fair-bit product law.  A program can consume the
source only through one charged `randBit` instruction.  There is no input-dependent distribution,
finite tape, observable tape length, or arbitrary bit-count schedule.

Two weaker compatibility abstractions remain available: `InputDependentTapeProblem` is relative
to an arbitrary tape law, while `ScheduledBitTapeProblem` is relative to an arbitrary
size-indexed finite-tape schedule.  Their theorem names disclose that relativity and are not
ordinary uniform randomized-algorithm claims.
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

/-- The fixed fair distribution on one bit, used only by finite scheduled-tape compatibility. -/
noncomputable def fairBit : PMF Bool := PMF.uniformOfFintype Bool

/-- Library-defined finite iid fair-bit tapes for the explicitly relative compatibility API. -/
noncomputable def iidBitArray : ℕ → PMF (Array Bool)
  | 0 => PMF.pure #[]
  | count + 1 => fairBit.bind fun bit =>
      (iidBitArray count).map fun tape => tape.push bit

/--
A finite iid-bit tape problem relative to a caller-supplied size-indexed length schedule.

The schedule is observable through the array header and can therefore encode nonuniform advice.
This structure is deliberately excluded from the preferred unqualified randomized claim.
-/
structure ScheduledBitTapeProblem where
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

namespace ScheduledBitTapeProblem

/-- Represented input-cell count; tape length and contents are excluded. -/
noncomputable def inputSize (problem : ScheduledBitTapeProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/--
Forget to the relative interface using the one library-defined iid fair-bit law.  Dependence is
only through represented size, not input contents.
-/
noncomputable def asTapeLaw (problem : ScheduledBitTapeProblem) :
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
structure MonteCarloAlgorithmCertificate (problem : ScheduledBitTapeProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) where
  /-- Concrete fixed first-order program. -/
  program : StructuredRealRAM.Program
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Worst-tape resource bound and success probability under the fixed law. -/
  solves : MonteCarloSolvesWithinRelativeToTapeLaw problem.asTapeLaw program bound failure

/-- Preferred fixed-program Monte Carlo claim over a sealed iid fair-bit tape profile. -/
noncomputable def HasMonteCarloAlgorithmRelativeToBitCountSchedule
    (problem : ScheduledBitTapeProblem)
    (bound : ℕ → StructuredRealRAM.Cost) (failure : problem.Input → Probability) : Prop :=
  Nonempty (MonteCarloAlgorithmCertificate problem bound failure)

/-- Typed total-tape Las Vegas step certificate over the sealed iid fair-bit tape profile. -/
structure TotalTapeLasVegasStepAlgorithmCertificate (problem : ScheduledBitTapeProblem)
    (bound : ℕ → ENNReal) where
  /-- Concrete fixed first-order program. -/
  program : StructuredRealRAM.Program
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Every-tape correctness and expected fetched-instruction bound. -/
  solves : LasVegasSolvesInExpectationRelativeToTapeLaw problem.asTapeLaw program
    StructuredRealRAM.Cost.steps bound

/-- Preferred total-tape Las Vegas step claim over a sealed iid fair-bit tape profile. -/
noncomputable def HasTotalTapeLasVegasStepAlgorithmRelativeToBitCountSchedule
    (problem : ScheduledBitTapeProblem)
    (bound : ℕ → ENNReal) : Prop :=
  Nonempty (TotalTapeLasVegasStepAlgorithmCertificate problem bound)

end ScheduledBitTapeProblem

/--
A problem for the sealed hidden-source random-bit structured real RAM.

There is intentionally no randomness field.  In particular, neither an `Input → PMF Tape` law
nor a `Nat → Nat` source-length schedule can be chosen by a problem or certificate author.
-/
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
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical success relation. -/
  post : Input → Output → Prop

namespace BitRandomizedMachineProblem

open MeasureTheory

/-- Represented input-cell count; the hidden random source contributes no input cells. -/
noncomputable def inputSize (problem : BitRandomizedMachineProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Canonical input memory contains only the mathematical input and zeros elsewhere. -/
noncomputable def initialMemory (problem : BitRandomizedMachineProblem)
    (input : problem.Input) : Memory :=
  problem.inputLayout.init input

/-- Relational output interpretation through the closed output layout. -/
noncomputable def OutputRep (problem : BitRandomizedMachineProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- The represented randomized output is unambiguous. -/
theorem OutputRep.functional (problem : BitRandomizedMachineProblem)
    {left right : problem.Output} {memory : Memory}
    (leftRep : problem.OutputRep left memory) (rightRep : problem.OutputRep right memory) :
    left = right :=
  problem.outputLayout.rep_functional problem.outputRegion leftRep rightRep

/--
One terminating randomized execution.  Final memory, result, cost, transition count, and number of
primitive draws all belong to the same source-indexed operational derivation.
-/
structure SuccessfulRun (problem : BitRandomizedMachineProblem)
    (program : StructuredRealRAM.RandomBit.Program) (input : problem.Input)
    (source : StructuredRealRAM.RandomBit.Source) where
  /-- Final ordinary memory. -/
  final : Memory
  /-- Scalar halt result. -/
  result : ℝ
  /-- Core resources and draw count from this trace. -/
  cost : StructuredRealRAM.RandomBit.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Final hidden source cursor. -/
  randomDraws : ℕ
  /-- Coupled operational derivation. -/
  trace : StructuredRealRAM.RandomBit.HaltingTrace program source
    (StructuredRealRAM.RandomBit.Configuration.initial (problem.initialMemory input))
    final result cost steps randomDraws

/-- The charged draw coordinate is exactly the number of source coordinates consumed. -/
theorem SuccessfulRun.cost_randomDraws
    {problem : BitRandomizedMachineProblem}
    {program : StructuredRealRAM.RandomBit.Program} {input : problem.Input}
    {source : StructuredRealRAM.RandomBit.Source}
    (run : SuccessfulRun problem program input source) :
    run.cost.randomDraws = run.randomDraws := by
  have accounting := run.trace.randomDraws_eq_cursorDifference
  simpa [StructuredRealRAM.RandomBit.Configuration.initial] using accounting

/-- Every-source termination and resource obligation for one input. -/
noncomputable def TerminatesWithin (problem : BitRandomizedMachineProblem)
    (program : StructuredRealRAM.RandomBit.Program) (input : problem.Input)
    (source : StructuredRealRAM.RandomBit.Source)
    (bound : StructuredRealRAM.RandomBit.Cost) : Prop :=
  ∃ (output : problem.Output) (run : SuccessfulRun problem program input source),
    problem.OutputRep output run.final ∧ run.cost ≤ bound

/-- Correct represented output within the resource bound for one source realization. -/
noncomputable def SucceedsWithin (problem : BitRandomizedMachineProblem)
    (program : StructuredRealRAM.RandomBit.Program) (input : problem.Input)
    (source : StructuredRealRAM.RandomBit.Source)
    (bound : StructuredRealRAM.RandomBit.Cost) : Prop :=
  ∃ (output : problem.Output) (run : SuccessfulRun problem program input source),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/-- Probability of a source event under the one fixed iid fair product law. -/
noncomputable def sourceProbability
    (event : StructuredRealRAM.RandomBit.Source → Prop) : ENNReal :=
  StructuredRealRAM.RandomBit.sourceLaw {source | event source}

/--
Monte Carlo semantics for the hidden lengthless source.  Runtime and primitive-draw bounds are
both worst-case over source realizations and are witnessed by the same traces used for outputs.
-/
noncomputable def MonteCarloSolvesWithin (problem : BitRandomizedMachineProblem)
    (program : StructuredRealRAM.RandomBit.Program)
    (bound : ℕ → StructuredRealRAM.RandomBit.Cost)
    (failure : problem.Input → Probability) : Prop :=
  ∀ input, problem.pre input →
    (∀ source, problem.TerminatesWithin program input source
      (bound (problem.inputSize input))) ∧
    sourceProbability (fun source ↦ problem.SucceedsWithin program input source
      (bound (problem.inputSize input))) ≥ 1 - (failure input : ENNReal)

/-- Typed certificate for one fixed program in the sealed hidden-source profile. -/
structure MonteCarloAlgorithmCertificate (problem : BitRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.RandomBit.Cost)
    (failure : problem.Input → Probability) where
  /-- Concrete finite random-bit program. -/
  program : StructuredRealRAM.RandomBit.Program
  /-- All successors remain in the program. -/
  valid : program.Valid
  /-- Every-input resource and probability guarantee. -/
  solves : problem.MonteCarloSolvesWithin program bound failure

/-- Preferred unqualified uniform Monte Carlo existence claim. -/
noncomputable def HasMonteCarloAlgorithm (problem : BitRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.RandomBit.Cost)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (MonteCarloAlgorithmCertificate problem bound failure)

/--
Every-source-correct Las Vegas semantics with expected fetched-instruction cost.  This is stronger
than almost-sure termination and is named accordingly.
-/
noncomputable def EverySourceLasVegasStepSolvesWithin
    (problem : BitRandomizedMachineProblem)
    (program : StructuredRealRAM.RandomBit.Program) (bound : ℕ → ENNReal) : Prop :=
  ∀ input, problem.pre input →
    ∃ costOf : StructuredRealRAM.RandomBit.Source → StructuredRealRAM.RandomBit.Cost,
      (∀ source, ∃ (output : problem.Output)
          (run : SuccessfulRun problem program input source),
        run.cost = costOf source ∧ problem.OutputRep output run.final ∧
          problem.post input output) ∧
      (∫⁻ source, (StructuredRealRAM.RandomBit.Cost.steps (costOf source) : ENNReal)
        ∂StructuredRealRAM.RandomBit.sourceLaw) ≤ bound (problem.inputSize input)

/-- Typed every-source Las Vegas certificate for the fixed step projection. -/
structure EverySourceLasVegasStepAlgorithmCertificate
    (problem : BitRandomizedMachineProblem) (bound : ℕ → ENNReal) where
  /-- Concrete finite random-bit program. -/
  program : StructuredRealRAM.RandomBit.Program
  /-- All successors remain in the program. -/
  valid : program.Valid
  /-- Every-source correctness and expected-step guarantee. -/
  solves : problem.EverySourceLasVegasStepSolvesWithin program bound

/-- Fixed-program Las Vegas existence with correctness/termination for every source realization. -/
noncomputable def HasEverySourceLasVegasStepAlgorithm
    (problem : BitRandomizedMachineProblem) (bound : ℕ → ENNReal) : Prop :=
  Nonempty (EverySourceLasVegasStepAlgorithmCertificate problem bound)

end BitRandomizedMachineProblem

/-! ## Separately named exact-continuous-randomness profile -/

/--
A problem for the sealed exact-uniform-real machine.  This profile is intentionally not an alias
of the random-bit profile: exact continuous sampling is a strictly stronger primitive.
-/
structure UniformRealRandomizedMachineProblem where
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
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical success relation. -/
  post : Input → Output → Prop

namespace UniformRealRandomizedMachineProblem

/-- Represented input-cell count. -/
noncomputable def inputSize (problem : UniformRealRandomizedMachineProblem)
    (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Canonical otherwise-zero input memory. -/
noncomputable def initialMemory (problem : UniformRealRandomizedMachineProblem)
    (input : problem.Input) : Memory :=
  problem.inputLayout.init input

/-- Closed relational output interpretation. -/
noncomputable def OutputRep (problem : UniformRealRandomizedMachineProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- One exact-uniform-source execution with coupled output, resources, and draws. -/
structure SuccessfulRun (problem : UniformRealRandomizedMachineProblem)
    (program : StructuredRealRAM.UniformReal.Program) (input : problem.Input)
    (source : StructuredRealRAM.UniformReal.Source) where
  /-- Final ordinary memory. -/
  final : Memory
  /-- Scalar halt result. -/
  result : ℝ
  /-- Core resources and continuous-sample count. -/
  cost : StructuredRealRAM.UniformReal.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Final hidden source cursor. -/
  randomDraws : ℕ
  /-- Coupled operational derivation. -/
  trace : StructuredRealRAM.UniformReal.HaltingTrace program source
    (StructuredRealRAM.RandomBit.Configuration.initial (problem.initialMemory input))
    final result cost steps randomDraws

/-- The charged sample count equals the final source cursor. -/
theorem SuccessfulRun.cost_randomDraws
    {problem : UniformRealRandomizedMachineProblem}
    {program : StructuredRealRAM.UniformReal.Program} {input : problem.Input}
    {source : StructuredRealRAM.UniformReal.Source}
    (run : SuccessfulRun problem program input source) :
    run.cost.randomDraws = run.randomDraws := by
  have accounting := run.trace.randomDraws_eq_cursorDifference
  simpa [StructuredRealRAM.RandomBit.Configuration.initial] using accounting

/-- Every-source termination and resource obligation. -/
noncomputable def TerminatesWithin (problem : UniformRealRandomizedMachineProblem)
    (program : StructuredRealRAM.UniformReal.Program) (input : problem.Input)
    (source : StructuredRealRAM.UniformReal.Source)
    (bound : StructuredRealRAM.UniformReal.Cost) : Prop :=
  ∃ (output : problem.Output) (run : SuccessfulRun problem program input source),
    problem.OutputRep output run.final ∧ run.cost ≤ bound

/-- Correct represented output within the bound for one source realization. -/
noncomputable def SucceedsWithin (problem : UniformRealRandomizedMachineProblem)
    (program : StructuredRealRAM.UniformReal.Program) (input : problem.Input)
    (source : StructuredRealRAM.UniformReal.Source)
    (bound : StructuredRealRAM.UniformReal.Cost) : Prop :=
  ∃ (output : problem.Output) (run : SuccessfulRun problem program input source),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/-- Probability of an event under the fixed exact-uniform product law. -/
noncomputable def sourceProbability
    (event : StructuredRealRAM.UniformReal.Source → Prop) : ENNReal :=
  StructuredRealRAM.UniformReal.sourceLaw {source | event source}

/-- Monte Carlo semantics for the fixed exact-uniform product source. -/
noncomputable def MonteCarloSolvesWithin (problem : UniformRealRandomizedMachineProblem)
    (program : StructuredRealRAM.UniformReal.Program)
    (bound : ℕ → StructuredRealRAM.UniformReal.Cost)
    (failure : problem.Input → Probability) : Prop :=
  ∀ input, problem.pre input →
    (∀ source, problem.TerminatesWithin program input source
      (bound (problem.inputSize input))) ∧
    sourceProbability (fun source ↦ problem.SucceedsWithin program input source
      (bound (problem.inputSize input))) ≥ 1 - (failure input : ENNReal)

/-- Typed fixed-program certificate for exact continuous uniform randomness. -/
structure MonteCarloAlgorithmCertificate (problem : UniformRealRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.UniformReal.Cost)
    (failure : problem.Input → Probability) where
  /-- Concrete finite exact-uniform-real program. -/
  program : StructuredRealRAM.UniformReal.Program
  /-- All successors remain in the program. -/
  valid : program.Valid
  /-- Every-input resource and probability guarantee. -/
  solves : problem.MonteCarloSolvesWithin program bound failure

/-- Explicitly named strong Monte Carlo claim using exact uniform real samples. -/
noncomputable def HasMonteCarloAlgorithm (problem : UniformRealRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.UniformReal.Cost)
    (failure : problem.Input → Probability) : Prop :=
  Nonempty (MonteCarloAlgorithmCertificate problem bound failure)

end UniformRealRandomizedMachineProblem

end Algolean.Algorithms
