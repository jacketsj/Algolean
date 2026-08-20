/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Layout
public import Algolean.Compiler.CFG

/-!
# Auditable structured machine problems

The strongest predicate in this module existentially quantifies only over one finite program in
the sealed core structured-real-RAM profile.  The program is selected before every input, input
memory is canonical, output is a `Layout.RepAt` relation, and cost belongs to the same halting
trace as the result.

Program families have deliberately different names and carry a code-size obligation.
-/

@[expose] public section

namespace Algolean.Algorithms

open StructuredRealRAM

/-- A deterministic problem over canonical structured inputs and outputs. -/
@[nolint checkUnivs]
structure MachineProblem where
  /-- Mathematical input carrier. -/
  Input : Type u
  /-- Computational output carrier; proof obligations belong in `post`. -/
  Output : Type v
  /-- Closed canonical input layout. -/
  inputLayout : Layout Input
  /-- Closed canonical output layout. -/
  outputLayout : Layout Output
  /-- Designated final-memory region. -/
  outputRegion : Region
  /-- Admissible-input precondition. -/
  pre : Input → Prop
  /-- Independent mathematical postcondition. -/
  post : Input → Output → Prop

namespace MachineProblem

/-- Input size is the total canonical memory footprint, not an arbitrary client function. -/
noncomputable def inputSize (problem : MachineProblem) (input : problem.Input) : ℕ :=
  (problem.inputLayout.footprint input).total

/-- Canonical zero-initialized memory received by a machine algorithm. -/
noncomputable def initialMemory (problem : MachineProblem) (input : problem.Input) : Memory :=
  problem.inputLayout.init input

/-- Relational interpretation of an output in the problem's designated output region. -/
noncomputable def OutputRep (problem : MachineProblem)
    (output : problem.Output) (memory : Memory) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- Output representation is functional because every public layout has a certified inverse. -/
theorem OutputRep.functional (problem : MachineProblem) {left right : problem.Output}
    {memory : Memory} (leftRep : problem.OutputRep left memory)
    (rightRep : problem.OutputRep right memory) : left = right :=
  problem.outputLayout.rep_functional problem.outputRegion leftRep rightRep

/-- A terminating execution whose output and resources come from one halting trace. -/
structure SuccessfulRun (program : StructuredRealRAM.Program) (initial : Memory) where
  /-- Final machine memory. -/
  final : Memory
  /-- Scalar halt result; structured output is read relationally from `final`. -/
  result : ℝ
  /-- Resource vector accumulated by the trace. -/
  cost : StructuredRealRAM.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Coupled behavior/resource evidence. -/
  trace : StructuredRealRAM.HaltingTrace program ⟨0, initial⟩ final result cost steps

/-- One program solves one fixed input within a given resource vector. -/
noncomputable def SolvesInputWithin (problem : MachineProblem)
    (program : StructuredRealRAM.Program) (input : problem.Input)
    (bound : StructuredRealRAM.Cost) : Prop :=
  ∃ (output : problem.Output)
      (run : SuccessfulRun program (problem.initialMemory input)),
    problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/--
One fixed finite program solves every valid canonical input within the footprint-indexed bound.
-/
noncomputable def SolvesWithin (problem : MachineProblem)
    (program : StructuredRealRAM.Program) (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  ∀ input, problem.pre input →
    SolvesInputWithin problem program input (bound (problem.inputSize input))

/--
Preferred deterministic existential algorithm claim: one valid finite program is fixed before all
inputs.  The core structured-real-RAM profile, layout semantics, and costed trace are not chosen by
the witness.
-/
noncomputable def HasFixedMachineAlgorithm (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  ∃ program : StructuredRealRAM.Program,
    program.Valid ∧ SolvesWithin problem program bound

/-- Concise compatibility name for the preferred fixed-program predicate. -/
abbrev HasAlgorithm := HasFixedMachineAlgorithm

/-- Short explicit alias for the preferred fixed-program predicate. -/
abbrev HasFixedAlgorithm := HasFixedMachineAlgorithm

/--
A first-order CFG source whose assembled target is valid and solves the problem.  The exact emitted
code size is available from `CFG.compile_length`; no continuation-valued source program appears in
this claim.
-/
noncomputable def HasCompiledAlgorithm (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  ∃ source : StructuredRealRAM.CFG.Program,
    source.WellFormed ∧
      (StructuredRealRAM.CFG.compile source).Valid ∧
      SolvesWithin problem (StructuredRealRAM.CFG.compile source) bound

/-- A visibly nonuniform family with an explicit emitted-code-size obligation. -/
noncomputable def HasNonuniformFamily (problem : MachineProblem)
    (timeBound : ℕ → StructuredRealRAM.Cost) (codeBound : ℕ → ℕ) : Prop :=
  ∃ code : ℕ → StructuredRealRAM.Program,
    (∀ size, (code size).Valid) ∧
    (∀ size, (code size).length ≤ codeBound size) ∧
    (∀ input, problem.pre input →
      let size := problem.inputSize input
      SolvesInputWithin problem (code size) input (timeBound size))

/--
A generated family certificate keeps generation, code size, and execution as separate obligations.
`Generates` is fixed by the caller's named generator model before the witness is chosen.
-/
noncomputable def HasUniformlyGeneratedFamily
    (problem : MachineProblem)
    (GeneratorProgram : Type w)
    (Generates : GeneratorProgram → ℕ → StructuredRealRAM.Program → Prop)
    (GenerationCost : GeneratorProgram → ℕ → ℕ)
    (generationBound codeBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) : Prop :=
  ∃ (generator : GeneratorProgram) (code : ℕ → StructuredRealRAM.Program),
    (∀ size, Generates generator size (code size)) ∧
    (∀ size, GenerationCost generator size ≤ generationBound size) ∧
    (∀ size, (code size).Valid) ∧
    (∀ size, (code size).length ≤ codeBound size) ∧
    (∀ input, problem.pre input →
      let size := problem.inputSize input
      SolvesInputWithin problem (code size) input (timeBound size))

end MachineProblem

end Algolean.Algorithms
