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

Program families have deliberately different names and carry both instruction-count and full
description-size obligations.  Caller-defined generator semantics are retained only under an
explicitly relative name; they are not presented as ordinary uniform generation.
-/

@[expose] public section

namespace Algolean.Algorithms

open StructuredRealRAM

/-- A deterministic problem over canonical structured inputs and outputs. -/
structure MachineProblem where
  /-- Mathematical input carrier. -/
  Input : Type
  /-- Computational output carrier; proof obligations belong in `post`. -/
  Output : Type
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
structure FixedAlgorithmCertificate (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- The concrete finite first-order witness. -/
  program : StructuredRealRAM.Program
  /-- All numeric successors stay within that program. -/
  valid : program.Valid
  /-- Correctness and resource use for every valid input. -/
  solves : SolvesWithin problem program bound

/-- Existence of a typed fixed-program certificate. -/
noncomputable def HasFixedMachineAlgorithm (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  Nonempty (FixedAlgorithmCertificate problem bound)

/-- Concise compatibility name for the preferred fixed-program predicate. -/
abbrev HasAlgorithm := HasFixedMachineAlgorithm

/-- Short explicit alias for the preferred fixed-program predicate. -/
abbrev HasFixedAlgorithm := HasFixedMachineAlgorithm

/--
A first-order CFG source whose assembled target is valid and solves the problem.  The exact emitted
code size is available from `CFG.compile_length`; no continuation-valued source program appears in
this claim.
-/
structure CompiledAlgorithmCertificate (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- Concrete first-order labeled source. -/
  source : StructuredRealRAM.CFG.Program
  /-- Static source well-formedness. -/
  wellFormed : source.WellFormed
  /-- Validity of the concrete assembled target. -/
  targetValid : (StructuredRealRAM.CFG.compile source).Valid
  /-- Correctness and cost of the assembled target. -/
  solves : SolvesWithin problem (StructuredRealRAM.CFG.compile source) bound

/-- Existence of a typed compiled-algorithm certificate. -/
noncomputable def HasCompiledAlgorithm (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) : Prop :=
  Nonempty (CompiledAlgorithmCertificate problem bound)

/-- A visibly nonuniform family with separate instruction and full-description size obligations. -/
structure NonuniformFamilyCertificate (problem : MachineProblem)
    (timeBound : ℕ → StructuredRealRAM.Cost)
    (instructionBound descriptionBound : ℕ → ℕ) where
  /-- One target program for each represented input size. -/
  code : ℕ → StructuredRealRAM.Program
  /-- Every member is closed under its jump targets. -/
  valid : ∀ size, (code size).Valid
  /-- Weaker instruction-count metadata, retained separately. -/
  instructionSize : ∀ size,
    StructuredRealRAM.Program.instructionCount (code size) ≤ instructionBound size
  /-- Full source-description bound, including literals, indices, and targets. -/
  descriptionSize : ∀ size,
    StructuredRealRAM.Program.descriptionSize (code size) ≤ descriptionBound size
  /-- The same member handles every valid input of its represented size. -/
  solves : ∀ input, problem.pre input →
    let size := problem.inputSize input
    SolvesInputWithin problem (code size) input (timeBound size)

/-- Existence of an explicitly nonuniform typed family certificate. -/
noncomputable def HasNonuniformFamily (problem : MachineProblem)
    (timeBound : ℕ → StructuredRealRAM.Cost)
    (instructionBound descriptionBound : ℕ → ℕ) : Prop :=
  Nonempty (NonuniformFamilyCertificate problem timeBound instructionBound descriptionBound)

/-- Fixed output region for the sealed program generator, disjoint from its canonical Nat input. -/
def generatorOutputRegion : Region := ⟨0, 4⟩

/--
The generated target program is represented by its canonical binary serialization in ordinary
structured memory.  No host-language `Program` value is returned by one generator step.
-/
noncomputable def GeneratedProgramRep (program : StructuredRealRAM.Program)
    (memory : Memory) : Prop :=
  (Layout.array Layout.bool).RepAt generatorOutputRegion
    (StructuredRealRAM.Program.encode program).toArray memory

/-- The generated binary representation denotes at most one target program. -/
theorem GeneratedProgramRep.functional {left right : StructuredRealRAM.Program} {memory : Memory}
    (leftRep : GeneratedProgramRep left memory)
    (rightRep : GeneratedProgramRep right memory) : left = right := by
  have arrays : (StructuredRealRAM.Program.encode left).toArray =
      (StructuredRealRAM.Program.encode right).toArray :=
    (Layout.array Layout.bool).rep_functional generatorOutputRegion leftRep rightRep
  have encodings : StructuredRealRAM.Program.encode left =
      StructuredRealRAM.Program.encode right := by
    simpa using congrArg Array.toList arrays
  have decoded := congrArg StructuredRealRAM.Program.decode encodings
  simpa using decoded

/-- Canonical input to the sealed generator machine. -/
noncomputable def generatorInitialMemory (size : ℕ) : Memory := Layout.nat.init size

/--
Typed certificate for ordinary uniform generation by one fixed sealed structured-real-RAM
program.  This is specifically a unit-cost unbounded-Nat generator model, not word-RAM or bit
complexity.  The generated binary target serialization is tied to final memory, its representation
is functional, and materializing every represented cell is charged by the same trace.
-/
structure UniformlyGeneratedFamilyCertificate
    (problem : MachineProblem)
    (generationBound : ℕ → StructuredRealRAM.Cost)
    (instructionBound descriptionBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) where
  /-- One fixed first-order generator program. -/
  generator : StructuredRealRAM.Program
  generatorValid : generator.Valid
  /-- Same-trace generation, output representation/materialization, and target obligations. -/
  generated : ∀ size,
    ∃ (code : StructuredRealRAM.Program)
      (run : SuccessfulRun generator (generatorInitialMemory size)),
      GeneratedProgramRep code run.final ∧
      run.cost ≤ generationBound size ∧
      ((Layout.array Layout.bool).footprint
        (StructuredRealRAM.Program.encode code).toArray).total ≤ run.cost.natWrites ∧
      code.Valid ∧
      StructuredRealRAM.Program.instructionCount code ≤ instructionBound size ∧
      StructuredRealRAM.Program.descriptionSize code ≤ descriptionBound size ∧
      ∀ input, problem.pre input → problem.inputSize input = size →
        SolvesInputWithin problem code input (timeBound size)

/--
Preferred absolute generated-family claim.  Generator syntax, semantics, and cost are the sealed
structured exact-real RAM definitions; callers cannot replace them with `Nat → Program` and a
zero-cost relation.
-/
noncomputable def HasUniformlyGeneratedFamily
    (problem : MachineProblem)
    (generationBound : ℕ → StructuredRealRAM.Cost)
    (instructionBound descriptionBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) : Prop :=
  Nonempty (UniformlyGeneratedFamilyCertificate problem generationBound instructionBound
    descriptionBound timeBound)

/--
A caller-defined generator specification.  This abstraction is useful for relative results, but it
does not establish ordinary uniformity: its syntax, semantics, and cost remain assumptions.
-/
structure RelativeGeneratorSpecification where
  /-- Caller-selected generator syntax. -/
  GeneratorProgram : Type w
  /-- Caller-selected generation relation. -/
  Generates : GeneratorProgram → ℕ → StructuredRealRAM.Program → Prop
  /-- Caller-selected generation cost. -/
  GenerationCost : GeneratorProgram → ℕ → ℕ

/-- Typed certificate for a family relative to explicitly supplied generator semantics. -/
structure RelativeGeneratedFamilyCertificate
    (problem : MachineProblem) (specification : RelativeGeneratorSpecification)
    (generationBound instructionBound descriptionBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) where
  /-- Generator witness relative to the supplied specification. -/
  generator : specification.GeneratorProgram
  /-- Size-indexed target family relative to the supplied relation. -/
  code : ℕ → StructuredRealRAM.Program
  /-- The supplied relation accepts every family member. -/
  generated : ∀ size, specification.Generates generator size (code size)
  /-- The supplied cost is within the advertised generation bound. -/
  generationCost : ∀ size,
    specification.GenerationCost generator size ≤ generationBound size
  /-- Every generated target is valid. -/
  valid : ∀ size, (code size).Valid
  /-- Instruction-count bound. -/
  instructionSize : ∀ size,
    StructuredRealRAM.Program.instructionCount (code size) ≤ instructionBound size
  /-- Full serialized-description bound. -/
  descriptionSize : ∀ size,
    StructuredRealRAM.Program.descriptionSize (code size) ≤ descriptionBound size
  /-- Relative family correctness and execution cost. -/
  solves : ∀ input, problem.pre input →
    let size := problem.inputSize input
    SolvesInputWithin problem (code size) input (timeBound size)

/--
Existence relative to caller-supplied generator syntax, semantics, and cost.  The deliberately long
name prevents this proposition from being mistaken for an absolute uniformity statement.
-/
noncomputable def HasFamilyRelativeToGeneratorSpecification
    (problem : MachineProblem) (specification : RelativeGeneratorSpecification)
    (generationBound instructionBound descriptionBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) : Prop :=
  Nonempty (RelativeGeneratedFamilyCertificate problem specification generationBound
    instructionBound descriptionBound timeBound)

end MachineProblem

end Algolean.Algorithms
