/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.RAMProblem
public import Algolean.Models.WordRAM.Layout

/-!
# Structured fixed-width Word-RAM algorithm certificates

The problem stores concrete closed layouts.  One finite program is chosen before every input, and
the structured output, halt result, cost, and transition count all arise from one `HaltingTrace`.
Bounds may depend on the structured input but cannot affect initialization or program selection.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- A structured problem for one explicit word width and the sealed ordinary Word-RAM profile. -/
structure StructuredProblem (w : ℕ) where
  /-- Widths below two cannot distinguish the three canonical scalar tags. -/
  widthAtLeastTwo : 2 ≤ w
  /-- Structured mathematical input carrier. -/
  Input : Type
  /-- Structured mathematical output carrier. -/
  Output : Type
  /-- Stored closed input-layout syntax. -/
  inputLayout : WordLayout w Input
  /-- Stored closed output-layout syntax. -/
  outputLayout : WordLayout w Output
  /-- Start of the caller-designated output region. -/
  outputRegion : Region w
  /-- Mathematical input promise. -/
  pre : Input → Prop
  /-- Mathematical correctness relation. -/
  post : Input → Output → Prop
  /-- Every admissible input is canonically addressable. -/
  inputFits : ∀ input, pre input → inputLayout.FitsInput input

/-- Ergonomic constructor which resolves each canonical layout exactly once. -/
def StructuredProblem.ofCanonical (w : ℕ) (Input Output : Type)
    [CanonicalLayout w Input] [CanonicalLayout w Output]
    (widthAtLeastTwo : 2 ≤ w) (outputRegion : Region w)
    (pre : Input → Prop) (post : Input → Output → Prop)
    (inputFits : ∀ input, pre input → (layoutOf w Input).FitsInput input) :
    StructuredProblem w where
  widthAtLeastTwo := widthAtLeastTwo
  Input := Input
  Output := Output
  inputLayout := layoutOf w Input
  outputLayout := layoutOf w Output
  outputRegion := outputRegion
  pre := pre
  post := post
  inputFits := inputFits

namespace StructuredProblem

/-- Canonical zero-padded memory determined solely by the stored input layout and value. -/
def initialMemory (problem : StructuredProblem w) (input : problem.Input)
    (valid : problem.pre input) : Memory w :=
  problem.inputLayout.init input (problem.inputFits input valid)

/-- Relational structured output interpretation from the designated final-memory region. -/
def OutputRep (problem : StructuredProblem w) (output : problem.Output)
    (memory : Memory w) : Prop :=
  problem.outputLayout.RepAt problem.outputRegion output memory

/-- A terminating run whose operational result and unit cost are coupled in one trace. -/
structure SuccessfulRun (problem : StructuredProblem w) (program : Program w)
    (input : problem.Input) (valid : problem.pre input) where
  /-- Final machine memory. -/
  final : Memory w
  /-- Halt word, retained even when the structured answer is in memory. -/
  result : BitVec w
  /-- Same-trace unit cost. -/
  cost : ℕ
  /-- Number of fetched instructions, including halt. -/
  steps : ℕ
  /-- Coupled operational trace. -/
  trace : RAM.HaltingTrace (stepCosted program)
    ⟨0, problem.initialMemory input valid⟩ final result cost steps

/-- One concrete program solves one structured input within an input-dependent bound. -/
def SolvesInputWithinBy (problem : StructuredProblem w) (program : Program w)
    (input : problem.Input) (valid : problem.pre input) (bound : ℕ) : Prop :=
  ∃ run : SuccessfulRun problem program input valid,
    ∃ output : problem.Output,
      problem.OutputRep output run.final ∧ problem.post input output ∧ run.cost ≤ bound

/-- One fixed program solves every admissible structured input. -/
def SolvesWithinBy (problem : StructuredProblem w) (program : Program w)
    (bound : problem.Input → ℕ) : Prop :=
  ∀ input, ∀ valid : problem.pre input,
    problem.SolvesInputWithinBy program input valid (bound input)

/-- Conventional footprint-indexed wrapper around the exact input-dependent predicate. -/
def SolvesWithin (problem : StructuredProblem w) (program : Program w)
    (bound : ℕ → ℕ) : Prop :=
  problem.SolvesWithinBy program fun input =>
    bound (problem.inputLayout.footprintWords input)

end StructuredProblem

/-- Publishable fixed-width certificate with an exact structured-input cost bound. -/
structure FixedWidthAlgorithmCertificateBy (problem : StructuredProblem w)
    (bound : problem.Input → ℕ) where
  /-- Concrete finite first-order Word-RAM program. -/
  program : Program w
  /-- Every numeric successor is a valid program counter. -/
  valid : program.Valid
  /-- Correctness and resource use from the same halting trace. -/
  solves : problem.SolvesWithinBy program bound

/-- Existential fixed-width structured Word-RAM algorithm claim. -/
def StructuredProblem.HasAlgorithmBy (problem : StructuredProblem w)
    (bound : problem.Input → ℕ) : Prop :=
  Nonempty (FixedWidthAlgorithmCertificateBy problem bound)

/-- Footprint-indexed fixed-width certificate. -/
abbrev FixedWidthAlgorithmCertificate (problem : StructuredProblem w) (bound : ℕ → ℕ) :=
  FixedWidthAlgorithmCertificateBy problem fun input =>
    bound (problem.inputLayout.footprintWords input)

/-- Preferred compatibility name for a footprint-indexed structured claim. -/
def StructuredProblem.HasWordRAMAlgorithm (problem : StructuredProblem w)
    (bound : ℕ → ℕ) : Prop :=
  Nonempty (FixedWidthAlgorithmCertificate problem bound)

namespace FixedWidthAlgorithmCertificateBy

/-- Weaken only the theorem-side cost bound; program and trace semantics are unchanged. -/
def weaken (certificate : FixedWidthAlgorithmCertificateBy problem oldBound)
    (larger : ∀ input, oldBound input ≤ newBound input) :
    FixedWidthAlgorithmCertificateBy problem newBound where
  program := certificate.program
  valid := certificate.valid
  solves input valid := by
    rcases certificate.solves input valid with ⟨run, output, represented, correct, cost⟩
    exact ⟨run, output, represented, correct, cost.trans (larger input)⟩

end FixedWidthAlgorithmCertificateBy

end


end Algolean.Algorithms.WordRAM
