/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMStructured
public import Algolean.Models.WordRAM.Uniform

/-!
# Width-uniform structured Word-RAM claims

The program witness is one finite `UniformProgram` template quantified before every width and
input.  An arbitrary function `Nat → Program` cannot inhabit this API.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- A width-indexed structured problem with an explicit admissibility promise. -/
structure UniformStructuredProblem where
  /-- Structured problem at each target width. -/
  problem : (w : ℕ) → StructuredProblem w
  /-- Explicit assumptions connecting a width to one input and all required no-overflow facts. -/
  WidthAdmissible : (w : ℕ) → (problem w).Input → Prop

/-- A dependent exact time bound for a width-uniform problem family. -/
abbrev UniformBound (family : UniformStructuredProblem) :=
  (w : ℕ) → (family.problem w).Input → ℕ

/-- One sealed template solves every admissible width/input pair. -/
structure UniformAlgorithmCertificate (family : UniformStructuredProblem)
    (bound : UniformBound family) where
  /-- One finite template, chosen before widths and inputs. -/
  program : UniformProgram
  /-- Every fixed structural instantiation has valid control-flow targets. -/
  valid : ∀ w, (program.instantiate w).Valid
  /-- Same-trace correctness for every mathematically and width-admissible input. -/
  solves : ∀ w input, ∀ validInput : (family.problem w).pre input,
    family.WidthAdmissible w input →
      (family.problem w).SolvesInputWithinBy
        (program.instantiate w) input validInput (bound w input)

/-- Preferred existential width-uniform Word-RAM claim. -/
def UniformStructuredProblem.HasUniformWordRAMAlgorithm
    (family : UniformStructuredProblem) (bound : UniformBound family) : Prop :=
  Nonempty (UniformAlgorithmCertificate family bound)

/-- Specialize a uniform certificate to one width while retaining its explicit admissibility. -/
def UniformAlgorithmCertificate.atWidth
    (certificate : UniformAlgorithmCertificate family bound) (w : ℕ)
    (allAdmissible : ∀ input, (family.problem w).pre input →
      family.WidthAdmissible w input) :
    FixedWidthAlgorithmCertificateBy (family.problem w) (bound w) where
  program := certificate.program.instantiate w
  valid := certificate.valid w
  solves input valid := certificate.solves w input valid (allAdmissible input valid)

end

end Algolean.Algorithms.WordRAM
