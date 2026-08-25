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

/-- Widths supported by the public Word-RAM semantics. -/
structure AdmissibleWidth where
  value : Nat
  atLeastTwo : 2 ≤ value
deriving DecidableEq

namespace AdmissibleWidth

instance : Coe AdmissibleWidth Nat := ⟨AdmissibleWidth.value⟩

def ofNat (offset : Nat) : AdmissibleWidth := ⟨offset + 2, by omega⟩

end AdmissibleWidth

/-- A width-indexed structured problem with an explicit admissibility promise. -/
structure UniformStructuredProblem where
  /-- Structured problem at each target width. -/
  problem : (width : AdmissibleWidth) → StructuredProblem width.value
  /-- Explicit assumptions connecting a width to one input and all required no-overflow facts. -/
  WidthAdmissible : (width : AdmissibleWidth) → (problem width).Input → Prop

/-- A dependent exact time bound for a width-uniform problem family. -/
abbrev UniformBound (family : UniformStructuredProblem) :=
  (width : AdmissibleWidth) → (family.problem width).Input → ℕ

/-- One sealed template solves every admissible width/input pair. -/
structure UniformAlgorithmCertificate (family : UniformStructuredProblem)
    (bound : UniformBound family) where
  /-- One finite template, chosen before widths and inputs. -/
  program : UniformProgram
  /-- Every fixed structural instantiation has valid control-flow targets. -/
  valid : ∀ (width : AdmissibleWidth), (program.instantiate width.value).Valid
  /-- Same-trace correctness for every mathematically and width-admissible input. -/
  solves : ∀ (width : AdmissibleWidth) input,
    ∀ validInput : (family.problem width).pre input,
    family.WidthAdmissible width input →
      (family.problem width).SolvesInputWithinBy
        (program.instantiate width.value) input validInput (bound width input)

/-- Preferred existential width-uniform Word-RAM claim. -/
def UniformStructuredProblem.HasUniformWordRAMAlgorithm
    (family : UniformStructuredProblem) (bound : UniformBound family) : Prop :=
  Nonempty (UniformAlgorithmCertificate family bound)

/-- Specialize a uniform certificate to one width while retaining its explicit admissibility. -/
def UniformAlgorithmCertificate.atWidth
    (certificate : UniformAlgorithmCertificate family bound) (width : AdmissibleWidth)
    (allAdmissible : ∀ input, (family.problem width).pre input →
      family.WidthAdmissible width input) :
    FixedWidthAlgorithmCertificateBy (family.problem width) (bound width) where
  program := certificate.program.instantiate width.value
  valid := certificate.valid width
  solves input valid := certificate.solves width input valid (allAdmissible input valid)

end

end Algolean.Algorithms.WordRAM
