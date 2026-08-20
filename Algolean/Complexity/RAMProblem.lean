/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM.Costed

/-!
# Fixed-program claims for integer RAM and word RAM

These wrappers give ordinary integer RAM and fixed-width word RAM the same essential guarantees as
the structured real-RAM claim: one sealed program, canonical zero-initialized input, and cost from
the execution trace that produces the result.

Inputs are machine-native cell arrays.  This deliberately avoids an arbitrary free encoder.  Cell
zero stores the payload length and payload cells begin at address one.  A word-RAM input carries a
proof that its header and payload fit the `2^w`-cell address space.
-/

@[expose] public section

namespace Algolean.Algorithms

namespace IntegerRAM

/-- Canonical integer-RAM input memory: length header, payload, then zeroes. -/
def canonicalMemory (cells : List ℤ) : Memory :=
  { data := fun address =>
      if address = 0 then cells.length
      else cells.getD (address - 1) 0
    address := fun _ => 0 }

/-- The sealed unit-cost semantics for ordinary integer RAM. -/
def costedSemantics : RAM.CostedSemantics ℤ ℤ ℕ Empty ℕ :=
  RAM.CostedSemantics.unit ops RAM.noExtra

/-- One costed step in the sealed integer-RAM profile. -/
def stepCosted (program : Program) :
    Configuration → RAM.StepObservation ℤ ℕ ℕ :=
  costedSemantics.step program

/-- A native integer-RAM problem with no client-supplied input codec. -/
structure Problem where
  /-- Admissible native integer-cell arrays. -/
  pre : List ℤ → Prop
  /-- Mathematical relation between input cells and the halt value. -/
  post : List ℤ → ℤ → Prop

/-- A terminating integer-RAM execution with its unit cost from the same trace. -/
structure SuccessfulRun (program : Program) (initial : Memory) where
  /-- Final integer-RAM memory. -/
  final : Memory
  /-- Halt result. -/
  result : ℤ
  /-- Accumulated unit cost. -/
  cost : ℕ
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Coupled behavior/resource evidence. -/
  trace : RAM.HaltingTrace (stepCosted program) ⟨0, initial⟩ final result cost steps

/-- One integer-RAM program solves one native cell-array input. -/
def SolvesInputWithin (problem : Problem) (program : Program)
    (input : List ℤ) (bound : ℕ) : Prop :=
  ∃ run : SuccessfulRun program (canonicalMemory input),
    problem.post input run.result ∧ run.cost ≤ bound

/-- One fixed integer-RAM program solves every valid input. -/
def SolvesWithin (problem : Problem) (program : Program) (bound : ℕ → ℕ) : Prop :=
  ∀ input, problem.pre input →
    SolvesInputWithin problem program input (bound (input.length + 1))

/-- Preferred ordinary integer-RAM existential claim. -/
structure FixedAlgorithmCertificate (problem : Problem) (bound : ℕ → ℕ) where
  /-- Concrete ordinary integer-RAM program. -/
  program : Program
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Correctness and same-trace unit cost. -/
  solves : SolvesWithin problem program bound

/-- Existence of a typed ordinary integer-RAM certificate. -/
def Problem.HasFixedMachineAlgorithm (problem : Problem) (bound : ℕ → ℕ) : Prop :=
  Nonempty (FixedAlgorithmCertificate problem bound)

/-- Concise compatibility name for the fixed integer-RAM predicate. -/
abbrev Problem.HasAlgorithm := Problem.HasFixedMachineAlgorithm

/-- Short explicit alias for the fixed integer-RAM predicate. -/
abbrev Problem.HasFixedAlgorithm := Problem.HasFixedMachineAlgorithm

/-- Full binary source-description size for the ordinary unbounded-integer RAM. -/
def descriptionSize (program : Program) : ℕ :=
  RAM.Program.descriptionSize RAM.intDescriptionSize RAM.natDescriptionSize
    (fun instruction : Empty => nomatch instruction) program

/-- A typed nonuniform ordinary-RAM family certificate with both code metrics. -/
structure NonuniformFamilyCertificate (problem : Problem)
    (timeBound instructionBound descriptionBound : ℕ → ℕ) where
  /-- One ordinary integer-RAM program per native input size. -/
  code : ℕ → Program
  /-- Program-counter validity for every member. -/
  valid : ∀ size, (code size).Valid
  /-- Instruction-count bound. -/
  instructionSize : ∀ size,
    RAM.Program.instructionCount (code size) ≤ instructionBound size
  /-- Full source-description bound. -/
  fullDescriptionSize : ∀ size, descriptionSize (code size) ≤ descriptionBound size
  /-- Correctness and time bound for every valid input. -/
  solves : ∀ input, problem.pre input →
    let size := input.length + 1
    SolvesInputWithin problem (code size) input (timeBound size)

/-- A separately named nonuniform integer-RAM family with full description-size metadata. -/
def Problem.HasNonuniformFamily (problem : Problem)
    (timeBound instructionBound descriptionBound : ℕ → ℕ) : Prop :=
  Nonempty (NonuniformFamilyCertificate problem timeBound instructionBound descriptionBound)

end IntegerRAM

namespace WordRAM

/-- A cell array that fits together with its length header in `w`-bit address space. -/
structure Input (w : ℕ) where
  /-- Native `w`-bit payload cells. -/
  cells : List (BitVec w)
  /-- The length header and payload do not wrap around the address space. -/
  fits : cells.length + 1 ≤ 2 ^ w

/-- Canonical fixed-width word-RAM memory. -/
def canonicalMemory (input : Input w) : Memory w :=
  { data := fun address =>
      if address.toNat = 0 then BitVec.ofNat w input.cells.length
      else input.cells.getD (address.toNat - 1) 0
    address := fun _ => 0 }

/-- The sealed unit-cost semantics for a fixed word width. -/
def costedSemantics (w : ℕ) :
    RAM.CostedSemantics (BitVec w) (BitVec w) (BitVec w) Empty ℕ :=
  RAM.CostedSemantics.unit (ops w) RAM.noExtra

/-- One costed step in the sealed `w`-bit word-RAM profile. -/
def stepCosted (program : Program w) :
    Configuration w → RAM.StepObservation (BitVec w) (BitVec w) ℕ :=
  (costedSemantics w).step program

/-- A native fixed-width word-RAM problem with no client-supplied input codec. -/
structure Problem (w : ℕ) where
  /-- Admissible native word-cell inputs. -/
  pre : Input w → Prop
  /-- Mathematical relation between input cells and the halt word. -/
  post : Input w → BitVec w → Prop

/-- A terminating word-RAM execution with its unit cost from the same trace. -/
structure SuccessfulRun (program : Program w) (initial : Memory w) where
  /-- Final word-RAM memory. -/
  final : Memory w
  /-- Halt word. -/
  result : BitVec w
  /-- Accumulated unit cost. -/
  cost : ℕ
  /-- Number of fetched transitions. -/
  steps : ℕ
  /-- Coupled behavior/resource evidence. -/
  trace : RAM.HaltingTrace (stepCosted program) ⟨0, initial⟩ final result cost steps

/-- One word-RAM program solves one native input. -/
def SolvesInputWithin (problem : Problem w) (program : Program w)
    (input : Input w) (bound : ℕ) : Prop :=
  ∃ run : SuccessfulRun program (canonicalMemory input),
    problem.post input run.result ∧ run.cost ≤ bound

/-- One fixed program solves every valid input at the explicitly fixed word width `w`. -/
def SolvesWithin (problem : Problem w) (program : Program w) (bound : ℕ → ℕ) : Prop :=
  ∀ input, problem.pre input →
    SolvesInputWithin problem program input (bound (input.cells.length + 1))

/-- Preferred fixed-width word-RAM existential claim.  Width is outside the program existential. -/
structure FixedAlgorithmCertificate (problem : Problem w) (bound : ℕ → ℕ) where
  /-- Concrete program at the explicitly fixed word width. -/
  program : Program w
  /-- Program-counter validity. -/
  valid : program.Valid
  /-- Correctness and same-trace unit cost. -/
  solves : SolvesWithin problem program bound

/-- Existence of a typed fixed-width word-RAM certificate. -/
def Problem.HasFixedMachineAlgorithm (problem : Problem w) (bound : ℕ → ℕ) : Prop :=
  Nonempty (FixedAlgorithmCertificate problem bound)

/-- Concise compatibility name for the fixed-width word-RAM predicate. -/
abbrev Problem.HasAlgorithm (problem : Problem w) (bound : ℕ → ℕ) : Prop :=
  problem.HasFixedMachineAlgorithm bound

/-- Short explicit alias for the fixed-width word-RAM predicate. -/
abbrev Problem.HasFixedAlgorithm (problem : Problem w) (bound : ℕ → ℕ) : Prop :=
  problem.HasFixedMachineAlgorithm bound

/-- Full binary source-description size for a `w`-bit word-RAM program. -/
def descriptionSize (program : Program w) : ℕ :=
  RAM.Program.descriptionSize (fun _ => w) (fun _ => w)
    (fun instruction : Empty => nomatch instruction) program

/-- A typed nonuniform fixed-width word-RAM family certificate with both code metrics. -/
structure NonuniformFamilyCertificate (problem : Problem w)
    (timeBound instructionBound descriptionBound : ℕ → ℕ) where
  /-- One fixed-width word-RAM program per native input size. -/
  code : ℕ → Program w
  /-- Program-counter validity for every member. -/
  valid : ∀ size, (code size).Valid
  /-- Instruction-count bound. -/
  instructionSize : ∀ size,
    RAM.Program.instructionCount (code size) ≤ instructionBound size
  /-- Full source-description bound at width `w`. -/
  fullDescriptionSize : ∀ size, descriptionSize (code size) ≤ descriptionBound size
  /-- Correctness and time bound for every valid input. -/
  solves : ∀ input, problem.pre input →
    let size := input.cells.length + 1
    SolvesInputWithin problem (code size) input (timeBound size)

/-- A separately named nonuniform family at one fixed width, with full description metadata. -/
def Problem.HasNonuniformFamily (problem : Problem w)
    (timeBound instructionBound descriptionBound : ℕ → ℕ) : Prop :=
  Nonempty (NonuniformFamilyCertificate problem timeBound instructionBound descriptionBound)

end WordRAM

end Algolean.Algorithms
