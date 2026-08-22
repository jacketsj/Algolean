/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMLinking
public import Algolean.Complexity.WordRAMUniformProcedure

/-!
# Width-uniform relative Word-RAM linking

The open client and final linked target are finite width-independent syntax.  Width specialization
is structural, and a link witness proves that every specialization is exactly the ordinary
shared-body linker output.  No field of type `Nat → WordRAM.Program` is accepted as a uniform
program family.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- One width-independent relative instruction. -/
inductive UniformOpenInstruction (signature : UniformDependencySignature) where
  | core (instruction : RAM.Instruction Nat Nat Empty)
  | call (op : signature.Op) (inputBase outputBase next : Nat)

/-- One finite width-independent relative client. -/
abbrev UniformOpenProgram (signature : UniformDependencySignature) :=
  List (UniformOpenInstruction signature)

namespace UniformOpenInstruction

/-- Numeric successors are independent of word width. -/
def successors : UniformOpenInstruction signature → List Nat
  | .core instruction => instruction.successors
  | .call _ _ _ next => [next]

/-- Fixed structural specialization to a closed width-specific call node. -/
def instantiate (w : Nat) : UniformOpenInstruction signature →
    OpenInstruction (signature.atWidth w)
  | .core instruction => .core (ProgramTemplate.instruction w instruction)
  | .call op inputBase outputBase next =>
      .call op ⟨BitVec.ofNat w inputBase⟩ ⟨BitVec.ofNat w outputBase⟩ next

@[simp] theorem instantiate_successors (instruction : UniformOpenInstruction signature) :
    (instruction.instantiate w).successors = instruction.successors := by
  cases instruction with
  | core instruction =>
      cases instruction <;> try rfl
      case extra impossible _ => exact Empty.elim impossible
  | call => rfl

end UniformOpenInstruction

namespace UniformOpenProgram

/-- Width-independent control-flow validity. -/
def Valid (program : UniformOpenProgram signature) : Prop :=
  ∀ (pc : Nat) (instruction : UniformOpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

/-- Structural specialization preserves code shape. -/
def instantiate (program : UniformOpenProgram signature) (w : Nat) :
    OpenProgram (signature.atWidth w) :=
  program.map (UniformOpenInstruction.instantiate w)

@[simp] theorem instantiate_length (program : UniformOpenProgram signature) :
    (program.instantiate w).length = program.length := by simp [instantiate]

/-- A valid finite open template specializes to a valid finite open program at every width. -/
theorem instantiate_valid (program : UniformOpenProgram signature) (valid : program.Valid)
    (w : Nat) : (program.instantiate w).Valid := by
  intro pc instruction fetch target successor
  simp only [instantiate, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨source, sourceFetch, rfl⟩
  rw [UniformOpenInstruction.instantiate_successors] at successor
  simpa using valid pc source sourceFetch target successor

end UniformOpenProgram

/-- Width-independent reserved linker resources. -/
structure UniformLinkerConfiguration where
  returnCell : Nat
  jumpRegister : Nat

/-- Fixed specialization of the linker resources. -/
def UniformLinkerConfiguration.instantiate
    (configuration : UniformLinkerConfiguration) (w : Nat) : Linker.Configuration w where
  returnCell := BitVec.ofNat w configuration.returnCell
  jumpRegister := configuration.jumpRegister

/-- One finite relative client and its width-specific contract proofs. -/
structure UniformRelativeAlgorithmCertificate
    (signature : UniformDependencySignature) (family : UniformStructuredProblem)
    (bound : UniformBound family) where
  program : UniformOpenProgram signature
  valid : program.Valid
  certificateAt : (w : Nat) →
    RelativeAlgorithmCertificate (signature.atWidth w) (family.problem w) (bound w)
  code_eq : ∀ w, (certificateAt w).program = program.instantiate w

/--
A finite target template whose every specialization is exactly the concrete linker output.
This proof-carrying artifact is the width-uniform analogue of invoking the fixed-width linker; it
cannot be replaced by an arbitrary width-indexed program function.
-/
structure UniformLinkWitness (signature : UniformDependencySignature)
    (client : UniformOpenProgram signature)
    (environment : UniformImplementationEnvironment signature)
    (configuration : UniformLinkerConfiguration) where
  program : UniformProgram
  instantiate_eq : ∀ w,
    program.instantiate w =
      Linker.link (client.instantiate w) (environment.atWidth w)
        (configuration.instantiate w)

namespace UniformRelativeAlgorithmCertificate

/--
Link a uniform relative client to uniform procedure templates.  The returned certificate contains
one finite target template; all functional and cost claims are inherited from the generic
same-trace fixed-width refinement theorem.
-/
def link
    (client : UniformRelativeAlgorithmCertificate signature family relativeBound)
    (environment : UniformImplementationEnvironment signature)
    (configuration : UniformLinkerConfiguration)
    (witness : UniformLinkWitness signature client.program environment configuration)
    (compatible : ∀ w,
      Linker.Compatibility (client.certificateAt w).program (environment.atWidth w)
        (configuration.instantiate w))
    (overheadBound : ∀ w (input : (family.problem w).Input)
      (validInput : (family.problem w).pre input)
      (final : Memory w) (result : BitVec w) (cost : Nat)
      (calls : List (DependencyCallRecord (signature.atWidth w))),
      OpenHaltingTrace (signature.atWidth w) (environment.atWidth w).responder
          (client.certificateAt w).program
          ⟨0, (family.problem w).initialMemory input validInput⟩ final result cost calls →
      cost ≤ relativeBound w input →
      cost + Linker.totalConcreteCallOverhead (environment.atWidth w) calls ≤
        linkedBound w input) :
    UniformAlgorithmCertificate family linkedBound where
  program := witness.program
  valid w := by
    rw [witness.instantiate_eq]
    rw [← client.code_eq w]
    exact Linker.link_valid _ _ _ (client.certificateAt w).valid
  solves w input validInput _widthAdmissible := by
    let concrete : FixedWidthAlgorithmCertificateBy (family.problem w) (linkedBound w) :=
      (client.certificateAt w).linkConcrete
        (environment.atWidth w) (configuration.instantiate w) (compatible w)
        (overheadBound w)
    rw [witness.instantiate_eq]
    rw [← client.code_eq w]
    have programEq : concrete.program =
        Linker.link (client.certificateAt w).program (environment.atWidth w)
          (configuration.instantiate w) := rfl
    rw [← programEq]
    exact concrete.solves input validInput

/-- Existential width-uniform discharge after both client and dependency templates are concrete. -/
theorem hasUniformAlgorithm
    (client : UniformRelativeAlgorithmCertificate signature family relativeBound)
    (environment : UniformImplementationEnvironment signature)
    (configuration : UniformLinkerConfiguration)
    (witness : UniformLinkWitness signature client.program environment configuration)
    (compatible : ∀ w,
      Linker.Compatibility (client.certificateAt w).program (environment.atWidth w)
        (configuration.instantiate w))
    (overheadBound : ∀ w (input : (family.problem w).Input)
      (validInput : (family.problem w).pre input)
      (final : Memory w) (result : BitVec w) (cost : Nat)
      (calls : List (DependencyCallRecord (signature.atWidth w))),
      OpenHaltingTrace (signature.atWidth w) (environment.atWidth w).responder
          (client.certificateAt w).program
          ⟨0, (family.problem w).initialMemory input validInput⟩ final result cost calls →
      cost ≤ relativeBound w input →
      cost + Linker.totalConcreteCallOverhead (environment.atWidth w) calls ≤
        linkedBound w input) :
    family.HasUniformWordRAMAlgorithm linkedBound :=
  ⟨client.link environment configuration witness compatible overheadBound⟩

end UniformRelativeAlgorithmCertificate

end

end Algolean.Algorithms.WordRAM
