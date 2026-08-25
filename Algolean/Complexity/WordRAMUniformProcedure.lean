/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMUniform
public import Algolean.Complexity.WordRAMRelative

/-!
# Width-uniform callable Word-RAM procedures

Width-specific callable code must be the fixed structural instantiation of one finite template.
The API contains no unconstrained `Nat → Program` witness.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Width-independent calling convention data. -/
structure CallingConventionTemplate where
  inputBase : Nat
  outputBase : Nat
  scratchStart : Nat
  scratchWords : Nat
  ownedRegisters : List Nat
  aliasingPolicy : AliasingPolicy := .disjoint

namespace CallingConventionTemplate

def instantiate (template : CallingConventionTemplate) (w : Nat) : CallingConvention w where
  inputRegion := ⟨BitVec.ofNat w template.inputBase⟩
  outputRegion := ⟨BitVec.ofNat w template.outputBase⟩
  scratchOwned address :=
    template.scratchStart ≤ address.toNat ∧
      address.toNat < template.scratchStart + template.scratchWords
  registerOwned register := register ∈ template.ownedRegisters
  aliasingPolicy := template.aliasingPolicy

end CallingConventionTemplate

/-- A contract and exact bound at each width. -/
structure UniformProcedureContract where
  contract : (width : AdmissibleWidth) → ProcedureContract width.value
  bound : (width : AdmissibleWidth) → ProcedureBound (contract width)

/-- One finite template implements the whole width-indexed contract family. -/
structure UniformProcedureCertificate (family : UniformProcedureContract) where
  program : UniformProgram
  entry : Nat
  calling : CallingConventionTemplate
  certificateAt : (width : AdmissibleWidth) →
    RestoringProcedureCertificate (family.contract width) (family.bound width)
  code_eq : ∀ (width : AdmissibleWidth),
    (certificateAt width).module.code = program.instantiate width.value
  entry_eq : ∀ (width : AdmissibleWidth), (certificateAt width).module.entry = entry
  calling_eq : ∀ (width : AdmissibleWidth),
    (certificateAt width).calling = calling.instantiate width.value

/-- Existential width-uniform procedure claim. -/
def HasUniformProcedure (family : UniformProcedureContract) : Prop :=
  Nonempty (UniformProcedureCertificate family)

/-- A finite operation set shared by every width. -/
structure UniformDependencySignature where
  Op : Type
  finiteOp : Fintype Op
  decEqOp : DecidableEq Op
  procedure : Op → UniformProcedureContract

attribute [instance] UniformDependencySignature.finiteOp
  UniformDependencySignature.decEqOp

/-- Width-uniform implementations retain one template per finite dependency operation. -/
structure UniformImplementationEnvironment (signature : UniformDependencySignature) where
  implementation : (op : signature.Op) →
    UniformProcedureCertificate (signature.procedure op)

/-- Specialize the contracts and declared bounds without consulting an implementation. -/
def UniformDependencySignature.atWidth (signature : UniformDependencySignature)
    (width : AdmissibleWidth) : DependencySignature width.value where
  Op := signature.Op
  finiteOp := signature.finiteOp
  decEqOp := signature.decEqOp
  contract op := (signature.procedure op).contract width
  bound op := (signature.procedure op).bound width

/-- Specialize a width-uniform environment without choosing new width-indexed code. -/
def UniformImplementationEnvironment.atWidth
    (environment : UniformImplementationEnvironment signature) (width : AdmissibleWidth) :
    ImplementationEnvironment (signature.atWidth width) where
  implementation op := (environment.implementation op).certificateAt width

end Algolean.Algorithms.WordRAM
