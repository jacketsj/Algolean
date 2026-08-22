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
  callOverhead : Nat

namespace CallingConventionTemplate

def instantiate (template : CallingConventionTemplate) (w : Nat) : CallingConvention w where
  inputRegion := ⟨BitVec.ofNat w template.inputBase⟩
  outputRegion := ⟨BitVec.ofNat w template.outputBase⟩
  scratchOwned address :=
    template.scratchStart ≤ address.toNat ∧
      address.toNat < template.scratchStart + template.scratchWords
  registerOwned register := register ∈ template.ownedRegisters
  callOverhead := template.callOverhead

end CallingConventionTemplate

/-- A contract and exact bound at each width. -/
structure UniformProcedureContract where
  contract : (w : Nat) → ProcedureContract w
  bound : (w : Nat) → ProcedureBound (contract w)

/-- One finite template implements the whole width-indexed contract family. -/
structure UniformProcedureCertificate (family : UniformProcedureContract) where
  program : UniformProgram
  entry : Nat
  calling : CallingConventionTemplate
  certificateAt : (w : Nat) → ProcedureCertificate (family.contract w) (family.bound w)
  code_eq : ∀ w, (certificateAt w).module.code = program.instantiate w
  entry_eq : ∀ w, (certificateAt w).module.entry = entry
  calling_eq : ∀ w, (certificateAt w).calling = calling.instantiate w

/-- Existential width-uniform procedure claim. -/
def HasUniformProcedure (family : UniformProcedureContract) : Prop :=
  Nonempty (UniformProcedureCertificate family)

/-- A finite operation set shared by every width. -/
structure UniformDependencySignature where
  Op : Type
  finiteOp : Fintype Op
  decEqOp : DecidableEq Op
  procedure : Op → UniformProcedureContract
  /-- Width-independent ABI overhead declared before implementations are chosen. -/
  callOverhead : Op → Nat

attribute [instance] UniformDependencySignature.finiteOp
  UniformDependencySignature.decEqOp

/-- Width-uniform implementations retain one template per finite dependency operation. -/
structure UniformImplementationEnvironment (signature : UniformDependencySignature) where
  implementation : (op : signature.Op) →
    UniformProcedureCertificate (signature.procedure op)
  callingOverhead_eq : ∀ op,
    (implementation op).calling.callOverhead = signature.callOverhead op

/-- Specialize the contracts and declared bounds without consulting an implementation. -/
def UniformDependencySignature.atWidth (signature : UniformDependencySignature) (w : Nat) :
    DependencySignature w where
  Op := signature.Op
  finiteOp := signature.finiteOp
  decEqOp := signature.decEqOp
  contract op := (signature.procedure op).contract w
  bound op := (signature.procedure op).bound w
  callOverhead := signature.callOverhead

/-- Specialize a width-uniform environment without choosing new width-indexed code. -/
def UniformImplementationEnvironment.atWidth
    (environment : UniformImplementationEnvironment signature) (w : Nat) :
    ImplementationEnvironment (signature.atWidth w) where
  implementation op := (environment.implementation op).certificateAt w
  callingOverhead_eq op := by
    rw [environment.implementation op |>.calling_eq w]
    exact environment.callingOverhead_eq op

end Algolean.Algorithms.WordRAM
