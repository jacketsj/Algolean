/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM

/-!
# Width-independent Word-RAM program templates

A `UniformProgram` contains one finite syntax tree with natural literals and addresses.  Width
instantiation is the fixed structural reduction modulo `2^w`; there is deliberately no field of
type `Nat → WordRAM.Program`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Width-independent source syntax for the fixed word/address bridge. -/
inductive TemplateExtraInstruction where
  | valueToAddress (source : RAM.Operand ℕ ℕ) (destinationAddressRegister : ℕ)
  | addressToValue (source destination : RAM.AddressOperand ℕ)
  | mulAddress (left right : RAM.AddressOperand ℕ) (destinationAddressRegister : ℕ)

namespace TemplateExtraInstruction

def descriptionSize : TemplateExtraInstruction → Nat
  | .valueToAddress source destination =>
      2 + source.descriptionSize RAM.natDescriptionSize RAM.natDescriptionSize +
        RAM.natDescriptionSize destination
  | .addressToValue source destination =>
      2 + source.descriptionSize RAM.natDescriptionSize +
        destination.descriptionSize RAM.natDescriptionSize
  | .mulAddress left right destination =>
      2 + left.descriptionSize RAM.natDescriptionSize +
        right.descriptionSize RAM.natDescriptionSize + RAM.natDescriptionSize destination

end TemplateExtraInstruction

/-- Width-independent finite source syntax. -/
abbrev ProgramTemplate := RAM.Program ℕ ℕ TemplateExtraInstruction

namespace ProgramTemplate

def addressOperand (w : ℕ) : RAM.AddressOperand ℕ → RAM.AddressOperand (BitVec w)
  | .immediate address => .immediate (BitVec.ofNat w address)
  | .reg register => .reg register

def operand (w : ℕ) : RAM.Operand ℕ ℕ → RAM.Operand (BitVec w) (BitVec w)
  | .immediate value => .immediate (BitVec.ofNat w value)
  | .load address => .load (addressOperand w address)

/-- Fixed structural instantiation of one template instruction. -/
def instruction (w : ℕ) : RAM.Instruction ℕ ℕ TemplateExtraInstruction →
    RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w)
  | .set source destination next => .set (operand w source) (addressOperand w destination) next
  | .add left right destination next =>
      .add (operand w left) (operand w right) (addressOperand w destination) next
  | .sub left right destination next =>
      .sub (operand w left) (operand w right) (addressOperand w destination) next
  | .mul left right destination next =>
      .mul (operand w left) (operand w right) (addressOperand w destination) next
  | .div left right destination next =>
      .div (operand w left) (operand w right) (addressOperand w destination) next
  | .neg source destination next => .neg (operand w source) (addressOperand w destination) next
  | .setAddress source destination next =>
      .setAddress (addressOperand w source) destination next
  | .addAddress left right destination next =>
      .addAddress (addressOperand w left) (addressOperand w right) destination next
  | .subAddress left right destination next =>
      .subAddress (addressOperand w left) (addressOperand w right) destination next
  | .compare left right less equal greater =>
      .compare (operand w left) (operand w right) less equal greater
  | .compareAddress left right less equal greater =>
      .compareAddress (addressOperand w left) (addressOperand w right) less equal greater
  | .extra (.valueToAddress source destination) next =>
      .extra (.valueToAddress (operand w source) destination) next
  | .extra (.addressToValue source destination) next =>
      .extra (.addressToValue (addressOperand w source) (addressOperand w destination)) next
  | .extra (.mulAddress left right destination) next =>
      .extra (.mulAddress (addressOperand w left) (addressOperand w right) destination) next
  | .halt result => .halt (operand w result)

/-- Instantiate every instruction without changing code shape or control-flow targets. -/
def instantiate (template : ProgramTemplate) (w : ℕ) : Program w :=
  template.map (instruction w)

@[simp] theorem instantiate_length (template : ProgramTemplate) (w : ℕ) :
    (template.instantiate w).length = template.length := by
  simp [instantiate]

/-- Width-independent serialized source size; literals and addresses use natural binary syntax. -/
def descriptionSize (template : ProgramTemplate) : ℕ :=
  RAM.Program.descriptionSize RAM.natDescriptionSize RAM.natDescriptionSize
    TemplateExtraInstruction.descriptionSize template

end ProgramTemplate

/-- One sealed width-uniform program witness.  It has no user-supplied instantiation function. -/
structure UniformProgram where
  /-- The sole finite width-independent source program. -/
  template : ProgramTemplate

namespace UniformProgram

/-- Fixed structural specialization at width `w`. -/
def instantiate (program : UniformProgram) (w : ℕ) : Program w :=
  program.template.instantiate w

/-- Template description size is independent of the target width. -/
def descriptionSize (program : UniformProgram) : ℕ := program.template.descriptionSize

end UniformProgram

end Algolean.Algorithms.WordRAM
