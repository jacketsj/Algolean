/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Core
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Closed arithmetic profiles for the structured exact-real/natural RAM

The storage architecture is fixed by `StructuredRealRAM`.  This module independently selects a
closed exact-real primitive set.  Profiles and instructions contain no Lean evaluator functions,
arbitrary real constants, or real-to-discrete operation unless the named floor profile is chosen.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Finite named constants; arbitrary kernel `Real` terms are deliberately absent. -/
inductive NamedRealConstant where
  | pi
  | e
  | logTwo
deriving DecidableEq, Repr

namespace NamedRealConstant

/-- Fixed library semantics of each finitely tagged constant. -/
noncomputable def value : NamedRealConstant → Real
  | .pi => Real.pi
  | .e => Real.exp 1
  | .logTwo => Real.log 2

/-- Canonical finite tag encoding. -/
def encode : NamedRealConstant → List Bool
  | .pi => [false, false]
  | .e => [false, true]
  | .logTwo => [true, false]

end NamedRealConstant

/-- Optional exact-real unary primitives with fixed library semantics. -/
inductive RealUnaryPrimitive where
  | sqrt
  | kthRoot (degree : Nat)
  | exp
  | log
  | sin
  | cos
deriving DecidableEq, Repr

namespace RealUnaryPrimitive

/-- Canonical finite primitive description, including the full degree literal. -/
def encode : RealUnaryPrimitive → List Bool
  | .sqrt => [false, false, false]
  | .kthRoot degree => [false, false, true] ++ Program.encodeNat degree
  | .exp => [false, true, false]
  | .log => [false, true, true]
  | .sin => [true, false, false]
  | .cos => [true, false, true]

/--
Fixed partial semantics.  Square root is stuck on negative inputs; roots are stuck at degree zero
and for negative even radicands; logarithm is stuck on nonpositive inputs.
-/
noncomputable def eval : RealUnaryPrimitive → Real → Option Real
  | .sqrt, value => if value < 0 then none else some (Real.sqrt value)
  | .kthRoot degree, value =>
      if degree = 0 then none
      else if value < 0 then
        if Odd degree then some (-((-value) ^ ((degree : Real)⁻¹))) else none
      else some (value ^ ((degree : Real)⁻¹))
  | .exp, value => some (Real.exp value)
  | .log, value => if value ≤ 0 then none else some (Real.log value)
  | .sin, value => some (Real.sin value)
  | .cos, value => some (Real.cos value)

end RealUnaryPrimitive

/-- Closed compositional arithmetic capability index. -/
inductive ArithmeticProfile where
  | algebraic
  | sqrt
  | fixedRoots (degrees : List Nat)
  | expLog
  | trigonometric
  | floorToNat
  | namedConstants (constants : List NamedRealConstant)
  | combine (left right : ArithmeticProfile)
deriving DecidableEq, Repr

namespace ArithmeticProfile

/-- Kernel-visible admission relation for unary primitives. -/
def AllowsUnary : ArithmeticProfile → RealUnaryPrimitive → Prop
  | .algebraic, _ => False
  | .sqrt, .sqrt => True
  | .sqrt, _ => False
  | .fixedRoots degrees, .kthRoot degree => degree ∈ degrees
  | .fixedRoots _, _ => False
  | .expLog, .exp | .expLog, .log => True
  | .expLog, _ => False
  | .trigonometric, .sin | .trigonometric, .cos => True
  | .trigonometric, _ => False
  | .floorToNat, _ | .namedConstants _, _ => False
  | .combine left right, primitive =>
      left.AllowsUnary primitive ∨ right.AllowsUnary primitive

/-- Whether the strong nonnegative real-to-natural floor bridge is available. -/
def AllowsFloorToNat : ArithmeticProfile → Prop
  | .floorToNat => True
  | .combine left right => left.AllowsFloorToNat ∨ right.AllowsFloorToNat
  | _ => False

/-- Admission relation for the finite named-constant list. -/
def AllowsConstant : ArithmeticProfile → NamedRealConstant → Prop
  | .namedConstants constants, constant => constant ∈ constants
  | .combine left right, constant =>
      left.AllowsConstant constant ∨ right.AllowsConstant constant
  | _, _ => False

/-- Stable arithmetic-profile name derived from closed syntax. -/
def name : ArithmeticProfile → String
  | .algebraic => "algebraic"
  | .sqrt => "exact square root"
  | .fixedRoots degrees => "fixed roots " ++ toString degrees
  | .expLog => "exact exp/log"
  | .trigonometric => "exact sin/cos"
  | .floorToNat => "nonnegative exact floor-to-Nat"
  | .namedConstants constants => "named constants " ++ reprStr constants
  | .combine left right => left.name ++ " + " ++ right.name

/-- Audit-visible primitive list derived only from the closed profile term. -/
def primitiveNames : ArithmeticProfile → List String
  | .algebraic => []
  | .sqrt => ["sqrt"]
  | .fixedRoots degrees => degrees.map (fun degree ↦ "root(" ++ toString degree ++ ")")
  | .expLog => ["exp", "log"]
  | .trigonometric => ["sin", "cos"]
  | .floorToNat => ["floor-to-Nat"]
  | .namedConstants _ => []
  | .combine left right => left.primitiveNames ++ right.primitiveNames

/-- Audit-visible constants derived only from the finite named-constant syntax. -/
def constantNames : ArithmeticProfile → List String
  | .namedConstants constants => constants.map reprStr
  | .combine left right => left.constantNames ++ right.constantNames
  | _ => []

/-- Audit-visible partial-domain rules for precisely the selected primitives. -/
def domainRules : ArithmeticProfile → List String
  | .sqrt => ["sqrt is stuck on negative inputs"]
  | .fixedRoots degrees => degrees.map fun degree ↦
      "root(" ++ toString degree ++ ") is stuck at degree zero and on negative even radicands"
  | .expLog => ["log is stuck on nonpositive inputs"]
  | .floorToNat => ["floor-to-Nat is stuck on negative inputs"]
  | .combine left right => left.domainRules ++ right.domainRules
  | _ => []

end ArithmeticProfile

/-- Resource coordinate for every non-core exact-real primitive. -/
inductive RealPrimitive where
  | unary (primitive : RealUnaryPrimitive)
  | floorToNat
  | namedConstant (constant : NamedRealConstant)
deriving DecidableEq, Repr

/-- Core resources together with operation-sensitive primitive counts. -/
structure ArithmeticCost where
  machine : Cost
  primitive : RealPrimitive → Nat

namespace ArithmeticCost

instance : Zero ArithmeticCost := ⟨0, fun _ ↦ 0⟩

instance : Add ArithmeticCost where
  add left right :=
    ⟨left.machine + right.machine, fun primitive ↦
      left.primitive primitive + right.primitive primitive⟩

instance : LE ArithmeticCost where
  le left right := left.machine ≤ right.machine ∧
    ∀ primitive, left.primitive primitive ≤ right.primitive primitive

instance : Preorder ArithmeticCost where
  le_refl cost := ⟨le_rfl, fun _ ↦ le_rfl⟩
  le_trans left middle right := by
    rintro ⟨leftMachine, leftPrimitive⟩ ⟨rightMachine, rightPrimitive⟩
    exact ⟨leftMachine.trans rightMachine,
      fun primitive ↦ (leftPrimitive primitive).trans (rightPrimitive primitive)⟩

/-- Lift one core transition without charging an optional primitive. -/
def ofCore (cost : Cost) : ArithmeticCost := ⟨cost, fun _ ↦ 0⟩

@[simp]
theorem ofCore_zero : ofCore 0 = 0 := rfl

@[simp]
theorem ofCore_add (left right : Cost) : ofCore (left + right) = ofCore left + ofCore right :=
  rfl

/-- Charge one optional primitive in the same fetched transition. -/
def ofPrimitive (machine : Cost) (selected : RealPrimitive) : ArithmeticCost :=
  ⟨machine, fun primitive ↦ if primitive = selected then 1 else 0⟩

/-- Total fetched transitions remain the first core cost coordinate. -/
def steps (cost : ArithmeticCost) : Nat := cost.machine.steps

/-- Count of one named optional primitive. -/
def count (cost : ArithmeticCost) (primitive : RealPrimitive) : Nat :=
  cost.primitive primitive

@[ext]
theorem ext {left right : ArithmeticCost} (machine : left.machine = right.machine)
    (primitive : ∀ operation, left.primitive operation = right.primitive operation) :
    left = right := by
  cases left
  cases right
  congr
  funext operation
  exact primitive operation

end ArithmeticCost

/-- Closed finite instructions indexed by an inert arithmetic capability profile. -/
inductive ArithmeticInstruction (profile : ArithmeticProfile) where
  | core (instruction : Instruction)
  | unary (primitive : RealUnaryPrimitive) (allowed : profile.AllowsUnary primitive)
      (source : RealOperand) (destinationRegister next : Nat)
  | floorToNat (allowed : profile.AllowsFloorToNat)
      (source : RealOperand) (destinationRegister next : Nat)
  | namedConstant (constant : NamedRealConstant) (allowed : profile.AllowsConstant constant)
      (destinationRegister next : Nat)

namespace ArithmeticInstruction

/-- Numeric successors of one profile-indexed instruction. -/
def successors : ArithmeticInstruction profile → List Nat
  | .core instruction => instruction.successors
  | .unary _ _ _ _ next | .floorToNat _ _ _ next |
      .namedConstant _ _ _ next => [next]

/-- Same-transition operation-sensitive charge. -/
def cost : ArithmeticInstruction profile → ArithmeticCost
  | .core instruction => .ofCore instruction.cost
  | .unary primitive _ source _ _ =>
      .ofPrimitive (Cost.ofFields 1 source.reads 1 1 0 0 0 0 0) (.unary primitive)
  | .floorToNat _ source _ _ =>
      .ofPrimitive (Cost.ofFields 1 source.reads 0 1 0 0 1 0 0) .floorToNat
  | .namedConstant constant _ _ _ =>
      .ofPrimitive (Cost.ofFields 1 0 1 0 0 0 0 0 0) (.namedConstant constant)

/-- Canonical binary syntax; admission proofs and other proof data are erased. -/
def encode : ArithmeticInstruction profile → List Bool
  | .core instruction => false :: Program.encodeInstruction instruction
  | .unary primitive _ source destination next =>
      [true, false, false] ++ primitive.encode ++ Program.encodeRealOperand source ++
        Program.encodeNat destination ++ Program.encodeNat next
  | .floorToNat _ source destination next =>
      [true, false, true] ++ Program.encodeRealOperand source ++
        Program.encodeNat destination ++ Program.encodeNat next
  | .namedConstant constant _ destination next =>
      [true, true, false] ++ constant.encode ++ Program.encodeNat destination ++
        Program.encodeNat next

end ArithmeticInstruction

/-- One finite first-order program in a closed arithmetic profile. -/
abbrev ArithmeticProgram (profile : ArithmeticProfile) := List (ArithmeticInstruction profile)

namespace ArithmeticProgram

/-- All explicit control-flow successors remain inside the same finite program. -/
def Valid (program : ArithmeticProgram profile) : Prop :=
  ∀ (pc : Nat) (instruction : ArithmeticInstruction profile),
    program[pc]? = some instruction →
    ∀ target ∈ ArithmeticInstruction.successors instruction, target < program.length

/-- Canonical finite description size, including degrees, addresses, and named-constant tags. -/
def descriptionSize (program : ArithmeticProgram profile) : Nat :=
  (Program.encodeNat program.length ++ (program.map ArithmeticInstruction.encode).flatten).length

end ArithmeticProgram

/-- Same-transition observation for a profile-indexed exact-real instruction. -/
structure ArithmeticStepObservation where
  outcome : StepResult
  cost : ArithmeticCost

/-- Execute one allowed instruction using only fixed library semantics. -/
noncomputable def executeArithmetic (configuration : Configuration)
    (instruction : ArithmeticInstruction profile) : ArithmeticStepObservation :=
  match instruction with
  | .core coreInstruction =>
      let observation := execute coreInstruction configuration.memory
      ⟨observation.outcome, .ofCore observation.cost⟩
  | .unary primitive _ source destination next =>
      let cost := instruction.cost
      match primitive.eval (source.eval configuration.memory) with
      | none => ⟨.stuck configuration, cost⟩
      | some value =>
          ⟨.running ⟨next, configuration.memory.writeReal
            (configuration.memory.natReg destination) value⟩, cost⟩
  | .floorToNat _ source destination next =>
      let cost := instruction.cost
      let value := source.eval configuration.memory
      if value < 0 then ⟨.stuck configuration, cost⟩
      else
        ⟨.running ⟨next, configuration.memory.writeReg destination ⌊value⌋.toNat⟩, cost⟩
  | .namedConstant constant _ destination next =>
      ⟨.running ⟨next, configuration.memory.writeReal
        (configuration.memory.natReg destination) constant.value⟩, instruction.cost⟩

/-- Fetch and execute one profile-indexed instruction. -/
noncomputable def arithmeticStep (program : ArithmeticProgram profile)
    (configuration : Configuration) : ArithmeticStepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => executeArithmetic configuration instruction

/-- Same trace carries final memory, result, total steps, and every primitive coordinate. -/
inductive ArithmeticHaltingTrace (program : ArithmeticProgram profile) :
    Configuration → Memory → Real → ArithmeticCost → Nat → Prop where
  | halt {configuration memory result cost}
      (observes : arithmeticStep program configuration = ⟨.halted memory result, cost⟩) :
      ArithmeticHaltingTrace program configuration memory result cost 1
  | next {configuration nextConfiguration memory result headCost tailCost steps}
      (observes : arithmeticStep program configuration = ⟨.running nextConfiguration, headCost⟩)
      (tail : ArithmeticHaltingTrace program nextConfiguration memory result tailCost steps) :
      ArithmeticHaltingTrace program configuration memory result (headCost + tailCost) (steps + 1)

/-- Closed structural core embedding into every arithmetic profile. -/
def liftCoreArithmetic (program : Program) : ArithmeticProgram profile :=
  program.map .core

@[simp]
theorem liftCoreArithmetic_length (program : Program) :
    (liftCoreArithmetic (profile := profile) program).length = program.length := by
  simp [liftCoreArithmetic]

/-- Core validity is preserved by the fixed `.core` injection. -/
theorem liftCoreArithmetic_valid (program : Program) (valid : program.Valid) :
    ArithmeticProgram.Valid (liftCoreArithmetic (profile := profile) program) := by
  intro pc instruction fetch target successor
  simp only [liftCoreArithmetic, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨core, coreFetch, rfl⟩
  simpa [liftCoreArithmetic] using
    valid pc core coreFetch target (by simpa [ArithmeticInstruction.successors] using successor)

/-- One core step is simulated exactly, with no optional-primitive count. -/
theorem liftCoreArithmetic_step (program : Program) (configuration : Configuration) :
    arithmeticStep (liftCoreArithmetic (profile := profile) program) configuration =
      let observation := step program configuration
      ⟨observation.outcome, ArithmeticCost.ofCore observation.cost⟩ := by
  simp only [arithmeticStep, liftCoreArithmetic, List.getElem?_map]
  cases fetch : program[configuration.pc]? with
  | none => simp [step, fetch]
  | some instruction => simp [step, fetch, executeArithmetic]

/-- Complete deterministic traces embed with identical memory, result, steps, and core cost. -/
theorem liftCoreArithmetic_trace
    (trace : HaltingTrace program initial final result cost steps) :
    ArithmeticHaltingTrace (liftCoreArithmetic (profile := profile) program)
      initial final result (ArithmeticCost.ofCore cost) steps := by
  induction trace with
  | halt observes =>
      apply ArithmeticHaltingTrace.halt
      rw [liftCoreArithmetic_step, observes]
  | next observes tail induction =>
      rw [ArithmeticCost.ofCore_add]
      apply ArithmeticHaltingTrace.next
      · rw [liftCoreArithmetic_step, observes]
      · simpa [ArithmeticCost.ofCore] using induction

/-- Core description size grows only by one constructor tag per instruction. -/
theorem liftCoreArithmetic_descriptionSize_bound (program : Program) :
    ArithmeticProgram.descriptionSize (liftCoreArithmetic (profile := profile) program) ≤
      program.descriptionSize + program.length := by
  simp only [ArithmeticProgram.descriptionSize, liftCoreArithmetic,
    Program.descriptionSize, Program.encode, List.map_map, Function.comp_apply,
    ArithmeticInstruction.encode, Program.encodeInstructions]
  induction program with
  | nil => simp [Program.encodeInstructions]
  | cons head tail induction =>
      simp only [List.length_append, List.length_cons, List.length_map, List.length_flatten,
        List.sum_cons, Program.encodeInstructions]
      simp_all [ArithmeticInstruction.encode]
      omega

/-! Stable named public profiles. -/

abbrev AlgebraicExactRealNatRAM : ArithmeticProfile := .algebraic
abbrev AlgebraicSqrtExactRealNatRAM : ArithmeticProfile := .combine .algebraic .sqrt
abbrev AlgebraicKthRootExactRealNatRAM (roots : List Nat) : ArithmeticProfile :=
  .combine .algebraic (.fixedRoots roots)
abbrev ExpLogExactRealNatRAM : ArithmeticProfile := .combine .algebraic .expLog
abbrev TrigExactRealNatRAM : ArithmeticProfile := .combine .algebraic .trigonometric
abbrev FloorExactRealNatRAM : ArithmeticProfile := .combine .algebraic .floorToNat

end Algolean.Algorithms.StructuredRealRAM
