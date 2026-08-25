/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.ArithmeticProfile
public import Algolean.Models.StructuredRealRAM.Random
public import Algolean.Models.StructuredRealRAM.UniformReal

/-!
# Orthogonally profiled structured exact-real/natural machines

One closed profile selects both the exact-real arithmetic capabilities and the hidden randomness
source.  Instructions remain finite first-order syntax.  In particular, neither arithmetic nor
randomness is supplied by an evaluator callback.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

open MeasureTheory

/-- Closed source capability.  Input distributions are deliberately not represented here. -/
inductive RandomnessProfile where
  | none
  | hiddenFairBits
  | hiddenUniformReal
deriving DecidableEq, Repr

namespace RandomnessProfile

def name : RandomnessProfile → String
  | .none => "none"
  | .hiddenFairBits => "hidden lengthless iid fair bits"
  | .hiddenUniformReal => "hidden lengthless iid exact uniform [0,1] reals"

/-- Source carrier is fixed by closed syntax. -/
def Source : RandomnessProfile → Type
  | .none => Unit
  | .hiddenFairBits => RandomBit.Source
  | .hiddenUniformReal => UniformReal.Source

/-- Measurable structure selected by the same closed source profile. -/
@[reducible] noncomputable def sourceMeasurableSpace :
    (profile : RandomnessProfile) → MeasurableSpace profile.Source
  | .none => inferInstanceAs (MeasurableSpace Unit)
  | .hiddenFairBits => inferInstanceAs (MeasurableSpace RandomBit.Source)
  | .hiddenUniformReal => inferInstanceAs (MeasurableSpace UniformReal.Source)

noncomputable instance (profile : RandomnessProfile) : MeasurableSpace profile.Source :=
  profile.sourceMeasurableSpace

/-- Fixed law for each source profile. -/
noncomputable def sourceLaw : (profile : RandomnessProfile) → Measure profile.Source
  | .none => Measure.dirac ()
  | .hiddenFairBits => RandomBit.sourceLaw
  | .hiddenUniformReal => UniformReal.sourceLaw

/-- Only equality and adding hidden randomness to a deterministic machine are free embeddings. -/
inductive Embeds : RandomnessProfile → RandomnessProfile → Type where
  | refl (profile) : Embeds profile profile
  | deterministic (target) : Embeds .none target

/-- A stronger source realization projects to the source needed by the weaker profile. -/
def Embeds.projectSource : Embeds source target → target.Source → source.Source
  | .refl _, value => value
  | .deterministic _, _ => ()

theorem Embeds.target_eq_fairBits
    (embedding : Embeds source target) (equal : source = .hiddenFairBits) :
    target = .hiddenFairBits := by
  cases embedding with
  | refl profile => exact equal
  | deterministic target => cases equal

theorem Embeds.target_eq_uniformReal
    (embedding : Embeds source target) (equal : source = .hiddenUniformReal) :
    target = .hiddenUniformReal := by
  cases embedding with
  | refl profile => exact equal
  | deterministic target => cases equal

end RandomnessProfile

/-- Complete closed machine capability. -/
structure ClosedMachineProfile where
  arithmetic : ArithmeticProfile
  randomness : RandomnessProfile
deriving DecidableEq, Repr

namespace ClosedMachineProfile

abbrev deterministic (arithmetic : ArithmeticProfile) : ClosedMachineProfile :=
  ⟨arithmetic, .none⟩

def fairBits (arithmetic : ArithmeticProfile) : ClosedMachineProfile :=
  ⟨arithmetic, .hiddenFairBits⟩

def uniformReal (arithmetic : ArithmeticProfile) : ClosedMachineProfile :=
  ⟨arithmetic, .hiddenUniformReal⟩

def name (profile : ClosedMachineProfile) : String :=
  "structured exact-real/unbounded-Nat RAM; arithmetic=" ++ profile.arithmetic.name ++
    "; randomness=" ++ profile.randomness.name

end ClosedMachineProfile

/-- Exact arithmetic-profile inclusion, stated only through closed admission relations. -/
structure ArithmeticProfile.Includes (source target : ArithmeticProfile) : Prop where
  unary : ∀ primitive, source.AllowsUnary primitive → target.AllowsUnary primitive
  floorToNat : source.AllowsFloorToNat → target.AllowsFloorToNat
  constant : ∀ value, source.AllowsConstant value → target.AllowsConstant value

namespace ArithmeticProfile.Includes

theorem refl (profile : ArithmeticProfile) : profile.Includes profile :=
  ⟨fun _ allowed ↦ allowed, id, fun _ allowed ↦ allowed⟩

theorem trans {source middle target : ArithmeticProfile}
    (left : source.Includes middle) (right : middle.Includes target) :
    source.Includes target :=
  ⟨fun primitive allowed ↦ right.unary primitive (left.unary primitive allowed),
    fun allowed ↦ right.floorToNat (left.floorToNat allowed),
    fun value allowed ↦ right.constant value (left.constant value allowed)⟩

theorem algebraic (target : ArithmeticProfile) :
    ArithmeticProfile.Includes .algebraic target := by
  constructor <;> simp [ArithmeticProfile.AllowsUnary, ArithmeticProfile.AllowsFloorToNat,
    ArithmeticProfile.AllowsConstant]

theorem combineLeft (left right : ArithmeticProfile) :
    left.Includes (.combine left right) := by
  exact ⟨fun _ allowed ↦ Or.inl allowed, Or.inl, fun _ allowed ↦ Or.inl allowed⟩

theorem combineRight (left right : ArithmeticProfile) :
    right.Includes (.combine left right) := by
  exact ⟨fun _ allowed ↦ Or.inr allowed, Or.inr, fun _ allowed ↦ Or.inr allowed⟩

end ArithmeticProfile.Includes

/-- Certified capability inclusion; no arbitrary instruction translator is accepted. -/
structure ClosedMachineProfile.Embedding (source target : ClosedMachineProfile) where
  arithmetic : source.arithmetic.Includes target.arithmetic
  randomness : RandomnessProfile.Embeds source.randomness target.randomness

namespace ClosedMachineProfile.Embedding

def refl (profile : ClosedMachineProfile) : profile.Embedding profile :=
  ⟨ArithmeticProfile.Includes.refl _, .refl _⟩

def deterministicInto (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (randomness : RandomnessProfile) :
    (ClosedMachineProfile.deterministic sourceArithmetic).Embedding
      ⟨targetArithmetic, randomness⟩ :=
  ⟨arithmetic, .deterministic randomness⟩

def sameRandomness (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (randomness : RandomnessProfile) :
    (ClosedMachineProfile.mk sourceArithmetic randomness).Embedding
      (ClosedMachineProfile.mk targetArithmetic randomness) :=
  ⟨arithmetic, .refl randomness⟩

end ClosedMachineProfile.Embedding

/-- Core state plus a hidden semantic source cursor. -/
abbrev ProfiledConfiguration := RandomBit.Configuration
abbrev ProfiledStepResult := RandomBit.StepResult

/-- Operation-sensitive arithmetic cost plus the selected primitive-source draw count. -/
@[ext]
structure ProfiledCost where
  arithmetic : ArithmeticCost
  randomDraws : Nat

namespace ProfiledCost

instance : Zero ProfiledCost := ⟨0, 0⟩

instance : Add ProfiledCost where
  add left right :=
    ⟨left.arithmetic + right.arithmetic, left.randomDraws + right.randomDraws⟩

instance : LE ProfiledCost where
  le left right := left.arithmetic ≤ right.arithmetic ∧ left.randomDraws ≤ right.randomDraws

instance : Preorder ProfiledCost where
  le_refl value := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ leftMiddle middleRight :=
    ⟨leftMiddle.1.trans middleRight.1, leftMiddle.2.trans middleRight.2⟩

def ofArithmetic (cost : ArithmeticCost) : ProfiledCost := ⟨cost, 0⟩

def ofSample (machine : Cost) : ProfiledCost :=
  ⟨ArithmeticCost.ofCore machine, 1⟩

def steps (cost : ProfiledCost) : Nat := cost.arithmetic.machine.steps

def primitiveCount (cost : ProfiledCost) (primitive : RealPrimitive) : Nat :=
  cost.arithmetic.count primitive

end ProfiledCost

/-- Closed syntax for the orthogonal arithmetic/randomness product profile. -/
inductive ProfiledInstruction (profile : ClosedMachineProfile) where
  | arithmetic (instruction : ArithmeticInstruction profile.arithmetic)
  | randBit (allowed : profile.randomness = .hiddenFairBits)
      (destinationRegister next : Nat)
  | sampleUniform (allowed : profile.randomness = .hiddenUniformReal)
      (destinationRegister next : Nat)

namespace ProfiledInstruction

def successors : ProfiledInstruction profile → List Nat
  | .arithmetic instruction => instruction.successors
  | .randBit _ _ next | .sampleUniform _ _ next => [next]

def encode : ProfiledInstruction profile → List Bool
  | .arithmetic instruction => false :: instruction.encode
  | .randBit _ destination next =>
      [true, false] ++ Program.encodeNat destination ++ Program.encodeNat next
  | .sampleUniform _ destination next =>
      [true, true] ++ Program.encodeNat destination ++ Program.encodeNat next

/-- The same closed syntax fixes every arithmetic and sampling charge. -/
def cost : ProfiledInstruction profile → ProfiledCost
  | .arithmetic instruction => .ofArithmetic instruction.cost
  | .randBit _ _ _ => .ofSample (Cost.ofFields 1 0 0 0 0 0 1 0 0)
  | .sampleUniform _ _ _ => .ofSample (Cost.ofFields 1 0 1 0 0 0 0 0 0)

end ProfiledInstruction

abbrev ProfiledProgram (profile : ClosedMachineProfile) := List (ProfiledInstruction profile)

namespace ProfiledProgram

def Valid (program : ProfiledProgram profile) : Prop :=
  ∀ (pc : Nat) (instruction : ProfiledInstruction profile), program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

def encode (program : ProfiledProgram profile) : List Bool :=
  Program.encodeNat program.length ++ (program.map ProfiledInstruction.encode).flatten

def descriptionSize (program : ProfiledProgram profile) : Nat := program.encode.length

end ProfiledProgram

/-- Same-transition profiled observation. -/
structure ProfiledStepObservation where
  outcome : ProfiledStepResult
  cost : ProfiledCost

def liftArithmeticOutcome (cursor : Nat) : StepResult → ProfiledStepResult
  | .running configuration => .running ⟨configuration.pc, configuration.memory, cursor⟩
  | .halted memory result => .halted memory result cursor
  | .stuck configuration => .stuck ⟨configuration.pc, configuration.memory, cursor⟩

def readFairBit (profile : RandomnessProfile) (source : profile.Source)
    (cursor : Nat) : Bool :=
  match profile with
  | .hiddenFairBits => source cursor
  | _ => false

noncomputable def readUniformReal (profile : RandomnessProfile)
    (source : profile.Source) (cursor : Nat) : Real :=
  match profile with
  | .hiddenUniformReal => source cursor
  | _ => 0

/-- Execute one closed profiled instruction against one fixed hidden source. -/
noncomputable def executeProfiled (source : profile.randomness.Source)
    (instruction : ProfiledInstruction profile)
    (configuration : ProfiledConfiguration) : ProfiledStepObservation :=
  match instruction with
  | .arithmetic arithmetic =>
      let observation := executeArithmetic ⟨configuration.pc, configuration.memory⟩ arithmetic
      ⟨liftArithmeticOutcome configuration.randomCursor observation.outcome,
        .ofArithmetic observation.cost⟩
  | .randBit _ destination next =>
      let value := if readFairBit profile.randomness source configuration.randomCursor then 1 else 0
      let memory := configuration.memory.writeNat
        (configuration.memory.natReg destination) value
      ⟨.running ⟨next, memory, configuration.randomCursor + 1⟩,
        .ofSample (Cost.ofFields 1 0 0 0 0 0 1 0 0)⟩
  | .sampleUniform _ destination next =>
      let value := readUniformReal profile.randomness source configuration.randomCursor
      let memory := configuration.memory.writeReal
        (configuration.memory.natReg destination) value
      ⟨.running ⟨next, memory, configuration.randomCursor + 1⟩,
        .ofSample (Cost.ofFields 1 0 1 0 0 0 0 0 0)⟩

theorem executeProfiled_cost (source : profile.randomness.Source)
    (instruction : ProfiledInstruction profile) (configuration : ProfiledConfiguration) :
    (executeProfiled source instruction configuration).cost = instruction.cost := by
  cases instruction with
  | arithmetic instruction =>
      simp [executeProfiled, ProfiledInstruction.cost, executeArithmetic_cost]
  | randBit => rfl
  | sampleUniform => rfl

/-- Fetch and execute one profiled instruction. -/
noncomputable def profiledStep (program : ProfiledProgram profile)
    (source : profile.randomness.Source)
    (configuration : ProfiledConfiguration) : ProfiledStepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => executeProfiled source instruction configuration

/-- Same trace carries output, full arithmetic vector, sample count, and transition count. -/
inductive ProfiledHaltingTrace (program : ProfiledProgram profile)
    (source : profile.randomness.Source) :
    ProfiledConfiguration → Memory → Real → ProfiledCost → Nat → Nat → Prop where
  | halt {configuration memory result cost draws}
      (observes : profiledStep program source configuration =
        ⟨.halted memory result draws, cost⟩) :
      ProfiledHaltingTrace program source configuration memory result cost 1 draws
  | next {configuration nextConfiguration memory result headCost tailCost steps draws}
      (observes : profiledStep program source configuration =
        ⟨.running nextConfiguration, headCost⟩)
      (tail : ProfiledHaltingTrace program source nextConfiguration
        memory result tailCost steps draws) :
      ProfiledHaltingTrace program source configuration memory result
        (headCost + tailCost) (steps + 1) draws

/-- Per-transition source-cursor accounting. -/
def ProfiledStepObservation.CursorAccounting (observation : ProfiledStepObservation)
    (initial : ProfiledConfiguration) : Prop :=
  match observation.outcome with
  | .running next => observation.cost.randomDraws + initial.randomCursor = next.randomCursor
  | .halted _ _ draws => observation.cost.randomDraws + initial.randomCursor = draws
  | .stuck _ => observation.cost.randomDraws = 0

theorem executeProfiled_cursorAccounting
    (source : profile.randomness.Source) (instruction : ProfiledInstruction profile)
    (configuration : ProfiledConfiguration) :
    (executeProfiled source instruction configuration).CursorAccounting configuration := by
  cases instruction with
  | arithmetic instruction =>
      simp only [executeProfiled]
      generalize observed : executeArithmetic
        ⟨configuration.pc, configuration.memory⟩ instruction = observation
      cases observation with
      | mk outcome cost =>
          cases outcome <;>
            simp [ProfiledStepObservation.CursorAccounting, liftArithmeticOutcome,
              ProfiledCost.ofArithmetic]
  | randBit allowed destination next =>
      simp [executeProfiled, ProfiledStepObservation.CursorAccounting,
        ProfiledCost.ofSample, Nat.add_comm]
  | sampleUniform allowed destination next =>
      simp [executeProfiled, ProfiledStepObservation.CursorAccounting,
        ProfiledCost.ofSample, Nat.add_comm]

theorem profiledStep_cursorAccounting (program : ProfiledProgram profile)
    (source : profile.randomness.Source) (configuration : ProfiledConfiguration) :
    (profiledStep program source configuration).CursorAccounting configuration := by
  simp only [profiledStep]
  split
  · rfl
  · exact executeProfiled_cursorAccounting source _ configuration

/-- One source cursor is accounted for by the same trace that carries all other costs. -/
theorem ProfiledHaltingTrace.randomDraws_eq_cursorDifference
    (trace : ProfiledHaltingTrace program source initial final result cost steps draws) :
    cost.randomDraws + initial.randomCursor = draws := by
  induction trace with
  | @halt configuration memory result headCost draws observes =>
      have accounting := profiledStep_cursorAccounting program source configuration
      rw [observes] at accounting
      exact accounting
  | @next configuration nextConfiguration memory result headCost tailCost steps draws
      observes tail induction =>
      have headAccounting := profiledStep_cursorAccounting program source configuration
      rw [observes] at headAccounting
      change headCost.randomDraws + configuration.randomCursor =
        nextConfiguration.randomCursor at headAccounting
      change headCost.randomDraws + tailCost.randomDraws + configuration.randomCursor = draws
      omega

/-- Lift one arithmetic instruction along a proof of closed capability inclusion. -/
def ArithmeticInstruction.lift (embedding : source.Includes target) :
    ArithmeticInstruction source → ArithmeticInstruction target
  | .core instruction => .core instruction
  | .unary primitive allowed source destination next =>
      .unary primitive (embedding.unary primitive allowed) source destination next
  | .floorToNat allowed source destination next =>
      .floorToNat (embedding.floorToNat allowed) source destination next
  | .namedConstant constant allowed destination next =>
      .namedConstant constant (embedding.constant constant allowed) destination next

/-- Structural instruction embedding between closed machine profiles. -/
def ProfiledInstruction.lift (embedding : source.Embedding target) :
    ProfiledInstruction source → ProfiledInstruction target
  | .arithmetic instruction => .arithmetic (instruction.lift embedding.arithmetic)
  | .randBit allowed destination next =>
      .randBit (embedding.randomness.target_eq_fairBits allowed) destination next
  | .sampleUniform allowed destination next =>
      .sampleUniform (embedding.randomness.target_eq_uniformReal allowed) destination next

def ProfiledProgram.lift (embedding : source.Embedding target)
    (program : ProfiledProgram source) : ProfiledProgram target :=
  program.map (ProfiledInstruction.lift embedding)

@[simp]
theorem ProfiledProgram.lift_length (embedding : source.Embedding target)
    (program : ProfiledProgram source) :
    (program.lift embedding).length = program.length := by
  simp [ProfiledProgram.lift]

theorem ProfiledProgram.lift_valid (embedding : source.Embedding target)
    (program : ProfiledProgram source) (valid : ProfiledProgram.Valid program) :
    ProfiledProgram.Valid (program.lift embedding) := by
  intro (pc : Nat) instruction fetch successor member
  simp only [ProfiledProgram.lift, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨original, originalFetch, rfl⟩
  rw [ProfiledProgram.lift_length]
  apply valid pc original originalFetch successor
  cases original with
  | arithmetic instruction =>
      cases instruction <;>
        simpa [ProfiledInstruction.lift, ArithmeticInstruction.lift,
          ProfiledInstruction.successors, ArithmeticInstruction.successors] using member
  | randBit allowed destination next =>
      simpa [ProfiledInstruction.lift, ProfiledInstruction.successors] using member
  | sampleUniform allowed destination next =>
      simpa [ProfiledInstruction.lift, ProfiledInstruction.successors] using member

theorem ArithmeticInstruction.execute_lift
    (embedding : source.Includes target) (instruction : ArithmeticInstruction source)
    (configuration : Configuration) :
    executeArithmetic configuration (instruction.lift embedding) =
      executeArithmetic configuration instruction := by
  cases instruction <;> rfl

/-- Arithmetic strengthening with an unchanged source preserves one transition exactly. -/
theorem executeProfiled_liftArithmetic
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (instruction : ProfiledInstruction ⟨sourceArithmetic, randomness⟩)
    (source : RandomnessProfile.Source randomness)
    (configuration : ProfiledConfiguration) :
    executeProfiled source
        (instruction.lift (ClosedMachineProfile.Embedding.sameRandomness
          arithmetic randomness)) configuration =
      executeProfiled source instruction configuration := by
  cases instruction with
  | arithmetic instruction =>
      simp [ProfiledInstruction.lift, executeProfiled,
        ArithmeticInstruction.execute_lift]
  | randBit allowed destination next => rfl
  | sampleUniform allowed destination next => rfl

/-- Adding hidden randomness to deterministic code preserves one transition and source cursor. -/
theorem executeProfiled_liftDeterministic
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (instruction : ProfiledInstruction ⟨sourceArithmetic, .none⟩)
    (source : RandomnessProfile.Source targetRandomness)
    (configuration : ProfiledConfiguration) :
    executeProfiled source
        (instruction.lift (ClosedMachineProfile.Embedding.deterministicInto
          arithmetic targetRandomness)) configuration =
      executeProfiled (profile := ClosedMachineProfile.deterministic sourceArithmetic)
        () instruction configuration := by
  cases instruction with
  | arithmetic instruction =>
      simp [ProfiledInstruction.lift, executeProfiled,
        ArithmeticInstruction.execute_lift]
  | randBit allowed destination next => cases allowed
  | sampleUniform allowed destination next => cases allowed

theorem profiledStep_liftArithmetic
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (program : ProfiledProgram ⟨sourceArithmetic, randomness⟩)
    (source : RandomnessProfile.Source randomness)
    (configuration : ProfiledConfiguration) :
    profiledStep (program.lift (ClosedMachineProfile.Embedding.sameRandomness
        arithmetic randomness)) source configuration =
      profiledStep program source configuration := by
  simp only [profiledStep, ProfiledProgram.lift, List.getElem?_map]
  cases fetch : program[configuration.pc]? with
  | none => simp
  | some instruction => simp [executeProfiled_liftArithmetic]

theorem profiledStep_liftDeterministic
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (program : ProfiledProgram ⟨sourceArithmetic, .none⟩)
    (source : RandomnessProfile.Source targetRandomness)
    (configuration : ProfiledConfiguration) :
    profiledStep (program.lift (ClosedMachineProfile.Embedding.deterministicInto
        arithmetic targetRandomness))
        source configuration = profiledStep program () configuration := by
  simp only [profiledStep, ProfiledProgram.lift, List.getElem?_map]
  cases fetch : program[configuration.pc]? with
  | none => simp [fetch]
  | some instruction => simp [fetch, executeProfiled_liftDeterministic]

theorem ProfiledHaltingTrace.liftArithmetic
    {sourceArithmetic targetArithmetic : ArithmeticProfile}
    {randomness : RandomnessProfile}
    {program : ProfiledProgram ⟨sourceArithmetic, randomness⟩}
    {source : RandomnessProfile.Source randomness}
    {initial : ProfiledConfiguration} {final : Memory} {result : Real}
    {cost : ProfiledCost} {steps draws : Nat}
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (trace : ProfiledHaltingTrace program source initial final result cost steps draws) :
    ProfiledHaltingTrace (program.lift (ClosedMachineProfile.Embedding.sameRandomness
      arithmetic randomness)) source
      initial final result cost steps draws := by
  induction trace with
  | halt observes =>
      apply ProfiledHaltingTrace.halt
      rw [profiledStep_liftArithmetic, observes]
  | next observes tail induction =>
      apply ProfiledHaltingTrace.next
      · rw [profiledStep_liftArithmetic, observes]
      · exact induction

theorem ProfiledHaltingTrace.liftDeterministic
    {sourceArithmetic targetArithmetic : ArithmeticProfile}
    {targetRandomness : RandomnessProfile}
    {program : ProfiledProgram (ClosedMachineProfile.deterministic sourceArithmetic)}
    {initial : ProfiledConfiguration} {final : Memory} {result : Real}
    {cost : ProfiledCost} {steps draws : Nat}
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (targetSource : RandomnessProfile.Source targetRandomness)
    (trace : ProfiledHaltingTrace program () initial final result cost steps draws) :
    ProfiledHaltingTrace
      (program.lift (ClosedMachineProfile.Embedding.deterministicInto
        arithmetic targetRandomness)) targetSource
      initial final result cost steps draws := by
  induction trace with
  | halt observes =>
      apply ProfiledHaltingTrace.halt
      rw [profiledStep_liftDeterministic, observes]
  | next observes tail induction =>
      apply ProfiledHaltingTrace.next
      · rw [profiledStep_liftDeterministic, observes]
      · exact induction

end Algolean.Algorithms.StructuredRealRAM
