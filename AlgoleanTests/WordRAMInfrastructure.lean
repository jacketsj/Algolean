/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.WordRAM
public meta import Algolean.Audit.WordRAM
public import Algolean.Complexity.WordRAMRelative
public import Algolean.Complexity.WordRAMLinking
public import Algolean.Complexity.WordRAMRandomized
public import Algolean.Complexity.WordRAMRandomizedRelative
public import Algolean.Complexity.WordRAMUniformProcedure
public import Algolean.Complexity.WordRAMUniformLinking
public import Algolean.Models.WordRAM.TypedRegion
public import Algolean.Models.WordRAM.Derive

/-! # Regression tests for closed structured Word-RAM claims -/

@[expose] public section

namespace AlgoleanTests.WordRAMInfrastructure

open Algolean Algorithms
open Algorithms.WordRAM

wordram_payload UserPayload : (BitVec 8 × Array Bool) where payload =>
  payload.2.size < 2 ^ 8

#synth CanonicalLayout 8 UserPayload

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 Nat

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 Int

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 Rat

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 Real

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check WordLayout.custom

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check WordLayout.viaEquiv

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check CanonicalLayout.ofEquiv

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth FixedFootprint 8 (WordArray 8 Bool)

inductive MerelyFinite where
  | first | second
deriving Fintype, DecidableEq

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 MerelyFinite

/-
error: failed to synthesize
-/
#guard_msgs (error, substring := true) in
#synth CanonicalLayout 8 (SimpleGraph (Fin 4))

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check RandomBit.randomBitCount

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check RandomBit.Instruction.callProcedure

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check UniformProgram.ofWidthFamily

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check UniformLinkWitness.ofWidthFamily

example (value : Bool) :
    (WordLayout.bool (w := 8)).decode ((WordLayout.bool (w := 8)).encode value) = some value := by
  apply WordLayout.decode_encode
  · decide
  · trivial

example (value : BitVec 8 × Option Bool) :
    (WordLayout.prod WordLayout.word (WordLayout.option WordLayout.bool)).decode
      ((WordLayout.prod WordLayout.word (WordLayout.option WordLayout.bool)).encode value) =
        some value := by
  apply WordLayout.decode_encode
  · decide
  · rcases value with ⟨word, value⟩
    cases value <;> simp [WordLayout.Fits, WordLayout.encode]

example (value : Bool) (fits : (WordLayout.bool (w := 8)).FitsInput value) :
    (WordLayout.bool (w := 8)).RepAt (WordLayout.inputRegion 8) value
      ((WordLayout.bool (w := 8)).init value fits) :=
  WordLayout.init_rep _ _ fits

/-- A length-bearing array occupying the whole address space is rejected before initialization. -/
example : ¬ (WordLayout.array (WordLayout.bool (w := 8))).Fits
    (Array.replicate 256 false) := by
  norm_num [WordLayout.Fits, WordLayout.encode, WordLayout.encodeList]

/-- Standard output representations are functional even when footprints depend on values. -/
example (memory : Memory 8) (region : Region 8) (left right : List Bool)
    (leftRep : (WordLayout.list WordLayout.bool).RepAt region left memory)
    (rightRep : (WordLayout.list WordLayout.bool).RepAt region right memory) : left = right :=
  WordLayout.RepAt.functional _ (by decide) region leftRep rightRep

/-- Program-family size sees the full word literal rather than only one instruction node. -/
example : WordRAM.descriptionSize
    ([.halt (.immediate (255 : BitVec 8))] : Algorithms.WordRAM.Program 8) > 1 := by
  decide

/-- Width-uniform template size charges the binary length of source literals. -/
example : ProgramTemplate.descriptionSize
    ([.halt (.immediate (2 ^ 100))] : ProgramTemplate) > 100 := by
  decide

/-- Modular word addition is not silently identified with mathematical natural addition. -/
example : ((255 : BitVec 8) + 1).toNat = 0 ∧ 255 + 1 ≠ ((255 : BitVec 8) + 1).toNat := by
  decide

/-- Fixed indexing compiles to an explicit, exactly charged first-order address plan. -/
example :
    ((AddressPlan.fixedIndex (w := 8) 4 1 3 0).compile 1 10 20).length = 2 := by
  decide

/-- The semantic address is exact only under an explicit no-wrap obligation. -/
example (memory : Memory 8)
    (fits : (AddressPlan.fixedIndex (w := 8) 4 1 3 0).NoWrap memory) :
    ((AddressPlan.fixedIndex (w := 8) 4 1 3 0).eval memory).toNat =
      (AddressPlan.fixedIndex (w := 8) 4 1 3 0).evalNat memory :=
  AddressPlan.eval_toNat_eq _ _ fits

#check AddressPlan.fixedIndex_trace
#check indirectLookup_trace

namespace AdversarialProcedureABI

def contract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := Bool
  Output := Bool
  inputLayout := .bool
  outputLayout := .bool
  pre _ := True
  post _ _ := True
  inputFits _ _ := trivial
  outputFits _ _ _ _ := trivial

def overlapping : CallingConvention 8 where
  inputRegion := ⟨0⟩
  outputRegion := ⟨0⟩
  scratchOwned _ := False
  registerOwned _ := False
  callOverhead := 0
  aliasingPolicy := .disjoint

/-- An impossible disjoint ABI is rejected before any code-correctness proof can begin. -/
theorem not_realizable : ¬ overlapping.Realizes contract := by
  intro realizes
  have disjoint := realizes.inputOutputPolicy false false trivial trivial
  change RepresentationsDisjoint WordLayout.bool (⟨0⟩ : Region 8) false
    WordLayout.bool ⟨0⟩ false at disjoint
  have inputOccupies : WordLayout.bool.Occupies (⟨0⟩ : Region 8) false
      (0 : BitVec 8) := by
    exact ⟨0, by simp [WordLayout.footprintWords, WordLayout.encode], by simp⟩
  have outputOccupies : WordLayout.bool.Occupies (⟨0⟩ : Region 8) false
      (0 : BitVec 8) := by
    exact ⟨0, by simp [WordLayout.footprintWords, WordLayout.encode], by simp⟩
  exact disjoint 0 ⟨inputOccupies, outputOccupies⟩

end AdversarialProcedureABI

namespace ActualOutputFrame

def contract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := Option Bool
  inputLayout := .unit
  outputLayout := .option .bool
  pre _ := True
  post _ _ := True
  inputFits _ _ := trivial
  outputFits _ output _ _ := by
    cases output with
    | none => trivial
    | some value =>
        change True ∧ (WordLayout.bool.encode value).length + 1 ≤ 2 ^ 8
        constructor
        · trivial
        · cases value <;> simp [WordLayout.encode]

def calling : CallingConvention 8 where
  inputRegion := ⟨10⟩
  outputRegion := ⟨0⟩
  scratchOwned _ := False
  registerOwned _ := False
  callOverhead := 0

def before : Memory 8 := ⟨fun _ ↦ 0, fun _ ↦ 0⟩

def after : Memory 8 :=
  ⟨fun address ↦ if address = 1 then 1 else 0, fun _ ↦ 0⟩

/-- The larger actual output footprint exempts its second payload word. -/
example : PreservesFrame contract calling () (some true) before after := by
  constructor
  · intro address inputFree scratchFree outputFree
    by_cases atOne : address = (1 : BitVec 8)
    · subst address
      change ¬ (WordLayout.option WordLayout.bool).Occupies (⟨0⟩ : Region 8)
        (some true) (1 : BitVec 8) at outputFree
      apply (outputFree ?_).elim
      simp only [WordLayout.Occupies, WordLayout.footprintWords, WordLayout.encode]
      exact ⟨1, by decide, by decide⟩
    · change (if address = (1 : BitVec 8) then 1 else 0) = 0
      rw [if_neg atOne]
  · intros
    rfl

/-- The same change is outside the smaller `none` footprint and must be preserved. -/
example : ¬ PreservesFrame contract calling () none before after := by
  intro frame
  have preserved := frame.1 (1 : BitVec 8) (by
    simp [contract, WordLayout.Occupies, WordLayout.footprintWords, WordLayout.encode])
    (by simp [calling]) (by
      simp [contract, calling, WordLayout.Occupies, WordLayout.footprintWords,
        WordLayout.encode])
  simp [before, after] at preserved

def scratchCalling : CallingConvention 8 where
  inputRegion := ⟨10⟩
  outputRegion := ⟨20⟩
  scratchOwned address := address = 1
  registerOwned _ := False
  callOverhead := 0

def unitContract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  pre _ := True
  post _ _ := True
  inputFits _ _ := trivial
  outputFits _ _ _ _ := trivial

/-- A general frame permits declared scratch changes. -/
example : PreservesFrame
    unitContract scratchCalling () () before after := by
  constructor
  · intro address inputFree scratchFree outputFree
    by_cases atOne : address = (1 : BitVec 8)
    · subst address
      exact (scratchFree rfl).elim
    · change (if address = (1 : BitVec 8) then 1 else 0) = 0
      rw [if_neg atOne]
  · intros
    rfl

/-- A restoring guarantee would reject that residual scratch change. -/
example : after ≠ WordLayout.unit.writeAt ⟨20⟩ () before := by
  intro equal
  have atOne := congrArg (fun memory : Memory 8 ↦ memory.data 1) equal
  simp [after, before, WordLayout.writeAt, WordLayout.footprintWords,
    WordLayout.encode] at atOne

end ActualOutputFrame

def malformedOffsets : WordArray 8 (BitVec 8) × WordArray 8 Bool :=
  (WordArray.mk #[0, 2] (by decide), WordArray.mk #[true] (by decide))

/-- Offset tables must equal actual successive element boundaries, not merely be monotone. -/
example : ¬ IndexedArray.Valid (w := 8) (fun _ : Bool ↦ 1) malformedOffsets := by
  intro valid
  have boundary := valid.2.2.1 0 (by
    change 0 < 1
    decide)
  change (2 : BitVec 8).toNat = (0 : BitVec 8).toNat + 1 at boundary
  have two : (2 : BitVec 8).toNat = 2 := by decide
  have zero : (0 : BitVec 8).toNat = 0 := by decide
  omega

#layout_audit WordRAM 8 (BitVec 8 × Option Bool)

namespace FixedCertificate

def problem : StructuredProblem 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := ⟨0⟩
  pre _ := True
  post _ _ := True
  inputFits _ _ := by simp [WordLayout.FitsInput, WordLayout.FitsAt, WordLayout.inputRegion,
    WordLayout.Fits, WordLayout.footprintWords, WordLayout.encode]

def program : Algorithms.WordRAM.Program 8 := [.halt (.immediate 0)]

def certificate : FixedWidthAlgorithmCertificateBy problem (fun _ => 1) where
  program := program
  valid := by
    intro pc instruction fetch target successor
    cases pc with
    | zero =>
        simp [program] at fetch
        subst instruction
        simp [RAM.Instruction.successors] at successor
    | succ pc => simp [program] at fetch
  solves input validInput := by
    refine ⟨{
      final := problem.initialMemory input validInput
      result := 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt ?_
    }, (), ?_, trivial, le_rfl⟩
    · simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, program, RAM.execute, RAM.Operand.eval, WordRAM.ops]
    · change WordLayout.unit.RepAt ⟨0⟩ () _
      refine ⟨?_, ?_⟩
      · refine ⟨trivial, ?_⟩
        simp only [WordLayout.footprintWords, WordLayout.encode, List.length_nil, Nat.add_zero]
        exact Nat.le_of_lt (BitVec.toNat_lt_twoPow_of_le (x := (0 : BitVec 8)) le_rfl)
      · intro index inRange
        simp [WordLayout.footprintWords, WordLayout.encode] at inRange

theorem exists_algorithm : problem.HasAlgorithmBy (fun _ => 1) := ⟨certificate⟩

def publication : Algorithms.WordRAM.Audit.FixedWidthPublication problem (fun _ => 1) where
  certificate := certificate
  certificateName := `certificate
  problemName := `problem
  boundName := `Nat.succ
  correctnessTheorem := `exists_algorithm

#algorithm_audit publication

end FixedCertificate

/- Relative certificates have no unconditional coercion. -/
/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check RelativeAlgorithmCertificate.toFixedWidthAlgorithmCertificate

#check Linker.link
#check Linker.link_length
#check Linker.sharedBody_count
#check Linker.link_valid
#check Linker.link_descriptionSize
#check CertifiedAccessor._cost
#check CertifiedAccessor._correct
#check CertifiedAccessor._preservesFrame
#check RandomizedConcreteLink.certificate
#check RandomizedConcreteLink.hasAlgorithm

#print axioms Linker.link_valid
#print axioms Linker.refine_trace

/-- Once implementations exist, existential discharge is one theorem application. -/
noncomputable example
    (client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound)
    (implementations : Nonempty (ImplementationEnvironment signature)) :
    problem.HasAlgorithmBy linkedBound :=
  client.hasAlgorithm implementations

/-- The concrete version exposes the actual linked finite core program. -/
noncomputable example
    (client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound)
    (implementations : ImplementationEnvironment signature) :
    FixedWidthAlgorithmCertificateBy problem linkedBound :=
  client.link implementations

end AlgoleanTests.WordRAMInfrastructure
