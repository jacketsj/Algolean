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
public import Algolean.Models.WordRAM.Data.IndexedArray
public import Algolean.Models.WordRAM.Data.Physical
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

/-
error: Application type mismatch
-/
#guard_msgs (error, substring := true) in
#check IndexedArrayWithLayout (w := 8) (fun value : Bool ↦ if value then 1 else 2)

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
#check AddressPlan.fixedIndex_trace_exact
#check indirectLookup_trace
#check ProdRef.sndFixed_rep
#check ArrayRef.getFixed_rep
#check ArrayRef.getFixed_runtime_trace_rep
#check MatrixRef.getFixed_rep_of_encoding
#check MatrixRef.getFixed_runtime_trace_rep_of_encoding
#check ParametricProcedureCertificate.forConvention

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

def finalAddressContract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := BitVec 8 × BitVec 8
  Output := Unit
  inputLayout := .prod .word .word
  outputLayout := .unit
  pre _ := True
  post _ _ := True
  inputFits _ _ := by
    simp [WordLayout.Fits, WordLayout.footprintWords, WordLayout.encode]
  outputFits _ _ _ _ := trivial

def finalAddressConvention : CallingConvention 8 where
  inputRegion := ⟨255⟩
  outputRegion := ⟨0⟩
  scratchOwned _ := False
  registerOwned _ := False
  aliasingPolicy := .inPlace

/-- A two-word value cannot start in the final addressable word without wrapping. -/
theorem multiword_at_final_address_not_realizable :
    ¬ finalAddressConvention.Realizes finalAddressContract := by
  intro realizes
  have fits := realizes.inputFitsAt ((0 : BitVec 8), (0 : BitVec 8)) trivial
  have addressFit := fits.2
  dsimp [finalAddressConvention, finalAddressContract] at addressFit
  norm_num [WordLayout.footprintWords, WordLayout.encode] at addressFit

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
example : ¬ IndexedArray.Valid (WordLayout.bool (w := 8)) malformedOffsets := by
  intro valid
  have boundary := valid.2.2.1 0 (by
    change 0 < 1
    decide)
  have left : (malformedOffsets.1.data.getD 1 0).toNat = 2 := by decide
  have right : (malformedOffsets.1.data.getD 0 0).toNat = 0 := by decide
  rw [left, right] at boundary
  norm_num [WordLayout.footprintWords, WordLayout.encode] at boundary

namespace CanonicalIndexedLookup

def elementLayout : WordLayout 8 (List Bool) := .list .bool

def payload : WordArray 8 (BitVec 8) × WordArray 8 (List Bool) :=
  (WordArray.mk #[0, 1, 4] (by decide),
    WordArray.mk #[[], [false, true]] (by decide))

def valid : IndexedArray.Valid elementLayout payload := by
  refine ⟨by decide, by decide, ?_, by native_decide, by decide⟩
  intro index inRange
  have : index = 0 ∨ index = 1 := by
    change index < 2 at inRange
    omega
  rcases this with rfl | rfl <;>
    native_decide

def value : IndexedArrayWithLayout elementLayout := Tagged.mk ⟨payload, valid⟩

def fits : (indexedArrayLayout elementLayout).FitsInput value := by
  simp [WordLayout.FitsInput, WordLayout.FitsAt, indexedArrayLayout, wordArrayLayout,
    value, payload, elementLayout, WordLayout.Fits, WordLayout.footprintWords,
    WordLayout.encode, WordLayout.encodeList]
  native_decide

def initial : Memory 8 :=
  ((indexedArrayLayout elementLayout).init value fits).writeAddress 0 1

def reference : IndexedArrayRef 8 (List Bool) := ⟨elementLayout, 0⟩

/-- Runtime lookup reads the canonical cached boundary for a variable-footprint element. -/
example :
    ∃ final,
      RAM.HaltingTrace (stepCosted (reference.getProgram 0 1 2 3 4 5))
        ⟨0, initial⟩ final 0 7 7 ∧
      final.data = initial.data ∧
      final.address 5 = (reference.elementRegion payload 1).base := by
  apply reference.getProgram_trace_canonical payload valid initial 1 0 1 2 3 4 5
  · simp [initial, RAM.Memory.writeAddress]
  · decide
  · decide
  · change (indexedArrayLayout elementLayout).RepAt (WordLayout.inputRegion 8) value initial
    have represented := (indexedArrayLayout elementLayout).init_rep value fits
    refine ⟨represented.1, ?_⟩
    intro offset inRange
    simpa [initial, RAM.Memory.writeAddress] using represented.2 offset inRange

end CanonicalIndexedLookup

namespace ExactGraphRepresentation

def payload : BitVec 8 × BitVec 8 × WordArray 8 (BitVec 8) ×
    WordArray 8 (BitVec 8) × WordArray 8 Unit :=
  (2, 1, WordArray.mk #[0] (by decide), WordArray.mk #[1] (by decide),
    WordArray.mk #[()] (by decide))

def valid : DirectedEdgeList.Valid payload := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro endpoint member
  change endpoint ∈ #[0#8] ++ #[1#8] at member
  simp at member
  rcases member with rfl | rfl <;> decide

def graph : DirectedEdgeList 8 Unit := Tagged.mk ⟨payload, valid⟩

def storedEdge (tail head : Nat) (_ : Unit) : Prop := tail = 0 ∧ head = 1

def intendedAdjacency (tail head : Nat) : Prop :=
  (tail = 0 ∧ head = 1) ∨ (tail = 1 ∧ head = 0)

/-- One-sided stored-edge validation does not establish completeness. -/
theorem everyStoredEdge : DirectedEdgeList.EveryStoredEdgeSatisfies graph storedEdge := by
  intro index below
  have edgeCount : graph.edgeCount.toNat = 1 := by native_decide
  have indexZero : index = 0 := by
    rw [edgeCount] at below
    omega
  subst index
  have tailZero : (graph.tail.data.getD 0 0).toNat = 0 := by native_decide
  have headOne : (graph.head.data.getD 0 0).toNat = 1 := by native_decide
  refine ⟨(), ?_, ?_⟩
  · native_decide
  · rw [tailZero, headOne]
    exact ⟨rfl, rfl⟩

/-- The omitted reverse edge witnesses failure of exact representation. -/
theorem notExact : ¬ DirectedEdgeList.RepresentsExactly graph intendedAdjacency := by
  intro exactRepresentation
  rcases exactRepresentation.2 1 0 (by right; exact ⟨rfl, rfl⟩) with
    ⟨index, below, tail, head⟩
  have edgeCount : graph.edgeCount.toNat = 1 := by native_decide
  have indexZero : index = 0 := by
    rw [edgeCount] at below
    omega
  subst index
  have tailZero : (graph.tail.data.getD 0 0).toNat = 0 := by native_decide
  rw [tailZero] at tail
  norm_num at tail

end ExactGraphRepresentation

/- No preferred instruction can package a host-language word operation as one step. -/
/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check ExtraInstruction.arbitraryWordOperation

#check RunningSegment.trans
#check RunningSegment.thenHalting
#check AddressPlan.fixedIndex_segment
#check PreprocessedWordOperationLibrary.preprocessing
#check RichWordAlgorithmCertificate.lowerToCore
#check RichWordAlgorithmCertificate.preprocessingBody_materialized_once
#check StructuredProblem.HighProbabilityBoundedSuccessCertificate
#check StructuredProblem.BoundedTimeMonteCarloCertificate
#check StructuredProblem.OneSidedBoundedTimeMonteCarloCertificate
#check StructuredProblem.LasVegasExpectedTimeCertificate
#check StructuredProblem.LasVegasHighProbabilityTimeCertificate
#check StructuredProblem.AlmostSureLasVegasCertificate
#check StructuredProblem.ExpectedApproximationCertificate
#check StructuredProblem.SamplerCertificate
#check StructuredProblem.finite_output_support_of_prefix_factor

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
#check CertifiedAccessor._lowering
#check CertifiedAccessor._preservesFrame
#check RandomizedConcreteLink.certificate
#check RandomizedConcreteLink.hasAlgorithm
#check RandomLinker.refine_trace
#check RandomLinker.certificate
#check RandomLinker.hasAlgorithm

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
