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
    ((AddressPlan.fixedIndex (w := 8) 4 1 3 0).compile 1 10 20).length = 5 := by
  decide

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
