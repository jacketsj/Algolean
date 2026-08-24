/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.WordRAM
public meta import Algolean.Audit.WordRAM

/-!
# Certified Word-RAM preprocessing and rich-to-core lowering regression

The initializer writes one fixed library word, the derived operation consumes that shared word,
and the rich client calls initialization exactly once before invoking the derived operation.  The
initializer input is fixed by the library package, so the table cannot encode client-input advice.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMDerivedOperations

open Algolean Algorithms
open Algorithms.WordRAM

def tableBase : Region 8 := ⟨1⟩
def tableValue : BitVec 8 := 37

theorem word_writeAt_eq_write (region : Region 8) (value : BitVec 8) (memory : Memory 8) :
    WordLayout.word.writeAt region value memory = memory.write region.base value := by
  cases memory with
  | mk data addressRegisters =>
    simp only [WordLayout.writeAt, RAM.Memory.write]
    congr 1
    funext address
    simp only [WordLayout.footprintWords, WordLayout.encode, List.length_singleton]
    by_cases equal : address = region.base
    · subst address
      simp
    · have toNatNe : address.toNat ≠ region.base.toNat := by
        intro same
        apply equal
        exact BitVec.eq_of_toNat_eq same
      have outside : ¬(region.base.toNat ≤ address.toNat ∧
          address.toNat - region.base.toNat < 1) := by
        omega
      rw [if_neg outside]
      simp [equal]

theorem word_writeAt_eq_of_rep (region : Region 8) (value : BitVec 8) (memory : Memory 8)
    (represented : WordLayout.word.RepAt region value memory) :
    WordLayout.word.writeAt region value memory = memory := by
  rw [word_writeAt_eq_write]
  cases memory with
  | mk data addressRegisters =>
    simp only [RAM.Memory.write]
    congr 1
    funext address
    by_cases equal : address = region.base
    · subst address
      have stored := represented.2 0 (by simp [WordLayout.footprintWords, WordLayout.encode])
      simp only [WordLayout.footprintWords, WordLayout.encode, BitVec.toNat_ofNat,
        Nat.zero_mod, Nat.add_zero, List.getElem_zero] at stored
      simpa using stored.symm
    · simp [equal]

namespace Contracts

def initializeContract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := BitVec 8
  inputLayout := .unit
  outputLayout := .word
  pre _ := True
  post _ output := output = tableValue
  inputFits _ _ := by simp [WordLayout.Fits]
  outputFits _ _ _ _ := by simp [WordLayout.Fits]

def initializeBound : ProcedureBound initializeContract := fun _ ↦ 2

def useTable : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := BitVec 8
  Output := BitVec 8
  inputLayout := .word
  outputLayout := .word
  pre input := input = tableValue
  post input output := output = input
  inputFits _ _ := by simp [WordLayout.Fits]
  outputFits _ _ _ _ := by simp [WordLayout.Fits]

def useTableBound : ProcedureBound useTable := fun _ ↦ 1

inductive Operation where
  | init
  | useTable
deriving DecidableEq, Fintype, Repr

def signature : DependencySignature 8 where
  Op := Operation
  finiteOp := inferInstance
  decEqOp := inferInstance
  contract
    | .init => initializeContract
    | .useTable => useTable
  bound
    | .init => initializeBound
    | .useTable => useTableBound

end Contracts

namespace Implementations

open Contracts

def initializeProgram : Program 8 := [
  .set (.immediate tableValue) (.immediate tableBase.base) 1,
  .halt (.immediate 0)]

def initializeCertificate :
    RestoringProcedureCertificate initializeContract initializeBound where
  module := ⟨initializeProgram, 0⟩
  calling := {
    inputRegion := ⟨0⟩
    outputRegion := tableBase
    scratchOwned := fun _ ↦ False
    registerOwned := fun _ ↦ False }
  callingRealizes := by
    refine {
      inputFitsAt := ?_
      outputFitsAt := ?_
      inputOutputPolicy := ?_
      scratchDisjointOutput := ?_ }
    · intro input valid
      cases input
      change WordLayout.unit.FitsAt ⟨0⟩ ()
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode]
    · intro input output valid correct
      cases input
      subst output
      change WordLayout.word.FitsAt tableBase tableValue
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode, tableBase]
    · intro input output valid correct address
      cases input
      subst output
      change ¬(WordLayout.unit.Occupies ⟨0⟩ () address ∧
        WordLayout.word.Occupies tableBase tableValue address)
      simp [RepresentationsDisjoint, WordLayout.Occupies,
        WordLayout.footprintWords, WordLayout.encode]
    · simp
  valid := by
    constructor
    · intro pc instruction fetch target member
      rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
      have pcBelow' : pc < 2 := by simpa [initializeProgram] using pcBelow
      interval_cases pc
      · simp [initializeProgram, RAM.Instruction.successors] at member
        change target < 2
        omega
      · simp [initializeProgram, RAM.Instruction.successors] at member
    · simp [initializeProgram]
  output _ := tableValue
  outputCorrect _ _ := rfl
  correct input valid initial represented := by
    cases input
    let final := initial.write tableBase.base tableValue
    have setStep : stepCosted initializeProgram ⟨0, initial⟩ =
        ⟨.running ⟨1, final⟩, 1⟩ := by
      simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, initializeProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops, final, tableBase]
    have haltStep : stepCosted initializeProgram ⟨1, final⟩ =
        ⟨.halted final 0, 1⟩ := by
      simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, initializeProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops]
    let run : ProcedureRun ⟨initializeProgram, 0⟩ initial := {
      final := final
      result := 0
      cost := 2
      steps := 2
      trace := RAM.HaltingTrace.next setStep (RAM.HaltingTrace.halt haltStep) }
    refine ⟨run, ?_, le_rfl, ?_⟩
    · change WordLayout.word.RepAt tableBase tableValue final
      rw [show final = WordLayout.word.writeAt tableBase tableValue initial by
        symm; exact word_writeAt_eq_write _ _ _]
      exact WordLayout.writeAt_rep _ _ _ _ (by
        simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
          WordLayout.encode, tableBase])
    · constructor
      · intro address _ _ outsideOutput
        change final.data address = initial.data address
        have unequal : address ≠ tableBase.base := by
          intro equal
          apply outsideOutput
          refine ⟨0, ?_, ?_⟩
          · change 0 < WordLayout.word.footprintWords tableValue
            simp [WordLayout.footprintWords, WordLayout.encode]
          · simpa [equal, tableBase]
        simp [final, RAM.Memory.write, unequal]
      · intro register _
        rfl
  restoringCorrect input valid initial represented := by
    cases input
    let final := initial.write tableBase.base tableValue
    have setStep : stepCosted initializeProgram ⟨0, initial⟩ =
        ⟨.running ⟨1, final⟩, 1⟩ := by
      simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, initializeProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops, final, tableBase]
    have haltStep : stepCosted initializeProgram ⟨1, final⟩ =
        ⟨.halted final 0, 1⟩ := by
      simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, initializeProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops]
    let run : ProcedureRun ⟨initializeProgram, 0⟩ initial := {
      final := final
      result := 0
      cost := 2
      steps := 2
      trace := RAM.HaltingTrace.next setStep (RAM.HaltingTrace.halt haltStep) }
    refine ⟨run, ?_, le_rfl, ?_⟩
    · change WordLayout.word.RepAt tableBase tableValue final
      rw [show final = WordLayout.word.writeAt tableBase tableValue initial by
        symm; exact word_writeAt_eq_write _ _ _]
      exact WordLayout.writeAt_rep _ _ _ _ (by
        simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
          WordLayout.encode, tableBase])
    · symm
      exact word_writeAt_eq_write _ _ _

def useTableProgram : Program 8 := [.halt (.immediate 0)]

def useTableCertificate : RestoringProcedureCertificate useTable useTableBound where
  module := ⟨useTableProgram, 0⟩
  calling := {
    inputRegion := tableBase
    outputRegion := tableBase
    scratchOwned := fun _ ↦ False
    registerOwned := fun _ ↦ False
    aliasingPolicy := .inPlace }
  callingRealizes := by
    refine {
      inputFitsAt := ?_
      outputFitsAt := ?_
      inputOutputPolicy := ?_
      scratchDisjointOutput := ?_ }
    · intro input valid
      change WordLayout.word.FitsAt tableBase input
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode, tableBase]
    · intro input output valid correct
      change WordLayout.word.FitsAt tableBase output
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode, tableBase]
    · simp
    · simp
  valid := by
    constructor
    · intro pc instruction fetch target member
      rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
      have pcBelow' : pc < 1 := by simpa [useTableProgram] using pcBelow
      interval_cases pc
      simp [useTableProgram, RAM.Instruction.successors] at member
    · simp [useTableProgram]
  output input := input
  outputCorrect _ _ := rfl
  correct input valid initial represented := by
    let run : ProcedureRun ⟨useTableProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt (by
        simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
          RAM.CostedSemantics.unit, useTableProgram, RAM.execute,
          RAM.Operand.eval, WordRAM.ops]) }
    refine ⟨run, represented, le_rfl, ?_⟩
    exact ⟨fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  restoringCorrect input valid initial represented := by
    let run : ProcedureRun ⟨useTableProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt (by
        simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
          RAM.CostedSemantics.unit, useTableProgram, RAM.execute,
          RAM.Operand.eval, WordRAM.ops]) }
    exact ⟨run, represented, le_rfl, (word_writeAt_eq_of_rep _ _ _ represented).symm⟩

def environment : ImplementationEnvironment signature where
  implementation
    | .init => initializeCertificate
    | .useTable => useTableCertificate

def assumptions : DerivedOperationAssumptions 8 where
  widthRelation := "fixed width 8; the fixed table occupies one word"
  maximumRegisterValue := 255
  maximumAddress := 255
  spaceWords := 2
  polynomialIntegerWords := 1
  maximumRegisterValue_fits := by decide
  maximumAddress_fits := by decide
  space_fits := by decide

def library : PreprocessedWordOperationLibrary 8 where
  signature := signature
  initializationOp := .init
  initializationInput := ()
  initializationInputValid := trivial
  operationKind
    | .init => none
    | .useTable => some .bitAnd
  initialization_not_derived := rfl
  implementations := environment
  assumptions := assumptions
  tableRegion := tableBase
  tableWords := 1
  tableWords_le_space := by decide
  tableReadOnlyAfterInit op notInit input valid initial represented address inTable := by
    cases op with
    | init => contradiction
    | useTable =>
        change (WordLayout.word.writeAt tableBase input initial).data address =
          initial.data address
        rw [word_writeAt_eq_of_rep tableBase input initial represented]

end Implementations

namespace Client

open Contracts Implementations

def problem : StructuredProblem 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := BitVec 8
  inputLayout := .unit
  outputLayout := .word
  outputRegion := tableBase
  pre _ := True
  post _ output := output = tableValue
  inputFits _ _ := by
    simp [WordLayout.FitsInput, WordLayout.FitsAt, WordLayout.inputRegion,
      WordLayout.Fits, WordLayout.footprintWords, WordLayout.encode]

def program : OpenProgram signature := [
  .call .init ⟨0⟩ tableBase 1,
  .call .useTable tableBase tableBase 2,
  .core (.halt (.immediate 0))]

def relativeBound : problem.Input → Nat := fun _ ↦ 6
def linkedBound : problem.Input → Nat := fun _ ↦ 40

def relativeCertificate : RelativeAlgorithmCertificate signature problem relativeBound where
  program := program
  valid := by
    intro pc instruction fetch target member
    rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
    have pcBelow' : pc < 3 := by simpa [program] using pcBelow
    interval_cases pc
    · simp [program, OpenInstruction.successors] at member
      change target < 3
      omega
    · simp [program, OpenInstruction.successors] at member
      change target < 3
      omega
    · simp [program, OpenInstruction.successors, RAM.Instruction.successors] at member
  solvesAgainstContracts responder input validInput := by
    cases input
    let initial := problem.initialMemory () validInput
    have initialRep : WordLayout.unit.RepAt ⟨0⟩ () initial :=
      WordLayout.init_rep _ _ (problem.inputFits () validInput)
    have initCorrect := responder.correct Operation.init () trivial
    have initOutput : responder.answer Operation.init () = tableValue := initCorrect
    let afterInit := (signature.contract Operation.init).outputLayout.writeAt
      tableBase tableValue initial
    have initStep : OpenStep signature responder program ⟨0, initial⟩
        (.running ⟨1, afterInit⟩) 3 (some {
          callSite := 0
          op := .init
          input := ()
          output := responder.answer .init ()
          outputCorrect := responder.correct .init () trivial
          chargedCost := 3
          chargedCost_eq := rfl }) := by
      have raw := OpenStep.call (responder := responder) (program := program)
        (configuration := ⟨0, initial⟩) (op := Operation.init)
        (inputRegion := ⟨0⟩) (outputRegion := tableBase) (next := 1)
        (input := ()) (by rfl) initialRep trivial
      simpa [signature, initializeBound, initOutput, afterInit] using raw
    have tableRep : WordLayout.word.RepAt tableBase tableValue afterInit :=
      by
        change WordLayout.word.RepAt tableBase tableValue
          (WordLayout.word.writeAt tableBase tableValue initial)
        exact WordLayout.writeAt_rep _ _ _ _ (by
        simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
          WordLayout.encode, tableBase])
    have useCorrect := responder.correct Operation.useTable tableValue rfl
    have useOutput : responder.answer Operation.useTable tableValue = tableValue := useCorrect
    let afterUse := (signature.contract Operation.useTable).outputLayout.writeAt
      tableBase tableValue afterInit
    have useStep : OpenStep signature responder program ⟨1, afterInit⟩
        (.running ⟨2, afterUse⟩) 2 (some {
          callSite := 1
          op := .useTable
          input := tableValue
          output := responder.answer .useTable tableValue
          outputCorrect := responder.correct .useTable tableValue rfl
          chargedCost := 2
          chargedCost_eq := rfl }) := by
      have raw := OpenStep.call (responder := responder) (program := program)
        (configuration := ⟨1, afterInit⟩) (op := Operation.useTable)
        (inputRegion := tableBase) (outputRegion := tableBase) (next := 2)
        (input := tableValue) (by rfl) tableRep rfl
      simpa [signature, useTableBound, useOutput, afterUse] using raw
    have afterUseRep : WordLayout.word.RepAt tableBase tableValue afterUse := by
      change WordLayout.word.RepAt tableBase tableValue
        (WordLayout.word.writeAt tableBase tableValue afterInit)
      exact WordLayout.writeAt_rep _ _ _ _ tableRep.1
    have haltStep : OpenStep signature responder program ⟨2, afterUse⟩
        (.halted afterUse 0) 1 none := by
      exact OpenStep.core (instruction := .halt (.immediate 0))
        (by simp [program]) (by rfl)
    have trace : OpenHaltingTrace signature responder program ⟨0, initial⟩
        afterUse 0 6 [
          { callSite := 0, op := .init, input := (), output := responder.answer .init (),
            outputCorrect := responder.correct .init () trivial,
            chargedCost := 3, chargedCost_eq := rfl },
          { callSite := 1, op := .useTable, input := tableValue,
            output := responder.answer .useTable tableValue,
            outputCorrect := responder.correct .useTable tableValue rfl,
            chargedCost := 2, chargedCost_eq := rfl }] :=
      OpenHaltingTrace.next initStep
        (OpenHaltingTrace.next useStep (OpenHaltingTrace.halt haltStep))
    exact ⟨afterUse, 0, 6, _, tableValue, trace, afterUseRep, rfl, le_rfl⟩

def configuration : Linker.Configuration 8 where
  returnCell := 0
  jumpRegister := 7

theorem compatible : Linker.Compatibility program environment configuration := by
  refine {
    clientFits := by decide
    clientAvoidsReturnRegister := ?_
    inputRegion_eq := ?_
    outputRegion_eq := ?_ }
  · intro pc instruction fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by simpa [program] using pcBelow
    interval_cases pc <;> simp [program] at fetch
    subst instruction
    simp [Linker.instructionAvoids, Linker.operandAvoids]
  · intro pc op inputRegion outputRegion next fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by simpa [program] using pcBelow
    interval_cases pc <;> simp [program] at fetch
    · rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  · intro pc op inputRegion outputRegion next fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by simpa [program] using pcBelow
    interval_cases pc <;> simp [program] at fetch
    · rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl

theorem overheadBound (input : problem.Input) (validInput : problem.pre input)
    (final : Memory 8) (result : BitVec 8) (cost : Nat)
    (calls : List (DependencyCallRecord signature))
    (trace : OpenHaltingTrace signature environment.responder program
      ⟨0, problem.initialMemory input validInput⟩ final result cost calls)
    (relativeCost : cost ≤ relativeBound input) :
    cost + Linker.totalConcreteCallOverhead environment calls ≤ linkedBound input := by
  have callSiteBound : ∀ call ∈ calls, call.callSite + 2 ≤ 4 := by
    intro call member
    have site := trace.callSite_lt call member
    simp [program] at site
    omega
  have overheadAtMost : Linker.totalConcreteCallOverhead environment calls ≤
      4 * calls.length := by
    unfold Linker.totalConcreteCallOverhead
    have sumBound : ∀ (items : List (DependencyCallRecord signature)),
        (∀ call ∈ items, call.callSite + 2 ≤ 4) →
        (items.map (Linker.concreteCallOverhead environment)).sum ≤ 4 * items.length := by
      intro items itemBound
      induction items with
      | nil => simp
      | cons call rest ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have head : Linker.concreteCallOverhead environment call ≤ 4 := by
            rw [Linker.concreteCallOverhead]
            exact itemBound call (by simp)
          have tail := ih (fun item member ↦ itemBound item (by simp [member]))
          omega
    exact sumBound calls callSiteBound
  have countBound := trace.calls_length_le_cost
  simp [relativeBound, linkedBound] at relativeCost ⊢
  omega

noncomputable def concreteLink :
    relativeCertificate.ConcreteLink environment configuration
      (relativeBound := relativeBound) (linkedBound := linkedBound) where
  compatible := compatible
  overheadBound := overheadBound

theorem callShape (responder : AdmissibleResponder signature)
    (input : problem.Input) (validInput : problem.pre input)
    (final : Memory 8) (result : BitVec 8) (cost : Nat)
    (calls : List (DependencyCallRecord signature))
    (trace : OpenHaltingTrace signature responder program
      ⟨0, problem.initialMemory input validInput⟩ final result cost calls) :
    ∃ initCall useCall, calls = [initCall, useCall] ∧
      initCall.op = Operation.init ∧ useCall.op = Operation.useTable := by
  cases trace with
  | halt step =>
      cases step with
      | core fetch execute => simp [program] at fetch
  | next firstStep firstTail =>
      cases firstStep with
      | core fetch execute => simp [program] at fetch
      | call firstFetch firstRep firstValid =>
          simp [program] at firstFetch
          rcases firstFetch with ⟨rfl, rfl, rfl, rfl⟩
          cases firstTail with
          | halt secondStep =>
              cases secondStep with
              | core fetch execute => simp [program] at fetch
          | next secondStep secondTail =>
              cases secondStep with
              | core fetch execute => simp [program] at fetch
              | call secondFetch secondRep secondValid =>
                  simp [program] at secondFetch
                  rcases secondFetch with ⟨rfl, rfl, rfl, rfl⟩
                  cases secondTail with
                  | halt finalStep =>
                      cases finalStep with
                      | core fetch execute =>
                          simp [program] at fetch
                          cases fetch
                          exact ⟨_, _, rfl, rfl, rfl⟩
                  | next finalStep tail =>
                      cases finalStep with
                      | core fetch execute =>
                          simp [program] at fetch
                          cases fetch
                          simp [RAM.execute] at execute
                      | call fetch inputRep valid =>
                          simp [program] at fetch

noncomputable def richCertificate :
    RichWordAlgorithmCertificate library problem relativeBound linkedBound where
  client := relativeCertificate
  linkerConfiguration := configuration
  link := concreteLink
  preprocessingRunsOnce responder input validInput final result cost calls trace := by
    rcases callShape responder input validInput final result cost calls trace with
      ⟨initCall, useCall, rfl, initOp, useOp⟩
    change dependencyCallCount Operation.init [initCall, useCall] = 1
    simp [dependencyCallCount, initOp, useOp]
  preprocessingInputFixed responder input validInput final result cost calls trace call member
      operation := by
    change call.op = Operation.init at operation
    cases call with
    | mk callSite op callInput output outputCorrect chargedCost chargedCost_eq =>
        dsimp at operation ⊢
        subst op
        cases callInput
        rfl
  usesDerivedOperation := by
    refine ⟨Operation.useTable, by simp [library], ?_⟩
    intro responder input validInput final result cost calls trace
    rcases callShape responder input validInput final result cost calls trace with
      ⟨initCall, useCall, rfl, initOp, useOp⟩
    change 0 < dependencyCallCount Operation.useTable [initCall, useCall]
    unfold dependencyCallCount
    by_cases initAlso : initCall.op = Operation.useTable
    · simp [initAlso, useOp]
    · simp [initAlso, useOp]

noncomputable def loweredCertificate : FixedWidthAlgorithmCertificateBy problem linkedBound :=
  richCertificate.lowerToCore

theorem loweredExists : problem.HasAlgorithmBy linkedBound :=
  richCertificate.hasCoreAlgorithm

theorem preprocessingBodyOnce :
    (Linker.implementationBody program environment configuration Operation.init).length =
      initializeProgram.length :=
  richCertificate.preprocessingBody_materialized_once

theorem loweredBoundIncludesInitialization : relativeBound () < linkedBound () := by decide

#print axioms loweredExists

end Client

end AlgoleanTests.WordRAMDerivedOperations
