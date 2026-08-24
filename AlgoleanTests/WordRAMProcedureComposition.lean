/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.WordRAM
public meta import Algolean.Audit.WordRAM

/-!
# Four-module Word-RAM dependency integration regression

The client is proved once against a typed procedure contract.  The later integration theorem
uses the concrete dependency certificate and the generic same-trace linker; it does not repeat
the client correctness proof.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMProcedureComposition

open Algolean Algorithms
open Algorithms.WordRAM

namespace ContractModule

def dependencyContract : ProcedureContract 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  pre _ := True
  post _ _ := True
  inputFits _ _ := by simp [WordLayout.Fits]
  outputFits _ _ _ _ := by simp [WordLayout.Fits]

def dependencyBound : ProcedureBound dependencyContract := fun _ ↦ 1

def signature : DependencySignature 8 where
  Op := Unit
  finiteOp := inferInstance
  decEqOp := inferInstance
  contract _ := dependencyContract
  bound _ := dependencyBound

end ContractModule

namespace RelativeClientModule

open ContractModule

def clientProblem : StructuredProblem 8 where
  widthAtLeastTwo := by decide
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := ⟨0⟩
  pre _ := True
  post _ _ := True
  inputFits _ _ := by
    simp [WordLayout.FitsInput, WordLayout.FitsAt, WordLayout.inputRegion,
      WordLayout.Fits, WordLayout.footprintWords, WordLayout.encode]

def clientProgram : OpenProgram signature :=
  [.call () ⟨0⟩ ⟨0⟩ 1, .core (.halt (.immediate 0))]

def relativeBound : clientProblem.Input → Nat := fun _ ↦ 3
def linkedBound : clientProblem.Input → Nat := fun _ ↦ 12

theorem unitWriteAt (region : Region 8) (memory : Memory 8) :
    WordLayout.unit.writeAt region () memory = memory := by
  cases memory
  simp [WordLayout.writeAt, WordLayout.footprintWords, WordLayout.encode]

def clientRelativeCertificate :
    RelativeAlgorithmCertificate signature clientProblem relativeBound where
  program := clientProgram
  valid := by
    intro pc instruction fetch target member
    rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · change target < 2
      simp [clientProgram, OpenInstruction.successors] at member
      omega
    · simp [clientProgram, OpenInstruction.successors, RAM.Instruction.successors] at member
  solvesAgainstContracts responder input validInput := by
    cases input
    let initial := clientProblem.initialMemory () validInput
    let after := WordLayout.unit.writeAt ⟨0⟩ (responder.answer () ()) initial
    have inputRep : WordLayout.unit.RepAt ⟨0⟩ () initial := by
      exact WordLayout.init_rep _ _ (clientProblem.inputFits () validInput)
    have callStep : OpenStep signature responder clientProgram ⟨0, initial⟩
        (.running ⟨1, after⟩) 2 (some {
          callSite := 0
          op := ()
          input := ()
          output := responder.answer () ()
          outputCorrect := responder.correct () () trivial
          chargedCost := 2
          chargedCost_eq := rfl }) := by
      exact OpenStep.call (by simp [clientProgram]) inputRep trivial
    have haltStep : OpenStep signature responder clientProgram ⟨1, after⟩
        (.halted after 0) 1 none := by
      exact OpenStep.core (instruction := .halt (.immediate 0))
        (by simp [clientProgram]) (by rfl)
    have trace : OpenHaltingTrace signature responder clientProgram
        ⟨0, initial⟩ after 0 3 [{
          callSite := 0
          op := ()
          input := ()
          output := responder.answer () ()
          outputCorrect := responder.correct () () trivial
          chargedCost := 2
          chargedCost_eq := rfl }] :=
      OpenHaltingTrace.next callStep (OpenHaltingTrace.halt haltStep)
    refine ⟨after, 0, 3, _, (), trace, ?_, trivial, le_rfl⟩
    exact WordLayout.writeAt_rep _ _ _ _ (by
      change WordLayout.unit.FitsAt ⟨0⟩ ()
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode])

end RelativeClientModule

namespace DependencyImplementationModule

open ContractModule

def dependencyProgram : Program 8 := [.halt (.immediate 0)]

def dependencyProcedureCertificate :
    RestoringProcedureCertificate dependencyContract dependencyBound where
  module := ⟨dependencyProgram, 0⟩
  calling := {
    inputRegion := ⟨0⟩
    outputRegion := ⟨0⟩
    scratchOwned := fun _ ↦ False
    registerOwned := fun _ ↦ False }
  callingRealizes := by
    refine {
      inputFitsAt := ?_
      outputFitsAt := ?_
      inputOutputPolicy := ?_
      scratchDisjointOutput := ?_ }
    · intro input validInput
      cases input
      change WordLayout.unit.FitsAt ⟨0⟩ ()
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode]
    · intro input output validInput correct
      cases input
      cases output
      change WordLayout.unit.FitsAt ⟨0⟩ ()
      simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
        WordLayout.encode]
    · intro input output validInput correct
      cases input
      cases output
      change RepresentationsDisjoint WordLayout.unit ⟨0⟩ ()
        WordLayout.unit ⟨0⟩ ()
      simp [RepresentationsDisjoint, WordLayout.Occupies,
        WordLayout.footprintWords, WordLayout.encode]
    · intro input output validInput correct address occupied
      simp
  valid := by
    constructor
    · intro pc instruction fetch target member
      rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
      have pcBelow' : pc < 1 := by simpa [dependencyProgram] using pcBelow
      interval_cases pc
      simp [dependencyProgram, RAM.Instruction.successors] at member
    · simp [dependencyProgram]
  output _ := ()
  outputCorrect _ _ := trivial
  correct input validInput initial represented := by
    cases input
    let run : ProcedureRun ⟨dependencyProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt (by
        simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
          RAM.CostedSemantics.unit, dependencyProgram, RAM.execute,
          RAM.Operand.eval, WordRAM.ops]) }
    refine ⟨run, represented, le_rfl, ?_⟩
    constructor
    · intro address _ _ _
      rfl
    · intro register _
      rfl
  restoringCorrect input validInput initial represented := by
    cases input
    let run : ProcedureRun ⟨dependencyProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := 1
      steps := 1
      trace := RAM.HaltingTrace.halt (by
        simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
          RAM.CostedSemantics.unit, dependencyProgram, RAM.execute,
          RAM.Operand.eval, WordRAM.ops]) }
    exact ⟨run, represented, le_rfl, (RelativeClientModule.unitWriteAt _ _).symm⟩

theorem dependency_exists : HasProcedure dependencyContract dependencyBound :=
  ⟨dependencyProcedureCertificate.toProcedureCertificate⟩

def implementations : ImplementationEnvironment signature where
  implementation _ := dependencyProcedureCertificate

end DependencyImplementationModule

namespace IntegrationModule

open ContractModule RelativeClientModule DependencyImplementationModule

def linkerConfiguration : Linker.Configuration 8 where
  returnCell := 0
  jumpRegister := 7

def compatibility :
    Linker.Compatibility clientProgram implementations linkerConfiguration := by
    refine {
      clientFits := by decide
      clientAvoidsReturnRegister := ?_
      inputRegion_eq := ?_
      outputRegion_eq := ?_ }
    · intro pc instruction fetch
      have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
      have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
      interval_cases pc <;> simp [clientProgram] at fetch
      subst instruction
      simp [Linker.instructionAvoids, Linker.operandAvoids]
    · intro pc op inputRegion outputRegion next fetch
      change Unit at op
      cases op
      have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
      have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
      interval_cases pc
      · change some (OpenInstruction.call (signature := signature) () ⟨0⟩ ⟨0⟩ 1) =
          some (OpenInstruction.call (signature := signature) ()
            inputRegion outputRegion next) at fetch
        cases fetch
        rfl
      · simp [clientProgram] at fetch
    · intro pc op inputRegion outputRegion next fetch
      change Unit at op
      cases op
      have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
      have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
      interval_cases pc
      · change some (OpenInstruction.call (signature := signature) () ⟨0⟩ ⟨0⟩ 1) =
          some (OpenInstruction.call (signature := signature) ()
            inputRegion outputRegion next) at fetch
        cases fetch
        rfl
      · simp [clientProgram] at fetch

theorem overheadBound (input : clientProblem.Input) (validInput : clientProblem.pre input)
    (final : Memory 8) (result : BitVec 8) (cost : Nat)
    (calls : List (DependencyCallRecord signature))
    (trace : OpenHaltingTrace signature implementations.responder clientProgram
      ⟨0, clientProblem.initialMemory input validInput⟩ final result cost calls)
    (relativeCost : cost ≤ relativeBound input) :
    cost + Linker.totalConcreteCallOverhead implementations calls ≤ linkedBound input := by
  have callSiteBound : ∀ call ∈ calls, call.callSite + 2 ≤ 3 := by
    intro call member
    have site := trace.callSite_lt call member
    simp [clientProgram] at site
    omega
  have overheadAtMost : Linker.totalConcreteCallOverhead implementations calls ≤
      3 * calls.length := by
    unfold Linker.totalConcreteCallOverhead
    have sumBound : ∀ (items : List (DependencyCallRecord signature)),
        (∀ call ∈ items, call.callSite + 2 ≤ 3) →
        (items.map (Linker.concreteCallOverhead implementations)).sum ≤
          3 * items.length := by
      intro items itemBound
      induction items with
      | nil => simp
      | cons call rest ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have head := itemBound call (by simp)
          have tail := ih (fun item member ↦ itemBound item (by simp [member]))
          cases call.op
          have head' : Linker.concreteCallOverhead implementations call ≤ 3 := by
            rw [Linker.concreteCallOverhead]
            exact head
          exact (Nat.add_le_add head' tail).trans_eq (by omega)
    exact sumBound calls callSiteBound
  have callCount := trace.calls_length_le_cost
  simp [relativeBound, linkedBound] at relativeCost ⊢
  omega

def expectedLinkedProgram : Program 8 := [
  .setAddress (.immediate 0) 7 2,
  .halt (.immediate 0),
  .compareAddress (.immediate 0) (.immediate 0) 3 3 3,
  .compareAddress (.reg 7) (.immediate 0) 5 4 5,
  .setAddress (.immediate 0) 7 1,
  .compareAddress (.reg 7) (.immediate 1) 7 6 7,
  .setAddress (.immediate 0) 7 7,
  .halt (.immediate 0)]

theorem linkedProgram_eq :
    Linker.link clientProgram implementations linkerConfiguration = expectedLinkedProgram := by
  simp [Linker.link, Linker.clientCode, Linker.dispatcherCode, Linker.dispatcherEntries,
    Linker.implementationBody, Linker.operations, Linker.operationBase,
    Linker.dispatcherBase, Linker.implementationCodeSize, Linker.codeBefore,
    Linker.relocateInstruction, Linker.clientInstruction, Linker.dispatcherInstruction,
    Linker.dispatcherCleanup, clientProgram, implementations, linkerConfiguration,
    expectedLinkedProgram, DependencyImplementationModule.dependencyProcedureCertificate,
    DependencyImplementationModule.dependencyProgram, ContractModule.signature]

theorem linkedValid :
    (Linker.link clientProgram implementations linkerConfiguration).Valid := by
  exact Linker.link_valid clientProgram implementations linkerConfiguration
    clientRelativeCertificate.valid

/-- Concrete publication artifact; the dependency body occurs once in the linked code. -/
noncomputable def concreteLink :
    clientRelativeCertificate.ConcreteLink implementations linkerConfiguration
      (relativeBound := relativeBound) (linkedBound := linkedBound) where
  compatible := compatibility
  overheadBound := overheadBound

/-- Concrete publication artifact; the dependency body occurs once in the linked code. -/
noncomputable def linkedClientCertificate :
    FixedWidthAlgorithmCertificateBy clientProblem linkedBound :=
  concreteLink.certificate

/-- Required one-line existential discharge after the dependency implementation arrives. -/
theorem client_unconditional : clientProblem.HasAlgorithmBy linkedBound :=
  concreteLink.hasAlgorithm

def dependencyPublication :
    Audit.RestoringProcedurePublication dependencyContract dependencyBound where
  certificate := dependencyProcedureCertificate
  certificateName := ``dependencyProcedureCertificate
  contractName := ``dependencyContract
  boundName := ``dependencyBound
  correctnessTheorem := ``dependency_exists

noncomputable def linkedPublication :
    Audit.LinkedPublication signature clientProblem relativeBound linkedBound where
  client := clientRelativeCertificate
  implementations := implementations
  configuration := linkerConfiguration
  link := concreteLink
  instructionCount := linkedClientCertificate.program.length
  instructionCount_eq := rfl
  descriptionSize := WordRAM.descriptionSize linkedClientCertificate.program
  descriptionSize_eq := rfl
  dependencyCount := 1
  dependencyCount_eq := by decide
  certificateName := ``linkedClientCertificate
  problemName := ``clientProblem
  boundName := ``linkedBound
  correctnessTheorem := ``client_unconditional

#algorithm_audit dependencyPublication
#check linkedPublication

#print axioms client_unconditional

end IntegrationModule

namespace RandomizedIntegrationModule

open ContractModule RelativeClientModule DependencyImplementationModule IntegrationModule
open MeasureTheory

def clientProgram : RandomOpenProgram signature :=
  [.call () ⟨0⟩ ⟨0⟩ 1, .machine (.core (.halt (.immediate 0)))]

def stepBound : clientProblem.Input → Nat := fun _ ↦ 3
def drawBound : clientProblem.Input → Nat := fun _ ↦ 0
def overheadBound : clientProblem.Input → Nat := fun _ ↦ 2
def failure : clientProblem.Input → Algolean.Algorithms.WordRAM.Probability :=
  fun _ ↦ ⟨0, by simp⟩

theorem relativeSuccessEvent_eq_univ
    (responder : AdmissibleResponder signature) (input : clientProblem.Input)
    (validInput : clientProblem.pre input) :
    RandomRelativeSuccessEvent signature responder clientProblem clientProgram
      stepBound drawBound input validInput = Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  cases input
  let initial := clientProblem.initialMemory () validInput
  let after := WordLayout.unit.writeAt ⟨0⟩ (responder.answer () ()) initial
  have inputRep : WordLayout.unit.RepAt ⟨0⟩ () initial :=
    WordLayout.init_rep _ _ (clientProblem.inputFits () validInput)
  have callStep : RandomOpenStep signature responder clientProgram source
      (RandomBit.Configuration.initial initial)
      (.running ⟨1, after, 0⟩) ⟨2, 0⟩ (some {
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := 2
        chargedCost_eq := rfl }) := by
    exact RandomOpenStep.call
      (by simp [RandomBit.Configuration.initial, clientProgram]) inputRep trivial
  have haltStep : RandomOpenStep signature responder clientProgram source ⟨1, after, 0⟩
      (.halted after 0 0) ⟨1, 0⟩ none := by
    exact RandomOpenStep.machine (instruction := .core (.halt (.immediate 0)))
      (by simp [clientProgram]) (by rfl)
  have trace : RandomOpenHaltingTrace signature responder clientProgram source
      (RandomBit.Configuration.initial initial) after 0 0 ⟨3, 0⟩ [{
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := 2
        chargedCost_eq := rfl }] :=
    RandomOpenHaltingTrace.next callStep (RandomOpenHaltingTrace.halt haltStep)
  refine ⟨after, 0, 0, ⟨3, 0⟩, _, (), trace, ?_, trivial, by decide, by decide⟩
  exact WordLayout.writeAt_rep _ _ _ _ (by
    change WordLayout.unit.FitsAt ⟨0⟩ ()
    simp [WordLayout.FitsAt, WordLayout.Fits, WordLayout.footprintWords,
      WordLayout.encode])

def clientCertificate :
    RandomRelativeAlgorithmCertificate signature clientProblem stepBound drawBound failure where
  program := clientProgram
  valid := by
    intro pc instruction fetch target member
    rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · change target < 2
      simp [clientProgram, RandomOpenInstruction.successors] at member
      omega
    · simp [clientProgram, RandomOpenInstruction.successors,
        RandomBit.Instruction.successors, RAM.Instruction.successors] at member
  measurableSuccess responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    exact MeasurableSet.univ
  successProbability responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    simp

theorem compatibility :
    Linker.Compatibility (RandomLinker.placement clientProgram) implementations
      linkerConfiguration := by
  simpa [clientProgram, RandomLinker.placement, RandomLinker.placementInstruction,
    RelativeClientModule.clientProgram] using IntegrationModule.compatibility

theorem overhead_le (source : RandomBit.Source) (input : clientProblem.Input)
    (validInput : clientProblem.pre input) (final : Memory 8) (result : BitVec 8)
    (draws : Nat) (cost : RandomBit.Cost)
    (calls : List (DependencyCallRecord signature))
    (trace : RandomOpenHaltingTrace signature implementations.responder clientProgram source
      (RandomBit.Configuration.initial (clientProblem.initialMemory input validInput))
      final result draws cost calls) :
    Linker.totalConcreteCallOverhead implementations calls ≤ overheadBound input := by
  cases trace with
  | halt step =>
      cases step with
      | machine fetch observed =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | @next _ nextConfiguration _ _ _ _ _ headCall tailCalls step tail =>
      cases step with
      | machine fetch observed =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
      | call fetch inputRep valid =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
          rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
          cases tail with
          | halt tailStep =>
              cases tailStep with
              | machine tailFetch tailObserved =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [Linker.totalConcreteCallOverhead, Linker.concreteCallOverhead,
                    overheadBound, RandomBit.Configuration.initial]
          | next tailStep tailTail =>
              cases tailStep with
              | machine tailFetch tailObserved =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [RandomBit.execute, RAM.execute] at tailObserved
              | call tailFetch _ _ =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch

theorem linkedSuccessEvent_eq_univ (input : clientProblem.Input)
    (validInput : clientProblem.pre input) :
    clientProblem.RandomSuccessEvent
      (RandomLinker.link clientProgram implementations linkerConfiguration)
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound input validInput =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  apply RandomLinker.successEvent_mono_of clientCertificate implementations
    linkerConfiguration overheadBound compatibility overhead_le input validInput
  change source ∈ RandomRelativeSuccessEvent signature implementations.responder clientProblem
    clientProgram stepBound drawBound input validInput
  rw [relativeSuccessEvent_eq_univ]
  trivial

def assumptions : RandomLinker.LinkingAssumptions clientCertificate implementations
    linkerConfiguration overheadBound where
  compatible := compatibility
  overhead_le := overhead_le
  measurableSuccess input validInput := by
    change MeasurableSet (clientProblem.RandomSuccessEvent
      (RandomLinker.link clientProgram implementations linkerConfiguration)
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound input validInput)
    rw [linkedSuccessEvent_eq_univ input validInput]
    exact MeasurableSet.univ

noncomputable def linkedCertificate :
    clientProblem.RandomizedAlgorithmCertificate
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound failure :=
  RandomLinker.certificate clientCertificate implementations linkerConfiguration overheadBound
    assumptions

/-- Randomized one-line discharge uses the same hidden source and the deterministic body code. -/
theorem client_unconditional :
    clientProblem.HasRandomizedWordRAMAlgorithm
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound failure :=
  RandomLinker.hasAlgorithm clientCertificate implementations linkerConfiguration overheadBound
    assumptions

#print axioms client_unconditional

end RandomizedIntegrationModule

end AlgoleanTests.WordRAMProcedureComposition
