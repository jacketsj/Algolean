/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.StructuredRealRAM
public meta import Algolean.Audit.StructuredRealRAM

/-!
# Structured exact-real/natural RAM procedure linking regression

The relative client is proved against a typed contract.  A separately certified deterministic
procedure is then linked into one finite core program; its halt instruction becomes a real jump
through the shared dispatcher and is charged in the final five-transition trace.
-/

@[expose] public section

namespace AlgoleanTests.StructuredRealRAMProcedureComposition

open Algolean Algorithms
open Algorithms.StructuredRealRAM

#check SealedProfile
#check RandomBit.CoreEmbedding.trace
#check UniformReal.CoreEmbedding.trace
#check ParametricProcedureCertificate.forConvention
#check RandomLinker.refine_trace
#check RandomLinker.certificate
#check RandomLinker.hasAlgorithm
#check RandomLinker.boundedTimeMonteCarloCertificate
#check RandomLinker.hasBoundedTimeMonteCarloAlgorithm
#check UniformRealLinker.refine_trace
#check UniformRealLinker.certificate
#check UniformRealLinker.hasBoundedTimeMonteCarloAlgorithm

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.sqrt

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check Instruction.floor

/-
error: Unknown constant
-/
#guard_msgs (error, substring := true) in
#check SealedProfile.custom

namespace ContractModule

def dependencyContract : ProcedureContract :=
  ProcedureContract.ofCanonical Unit Unit (fun _ ↦ True) (fun _ _ ↦ True)

def dependencyBound : ProcedureBound dependencyContract :=
  fun _ ↦ (Instruction.halt (.literal 0)).cost

def signature : DependencySignature where
  Op := Unit
  finiteOp := inferInstance
  decEqOp := inferInstance
  contract _ := dependencyContract
  bound _ := dependencyBound

end ContractModule

namespace RelativeClientModule

open ContractModule

def clientProblem : MachineProblem :=
  MachineProblem.ofCanonical Unit Unit Layout.inputRegion (fun _ ↦ True) (fun _ _ ↦ True)

def clientProgram : OpenProgram signature :=
  [.call () Layout.inputRegion Layout.inputRegion 1,
    .core (.halt (.literal 0))]

def relativeBound : clientProblem.Input → Cost := fun _ ↦
  dependencyBound () + (Instruction.halt (.literal 0)).cost

theorem unit_writeAt_of_rep (region : Region) (memory : Memory)
    (represented : Layout.unit.RepAt region () memory) :
    Layout.unit.writeAt region () memory = memory := by
  rcases represented with ⟨realLength, natLength, reals, nats⟩
  cases memory with
  | mk realMem natMem natReg =>
      simp only [Layout.writeAt, Layout.encode]
      have realEq : Layout.overwrite [] region.realBase realMem = realMem := by
        funext address
        simp [Layout.overwrite]
      rw [realEq]
      have natEq : (fun address =>
          if address = region.natBase then 0
          else if address = region.natBase + 1 then 0
          else Layout.overwrite [] (region.natBase + 2) natMem address) = natMem := by
        funext address
        by_cases atBase : address = region.natBase
        · subst address
          simpa [Layout.encode] using realLength.symm
        · by_cases atLength : address = region.natBase + 1
          · subst address
            simpa [Layout.encode] using natLength.symm
          · simp [atBase, atLength, Layout.overwrite]
      change Memory.mk realMem (fun address =>
          if address = region.natBase then 0
          else if address = region.natBase + 1 then 0
          else Layout.overwrite [] (region.natBase + 2) natMem address) natReg = _
      rw [natEq]

def clientRelativeCertificate :
    RelativeAlgorithmCertificate signature clientProblem relativeBound where
  module := clientProgram
  valid := by
    intro pc instruction fetch target member
    rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · simp [clientProgram, OpenInstruction.successors] at member ⊢
      omega
    · simp [clientProgram, OpenInstruction.successors, Instruction.successors] at member
  solvesAgainstContracts responder input validInput := by
    cases input
    let initial := clientProblem.initialMemory ()
    have inputRep : Layout.unit.RepAt Layout.inputRegion () initial := Layout.unit.init_rep ()
    have unchanged : Layout.unit.writeAt Layout.inputRegion (responder.answer () ()) initial =
        initial := by
      exact unit_writeAt_of_rep Layout.inputRegion initial inputRep
    have contractUnchanged :
        (signature.contract ()).outputLayout.writeAt Layout.inputRegion
          (responder.answer () ()) initial = initial := by
      change Layout.unit.writeAt Layout.inputRegion (responder.answer () ()) initial = initial
      exact unchanged
    have boundEq : signature.bound () () = dependencyBound () := rfl
    have callStep : OpenStep signature responder clientProgram ⟨0, initial⟩
        (.running ⟨1, initial⟩) (dependencyBound ())
        (some {
          callSite := 0
          op := ()
          input := ()
          output := responder.answer () ()
          outputCorrect := responder.correct () () trivial
          chargedCost := dependencyBound ()
          chargedCost_eq := rfl }) := by
      have raw := OpenStep.call
        (responder := responder)
        (program := clientProgram)
        (configuration := ⟨0, initial⟩)
        (op := ())
        (inputRegion := Layout.inputRegion)
        (outputRegion := Layout.inputRegion)
        (next := 1)
        (input := ())
        (by rfl) inputRep trivial
      simpa only [contractUnchanged, boundEq] using raw
    have haltStep : OpenStep signature responder clientProgram ⟨1, initial⟩
        (.halted initial 0) (Instruction.halt (.literal 0)).cost none :=
      OpenStep.core
        (instruction := .halt (.literal 0))
        (by simp [clientProgram]) (by simp [execute, RealOperand.eval])
    have trace := OpenHaltingTrace.call callStep (OpenHaltingTrace.halt haltStep)
    exact ⟨(), initial, 0, relativeBound (), 2, [_], trace, inputRep, trivial, le_rfl⟩

end RelativeClientModule

namespace DependencyImplementationModule

open ContractModule RelativeClientModule

def dependencyProgram : Program := [.halt (.literal 0)]

def dependencyProcedureCertificate :
    RestoringProcedureCertificate dependencyContract dependencyBound where
  module := ⟨dependencyProgram, 0⟩
  calling := {
    inputRegion := Layout.inputRegion
    outputRegion := Layout.inputRegion
    scratchRealOwned := fun _ ↦ False
    scratchNatOwned := fun _ ↦ False
    natRegisterOwned := fun _ ↦ False
    aliasingPolicy := .inPlace }
  callingRealizes := by
    refine {
      inputOutputPolicy := ?_
      scratchRealDisjointOutput := ?_
      scratchNatDisjointOutput := ?_ }
    · intros
      trivial
    · intros
      simp
    · intros
      simp
  valid := by
    constructor
    · intro pc instruction fetch target member
      cases pc with
      | zero =>
          simp [dependencyProgram] at fetch
          subst instruction
          simp [Instruction.successors] at member
      | succ pc => simp [dependencyProgram] at fetch
    · simp [dependencyProgram]
  output _ := ()
  outputCorrect _ _ := trivial
  correct input validInput initial represented := by
    cases input
    let run : ProcedureRun ⟨dependencyProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := (Instruction.halt (.literal 0)).cost
      steps := 1
      trace := .halt (by simp [step, execute, dependencyProgram, RealOperand.eval]) }
    refine ⟨run, represented, ?_, ?_⟩
    · exact le_rfl
    · exact ⟨fun _ _ _ _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  restoringCorrect input validInput initial represented := by
    cases input
    let run : ProcedureRun ⟨dependencyProgram, 0⟩ initial := {
      final := initial
      result := 0
      cost := (Instruction.halt (.literal 0)).cost
      steps := 1
      trace := .halt (by simp [step, execute, dependencyProgram, RealOperand.eval]) }
    exact ⟨run, represented, le_rfl,
      (unit_writeAt_of_rep Layout.inputRegion initial represented).symm⟩

theorem dependency_exists : HasProcedure dependencyContract dependencyBound :=
  ⟨dependencyProcedureCertificate.toProcedureCertificate⟩

def implementations : ImplementationEnvironment signature where
  implementation _ := dependencyProcedureCertificate

end DependencyImplementationModule

namespace IntegrationModule

open ContractModule RelativeClientModule DependencyImplementationModule

def linkerConfiguration : Linker.Configuration := ⟨7⟩

def expectedLinkedProgram : Program := [
  .nset (.literal 0) 7 2,
  .halt (.literal 0),
  .jump 3,
  .ncompare (.reg 7) (.literal 0) 5 4 5,
  .nset (.literal 0) 7 1,
  .ncompare (.reg 7) (.literal 1) 7 6 7,
  .nset (.literal 0) 7 7,
  .halt (.literal 0)]

theorem linkedProgram_eq :
    Linker.link clientProgram implementations linkerConfiguration = expectedLinkedProgram := by
  simp [Linker.link, Linker.clientCode, Linker.dispatcherCode, Linker.dispatcherEntries,
    Linker.dispatcherInstruction, Linker.dispatcherCleanup,
    Linker.implementationBody, Linker.operations, Linker.operationBase,
    Linker.dispatcherBase, Linker.implementationCodeSize, Linker.codeBefore,
    Linker.relocateInstruction, Linker.clientInstruction, clientProgram, implementations,
    linkerConfiguration, expectedLinkedProgram, dependencyProcedureCertificate,
    dependencyProgram, signature]

def linkedBound : clientProblem.Input → Cost := fun _ ↦
  (Instruction.nset (.literal 0) 7 2).cost +
    ((Instruction.jump 3).cost +
      ((Instruction.ncompare (.reg 7) (.literal 0) 5 4 5).cost +
        ((Instruction.nset (.literal 0) 7 1).cost +
          (Instruction.halt (.literal 0)).cost)))

def compatibility :
    Linker.Compatibility clientProgram implementations linkerConfiguration where
  clientAvoidsReturnRegister pc instruction fetch := by
    have pcBelow := (List.getElem?_eq_some_iff.mp fetch).1
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · simp [clientProgram] at fetch
    · simp [clientProgram] at fetch
      subst instruction
      trivial
  inputRegion_eq pc op inputRegion outputRegion next fetch := by
    have pcBelow := (List.getElem?_eq_some_iff.mp fetch).1
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · simp [clientProgram] at fetch
      rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · simp [clientProgram] at fetch
  outputRegion_eq pc op inputRegion outputRegion next fetch := by
    have pcBelow := (List.getElem?_eq_some_iff.mp fetch).1
    have pcBelow' : pc < 2 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · simp [clientProgram] at fetch
      rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
      rfl
    · simp [clientProgram] at fetch

theorem returnRegisterInitiallyZero (input : clientProblem.Input) :
    (clientProblem.initialMemory input).natReg linkerConfiguration.returnRegister = 0 := by
  simp [clientProblem, MachineProblem.initialMemory, linkerConfiguration, Layout.init]

theorem boundCovers :
    Linker.BoundCovers clientRelativeCertificate implementations linkedBound := by
  intro input final result cost steps calls validInput trace costBound
  cases input
  cases trace with
  | halt openStep =>
      cases openStep with
      | core fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | core openStep tail =>
      cases openStep with
      | core fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | call openStep tail =>
      cases openStep with
      | call fetch inputRep validContractInput =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
          rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
          rename_i tailCost tailSteps tailCalls inputValue
          cases inputValue
          cases tail with
          | halt tailStep =>
              cases tailStep with
              | core tailFetch tailExec =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [execute, RealOperand.eval] at tailExec
                  rcases tailExec with ⟨⟨rfl, rfl⟩, rfl⟩
                  intro coordinate
                  apply (Nat.add_le_add_right (costBound coordinate) _).trans
                  fin_cases coordinate <;>
                    norm_num [ContractModule.dependencyBound, relativeBound, linkedBound,
                      Linker.totalConcreteCallOverhead,
                      Linker.concreteCallOverhead, implementations,
                      dependencyProcedureCertificate, NatOperand.reads, RealOperand.reads,
                      Instruction.cost, Cost.control, Cost.ofFields, Matrix.vecHead,
                      Matrix.vecTail]
          | core tailStep tailTail =>
              cases tailStep with
              | core tailFetch tailExec =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [execute] at tailExec
          | call tailStep tailTail =>
              cases tailStep with
              | call tailFetch tailInputRep tailValid =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch

def concreteRefinement :
    Linker.Refinement clientRelativeCertificate implementations linkerConfiguration
      linkedBound :=
  Linker.Refinement.ofCompatibility clientRelativeCertificate implementations
    linkerConfiguration linkedBound compatibility returnRegisterInitiallyZero boundCovers

noncomputable def linkedClientCertificate :
    MachineProblem.FixedAlgorithmCertificateBy clientProblem linkedBound :=
  Linker.RelativeAlgorithmCertificate.link clientRelativeCertificate implementations
    linkerConfiguration linkedBound concreteRefinement

theorem client_unconditional : clientProblem.HasAlgorithmBy linkedBound :=
  ⟨linkedClientCertificate⟩

noncomputable def publication :
    Audit.LinkedPublication signature clientProblem relativeBound linkedBound where
  client := clientRelativeCertificate
  implementations := implementations
  configuration := linkerConfiguration
  refinement := concreteRefinement
  certificateName := ``linkedClientCertificate
  problemName := ``clientProblem
  boundName := ``linkedBound
  correctnessTheorem := ``client_unconditional

#check publication
#print axioms client_unconditional

end IntegrationModule

namespace RandomizedIntegrationModule

open ContractModule RelativeClientModule DependencyImplementationModule IntegrationModule
open MeasureTheory

def problem : BitRandomizedMachineProblem where
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := Layout.inputRegion
  pre _ := True
  post _ _ := True

def clientProgram : RandomOpenProgram signature :=
  [.call () Layout.inputRegion Layout.inputRegion 1,
    .machine (.core (.halt (.literal 0)))]

def bound : Nat → RandomBit.Cost := fun _ ↦
  RandomBit.Cost.ofCore
    (dependencyBound () + (Instruction.halt (.literal 0)).cost)

def fixedOverhead : Cost :=
  (Instruction.nset (.literal 0) 0 0).cost +
    (fun coordinate ↦
      (Instruction.ncompare (.literal 0) (.literal 0) 0 0 0).cost coordinate +
        (Instruction.nset (.literal 0) 0 0).cost coordinate)

theorem concreteCallOverhead_zero (call : DependencyCallRecord signature)
    (site : call.callSite = 0) :
    Linker.concreteCallOverhead implementations call = fixedOverhead := by
  funext coordinate
  simp [Linker.concreteCallOverhead, fixedOverhead, site]

def linkedBound : Nat → RandomBit.Cost := fun size ↦
  bound size + RandomBit.Cost.ofCore fixedOverhead

def failure : problem.Input → Algolean.Algorithms.Probability :=
  fun _ ↦ ⟨0, by simp⟩

theorem relativeSuccessEvent_eq_univ
    (responder : AdmissibleResponder signature) (input : problem.Input)
    (validInput : problem.pre input) :
    RandomRelativeSuccessEvent signature responder problem clientProgram bound input =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  cases input
  let initial := problem.initialMemory ()
  have inputRep : Layout.unit.RepAt Layout.inputRegion () initial := Layout.unit.init_rep ()
  have unchanged : Layout.unit.writeAt Layout.inputRegion (responder.answer () ()) initial =
      initial := RelativeClientModule.unit_writeAt_of_rep Layout.inputRegion initial inputRep
  have contractUnchanged :
      (signature.contract ()).outputLayout.writeAt Layout.inputRegion
        (responder.answer () ()) initial = initial := by
    change Layout.unit.writeAt Layout.inputRegion (responder.answer () ()) initial = initial
    exact unchanged
  have callStep : RandomOpenStep signature responder clientProgram source
      (RandomBit.Configuration.initial initial) (.running ⟨1, initial, 0⟩)
      (RandomBit.Cost.ofCore (signature.bound () ())) (some {
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := signature.bound () ()
        chargedCost_eq := rfl }) := by
    simpa [RandomBit.Configuration.initial, contractUnchanged] using
      (RandomOpenStep.call
        (signature := signature) (responder := responder) (program := clientProgram)
        (source := source) (configuration := RandomBit.Configuration.initial initial) (op := ())
        (inputRegion := Layout.inputRegion) (outputRegion := Layout.inputRegion)
        (next := 1) (input := ())
        (by simp [RandomBit.Configuration.initial, clientProgram]) inputRep trivial)
  have haltStep : RandomOpenStep signature responder clientProgram source ⟨1, initial, 0⟩
      (.halted initial 0 0)
      (RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost) none := by
    exact RandomOpenStep.machine (instruction := .core (.halt (.literal 0)))
      (by simp [clientProgram]) (by
        simp [RandomBit.execute, RandomBit.liftCoreOutcome, execute, RealOperand.eval])
  have trace : RandomOpenHaltingTrace signature responder clientProgram source
      (RandomBit.Configuration.initial initial) initial 0
      (RandomBit.Cost.ofCore (signature.bound () ()) +
        RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost)
      2 0 [{
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := signature.bound () ()
        chargedCost_eq := rfl }] :=
    RandomOpenHaltingTrace.call callStep (RandomOpenHaltingTrace.halt haltStep)
  refine ⟨(), initial, 0, _, 2, 0, _, trace, inputRep, trivial, ?_⟩
  change RandomBit.Cost.ofCore (signature.bound () ()) +
      RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost ≤
    RandomBit.Cost.ofCore
      (dependencyBound () + (Instruction.halt (.literal 0)).cost)
  constructor
  · intro coordinate
    rfl
  · rfl

def clientCertificate :
    BoundedTimeMonteCarloRelativeCertificate signature problem bound failure where
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
        RandomBit.Instruction.successors, Instruction.successors] at member
  measurableSuccess responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    exact MeasurableSet.univ
  terminates responder input validInput source := by
    have success : source ∈
        RandomRelativeSuccessEvent signature responder problem clientProgram bound input := by
      rw [relativeSuccessEvent_eq_univ responder input validInput]
      trivial
    rcases success with ⟨output, final, result, cost, steps, draws, calls, trace,
      outputRep, correct, costBound⟩
    exact ⟨output, final, result, cost, steps, draws, calls, trace, outputRep, costBound⟩
  successProbability responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    simp

theorem compatibility :
    Linker.Compatibility (RandomLinker.placement clientProgram) implementations
      linkerConfiguration := by
  simpa [clientProgram, RandomLinker.placement, RandomLinker.placementInstruction,
    RelativeClientModule.clientProgram] using IntegrationModule.compatibility

theorem returnRegisterInitiallyZero (input : problem.Input) :
    (problem.initialMemory input).natReg linkerConfiguration.returnRegister = 0 := by
  simp [problem, BitRandomizedMachineProblem.initialMemory, linkerConfiguration, Layout.init]

theorem boundCovers : RandomLinker.BoundCovers clientCertificate implementations linkedBound := by
  intro source input final result cost steps draws calls validInput trace costBound
  cases input
  cases trace with
  | halt openStep =>
      cases openStep with
      | machine fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | machine openStep tail =>
      cases openStep with
      | machine fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | call openStep tail =>
      cases openStep with
      | call fetch inputRep validContractInput =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
          rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
          cases tail with
          | halt tailStep =>
              cases tailStep with
              | machine tailFetch tailExec =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [RandomBit.execute, execute, RealOperand.eval] at tailExec
                  rcases tailExec with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
                  simp only [Linker.totalConcreteCallOverhead, List.map_cons, List.map_nil,
                    List.sum_cons, List.sum_nil, add_zero]
                  rw [concreteCallOverhead_zero _ (by
                    simp [RandomBit.Configuration.initial])]
                  simp only [linkedBound]
                  constructor
                  · intro coordinate
                    change
                      (RandomBit.Cost.ofCore (signature.bound () _) +
                            RandomBit.Cost.ofCore
                              (Instruction.halt (.literal 0)).cost).machine coordinate +
                          fixedOverhead coordinate ≤
                        (bound (problem.inputSize ())).machine coordinate +
                          fixedOverhead coordinate
                    exact Nat.add_le_add_right (costBound.1 coordinate)
                      (fixedOverhead coordinate)
                  · change
                      (RandomBit.Cost.ofCore (signature.bound () _) +
                            RandomBit.Cost.ofCore
                              (Instruction.halt (.literal 0)).cost).randomDraws + 0 ≤
                        (bound (problem.inputSize ())).randomDraws + 0
                    exact Nat.add_le_add_right costBound.2 0
          | machine tailStep tailTail =>
              cases tailStep with
              | machine tailFetch tailExec =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch
                  cases tailFetch
                  simp [RandomBit.execute, RandomBit.liftCoreOutcome, execute] at tailExec
          | call tailStep tailTail =>
              cases tailStep with
              | call tailFetch tailInputRep tailValid =>
                  change clientProgram[1]? = _ at tailFetch
                  simp [clientProgram] at tailFetch

theorem linkedSuccessEvent_eq_univ (input : problem.Input) (validInput : problem.pre input) :
    problem.SuccessEvent (RandomLinker.link clientProgram implementations linkerConfiguration)
      input (linkedBound (problem.inputSize input)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  apply RandomLinker.successEvent_mono_of clientCertificate implementations
    linkerConfiguration linkedBound compatibility returnRegisterInitiallyZero boundCovers
    input validInput
  change source ∈ RandomRelativeSuccessEvent signature implementations.responder problem
    clientProgram bound input
  rw [relativeSuccessEvent_eq_univ implementations.responder input validInput]
  trivial

def assumptions : RandomLinker.LinkingAssumptions clientCertificate implementations
    linkerConfiguration linkedBound where
  compatible := compatibility
  returnRegisterInitiallyZero := returnRegisterInitiallyZero
  boundCovers := boundCovers
  measurableSuccess input validInput := by
    change MeasurableSet (problem.SuccessEvent
      (RandomLinker.link clientProgram implementations linkerConfiguration) input
      (linkedBound (problem.inputSize input)))
    rw [linkedSuccessEvent_eq_univ input validInput]
    exact MeasurableSet.univ

noncomputable def linkedCertificate :
    BitRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
      problem linkedBound failure :=
  RandomLinker.boundedTimeMonteCarloCertificate clientCertificate implementations
    linkerConfiguration linkedBound
    assumptions

/-- Randomized discharge reuses the deterministic dependency without changing the source. -/
theorem client_unconditional :
    problem.HasBoundedTimeMonteCarloAlgorithm linkedBound failure :=
  RandomLinker.hasBoundedTimeMonteCarloAlgorithm clientCertificate implementations
    linkerConfiguration linkedBound assumptions

#print axioms client_unconditional

end RandomizedIntegrationModule

namespace UniformRealIntegrationSyntax

open ContractModule RelativeClientModule DependencyImplementationModule IntegrationModule

/-- A concrete relative client containing both one exact sample and one deterministic call. -/
def clientProgram : UniformOpenProgram signature :=
  [.machine (.sampleUniform 0 1),
    .call () Layout.inputRegion Layout.inputRegion 2,
    .machine (.core (.halt (.literal 0)))]

/-- Linking preserves the exact-uniform instruction rather than replacing its hidden source. -/
example :
    (UniformRealLinker.link clientProgram implementations linkerConfiguration)[0]? =
      some (.sampleUniform 0 1) := by
  have fetched : clientProgram[0]? = some (.machine (.sampleUniform 0 1)) := by
    simp [clientProgram]
  simpa [UniformRealLinker.clientInstruction] using
    UniformRealLinker.link_fetch_client clientProgram implementations linkerConfiguration
      0 (.machine (.sampleUniform 0 1)) fetched

/-- The deterministic call site is resolved to ordinary shared-body linker syntax. -/
example :
    (UniformRealLinker.link clientProgram implementations linkerConfiguration)[1]? =
      some (.core (Linker.clientInstruction
        (UniformRealLinker.placement clientProgram) implementations linkerConfiguration 1
        (.call () Layout.inputRegion Layout.inputRegion 2))) := by
  have fetched : clientProgram[1]? =
      some (.call () Layout.inputRegion Layout.inputRegion 2) := by
    simp [clientProgram]
  simpa [UniformRealLinker.clientInstruction] using
    UniformRealLinker.link_fetch_client clientProgram implementations linkerConfiguration
      1 (.call () Layout.inputRegion Layout.inputRegion 2) fetched

/-- Exact-uniform linking has the same finite instruction count as its deterministic artifact. -/
example :
    (UniformRealLinker.link clientProgram implementations linkerConfiguration).length =
      (UniformRealLinker.deterministicArtifact clientProgram implementations
        linkerConfiguration).length :=
  UniformRealLinker.link_length clientProgram implementations linkerConfiguration

/- The refinement theorem keeps the source, cursor, and draw count in one linked trace. -/
#check UniformRealLinker.refine_trace

/-- Completed assumptions discharge the relative theorem in one application. -/
example
    {problem : UniformRealRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → UniformReal.Cost}
    {failure : problem.Input → Probability}
    (client : UniformRealBoundedTimeMonteCarloRelativeCertificate signature problem
      relativeBound failure)
    (assumptions : UniformRealLinker.LinkingAssumptions client implementations
      linkerConfiguration linkedBound) :
    problem.HasBoundedTimeMonteCarloAlgorithm linkedBound failure :=
  UniformRealLinker.hasBoundedTimeMonteCarloAlgorithm client implementations
    linkerConfiguration linkedBound assumptions

end UniformRealIntegrationSyntax

namespace UniformRealConcreteIntegration

open ContractModule RelativeClientModule DependencyImplementationModule IntegrationModule
open MeasureTheory

def problem : UniformRealRandomizedMachineProblem where
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := Layout.inputRegion
  pre _ := True
  post _ _ := True

/-- One deterministic call, one exact sample, and one halt in finite first-order syntax. -/
def clientProgram : UniformOpenProgram signature :=
  [.call () Layout.inputRegion Layout.inputRegion 1,
    .machine (.sampleUniform 0 2),
    .machine (.core (.halt (.literal 0)))]

def relativeBound : Nat → UniformReal.Cost := fun _ ↦
  RandomBit.Cost.ofCore (dependencyBound ()) + (UniformReal.sampleCost +
    RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost)

def failure : problem.Input → Probability := fun _ ↦ ⟨0, by simp⟩

theorem unitRep_writeReal (memory : Memory)
    (represented : Layout.unit.RepAt Layout.inputRegion () memory)
    (address : Nat) (value : Real) :
    Layout.unit.RepAt Layout.inputRegion () (memory.writeReal address value) := by
  simpa [Layout.RepAt, Layout.encode, Layout.readReals, Layout.readNats,
    Memory.writeReal] using represented

theorem relativeSuccessEvent_eq_univ
    (responder : AdmissibleResponder signature) (input : problem.Input)
    (validInput : problem.pre input) :
    UniformRelativeSuccessEvent signature responder problem clientProgram relativeBound input =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  cases input
  let initial := problem.initialMemory ()
  have inputRep : Layout.unit.RepAt Layout.inputRegion () initial := Layout.unit.init_rep ()
  let afterCall := (signature.contract ()).outputLayout.writeAt Layout.inputRegion
    (responder.answer () ()) initial
  have callStep : UniformOpenStep signature responder clientProgram source
      (RandomBit.Configuration.initial initial) (.running ⟨1, afterCall, 0⟩)
      (RandomBit.Cost.ofCore (signature.bound () ())) (some {
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := signature.bound () ()
        chargedCost_eq := rfl }) := by
    have raw := UniformOpenStep.call
      (signature := signature) (responder := responder) (program := clientProgram)
      (source := source) (configuration := RandomBit.Configuration.initial initial) (op := ())
      (inputRegion := Layout.inputRegion) (outputRegion := Layout.inputRegion)
      (next := 1) (input := ()) (by simp [clientProgram, RandomBit.Configuration.initial])
      inputRep trivial
    simpa [afterCall, RandomBit.Configuration.initial] using raw
  have afterCallRep : Layout.unit.RepAt Layout.inputRegion () afterCall := by
    change Layout.unit.RepAt Layout.inputRegion ()
      (Layout.unit.writeAt Layout.inputRegion () initial)
    exact Layout.unit.writeAt_rep Layout.inputRegion () initial
  let afterSample := afterCall.writeReal (afterCall.natReg 0) (source 0)
  have sampleStep : UniformOpenStep signature responder clientProgram source ⟨1, afterCall, 0⟩
      (.running ⟨2, afterSample, 1⟩) UniformReal.sampleCost none := by
    exact UniformOpenStep.machine (instruction := .sampleUniform 0 2)
      (by simp [clientProgram]) (by simp [UniformReal.execute, afterSample])
  have afterSampleRep : Layout.unit.RepAt Layout.inputRegion () afterSample :=
    unitRep_writeReal afterCall afterCallRep _ _
  have haltStep : UniformOpenStep signature responder clientProgram source ⟨2, afterSample, 1⟩
      (.halted afterSample 0 1)
      (RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost) none := by
    exact UniformOpenStep.machine (instruction := .core (.halt (.literal 0)))
      (by simp [clientProgram]) (by
        simp [UniformReal.execute, UniformReal.liftCoreOutcome, execute, RealOperand.eval])
  have trace : UniformOpenHaltingTrace signature responder clientProgram source
      (RandomBit.Configuration.initial initial) afterSample 0
      (RandomBit.Cost.ofCore (signature.bound () ()) + (UniformReal.sampleCost +
        RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost))
      3 1 [{
        callSite := 0
        op := ()
        input := ()
        output := responder.answer () ()
        outputCorrect := responder.correct () () trivial
        chargedCost := signature.bound () ()
        chargedCost_eq := rfl }] :=
    UniformOpenHaltingTrace.call callStep
      (UniformOpenHaltingTrace.machine sampleStep (UniformOpenHaltingTrace.halt haltStep))
  refine ⟨(), afterSample, 0, _, 3, 1, _, trace, afterSampleRep, trivial, ?_⟩
  change RandomBit.Cost.ofCore (signature.bound () ()) + (UniformReal.sampleCost +
      RandomBit.Cost.ofCore (Instruction.halt (.literal 0)).cost) ≤ relativeBound 2
  exact le_rfl

def clientCertificate :
    UniformRealBoundedTimeMonteCarloRelativeCertificate signature problem relativeBound failure where
  program := clientProgram
  valid := by
    intro pc instruction fetch target member
    rcases List.getElem?_eq_some_iff.mp fetch with ⟨pcBelow, rfl⟩
    have pcBelow' : pc < 3 := by simpa [clientProgram] using pcBelow
    interval_cases pc
    · simp [clientProgram, UniformOpenInstruction.successors] at member
      change target < 3
      omega
    · simp [clientProgram, UniformOpenInstruction.successors,
        UniformReal.Instruction.successors] at member
      change target < 3
      omega
    · simp [clientProgram, UniformOpenInstruction.successors,
        UniformReal.Instruction.successors, Instruction.successors] at member
  measurableSuccess responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    exact MeasurableSet.univ
  terminates responder input validInput source := by
    have success : source ∈ UniformRelativeSuccessEvent signature responder problem
        clientProgram relativeBound input := by
      rw [relativeSuccessEvent_eq_univ responder input validInput]
      trivial
    rcases success with ⟨output, final, result, cost, steps, draws, calls, trace,
      outputRep, correct, costBound⟩
    exact ⟨output, final, result, cost, steps, draws, calls, trace, outputRep, costBound⟩
  successProbability responder input validInput := by
    rw [relativeSuccessEvent_eq_univ responder input validInput]
    simp

theorem compatibility :
    Linker.Compatibility (UniformRealLinker.placement clientProgram) implementations
      linkerConfiguration := by
  refine {
    clientAvoidsReturnRegister := ?_
    inputRegion_eq := ?_
    outputRegion_eq := ?_ }
  · intro pc instruction fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by
      simpa [UniformRealLinker.placement, clientProgram] using pcBelow
    interval_cases pc <;>
      simp [UniformRealLinker.placement, UniformRealLinker.placementInstruction,
        clientProgram] at fetch
    · subst instruction
      trivial
    · subst instruction
      trivial
  · intro pc op inputRegion outputRegion next fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by
      simpa [UniformRealLinker.placement, clientProgram] using pcBelow
    interval_cases pc <;>
      simp [UniformRealLinker.placement, UniformRealLinker.placementInstruction,
        clientProgram] at fetch
    rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  · intro pc op inputRegion outputRegion next fetch
    have pcBelow := List.getElem?_eq_some_iff.mp fetch |>.1
    have pcBelow' : pc < 3 := by
      simpa [UniformRealLinker.placement, clientProgram] using pcBelow
    interval_cases pc <;>
      simp [UniformRealLinker.placement, UniformRealLinker.placementInstruction,
        clientProgram] at fetch
    rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem returnRegisterInitiallyZero (input : problem.Input) :
    (problem.initialMemory input).natReg linkerConfiguration.returnRegister = 0 := by
  simp [problem, UniformRealRandomizedMachineProblem.initialMemory,
    linkerConfiguration, Layout.init]

theorem calls_singleton (source : UniformReal.Source) (input : problem.Input)
    (validInput : problem.pre input) (final : Memory) (result : Real)
    (cost : UniformReal.Cost) (steps draws : Nat)
    (calls : List (DependencyCallRecord signature))
    (trace : UniformOpenHaltingTrace signature implementations.responder clientProgram source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls) :
    ∃ call, calls = [call] ∧ call.callSite = 0 := by
  cases trace with
  | halt step =>
      cases step with
      | machine fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | machine step tail =>
      cases step with
      | machine fetch executes =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
  | call step tail =>
      cases step with
      | call fetch inputRep valid =>
          change clientProgram[0]? = _ at fetch
          simp [clientProgram] at fetch
          rcases fetch with ⟨rfl, rfl, rfl, rfl⟩
          cases tail with
          | halt secondStep =>
              cases secondStep with
              | machine secondFetch secondExec =>
                  change clientProgram[1]? = _ at secondFetch
                  simp [clientProgram] at secondFetch
                  cases secondFetch
                  simp [UniformReal.execute] at secondExec
          | call secondStep secondTail =>
              cases secondStep with
              | call secondFetch secondRep secondValid =>
                  change clientProgram[1]? = _ at secondFetch
                  simp [clientProgram] at secondFetch
          | @machine secondConfiguration nextConfiguration finalMemory finalResult
              secondHeadCost secondTailCost secondSteps secondDraws secondCalls
              secondStep secondTail =>
              cases secondStep with
              | machine secondFetch secondExec =>
                  change clientProgram[1]? = _ at secondFetch
                  simp [clientProgram] at secondFetch
                  cases secondFetch
                  have nextPc : nextConfiguration.pc = 2 := by
                    have observedPc := congrArg (fun observation =>
                      match observation.outcome with
                      | .running configuration => configuration.pc
                      | _ => 0) secondExec
                    simpa [UniformReal.execute] using observedPc.symm
                  cases secondTail with
                  | halt finalStep =>
                      cases finalStep with
                      | machine finalFetch finalExec =>
                          rw [nextPc] at finalFetch
                          simp [clientProgram] at finalFetch
                          cases finalFetch
                          exact ⟨_, rfl, rfl⟩
                  | call finalStep finalTail =>
                      cases finalStep with
                      | call finalFetch finalRep finalValid =>
                          rw [nextPc] at finalFetch
                          simp [clientProgram] at finalFetch
                  | machine finalStep finalTail =>
                      cases finalStep with
                      | machine finalFetch finalExec =>
                          rw [nextPc] at finalFetch
                          simp [clientProgram] at finalFetch
                          cases finalFetch
                          simp [UniformReal.execute, UniformReal.liftCoreOutcome,
                            StructuredRealRAM.execute] at finalExec

def fixedOverhead : Cost := RandomizedIntegrationModule.fixedOverhead

def linkedBound : Nat → UniformReal.Cost := fun size ↦
  relativeBound size + RandomBit.Cost.ofCore fixedOverhead

theorem boundCovers :
    UniformRealLinker.BoundCovers clientCertificate implementations linkedBound := by
  intro source input final result cost steps draws calls validInput trace costBound
  rcases calls_singleton source input validInput final result cost steps draws calls trace with
    ⟨call, rfl, callSite⟩
  have overhead : Linker.concreteCallOverhead implementations call = fixedOverhead := by
    exact RandomizedIntegrationModule.concreteCallOverhead_zero call callSite
  simp only [Linker.totalConcreteCallOverhead, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, overhead, linkedBound]
  constructor
  · intro coordinate
    exact Nat.add_le_add_right (costBound.1 coordinate) (fixedOverhead coordinate)
  · exact Nat.add_le_add_right costBound.2 0

theorem linkedSuccessEvent_eq_univ (input : problem.Input) (validInput : problem.pre input) :
    problem.SuccessEvent
      (UniformRealLinker.link clientProgram implementations linkerConfiguration) input
      (linkedBound (problem.inputSize input)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  apply UniformRealLinker.successEvent_mono_of clientCertificate implementations
    linkerConfiguration linkedBound compatibility returnRegisterInitiallyZero boundCovers
    input validInput
  change source ∈ UniformRelativeSuccessEvent signature implementations.responder problem
    clientProgram relativeBound input
  rw [relativeSuccessEvent_eq_univ implementations.responder input validInput]
  trivial

def assumptions : UniformRealLinker.LinkingAssumptions clientCertificate implementations
    linkerConfiguration linkedBound where
  compatible := compatibility
  returnRegisterInitiallyZero := returnRegisterInitiallyZero
  boundCovers := boundCovers
  measurableSuccess input validInput := by
    change MeasurableSet (problem.SuccessEvent
      (UniformRealLinker.link clientProgram implementations linkerConfiguration) input
      (linkedBound (problem.inputSize input)))
    rw [linkedSuccessEvent_eq_univ input validInput]
    exact MeasurableSet.univ

noncomputable def linkedCertificate :
    problem.BoundedTimeMonteCarloAlgorithmCertificate linkedBound failure :=
  UniformRealLinker.certificate clientCertificate implementations linkerConfiguration
    linkedBound assumptions

theorem client_unconditional :
    problem.HasBoundedTimeMonteCarloAlgorithm linkedBound failure :=
  UniformRealLinker.hasBoundedTimeMonteCarloAlgorithm clientCertificate implementations
    linkerConfiguration linkedBound assumptions

/-- The deterministic callee is ordinary shared body syntax, not a one-step callback. -/
example :
    (UniformRealLinker.link clientProgram implementations linkerConfiguration)[
      Linker.operationBase (UniformRealLinker.placement clientProgram) implementations ()]? =
      some (.core (Linker.relocateInstruction
        (Linker.operationBase (UniformRealLinker.placement clientProgram) implementations ())
        (Linker.dispatcherBase (UniformRealLinker.placement clientProgram) implementations)
        (.halt (.literal 0)))) := by
  exact UniformRealLinker.bodyMaterialized clientProgram implementations linkerConfiguration
    (signature := signature) () 0 (.halt (.literal 0)) (by
      change dependencyProgram[0]? = some (.halt (.literal 0))
      simp [dependencyProgram,
      DependencyImplementationModule.dependencyProgram])

#print axioms client_unconditional

end UniformRealConcreteIntegration

end AlgoleanTests.StructuredRealRAMProcedureComposition
