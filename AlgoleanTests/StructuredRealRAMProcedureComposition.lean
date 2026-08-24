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
    callOverhead := 0
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

end AlgoleanTests.StructuredRealRAMProcedureComposition
