/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.StructuredRealRAMProfiled

/-! # Closed arithmetic/randomness product-profile regressions -/

@[expose] public section

namespace AlgoleanTests.StructuredRealRAMProfiled

open Algolean Algorithms MeasureTheory
open Algorithms.StructuredRealRAM

def richArithmetic : ArithmeticProfile :=
  .combine .sqrt (.combine .expLog (.namedConstants [.pi]))

def deterministicProfile : ClosedMachineProfile := .deterministic richArithmetic
def uniformProfile : ClosedMachineProfile := .uniformReal richArithmetic

/-! Admission and isolation are kernel-visible propositions. -/

example : ¬ ArithmeticProfile.algebraic.AllowsUnary .sqrt := by
  simp [ArithmeticProfile.AllowsUnary]

example : richArithmetic.AllowsUnary .sqrt ∧ richArithmetic.AllowsUnary .log := by
  simp [richArithmetic, ArithmeticProfile.AllowsUnary]

example : (ArithmeticProfile.fixedRoots [3, 5]).AllowsUnary (.kthRoot 3) := by
  simp [ArithmeticProfile.AllowsUnary]

example : ¬ (ArithmeticProfile.fixedRoots [3, 5]).AllowsUnary (.kthRoot 4) := by
  simp [ArithmeticProfile.AllowsUnary]

example : ¬ richArithmetic.AllowsFloorToNat := by
  simp [richArithmetic, ArithmeticProfile.AllowsFloorToNat]

example : richArithmetic.AllowsConstant .pi ∧ ¬ richArithmetic.AllowsConstant .e := by
  simp [richArithmetic, ArithmeticProfile.AllowsConstant]

/-- There is no capability inclusion from square-root syntax back into the algebraic core. -/
example : ¬ ArithmeticProfile.sqrt.Includes .algebraic := by
  intro inclusion
  have := inclusion.unary .sqrt (by simp [ArithmeticProfile.AllowsUnary])
  simpa [ArithmeticProfile.AllowsUnary] using this

/-! Exact operation-sensitive cost of an actual halting trace. -/

def coreAdd (next : Nat) : ProfiledInstruction deterministicProfile :=
  .arithmetic (.core (.radd (.literal 0) (.literal 0) 0 next))

def rootZero (next : Nat) : ProfiledInstruction deterministicProfile :=
  .arithmetic (.unary .sqrt (by simp [deterministicProfile, richArithmetic,
    ArithmeticProfile.AllowsUnary]) (.literal 0) 0 next)

def logOne (next : Nat) : ProfiledInstruction deterministicProfile :=
  .arithmetic (.unary .log (by simp [deterministicProfile, richArithmetic,
    ArithmeticProfile.AllowsUnary]) (.literal 1) 0 next)

def piConstant (next : Nat) : ProfiledInstruction deterministicProfile :=
  .arithmetic (.namedConstant .pi (by simp [deterministicProfile, richArithmetic,
    ArithmeticProfile.AllowsConstant]) 0 next)

def haltZero : ProfiledInstruction deterministicProfile :=
  .arithmetic (.core (.halt (.literal 0)))

def costProgram : ProfiledProgram deterministicProfile :=
  [coreAdd 1, rootZero 2, rootZero 3, logOne 4, piConstant 5, haltZero]

def costProgramCharge : ProfiledCost :=
  (coreAdd 1).cost + ((rootZero 2).cost + ((rootZero 3).cost +
    ((logOne 4).cost + ((piConstant 5).cost + haltZero.cost))))

theorem writeReal_zero_empty : Memory.empty.writeReal 0 0 = Memory.empty := by
  unfold Memory.writeReal Memory.empty
  congr
  funext address
  simp

noncomputable def costProgramTrace :
    ∃ final result, ProfiledHaltingTrace costProgram ()
      (RandomBit.Configuration.initial Memory.empty) final result costProgramCharge 6 0 := by
  let piMemory := Memory.empty.writeReal 0 Real.pi
  refine ⟨piMemory, 0, ?_⟩
  apply ProfiledHaltingTrace.next (nextConfiguration := ⟨1, Memory.empty, 0⟩)
  · simp [profiledStep, costProgram, coreAdd, executeProfiled, executeArithmetic, execute,
      RealOperand.eval, writeReal_zero_empty, costProgramCharge, liftArithmeticOutcome,
      ProfiledInstruction.cost, ArithmeticInstruction.cost, RandomBit.Configuration.initial]
  · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨2, Memory.empty, 0⟩)
    · simp [profiledStep, costProgram, rootZero, executeProfiled, executeArithmetic,
        RealUnaryPrimitive.eval, RealOperand.eval, writeReal_zero_empty, liftArithmeticOutcome,
        ProfiledInstruction.cost, ArithmeticInstruction.cost]
    · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨3, Memory.empty, 0⟩)
      · simp [profiledStep, costProgram, rootZero, executeProfiled, executeArithmetic,
          RealUnaryPrimitive.eval, RealOperand.eval, writeReal_zero_empty, liftArithmeticOutcome,
          ProfiledInstruction.cost, ArithmeticInstruction.cost]
      · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨4, Memory.empty, 0⟩)
        · norm_num [profiledStep, costProgram, logOne, executeProfiled, executeArithmetic,
            RealUnaryPrimitive.eval, RealOperand.eval, writeReal_zero_empty, Real.log_one,
            liftArithmeticOutcome, ProfiledInstruction.cost, ArithmeticInstruction.cost]
        · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨5, piMemory, 0⟩)
          · simp [profiledStep, costProgram, piConstant, executeProfiled, executeArithmetic,
              NamedRealConstant.value, piMemory, liftArithmeticOutcome,
              ProfiledInstruction.cost, ArithmeticInstruction.cost]
          · apply ProfiledHaltingTrace.halt
            simp [profiledStep, costProgram, haltZero, executeProfiled, executeArithmetic,
              execute, RealOperand.eval, piMemory, liftArithmeticOutcome,
              ProfiledInstruction.cost, ArithmeticInstruction.cost]

theorem costProgram_exact_coordinates :
    costProgramCharge.randomDraws = 0 ∧
    costProgramCharge.arithmetic.count (.unary .sqrt) = 2 ∧
    costProgramCharge.arithmetic.count (.unary .log) = 1 ∧
    costProgramCharge.arithmetic.count (.namedConstant .pi) = 1 ∧
    costProgramCharge.steps = 6 := by
  decide

/-! Root semantics are characterized, not merely assigned an evaluator. -/

#check RealUnaryPrimitive.kthRoot_eval_pow
#check RealUnaryPrimitive.kthRoot_eval_result_nonnegative
#check RealUnaryPrimitive.kthRoot_eval_unique_nonnegative
#check RealUnaryPrimitive.kthRoot_eval_negative_odd

/-! Randomized guarantee structures have intentionally different proof fields. -/

#check ProfiledMachineProblem.LasVegasExpectedTimeCertificate.expectedBound_finite
#check ProfiledMachineProblem.LasVegasHighProbabilityTimeCertificate.terminatesAlmostSurely
#check ProfiledMachineProblem.ZeroErrorHighProbabilityBoundedTerminationCertificate.withinProbability
#check ProfiledMachineProblem.ApproximateSamplerCertificate.approximate
#check ProfiledMachineProblem.InputDistributionModel.law

/-- An advertised finite expected bound cannot equal top on a valid input. -/
theorem finiteExpectedBound_not_top
    (certificate : ProfiledMachineProblem.LasVegasExpectedTimeCertificate problem expectedBound)
    (input : problem.Input) (valid : problem.pre input) :
    expectedBound input ≠ ⊤ :=
  certificate.expectedBound_finite input valid

/-! Arithmetic embeddings compose only toward stronger closed capabilities. -/

def algebraicIntoRich : ArithmeticProfile.algebraic.Includes richArithmetic :=
  ArithmeticProfile.Includes.algebraic _

def deterministicIntoUniform :
    (ClosedMachineProfile.deterministic .algebraic).Embedding uniformProfile :=
  ClosedMachineProfile.Embedding.deterministicInto algebraicIntoRich .hiddenUniformReal

example (program : ProfiledProgram (ClosedMachineProfile.deterministic .algebraic))
    (valid : program.Valid) :
    (program.lift deterministicIntoUniform).Valid :=
  program.lift_valid deterministicIntoUniform valid

namespace MixedLink

def contract : ProcedureContract :=
  ProcedureContract.ofCanonical Unit Unit (fun _ ↦ True) (fun _ _ ↦ True)

def algebraicProfile : ClosedMachineProfile := .deterministic .algebraic

def procedureBound : ProfiledProcedureBound contract := fun _ ↦
  ProfiledCost.ofArithmetic
    (ArithmeticCost.ofCore (Instruction.halt (.literal 0)).cost)

def procedureProgram : ProfiledProgram algebraicProfile :=
  [.arithmetic (.core (.halt (.literal 0)))]

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
      have natEq : (fun address ↦
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
      change Memory.mk realMem (fun address ↦
          if address = region.natBase then 0
          else if address = region.natBase + 1 then 0
          else Layout.overwrite [] (region.natBase + 2) natMem address) natReg = _
      rw [natEq]

def algebraicProcedure :
    ProfiledRestoringProcedureCertificate algebraicProfile contract procedureBound where
  module := ⟨procedureProgram, 0⟩
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
      rcases List.getElem?_eq_some_iff.mp fetch with ⟨below, rfl⟩
      have : pc = 0 := by simpa [procedureProgram] using below
      subst pc
      simp [procedureProgram, ProfiledInstruction.successors,
        ArithmeticInstruction.successors, Instruction.successors] at member
    · simp [procedureProgram]
  output _ := ()
  outputCorrect _ _ := trivial
  correct input validInput initial represented source cursor := by
    cases input
    let run : ProfiledProcedureRun ⟨procedureProgram, 0⟩ source cursor initial := {
      final := initial
      result := 0
      cost := procedureBound ()
      steps := 1
      draws := cursor
      trace := .halt (by
        simp [profiledStep, procedureProgram, executeProfiled, executeArithmetic, execute,
          liftArithmeticOutcome, RealOperand.eval, procedureBound,
          ProfiledInstruction.cost, ArithmeticInstruction.cost]) }
    refine ⟨run, represented, le_rfl, ?_⟩
    exact ⟨fun _ _ _ _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  restoringCorrect input validInput initial represented source cursor := by
    cases input
    let run : ProfiledProcedureRun ⟨procedureProgram, 0⟩ source cursor initial := {
      final := initial
      result := 0
      cost := procedureBound ()
      steps := 1
      draws := cursor
      trace := .halt (by
        simp [profiledStep, procedureProgram, executeProfiled, executeArithmetic, execute,
          liftArithmeticOutcome, RealOperand.eval, procedureBound,
          ProfiledInstruction.cost, ArithmeticInstruction.cost]) }
    exact ⟨run, represented, le_rfl,
      (unit_writeAt_of_rep Layout.inputRegion initial represented).symm⟩

/-- A weaker algebraic procedure is lifted into the caller's richer arithmetic/randomness profile. -/
def uniformProcedure :
    ProfiledRestoringProcedureCertificate uniformProfile contract procedureBound :=
  algebraicProcedure.embedDeterministic (ArithmeticProfile.Includes.algebraic _)
    .hiddenUniformReal

/-- Same-profile implementation used by the concrete linker regression. -/
def uniformProcedureDirect :
    ProfiledRestoringProcedureCertificate uniformProfile contract procedureBound where
  module := ⟨[.arithmetic (.core (.halt (.literal 0)))], 0⟩
  calling := algebraicProcedure.calling
  callingRealizes := algebraicProcedure.callingRealizes
  valid := by
    constructor
    · intro pc instruction fetch target member
      rcases List.getElem?_eq_some_iff.mp fetch with ⟨below, rfl⟩
      have : pc = 0 := by simpa using below
      subst pc
      simp [ProfiledInstruction.successors, ArithmeticInstruction.successors,
        Instruction.successors] at member
    · simp
  output _ := ()
  outputCorrect _ _ := trivial
  correct input validInput initial represented source cursor := by
    cases input
    let run : ProfiledProcedureRun
        ⟨[.arithmetic (.core (.halt (.literal 0)))], 0⟩ source cursor initial := {
      final := initial
      result := 0
      cost := procedureBound ()
      steps := 1
      draws := cursor
      trace := .halt (by
        simp [profiledStep, executeProfiled, executeArithmetic, execute,
          liftArithmeticOutcome, RealOperand.eval, procedureBound,
          ProfiledInstruction.cost, ArithmeticInstruction.cost]) }
    refine ⟨run, represented, le_rfl, ?_⟩
    exact ⟨fun _ _ _ _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  restoringCorrect input validInput initial represented source cursor := by
    cases input
    let run : ProfiledProcedureRun
        ⟨[.arithmetic (.core (.halt (.literal 0)))], 0⟩ source cursor initial := {
      final := initial
      result := 0
      cost := procedureBound ()
      steps := 1
      draws := cursor
      trace := .halt (by
        simp [profiledStep, executeProfiled, executeArithmetic, execute,
          liftArithmeticOutcome, RealOperand.eval, procedureBound,
          ProfiledInstruction.cost, ArithmeticInstruction.cost]) }
    exact ⟨run, represented, le_rfl,
      (unit_writeAt_of_rep Layout.inputRegion initial represented).symm⟩

inductive Operation where
  | dependency
deriving DecidableEq, Fintype

def signature : ProfiledDependencySignature uniformProfile where
  Op := Operation
  finiteOp := inferInstance
  decEqOp := inferInstance
  contract _ := contract
  bound _ := procedureBound

def environment : ProfiledImplementationEnvironment signature where
  implementation _ := uniformProcedureDirect

def client : ProfiledOpenProgram signature :=
  [.call .dependency Layout.inputRegion Layout.inputRegion 1,
    .machine (.sampleUniform rfl 0 2),
    .machine (.arithmetic (.unary .sqrt (by simp [uniformProfile, richArithmetic,
      ClosedMachineProfile.uniformReal, ArithmeticProfile.AllowsUnary]) (.load 0) 0 3)),
    .machine (.arithmetic (.core (.halt (.literal 0))))]

def configuration : ProfiledLinker.Configuration := ⟨7⟩

theorem operations_eq : ProfiledLinker.operations signature = [.dependency] := by
  have univEq : (Finset.univ : Finset Operation) = {.dependency} := by
    apply Finset.ext
    intro operation
    cases operation
    simp
  unfold ProfiledLinker.operations
  change (Finset.univ : Finset Operation).toList = [.dependency]
  rw [univEq]
  exact Finset.toList_singleton _

theorem codeBefore_eq :
    ProfiledLinker.codeBefore environment (ProfiledLinker.operations signature)
      .dependency = 0 := by
  rw [operations_eq]
  simp [ProfiledLinker.codeBefore]

theorem implementationCodeSize_eq :
    ProfiledLinker.implementationCodeSize environment = 1 := by
  simp [ProfiledLinker.implementationCodeSize, operations_eq, environment,
    uniformProcedureDirect]

theorem operationBase_eq :
    ProfiledLinker.operationBase client environment .dependency = 4 := by
  simp [ProfiledLinker.operationBase, codeBefore_eq, client]

theorem dispatcherBase_eq :
    ProfiledLinker.dispatcherBase client environment = 5 := by
  simp [ProfiledLinker.dispatcherBase, implementationCodeSize_eq, client]

def expectedLinkedProgram : ProfiledProgram uniformProfile :=
  [.arithmetic (.core (.nset (.literal 0) 7 4)),
    .sampleUniform rfl 0 2,
    .arithmetic (.unary .sqrt (by simp [uniformProfile, richArithmetic,
      ClosedMachineProfile.uniformReal, ArithmeticProfile.AllowsUnary]) (.load 0) 0 3),
    .arithmetic (.core (.halt (.literal 0))),
    .arithmetic (.core (.jump 5)),
    .arithmetic (.core (.ncompare (.reg 7) (.literal 0) 7 6 7)),
    .arithmetic (.core (.nset (.literal 0) 7 1)),
    .arithmetic (.core (.ncompare (.reg 7) (.literal 1) 9 8 9)),
    .arithmetic (.core (.nset (.literal 0) 7 9)),
    .arithmetic (.core (.ncompare (.reg 7) (.literal 2) 11 10 11)),
    .arithmetic (.core (.nset (.literal 0) 7 11)),
    .arithmetic (.core (.ncompare (.reg 7) (.literal 3) 13 12 13)),
    .arithmetic (.core (.nset (.literal 0) 7 13)),
    .arithmetic (.core (.halt (.literal 0)))]

theorem linkedProgram_eq :
    ProfiledLinker.link client environment configuration = expectedLinkedProgram := by
  have lengthEq : (ProfiledLinker.link client environment configuration).length = 14 := by
    rw [ProfiledLinker.link_length]
    simp [client, implementationCodeSize_eq]
  apply List.ext_getElem (by simpa [expectedLinkedProgram] using lengthEq)
  intro index leftInRange rightInRange
  have indexBelow : index < 14 := by simpa [expectedLinkedProgram] using rightInRange
  interval_cases index <;>
    simp [ProfiledLinker.link, ProfiledLinker.clientCode, ProfiledLinker.dispatcherCode,
      ProfiledLinker.dispatcherEntries, ProfiledLinker.dispatcherInstruction,
      ProfiledLinker.dispatcherCleanup, ProfiledLinker.implementationBody,
      ProfiledLinker.operationBase, ProfiledLinker.dispatcherBase,
      ProfiledLinker.implementationCodeSize, ProfiledLinker.codeBefore,
      ProfiledLinker.relocateInstruction, ProfiledLinker.relocateArithmeticInstruction,
      Linker.relocateInstruction,
      ProfiledLinker.clientInstruction, client, environment, configuration,
      expectedLinkedProgram, uniformProcedureDirect, operations_eq, codeBefore_eq,
      implementationCodeSize_eq, operationBase_eq, dispatcherBase_eq]

theorem writeReg_zero_empty (register : Nat) :
    Memory.empty.writeReg register 0 = Memory.empty := by
  unfold Memory.writeReg Memory.empty
  congr
  funext index
  simp

def linkedCharge : ProfiledCost :=
  (ProfiledInstruction.arithmetic (.core (.nset (.literal 0) 7 4)) :
      ProfiledInstruction uniformProfile).cost +
    ((ProfiledInstruction.arithmetic (.core (.jump 5)) :
        ProfiledInstruction uniformProfile).cost +
      ((ProfiledInstruction.arithmetic
          (.core (.ncompare (.reg 7) (.literal 0) 7 6 7)) :
          ProfiledInstruction uniformProfile).cost +
        ((ProfiledInstruction.arithmetic (.core (.nset (.literal 0) 7 1)) :
            ProfiledInstruction uniformProfile).cost +
          ((ProfiledInstruction.sampleUniform rfl 0 2 :
              ProfiledInstruction uniformProfile).cost +
            ((ProfiledInstruction.arithmetic (.unary .sqrt (by
                simp [uniformProfile, richArithmetic, ClosedMachineProfile.uniformReal,
                  ArithmeticProfile.AllowsUnary]) (.load 0) 0 3) :
                ProfiledInstruction uniformProfile).cost +
              (ProfiledInstruction.arithmetic (.core (.halt (.literal 0))) :
                ProfiledInstruction uniformProfile).cost)))))

/--
The concrete linked trace executes the callee jump, dispatcher, exact-uniform sample, and square
root.  The one hidden cursor and the complete operation-sensitive cost travel through that trace.
-/
noncomputable def mixedFinal (source : uniformProfile.randomness.Source) : Memory :=
  (Memory.empty.writeReal 0 (source 0 : Real)).writeReal 0
    (Real.sqrt (source 0 : Real))

noncomputable def mixedLinkedTrace (source : uniformProfile.randomness.Source) :
    ProfiledHaltingTrace (ProfiledLinker.link client environment configuration) source
      (RandomBit.Configuration.initial Memory.empty) (mixedFinal source) 0 linkedCharge 7 1 := by
  rw [linkedProgram_eq]
  let sample := (source 0 : Real)
  let sampled := Memory.empty.writeReal 0 sample
  let rooted := sampled.writeReal 0 (Real.sqrt sample)
  have nonnegative : 0 ≤ sample := (source 0).property.1
  change ProfiledHaltingTrace expectedLinkedProgram source
    (RandomBit.Configuration.initial Memory.empty) rooted 0 linkedCharge 7 1
  apply ProfiledHaltingTrace.next (nextConfiguration := ⟨4, Memory.empty, 0⟩)
  · simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic, execute,
      liftArithmeticOutcome, RealOperand.eval, ProfiledInstruction.cost,
      ArithmeticInstruction.cost, linkedCharge, RandomBit.Configuration.initial,
      writeReg_zero_empty, NatOperand.eval]
  · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨5, Memory.empty, 0⟩)
    · simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic, execute,
        liftArithmeticOutcome, RealOperand.eval, ProfiledInstruction.cost,
        ArithmeticInstruction.cost]
    · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨6, Memory.empty, 0⟩)
      · simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic, execute,
          liftArithmeticOutcome, NatOperand.eval, ProfiledInstruction.cost,
          ArithmeticInstruction.cost, branch]
      · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨1, Memory.empty, 0⟩)
        · simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic, execute,
            liftArithmeticOutcome, NatOperand.eval, ProfiledInstruction.cost,
            ArithmeticInstruction.cost, writeReg_zero_empty]
        · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨2, sampled, 1⟩)
          · rfl
          · apply ProfiledHaltingTrace.next (nextConfiguration := ⟨3, rooted, 1⟩)
            · have loaded : RealOperand.eval sampled (.load 0) = sample := by
                simp [RealOperand.eval, sampled, Memory.writeReal, Memory.empty]
              have sampledAddress : sampled.natReg 0 = 0 := by
                simp [sampled, Memory.writeReal, Memory.empty]
              have rootEval : RealUnaryPrimitive.eval .sqrt sample = some (Real.sqrt sample) := by
                simp [RealUnaryPrimitive.eval, not_lt.mpr nonnegative]
              simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic,
                loaded, rootEval, rooted, liftArithmeticOutcome,
                ProfiledInstruction.cost, ArithmeticInstruction.cost, client, sampledAddress]
            · apply ProfiledHaltingTrace.halt
              simp [profiledStep, expectedLinkedProgram, executeProfiled, executeArithmetic,
                execute, liftArithmeticOutcome, RealOperand.eval,
                ProfiledInstruction.cost, ArithmeticInstruction.cost]

theorem mixedLinked_exact_coordinates :
    linkedCharge.randomDraws = 1 ∧
    linkedCharge.arithmetic.count (.unary .sqrt) = 1 ∧
    linkedCharge.steps = 7 := by
  decide

theorem implementationBody_shared_once :
    (ProfiledLinker.implementationBody client environment .dependency).length =
      uniformProcedureDirect.module.code.length :=
  ProfiledLinker.implementationBody_length client environment .dependency

def problem : ProfiledMachineProblem uniformProfile where
  Input := Unit
  Output := Unit
  inputLayout := .unit
  outputLayout := .unit
  outputRegion := Layout.inputRegion
  pre _ := True
  post _ _ := True

def bound : problem.Input → ProfiledCost := fun _ ↦ linkedCharge
def failure : problem.Input → Probability := fun _ ↦ ⟨0, by simp⟩

theorem linkedValid :
    (ProfiledLinker.link client environment configuration).Valid := by
  rw [linkedProgram_eq]
  intro pc instruction fetch target member
  rcases List.getElem?_eq_some_iff.mp fetch with ⟨below, rfl⟩
  have pcBelow : pc < 14 := by simpa [expectedLinkedProgram] using below
  interval_cases pc <;>
    simp [expectedLinkedProgram, ProfiledInstruction.successors,
      ArithmeticInstruction.successors, Instruction.successors] at member ⊢ <;> omega

theorem initialMemory_eq_empty : problem.initialMemory () = Memory.empty := by
  unfold ProfiledMachineProblem.initialMemory Layout.init Layout.initAt
  change Memory.mk (Layout.place [] 0) (fun address ↦
    if address = 0 then 0 else if address = 1 then 0 else Layout.place [] 2 address)
      (fun _ ↦ 0) = Memory.empty
  congr 1
  · funext address
    simp [Layout.place]

theorem unitRep_after_mixed_write (source : uniformProfile.randomness.Source) :
    problem.OutputRep () (mixedFinal source) := by
  simp [ProfiledMachineProblem.OutputRep, problem, Layout.RepAt, Layout.encode,
    Layout.readReals, Layout.readNats, Memory.writeReal, Memory.empty, mixedFinal]

theorem successEvent_eq_univ :
    problem.SuccessEvent (ProfiledLinker.link client environment configuration) bound () =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro source
  have trace := mixedLinkedTrace source
  rw [← initialMemory_eq_empty] at trace
  let run : problem.SuccessfulRun
      (ProfiledLinker.link client environment configuration) source () := {
    final := mixedFinal source
    result := 0
    cost := linkedCharge
    steps := 7
    draws := 1
    trace := trace }
  refine ⟨run, (), ?_, trivial, le_rfl⟩
  exact unitRep_after_mixed_write source

noncomputable def boundedTimeMonteCarlo :
    ProfiledMachineProblem.BoundedTimeMonteCarloCertificate problem bound failure where
  hasRandomness := by simp [uniformProfile, ClosedMachineProfile.uniformReal]
  program := ProfiledLinker.link client environment configuration
  valid := linkedValid
  terminatesWithin input validInput source := by
    cases input
    have success := Set.eq_univ_iff_forall.mp successEvent_eq_univ source
    rcases success with ⟨run, output, outputRep, correct, costBound⟩
    exact ⟨run, costBound⟩
  successMeasurable input validInput := by
    cases input
    rw [successEvent_eq_univ]
    exact MeasurableSet.univ
  successProbability input validInput := by
    cases input
    rw [successEvent_eq_univ]
    change UniformReal.sourceLaw Set.univ ≥ 1 - 0
    simp

theorem boundedTimeMonteCarlo_one_sample :
    boundedTimeMonteCarlo.program =
      ProfiledLinker.link client environment configuration ∧
    linkedCharge.randomDraws = 1 := by
  exact ⟨rfl, mixedLinked_exact_coordinates.1⟩

end MixedLink

end AlgoleanTests.StructuredRealRAMProfiled
