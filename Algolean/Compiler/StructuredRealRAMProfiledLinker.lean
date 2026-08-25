/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.StructuredRealRAMProfiledRelative
public import Algolean.Compiler.StructuredRealRAMLinker

/-! # Shared-body linker for closed-profile structured exact-real procedures -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.ProfiledLinker

open MeasureTheory
noncomputable section

variable {profile : ClosedMachineProfile}

structure Configuration where
  returnRegister : Nat

def operations (signature : ProfiledDependencySignature profile) : List signature.Op :=
  Finset.univ.toList

def codeBefore {signature : ProfiledDependencySignature profile}
    (environment : ProfiledImplementationEnvironment signature) :
    List signature.Op → signature.Op → Nat
  | [], _ => 0
  | current :: rest, op =>
      if current = op then 0
      else (environment.implementation current).module.code.length +
        codeBefore environment rest op

def implementationCodeSize {signature : ProfiledDependencySignature profile}
    (environment : ProfiledImplementationEnvironment signature) : Nat :=
  ((operations signature).map fun op ↦
    (environment.implementation op).module.code.length).sum

def operationBase {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature) (op : signature.Op) : Nat :=
  client.length + codeBefore environment (operations signature) op

def dispatcherBase {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature) : Nat :=
  client.length + implementationCodeSize environment

def relocateArithmeticInstruction (base dispatcher : Nat) :
    ArithmeticInstruction arithmetic → ArithmeticInstruction arithmetic
  | .core instruction => .core (Linker.relocateInstruction base dispatcher instruction)
  | .unary primitive allowed source destination next =>
      .unary primitive allowed source destination (base + next)
  | .floorToNat allowed source destination next =>
      .floorToNat allowed source destination (base + next)
  | .namedConstant constant allowed destination next =>
      .namedConstant constant allowed destination (base + next)

def relocateInstruction (base dispatcher : Nat) :
    ProfiledInstruction profile → ProfiledInstruction profile
  | .arithmetic instruction =>
      .arithmetic (relocateArithmeticInstruction base dispatcher instruction)
  | .randBit allowed destination next => .randBit allowed destination (base + next)
  | .sampleUniform allowed destination next =>
      .sampleUniform allowed destination (base + next)

def implementationBody {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (op : signature.Op) : ProfiledProgram profile :=
  let base := operationBase client environment op
  let dispatcher := dispatcherBase client environment
  (environment.implementation op).module.code.map (relocateInstruction base dispatcher)

def clientInstruction {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (pc : Nat) :
    ProfiledOpenInstruction signature → ProfiledInstruction profile
  | .machine instruction => instruction
  | .call op _ _ _ =>
      .arithmetic (.core (.nset (.literal pc) configuration.returnRegister
        (operationBase client environment op + (environment.implementation op).module.entry)))

def clientCode {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) : ProfiledProgram profile :=
  client.zipIdx.map fun (instruction, pc) ↦
    clientInstruction client environment configuration pc instruction

def dispatcherInstruction (configuration : Configuration) (position pc : Nat) :
    ProfiledInstruction profile :=
  .arithmetic (.core (.ncompare (.reg configuration.returnRegister) (.literal pc)
    (position + 2) (position + 1) (position + 2)))

def dispatcherCleanup {signature : ProfiledDependencySignature profile}
    (configuration : Configuration) (position : Nat) :
    ProfiledOpenInstruction signature → ProfiledInstruction profile
  | .machine _ =>
      .arithmetic (.core (.nset (.literal 0) configuration.returnRegister (position + 1)))
  | .call _ _ _ next =>
      .arithmetic (.core (.nset (.literal 0) configuration.returnRegister next))

def dispatcherEntries {signature : ProfiledDependencySignature profile}
    (configuration : Configuration) (base pc : Nat) :
    ProfiledOpenProgram signature → ProfiledProgram profile
  | [] => []
  | instruction :: rest =>
      let position := base + 2 * pc
      dispatcherInstruction configuration position pc ::
        dispatcherCleanup configuration (position + 1) instruction ::
        dispatcherEntries configuration base (pc + 1) rest

def dispatcherCode {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) : ProfiledProgram profile :=
  dispatcherEntries configuration (dispatcherBase client environment) 0 client ++
    [.arithmetic (.core (.halt (.literal 0)))]

/-- Concrete finite code; every implementation body is emitted exactly once. -/
def link {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) : ProfiledProgram profile :=
  clientCode client environment configuration ++
    (operations signature).flatMap (implementationBody client environment) ++
    dispatcherCode client environment configuration

theorem clientCode_length {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) :
    (clientCode client environment configuration).length = client.length := by
  simp [clientCode]

theorem implementationBody_length {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature) (op : signature.Op) :
    (implementationBody client environment op).length =
      (environment.implementation op).module.code.length := by
  simp [implementationBody]

theorem dispatcherEntries_length {signature : ProfiledDependencySignature profile}
    (configuration : Configuration) (base pc : Nat)
    (client : ProfiledOpenProgram signature) :
    (dispatcherEntries configuration base pc client).length = 2 * client.length := by
  induction client generalizing pc with
  | nil => rfl
  | cons instruction rest induction => simp [dispatcherEntries, induction, Nat.mul_add]

theorem link_length {signature : ProfiledDependencySignature profile}
    (client : ProfiledOpenProgram signature)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) :
    (link client environment configuration).length =
      3 * client.length + implementationCodeSize environment + 1 := by
  simp [link, dispatcherCode, clientCode_length, dispatcherEntries_length,
    implementationCodeSize, implementationBody_length]
  omega

/--
Machine-only refinement tied definitionally to the emitted shared-body program.  It simulates an
open trace without restating the client's mathematical correctness proof: final memory, result,
source cursor, and draw count are preserved, and only explicit linker overhead is added.
-/
structure Refinement {signature : ProfiledDependencySignature profile}
    (client : ProfiledRelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (linkedBound : problem.Input → ProfiledCost) where
  returnRegisterInitiallyZero : ∀ input,
    (problem.initialMemory input).natReg configuration.returnRegister = 0
  linkedValid : (link client.module environment configuration).Valid
  overhead : List (ProfiledDependencyCallRecord signature) → ProfiledCost
  refineTrace : ∀ source initial final result cost steps draws calls,
    ProfiledOpenHaltingTrace signature environment.responder client.module source initial
      final result cost steps draws calls →
    ∃ linkedCost linkedSteps,
      ProfiledHaltingTrace (link client.module environment configuration) source initial
        final result linkedCost linkedSteps draws ∧
      linkedCost ≤ cost + overhead calls
  overheadBound : ∀ input cost calls,
    cost ≤ relativeBound input → cost + overhead calls ≤ linkedBound input

def ProfiledRelativeAlgorithmCertificate.link
    {signature : ProfiledDependencySignature profile}
    (client : ProfiledRelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (linkedBound : problem.Input → ProfiledCost)
    (refinement : Refinement client environment configuration linkedBound) :
    ProfiledMachineProblem.FixedAlgorithmCertificateBy problem linkedBound where
  program := ProfiledLinker.link client.module environment configuration
  valid := refinement.linkedValid
  solves input validInput source := by
    rcases client.solvesAgainstContracts environment.responder input validInput source with
      ⟨output, final, result, cost, steps, draws, calls, trace, outputRep, correct, costBound⟩
    rcases refinement.refineTrace source _ final result cost steps draws calls trace with
      ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
    refine ⟨{
      final := final
      result := result
      cost := linkedCost
      steps := linkedSteps
      draws := draws
      trace := linkedTrace }, output, outputRep, correct, ?_⟩
    exact linkedCostBound.trans
      (refinement.overheadBound input cost calls costBound)

theorem ProfiledRelativeAlgorithmCertificate.hasAlgorithm
    {signature : ProfiledDependencySignature profile}
    (client : ProfiledRelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (linkedBound : problem.Input → ProfiledCost)
    (refinement : Refinement client environment configuration linkedBound) :
    problem.HasAlgorithmBy linkedBound :=
  ⟨ProfiledRelativeAlgorithmCertificate.link client environment configuration
    linkedBound refinement⟩

/-- Same-source obligations for bounded-time Monte Carlo linking. -/
structure BoundedTimeMonteCarloRefinement
    {signature : ProfiledDependencySignature profile}
    {problem : ProfiledMachineProblem profile}
    {relativeBound : problem.Input → ProfiledCost}
    {failure : problem.Input → Probability}
    (client : ProfiledBoundedTimeMonteCarloRelativeCertificate
      signature problem relativeBound failure)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (linkedBound : problem.Input → ProfiledCost) : Prop where
  linkedValid : (link client.program environment configuration).Valid
  terminates : ∀ input, problem.pre input → ∀ source,
    source ∈ problem.TerminationWithinEvent
      (link client.program environment configuration) linkedBound input
  successEvent_mono : ∀ input, problem.pre input →
    ProfiledRelativeSuccessEvent signature environment.responder problem
      client.program relativeBound input ⊆
      problem.SuccessEvent (link client.program environment configuration) linkedBound input
  successMeasurable : ∀ input, problem.pre input →
    MeasurableSet
      (problem.SuccessEvent (link client.program environment configuration) linkedBound input)

noncomputable def ProfiledBoundedTimeMonteCarloRelativeCertificate.link
    {signature : ProfiledDependencySignature profile}
    {problem : ProfiledMachineProblem profile}
    {relativeBound : problem.Input → ProfiledCost}
    {failure : problem.Input → Probability}
    (client : ProfiledBoundedTimeMonteCarloRelativeCertificate
      signature problem relativeBound failure)
    (environment : ProfiledImplementationEnvironment signature)
    (configuration : Configuration) (linkedBound : problem.Input → ProfiledCost)
    (refinement : BoundedTimeMonteCarloRefinement client environment configuration linkedBound) :
    ProfiledMachineProblem.BoundedTimeMonteCarloCertificate problem linkedBound failure where
  hasRandomness := client.hasRandomness
  program := ProfiledLinker.link client.program environment configuration
  valid := refinement.linkedValid
  terminatesWithin := refinement.terminates
  successMeasurable := refinement.successMeasurable
  successProbability input validInput :=
    (client.successProbability environment.responder input validInput).trans
      (measure_mono (refinement.successEvent_mono input validInput))

end

end Algolean.Algorithms.StructuredRealRAM.ProfiledLinker
