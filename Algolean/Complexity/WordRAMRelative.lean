/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMProcedure

/-!
# Contract-relative Word-RAM modules

Relative calls are finite first-order syntax.  Their semantics reads and writes only through
closed layouts, quantifies over every contract-correct responder, charges the declared call bound,
and records every structured call.  Relative certificates are intentionally not coercible to
unconditional machine certificates.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- A finite typed signature of abstract procedure dependencies. -/
structure DependencySignature (w : ℕ) where
  Op : Type
  finiteOp : Fintype Op
  decEqOp : DecidableEq Op
  contract : Op → ProcedureContract w
  bound : (op : Op) → ProcedureBound (contract op)
  /-- Fixed call/return ABI overhead; implementations may not select another value. -/
  callOverhead : Op → Nat

attribute [instance] DependencySignature.finiteOp DependencySignature.decEqOp

/-- One coherent contract-level answer source for a complete relative execution. -/
structure AdmissibleResponder (signature : DependencySignature w) where
  answer : (op : signature.Op) →
    (input : (signature.contract op).Input) → (signature.contract op).Output
  correct : ∀ op input, (signature.contract op).pre input →
    (signature.contract op).post input (answer op input)

/-- A typed record of one actual abstract call. -/
structure DependencyCallRecord (signature : DependencySignature w) where
  callSite : Nat
  op : signature.Op
  input : (signature.contract op).Input
  output : (signature.contract op).Output
  outputCorrect : (signature.contract op).post input output
  chargedCost : ℕ
  chargedCost_eq : chargedCost = signature.bound op input + 1

/-- Closed first-order open-module instructions. -/
inductive OpenInstruction (signature : DependencySignature w) where
  | core (instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w))
  | call (op : signature.Op) (inputRegion outputRegion : Region w) (next : ℕ)

/-- A finite relative program with no host-language continuation or implementation. -/
abbrev OpenProgram (signature : DependencySignature w) := List (OpenInstruction signature)

namespace OpenInstruction

def successors : OpenInstruction signature → List ℕ
  | .core instruction => RAM.Instruction.successors instruction
  | .call _ _ _ next => [next]

end OpenInstruction

/-- Every explicit successor of an open program is in bounds. -/
def OpenProgram.Valid (program : OpenProgram signature) : Prop :=
  ∀ (pc : ℕ) (instruction : OpenInstruction signature),
    program[pc]? = some instruction →
    ∀ target ∈ OpenInstruction.successors instruction, target < program.length

/-- One relational transition, including an optional typed call record. -/
inductive OpenStep (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (program : OpenProgram signature) :
    Configuration w → RAM.StepResult (BitVec w) (BitVec w) → ℕ →
      Option (DependencyCallRecord signature) → Prop where
  | core {configuration instruction outcome}
      (fetch : program[configuration.pc]? = some (.core instruction))
      (execute : RAM.execute (ops w) WordRAM.evalExtra instruction configuration.memory = outcome) :
      OpenStep signature responder program configuration outcome 1 none
  | call {configuration op inputRegion outputRegion next input}
      (fetch : program[configuration.pc]? = some (.call op inputRegion outputRegion next))
      (inputRep : (signature.contract op).inputLayout.RepAt
        inputRegion input configuration.memory)
      (validInput : (signature.contract op).pre input) :
      OpenStep signature responder program configuration
        (.running ⟨next, (signature.contract op).outputLayout.writeAt
          outputRegion (responder.answer op input) configuration.memory⟩)
        (signature.bound op input + 1)
        (some {
          callSite := configuration.pc
          op := op
          input := input
          output := responder.answer op input
          outputCorrect := responder.correct op input validInput
          chargedCost := signature.bound op input + 1
          chargedCost_eq := rfl })

/-- Same-trace relative execution accumulating exact cost and call sequence. -/
inductive OpenHaltingTrace (signature : DependencySignature w)
    (responder : AdmissibleResponder signature) (program : OpenProgram signature) :
    Configuration w → Memory w → BitVec w → ℕ →
      List (DependencyCallRecord signature) → Prop where
  | halt {configuration memory result cost call}
      (step : OpenStep signature responder program configuration
        (.halted memory result) cost call) :
      OpenHaltingTrace signature responder program configuration memory result cost
        call.toList
  | next {configuration nextConfiguration memory result headCost tailCost headCall calls}
      (step : OpenStep signature responder program configuration
        (.running nextConfiguration) headCost headCall)
      (tail : OpenHaltingTrace signature responder program nextConfiguration
        memory result tailCost calls) :
      OpenHaltingTrace signature responder program configuration memory result
        (headCost + tailCost) (headCall.toList ++ calls)

/-- Every recorded call consumes at least its explicit one-step abstract dispatch charge. -/
theorem OpenHaltingTrace.calls_length_le_cost
    (trace : OpenHaltingTrace signature responder program initial final result cost calls) :
    calls.length ≤ cost := by
  induction trace with
  | halt step =>
      cases step
      all_goals simp
  | next step tail ih =>
      cases step <;> simp_all <;> omega

/-- Every dynamic call record names an actual in-range call instruction. -/
theorem OpenHaltingTrace.callSite_lt
    (trace : OpenHaltingTrace signature responder program initial final result cost calls)
    (call : DependencyCallRecord signature) (member : call ∈ calls) :
    call.callSite < program.length := by
  induction trace with
  | halt step =>
      cases step with
      | core => simp at member
  | next step tail ih =>
      cases step with
      | core => simpa using ih member
      | call fetch inputRep validInput =>
          simp only [Option.toList_some, List.singleton_append, List.mem_cons] at member
          rcases member with rfl | member
          · exact List.getElem?_eq_some_iff.mp fetch |>.1
          · exact ih member

/-- Total declared dependency cost exposed from a typed call trace. -/
def totalDependencyCost (calls : List (DependencyCallRecord signature)) : ℕ :=
  (calls.map (fun call => call.chargedCost)).sum

/-- Sum of the dependency bounds before the explicit one-step abstract-call dispatch charge. -/
def totalDeclaredDependencyCost (calls : List (DependencyCallRecord signature)) : ℕ :=
  (calls.map (fun call ↦ signature.bound call.op call.input)).sum

/-- Exact decomposition into declared callee work and one unit of dispatch per call. -/
theorem totalDependencyCost_eq (calls : List (DependencyCallRecord signature)) :
    totalDependencyCost calls = totalDeclaredDependencyCost calls + calls.length := by
  induction calls with
  | nil => rfl
  | cons call calls ih =>
      simp only [totalDependencyCost, totalDeclaredDependencyCost, List.map_cons,
        List.sum_cons, List.length_cons] at ih ⊢
      rw [call.chargedCost_eq, ih]
      omega

/-- Number of dynamic calls to one typed operation. -/
def dependencyCallCount (op : signature.Op)
    (calls : List (DependencyCallRecord signature)) : ℕ :=
  (calls.filter fun call ↦ call.op = op).length

/-- Total represented input footprint of all calls, retaining actual dynamic call sizes. -/
def totalCallInputFootprint (calls : List (DependencyCallRecord signature)) : ℕ :=
  (calls.map fun call ↦
    (signature.contract call.op).inputLayout.footprintWords call.input).sum

/-- Maximum represented input footprint among dynamic calls. -/
def maximumCallInputFootprint : List (DependencyCallRecord signature) → ℕ
  | [] => 0
  | call :: calls => max
      ((signature.contract call.op).inputLayout.footprintWords call.input)
      (maximumCallInputFootprint calls)

/-- Pointwise larger call charges yield a larger exact sum; no opaque call counter is used. -/
theorem sumCallCost_mono (calls : List (DependencyCallRecord signature))
    (oldCost newCost : (call : DependencyCallRecord signature) → ℕ)
    (larger : ∀ call, oldCost call ≤ newCost call) :
    (calls.map oldCost).sum ≤ (calls.map newCost).sum := by
  induction calls with
  | nil => simp
  | cons call calls ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (larger call) ih

/-- Every individual call footprint is bounded by the reported maximum. -/
theorem callInputFootprint_le_maximum (calls : List (DependencyCallRecord signature))
    (call : DependencyCallRecord signature) (member : call ∈ calls) :
    (signature.contract call.op).inputLayout.footprintWords call.input ≤
      maximumCallInputFootprint calls := by
  induction calls with
  | nil => simp at member
  | cons head tail ih =>
      rw [List.mem_cons] at member
      simp only [maximumCallInputFootprint]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact (ih member).trans (Nat.le_max_right _ _)

/-- A relative problem certificate, visibly distinct from a concrete fixed-machine certificate. -/
structure RelativeAlgorithmCertificate (signature : DependencySignature w)
    (problem : StructuredProblem w) (bound : problem.Input → ℕ) where
  program : OpenProgram signature
  valid : program.Valid
  solvesAgainstContracts : ∀ responder : AdmissibleResponder signature,
    ∀ input, ∀ validInput : problem.pre input,
      ∃ final result cost calls output,
        OpenHaltingTrace signature responder program
          ⟨0, problem.initialMemory input validInput⟩ final result cost calls ∧
        problem.OutputRep output final ∧ problem.post input output ∧ cost ≤ bound input

/-- Concrete certified implementations for every operation in a finite signature. -/
structure ImplementationEnvironment (signature : DependencySignature w) where
  implementation : (op : signature.Op) →
    RestoringProcedureCertificate (signature.contract op) (signature.bound op)
  callingOverhead_eq : ∀ op,
    (implementation op).calling.callOverhead = signature.callOverhead op

namespace ImplementationEnvironment

/-- The coherent responder canonically induced by deterministic certified implementations. -/
def responder (environment : ImplementationEnvironment signature) :
    AdmissibleResponder signature where
  answer op input := (environment.implementation op).output input
  correct op input validInput :=
    (environment.implementation op).outputCorrect input validInput

end ImplementationEnvironment

/-- Existence of every dependency implementation, without pretending the client is linked yet. -/
def HasImplementations (signature : DependencySignature w) : Prop :=
  Nonempty (ImplementationEnvironment signature)

end

end Algolean.Algorithms.WordRAM
