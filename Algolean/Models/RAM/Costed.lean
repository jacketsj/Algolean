/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM

/-!
# Costed execution for finite RAM programs

This module couples the operational result of every machine transition to the resources charged
for that same transition.  It is deliberately additive: the existing unit-step interpreter in
`Algolean.Models.RAM` remains available for compatibility.

The public structured-algorithm API uses `HaltingTrace`, so functional correctness and resource
bounds cannot accidentally refer to unrelated executions.
-/

@[expose] public section

namespace Algolean.Algorithms.RAM

/-- The observable result and cost of one fetched instruction. -/
structure StepObservation (Value Address Cost : Type*) where
  /-- The operational result of the transition. -/
  outcome : StepResult Value Address
  /-- The resources charged by this exact transition. -/
  cost : Cost

/-- The observable result, accumulated cost, and actual transition count of a fuel-bounded run. -/
structure RunObservation (Value Address Cost : Type*) where
  /-- Halt, timeout, or stuck result of the run. -/
  outcome : RunResult Value Address
  /-- Sum of the costs returned by the transitions that were actually observed. -/
  cost : Cost
  /-- Number of fetched instructions, including a final halt or stuck fetch. -/
  steps : ℕ

/--
Run a costed step function for at most `fuel` transitions.

The transition itself returns both behavior and cost.  In particular, this runner has no second
interpreter from which it could obtain a resource bound.
-/
def runForCosted [AddMonoid Cost]
    (step : Configuration Value Address → StepObservation Value Address Cost) :
    ℕ → Configuration Value Address → RunObservation Value Address Cost
  | 0, configuration => ⟨.outOfFuel configuration, 0, 0⟩
  | fuel + 1, configuration =>
      let observation := step configuration
      match observation.outcome with
      | .running next =>
          let rest := runForCosted step fuel next
          ⟨rest.outcome, observation.cost + rest.cost, rest.steps + 1⟩
      | .halted memory result =>
          ⟨.halted memory result, observation.cost, 1⟩
      | .stuck stuck =>
          ⟨.stuck stuck, observation.cost, 1⟩

/--
A proof-relevant finite halting trace.  The final memory, result, accumulated cost, and step count
all arise from the same sequence of `step` observations.
-/
inductive HaltingTrace [Add Cost]
    (step : Configuration Value Address → StepObservation Value Address Cost) :
    Configuration Value Address → Memory Value Address → Value → Cost → ℕ → Prop where
  /-- The current instruction halts. -/
  | halt {configuration memory result cost}
      (observes : step configuration = ⟨.halted memory result, cost⟩) :
      HaltingTrace step configuration memory result cost 1
  /-- One running transition followed by a halting trace. -/
  | next {configuration nextConfiguration memory result headCost tailCost steps}
      (observes : step configuration = ⟨.running nextConfiguration, headCost⟩)
      (tail : HaltingTrace step nextConfiguration memory result tailCost steps) :
      HaltingTrace step configuration memory result (headCost + tailCost) (steps + 1)

/-- A costed semantics for the existing generic RAM instruction set. -/
structure CostedSemantics (Literal Value Address Extra Cost : Type*) where
  /-- Arithmetic and comparisons used by core instructions. -/
  ops : Ops Literal Value Address
  /-- Execute a closed extension instruction. -/
  executeExtra : Extra → Memory Value Address → Memory Value Address
  /-- Charge a fetched instruction, optionally as a function of the memory it observes. -/
  instructionCost : Instruction Literal Address Extra → Memory Value Address → Cost
  /-- Cost charged for an invalid program counter. -/
  stuckCost : Cost

namespace CostedSemantics

/-- Fetch and execute once, returning behavior and cost together. -/
def step [DecidableEq Address]
    (semantics : CostedSemantics Literal Value Address Extra Cost)
    (program : Program Literal Address Extra)
    (configuration : Configuration Value Address) : StepObservation Value Address Cost :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, semantics.stuckCost⟩
  | some instruction =>
      ⟨execute semantics.ops semantics.executeExtra instruction configuration.memory,
        semantics.instructionCost instruction configuration.memory⟩

/-- Run a generic costed RAM semantics for at most `fuel` transitions. -/
def runFor [DecidableEq Address] [AddMonoid Cost]
    (semantics : CostedSemantics Literal Value Address Extra Cost)
    (program : Program Literal Address Extra) (fuel : ℕ)
    (configuration : Configuration Value Address) : RunObservation Value Address Cost :=
  runForCosted (semantics.step program) fuel configuration

/-- The unit-cost wrapper for an existing uncosted RAM semantics. -/
def unit (ops : Ops Literal Value Address)
    (extra : Extra → Memory Value Address → Memory Value Address) :
    CostedSemantics Literal Value Address Extra ℕ where
  ops := ops
  executeExtra := extra
  instructionCost _ _ := 1
  stuckCost := 0

@[simp]
theorem unit_step_outcome [DecidableEq Address]
    (ops : Ops Literal Value Address)
    (extra : Extra → Memory Value Address → Memory Value Address)
    (program : Program Literal Address Extra) (configuration : Configuration Value Address) :
    ((unit ops extra).step program configuration).outcome =
      RAM.step ops extra program configuration := by
  simp only [CostedSemantics.step, unit, RAM.step]
  split <;> simp_all

/-- Costing the existing machine uniformly does not alter any fuel-bounded outcome. -/
theorem unit_runFor_outcome [DecidableEq Address]
    (ops : Ops Literal Value Address)
    (extra : Extra → Memory Value Address → Memory Value Address)
    (program : Program Literal Address Extra) (fuel : ℕ)
    (configuration : Configuration Value Address) :
    ((unit ops extra).runFor program fuel configuration).outcome =
      RAM.runFor ops extra program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel induction =>
      simp only [CostedSemantics.runFor, runForCosted, RAM.runFor]
      rw [unit_step_outcome]
      cases h : RAM.step ops extra program configuration with
      | running next =>
          simp only
          exact induction next
      | halted memory result => rfl
      | stuck stuck => rfl

end CostedSemantics

end Algolean.Algorithms.RAM
