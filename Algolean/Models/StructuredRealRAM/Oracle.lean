/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Layout

/-!
# Auditable oracle contracts

This module defines the typed, layout-aware contract needed before an oracle instruction can be
added to a named machine profile.  It intentionally does not represent an oracle as an arbitrary
memory transformer.  Query cost is named, answer-transfer cells are derived from the closed layout,
and non-vacuity is a separate property.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- A closed typed query/answer interface with canonical memory layouts. -/
structure OracleInterface (Cost : Type w) where
  /-- Query carrier. -/
  Query : Type
  /-- Query-dependent answer carrier. -/
  Answer : Query → Type
  /-- Closed canonical query layout. -/
  queryLayout : Layout Query
  /-- Closed canonical answer layout for each query. -/
  answerLayout : (query : Query) → Layout (Answer query)
  /-- Independent admissibility relation for returned answers. -/
  ValidAnswer : (query : Query) → Answer query → Prop
  /-- Cost of issuing a query. -/
  queryCost : (query : Query) → Cost

/-- One fixed responder satisfying the interface's advertised answer relation. -/
structure AdmissibleOracle (interface : OracleInterface Cost) where
  /-- Fixed answer selected for every typed query. -/
  answer : (query : interface.Query) → interface.Answer query
  correct : ∀ query, interface.ValidAnswer query (answer query)

namespace OracleInterface

/-- Whether the advertised oracle assumption is non-vacuous. -/
abbrev Nonvacuous (interface : OracleInterface Cost) : Prop :=
  Nonempty (AdmissibleOracle interface)

/-- Canonical query memory; no query encoder is supplied by an algorithm witness. -/
noncomputable def queryMemory (interface : OracleInterface Cost)
    (query : interface.Query) : Memory :=
  interface.queryLayout.init query

/-- Canonical answer representation in a designated result region. -/
noncomputable def AnswerRep (interface : OracleInterface Cost) (query : interface.Query)
    (region : Region) (answer : interface.Answer query) (memory : Memory) : Prop :=
  (interface.answerLayout query).RepAt region answer memory

/--
Canonical answer-transfer cell count, derived from the closed answer layout rather than supplied
as an arbitrary possibly-zero cost function.
-/
noncomputable def answerTransferCells (interface : OracleInterface Cost)
    (query : interface.Query) (answer : interface.Answer query) : ℕ :=
  ((interface.answerLayout query).footprint answer).total

/-- Canonical oracle answers have a functional memory interpretation. -/
theorem AnswerRep.functional (interface : OracleInterface Cost) (query : interface.Query)
    (region : Region) {left right : interface.Answer query} {memory : Memory}
    (leftRep : interface.AnswerRep query region left memory)
    (rightRep : interface.AnswerRep query region right memory) : left = right :=
  (interface.answerLayout query).rep_functional region leftRep rightRep

end OracleInterface

/-! ## Sealed same-trace oracle machine -/

namespace OracleMachine

/-- Closed syntax for one named structured-real-RAM oracle profile. -/
inductive Instruction where
  /-- Execute an ordinary deterministic core instruction. -/
  | core (instruction : StructuredRealRAM.Instruction)
  /-- Decode a query, invoke the fixed responder, and canonically write its answer. -/
  | oracleCall (queryRegion answerRegion : Region) (next : ℕ)
deriving DecidableEq

/-- One finite oracle program. -/
abbrev Program := List Instruction

namespace Instruction

/-- Numeric successors stored in the closed syntax. -/
def successors : Instruction → List ℕ
  | .core instruction => instruction.successors
  | .oracleCall _ _ next => [next]

/-- Canonical finite encoding used for fixed-program description-size reports. -/
def encode : Instruction → List Bool
  | .core instruction => false :: StructuredRealRAM.Program.encodeInstruction instruction
  | .oracleCall queryRegion answerRegion next =>
      true :: StructuredRealRAM.Program.encodeNat queryRegion.realBase ++
        StructuredRealRAM.Program.encodeNat queryRegion.natBase ++
        StructuredRealRAM.Program.encodeNat answerRegion.realBase ++
        StructuredRealRAM.Program.encodeNat answerRegion.natBase ++
        StructuredRealRAM.Program.encodeNat next

end Instruction

namespace Program

/-- Every successor stays within the same finite program. -/
def Valid (program : Program) : Prop :=
  ∀ (pc : ℕ) (instruction : Instruction), program[pc]? = some instruction →
    ∀ target ∈ instruction.successors, target < program.length

/-- Canonical concatenation of instruction descriptions. -/
def encodeInstructions : List Instruction → List Bool
  | [] => []
  | instruction :: instructions => instruction.encode ++ encodeInstructions instructions

/-- Canonical binary description of a complete oracle program. -/
def encode (program : Program) : List Bool :=
  StructuredRealRAM.Program.encodeNat program.length ++ encodeInstructions program

/-- Number of fetched instruction positions. -/
def instructionCount (program : Program) : ℕ := program.length

/-- Full finite description size, including regions and jump targets. -/
def descriptionSize (program : Program) : ℕ := program.encode.length

end Program

/-- Operational result and cost of the same oracle-machine transition. -/
structure StepObservation where
  /-- Operational effect. -/
  outcome : StructuredRealRAM.StepResult
  /-- Resources returned by the same transition. -/
  cost : StructuredRealRAM.Cost

/-- Fuel-bounded oracle-machine observation. -/
structure RunObservation where
  /-- Halt, timeout, or stuck outcome. -/
  outcome : StructuredRealRAM.RunResult
  /-- Accumulated same-trace charge. -/
  cost : StructuredRealRAM.Cost
  /-- Number of fetched transitions. -/
  steps : ℕ

/--
Canonical cost of fetching an oracle call, reading its represented query, invoking the named
abstract oracle cost, and writing its represented answer.
-/
noncomputable def callCost (interface : OracleInterface StructuredRealRAM.Cost)
    (query : interface.Query) (answer : interface.Answer query) : StructuredRealRAM.Cost :=
  let queryFootprint := interface.queryLayout.footprint query
  let answerFootprint := (interface.answerLayout query).footprint answer
  StructuredRealRAM.Cost.ofFields 1 queryFootprint.realCells answerFootprint.realCells 0 0
      queryFootprint.natCells answerFootprint.natCells 0 0 +
    interface.queryCost query

/-- Execute one fetched instruction using one responder fixed for the whole run. -/
noncomputable def execute (interface : OracleInterface StructuredRealRAM.Cost)
    (oracle : AdmissibleOracle interface) (instruction : Instruction)
    (configuration : StructuredRealRAM.Configuration) : StepObservation :=
  match instruction with
  | .core coreInstruction =>
      let observation := StructuredRealRAM.execute coreInstruction configuration.memory
      ⟨observation.outcome, observation.cost⟩
  | .oracleCall queryRegion answerRegion next =>
      match interface.queryLayout.readAt queryRegion configuration.memory with
      | none => ⟨.stuck configuration, StructuredRealRAM.Cost.control⟩
      | some query =>
          let answer := oracle.answer query
          let memory := (interface.answerLayout query).writeAt answerRegion answer
            configuration.memory
          ⟨.running ⟨next, memory⟩, callCost interface query answer⟩

/-- Fetch and execute once. -/
noncomputable def step (interface : OracleInterface StructuredRealRAM.Cost)
    (oracle : AdmissibleOracle interface) (program : Program)
    (configuration : StructuredRealRAM.Configuration) : StepObservation :=
  match program[configuration.pc]? with
  | none => ⟨.stuck configuration, 0⟩
  | some instruction => execute interface oracle instruction configuration

/-- Run at most `fuel` instructions with one fixed admissible responder. -/
noncomputable def runFor (interface : OracleInterface StructuredRealRAM.Cost)
    (oracle : AdmissibleOracle interface) (program : Program) :
    ℕ → StructuredRealRAM.Configuration → RunObservation
  | 0, configuration => ⟨.outOfFuel configuration, 0, 0⟩
  | fuel + 1, configuration =>
      let observation := step interface oracle program configuration
      match observation.outcome with
      | .running next =>
          let rest := runFor interface oracle program fuel next
          ⟨rest.outcome, observation.cost + rest.cost, rest.steps + 1⟩
      | .halted memory result => ⟨.halted memory result, observation.cost, 1⟩
      | .stuck stuck => ⟨.stuck stuck, observation.cost, 1⟩

/--
One derivation coupling final memory, output, oracle/transfer charges, and fetched transitions.
The responder parameter is fixed throughout the derivation.
-/
inductive HaltingTrace (interface : OracleInterface StructuredRealRAM.Cost)
    (oracle : AdmissibleOracle interface) (program : Program) :
    StructuredRealRAM.Configuration → Memory → ℝ →
      StructuredRealRAM.Cost → ℕ → Prop where
  | halt {configuration memory result cost}
      (observes : step interface oracle program configuration =
        ⟨.halted memory result, cost⟩) :
      HaltingTrace interface oracle program configuration memory result cost 1
  | next {configuration nextConfiguration memory result headCost tailCost steps}
      (observes : step interface oracle program configuration =
        ⟨.running nextConfiguration, headCost⟩)
      (tail : HaltingTrace interface oracle program nextConfiguration
        memory result tailCost steps) :
      HaltingTrace interface oracle program configuration memory result
        (headCost + tailCost) (steps + 1)

/-- Stable profile metadata.  The concrete interface is an explicit theorem parameter. -/
structure Profile where
  /-- Stable human-readable profile description. -/
  name : String

/-- Named sealed structured oracle profile. -/
def profile : Profile :=
  ⟨"structured exact-real oracle RAM; closed oracleCall syntax; canonical query reads and " ++
    "answer writes; one fixed admissible responder; same-trace query and transfer costs"⟩

end OracleMachine

end Algolean.Algorithms.StructuredRealRAM
