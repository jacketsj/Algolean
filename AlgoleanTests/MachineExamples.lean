/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Machine.RealRAM
public import Algolean.Complexity.Basic
public import Algolean.QueryComposition

/-!
# Finite machine code with a dependent oracle

This example extends the address-level real RAM with an oracle whose response type depends on its
request. The reduction stores every returned coordinate through a charged write; source control
flow sees only failure or success.
-/

@[expose] public section

namespace AlgoleanTests.MachineExamples

open Algolean Algorithms Cslib Machine

noncomputable section

/-- Structural data supplied to the oracle. -/
structure Request where
  size : ℕ
  key : ℕ

/-- The response type records the requested number of real coordinates. -/
abbrev Response (request : Request) :=
  Option (Vector ℝ request.size)

/-- A request-indexed oracle query. -/
inductive OracleQuery : Type → Type where
  | solve (request : Request) : OracleQuery (Response request)

/-- The real RAM extended by the oracle. -/
abbrev TargetQuery : Type → Type :=
  compositeQuery RealRAM OracleQuery

def oracleModel (oracle : (request : Request) → Response request) : Model OracleQuery ℕ where
  evalQuery
    | .solve request => oracle request
  cost _ := 1

def model (oracle : (request : Request) → Response request) : Model TargetQuery ℕ :=
  RealRAM.natCost.combine (oracleModel oracle)

def liftReal (query : RealRAM α) : Prog TargetQuery α :=
  FreeM.lift (.inl query)

def callOracle (request : Request) : Prog TargetQuery (Response request) :=
  FreeM.lift (.inr (.solve request))

/-- Store a runtime list in consecutive registers using one charged write per coordinate. -/
def storeList : List ℝ → RealRAM.Memory → ℕ → Prog TargetQuery RealRAM.Memory
  | [], memory, _ => pure memory
  | value :: values, memory, destination => do
      let memory ← liftReal (.write memory destination value)
      storeList values memory (destination + 1)

/-- Pure meaning of `storeList`, used in the independently stated source model. -/
def storeListValue : List ℝ → RealRAM.Memory → ℕ → RealRAM.Memory
  | [], memory, _ => memory
  | value :: values, memory, destination =>
      storeListValue values (RealRAM.Memory.write memory destination value) (destination + 1)

@[simp]
theorem storeList_eval (oracle : (request : Request) → Response request)
    (values : List ℝ) (memory : RealRAM.Memory) (destination : ℕ) :
    (storeList values memory destination).eval (model oracle) =
      storeListValue values memory destination := by
  induction values generalizing memory destination with
  | nil => rfl
  | cons value values induction =>
      rw [storeList, Prog.eval_bind]
      change
        (storeList values (RealRAM.Memory.write memory destination value)
          (destination + 1)).eval (model oracle) =
        storeListValue values (RealRAM.Memory.write memory destination value) (destination + 1)
      exact induction _ _

@[simp]
theorem storeList_time (oracle : (request : Request) → Response request)
    (values : List ℝ) (memory : RealRAM.Memory) (destination : ℕ) :
    (storeList values memory destination).time (model oracle) = values.length := by
  induction values generalizing memory destination with
  | nil => rfl
  | cons value values induction =>
      rw [storeList, Prog.time_bind]
      change 1 +
        (storeList values (RealRAM.Memory.write memory destination value)
          (destination + 1)).time (model oracle) = values.length + 1
      rw [induction]
      omega

theorem storeListValue_of_lt (values : List ℝ) (memory : RealRAM.Memory)
    {address destination : ℕ} (less : address < destination) :
    storeListValue values memory destination address = memory address := by
  induction values generalizing memory destination with
  | nil => rfl
  | cons value values induction =>
      rw [storeListValue, induction]
      · exact RealRAM.Memory.write_of_ne memory value (Nat.ne_of_lt less)
      · omega

@[simp]
theorem storeListValue_cons_first (value : ℝ) (values : List ℝ)
    (memory : RealRAM.Memory) (destination : ℕ) :
    storeListValue (value :: values) memory destination destination = value := by
  rw [storeListValue, storeListValue_of_lt]
  · exact RealRAM.Memory.write_same memory destination value
  · omega

/-- A two-successor oracle instruction. -/
inductive OracleInstruction where
  | solve (request : Request) (firstDestination : ℕ)

/-- Real-RAM instructions plus one oracle-status branch. -/
abbrev language : Language where
  Next := RealRAMMachine.Instruction
  Choose2 := OracleInstruction
  Choose3 := RealRAMMachine.Compare

/-- The recorded query language generated from this instruction set. -/
abbrev SourceQuery : Type → Type :=
  Machine.Query language (ℝ × ℝ) ℕ RealRAM.Memory ℝ

/--
Lower each recorded machine operation to charged real-RAM and oracle queries. Rich responses are
written to private memory before a finite status branch is returned.
-/
def implementation : Reduction SourceQuery TargetQuery where
  reduce
    | .init input => do
        let memory ← liftReal (.write RealRAM.Memory.empty 0 input.1)
        liftReal (.write memory 1 input.2)
    | .execute instruction memory =>
        (RealRAMMachine.lowerInstruction instruction memory).extend OracleQuery
    | .choose2 (.solve request destination) memory => do
        match ← callOracle request with
        | none => pure (memory, .first)
        | some answer => do
            let memory ← storeList answer.toList memory destination
            pure (memory, .second)
    | .choose3 instruction memory =>
        (RealRAMMachine.lowerCompare instruction memory).extend OracleQuery
    | .finish address memory =>
        (RealRAMMachine.lowerFinish address memory).extend OracleQuery

/-- Independent source semantics and cost, relative to a particular oracle. -/
noncomputable def sourceModel (oracle : (request : Request) → Response request) :
    Model SourceQuery ℕ where
  evalQuery
    | .init input =>
        RealRAM.Memory.write (RealRAM.Memory.write RealRAM.Memory.empty 0 input.1) 1 input.2
    | .execute instruction memory => RealRAMMachine.evalInstruction instruction memory
    | .choose2 (.solve request destination) memory =>
        match oracle request with
        | none => (memory, .first)
        | some answer => (storeListValue answer.toList memory destination, .second)
    | .choose3 instruction memory => RealRAMMachine.evalCompare instruction memory
    | .finish address memory => RealRAM.Memory.read memory address
  cost
    | .init _ => 2
    | .execute instruction _ => RealRAMMachine.instructionCost instruction
    | .choose2 (.solve request _) _ =>
        match oracle request with
        | none => 1
        | some _ => 1 + request.size
    | .choose3 _ _ => 3
    | .finish _ _ => 1

/-- The oracle-extended lowering has exactly the displayed source semantics and cost. -/
theorem implementation_isExact (oracle : (request : Request) → Response request) :
    Reduction.IsExact implementation (sourceModel oracle) (model oracle) := by
  constructor
  · intro result query
    cases query with
    | init input =>
        simp [implementation, liftReal, sourceModel, model, RealRAM.natCost]
    | execute instruction memory =>
        have exact := RealRAMMachine.implementation_isExact.eval_query
          (Machine.Query.execute instruction memory : RealRAMMachine.Query RealRAM.Memory)
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact
    | choose2 instruction memory =>
        cases instruction with
        | solve request destination =>
            cases h : oracle request with
            | none =>
                simp [implementation, callOracle, sourceModel, model, oracleModel, h]
            | some answer =>
                simpa [implementation, callOracle, sourceModel, model, oracleModel, h] using
                  storeList_eval oracle answer.toList memory destination
    | choose3 instruction memory =>
        have exact := RealRAMMachine.implementation_isExact.eval_query
          (Machine.Query.choose3 instruction memory : RealRAMMachine.Query
            (RealRAM.Memory × Choice3))
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact
    | finish address memory =>
        have exact := RealRAMMachine.implementation_isExact.eval_query
          (Machine.Query.finish address memory : RealRAMMachine.Query ℝ)
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact
  · intro result query
    cases query with
    | init input =>
        simp [implementation, liftReal, sourceModel, model, RealRAM.natCost]
    | execute instruction memory =>
        have exact := RealRAMMachine.implementation_isExact.time_query
          (Machine.Query.execute instruction memory : RealRAMMachine.Query RealRAM.Memory)
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact
    | choose2 instruction memory =>
        cases instruction with
        | solve request destination =>
            cases h : oracle request with
            | none =>
                simp [implementation, callOracle, sourceModel, model, oracleModel, h]
            | some answer =>
                simpa [implementation, callOracle, sourceModel, model, oracleModel, h] using
                  storeList_time oracle answer.toList memory destination
    | choose3 instruction memory =>
        have exact := RealRAMMachine.implementation_isExact.time_query
          (Machine.Query.choose3 instruction memory : RealRAMMachine.Query
            (RealRAM.Memory × Choice3))
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact
    | finish address memory =>
        have exact := RealRAMMachine.implementation_isExact.time_query
          (Machine.Query.finish address memory : RealRAMMachine.Query ℝ)
        simpa [implementation, RealRAMMachine.implementation, sourceModel,
          RealRAMMachine.natModel, model] using exact

/-- The fixed request made by the example program. -/
abbrev request : Request := ⟨2, 5⟩

/--
Add the inputs, then call the oracle. Return the sum on failure and the first returned coordinate
on success. Both possible successors are explicit subterms.
-/
def code : Program language ℕ :=
  .next (.add 0 1 2)
    (.choose2 (.solve request 3) (.halt 2) (.halt 3))

/-- Compile the source tree, then lower its recorded operations. -/
def run (program : Program language ℕ) (input : ℝ × ℝ) : Prog TargetQuery ℝ :=
  (program.compile (State := RealRAM.Memory) (Result := ℝ) input).reduceProg implementation

@[simp]
theorem code_eval (oracle : (request : Request) → Response request) (x y : ℝ) :
    (run code (x, y)).eval (model oracle) =
      match oracle request with
      | none => x + y
      | some answer => answer.toList.headD 0 := by
  change
    (((code.compile (State := RealRAM.Memory) (Result := ℝ) (x, y)).reduceProg
      implementation).eval (model oracle)) = _
  rw [(implementation_isExact oracle).reduceProg_eval]
  cases h : oracle request with
  | none =>
      simp [code, sourceModel, request, h, RealRAMMachine.evalInstruction,
        RealRAM.Memory.read]
  | some answer =>
      cases hlist : answer.toList with
      | nil =>
          have length := Vector.length_toList (xs := answer)
          simp [request, hlist] at length
      | cons value values =>
          simp [code, sourceModel, request, h, hlist, RealRAMMachine.evalInstruction,
            RealRAM.Memory.read]

@[simp]
theorem code_time (oracle : (request : Request) → Response request) (x y : ℝ) :
    (run code (x, y)).time (model oracle) =
      match oracle request with
      | none => 8
      | some _ => 10 := by
  change
    (((code.compile (State := RealRAM.Memory) (Result := ℝ) (x, y)).reduceProg
      implementation).time (model oracle)) = _
  rw [(implementation_isExact oracle).reduceProg_time]
  cases h : oracle request <;>
    simp [code, sourceModel, request, h, RealRAMMachine.instructionCost]

/-- Correctness requirement for one input, relative to the oracle in the query model. -/
def problem (x y : ℝ) : QueryProblem TargetQuery ℕ ℝ where
  spec queryModel result :=
    result = match queryModel.evalQuery (Sum.inr (.solve request)) with
      | none => x + y
      | some answer => answer.toList.headD 0

/--
One input-independent finite program works for every input and every implementation of the
dependent oracle. The bound includes initialization, all response writes, and output decoding.
-/
theorem exists_program :
    ∃ program : Program language ℕ,
      ∀ (oracle : (request : Request) → Response request) (x y : ℝ),
        SolvesWithinModel (run program (x, y))
          (problem x y) (model oracle) 10 := by
  refine ⟨code, ?_⟩
  intro oracle x y
  constructor
  · simpa [problem, model, oracleModel] using code_eval oracle x y
  · rw [code_time]
    split <;> omega

end

end AlgoleanTests.MachineExamples
