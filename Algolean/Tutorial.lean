/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.Basic
public import Algolean.Machine.RealRAM
public import Algolean.QueryComposition

/-!
# Formalize an algorithm and know what is proved

This is a checked, end-to-end introduction to functional correctness, query cost, independent
machine programs, and oracles.

Four objects form the basic interface:

```text
query language Q
    + Model.evalQuery / Model.cost
    + program Prog Q α
    = result through Prog.eval, charged path through Prog.time
```

The example below asks an oracle for the first available value at two indices.

## 1. Declare the observable operations

An indexed query type states both the operation and its answer type. A value of
`Lookup α (Option α)` is therefore an observable operation returning `Option α`.
-/

@[expose] public section

namespace Algolean.Tutorial

open Algorithms Cslib

/-- Query a partial lookup oracle at one natural-number index. -/
inductive Lookup (α : Type) : Type → Type where
  | get (index : ℕ) : Lookup α (Option α)

namespace Lookup

/-!
## 2. Give the operations meaning and cost

`evalQuery` is the semantic oracle. `cost` is a declared abstraction, not wall-clock time. This
model charges one unit for each lookup.
-/

/-- Unit-cost semantics for a supplied partial lookup function. -/
def unitCost (oracle : ℕ → Option α) : Model (Lookup α) ℕ where
  evalQuery
    | .get index => oracle index
  cost _ := 1

end Lookup

/-!
## 3. Write the algorithm

Only emitted queries are charged. Pattern matching and packaging the returned option are pure Lean
work. Substantial computation hidden in a pure term would likewise be uncharged, so the query
language must expose every operation that belongs to the intended cost model.
-/

/-- Return the first successful lookup, trying `second` only when `first` fails. -/
def firstAvailable (first second : ℕ) : Prog (Lookup α) (Option α) := do
  match ← FreeM.lift (.get first) with
  | some value => pure (some value)
  | none => FreeM.lift (.get second)

/-!
## 4. Prove the returned value

Evaluation is always relative to a model. This theorem works for every model because the right
side refers to the same model's query answers.
-/

@[simp]
theorem firstAvailable_eval (first second : ℕ) (M : Model (Lookup α) Cost) :
    (firstAvailable first second).eval M =
      match M.evalQuery (.get first) with
      | some value => some value
      | none => M.evalQuery (.get second) := by
  simp [firstAvailable]
  split <;> simp_all

/-!
## 5. Prove the executed-path cost

`Prog.time` follows the branch selected by `evalQuery`. The exact cost is one on immediate success
and two on failure of the first lookup.
-/

@[simp]
theorem firstAvailable_time (oracle : ℕ → Option α) (first second : ℕ) :
    (firstAvailable first second).time (Lookup.unitCost oracle) =
      match oracle first with
      | some _ => 1
      | none => 2 := by
  simp [firstAvailable, Lookup.unitCost]
  split <;> simp_all

/-!
## 6. Package correctness as a problem

A `QueryProblem` can depend on its model. That is important for oracle problems: the correct answer
depends on the oracle supplied by the model.
-/

/-- Model-relative specification of `firstAvailable`. -/
def firstAvailableProblem (first second : ℕ) :
    QueryProblem (Lookup α) ℕ (Option α) where
  spec M result :=
    result = match M.evalQuery (.get first) with
      | some value => some value
      | none => M.evalQuery (.get second)

/-- Functional correctness holds for every model of the lookup query language. -/
theorem firstAvailable_solves (first second : ℕ) :
    Solves (firstAvailable (α := α) first second) (firstAvailableProblem first second) := by
  intro M
  exact firstAvailable_eval first second M

/-- The intended unit-cost oracle family satisfies the uniform two-query bound. -/
theorem firstAvailable_solvesWithinModel
    (oracle : ℕ → Option α) (first second : ℕ) :
    SolvesWithinModel (firstAvailable first second) (firstAvailableProblem first second)
      (Lookup.unitCost oracle) 2 := by
  constructor
  · exact firstAvailable_eval (Cost := ℕ) first second (Lookup.unitCost oracle)
  · rw [firstAvailable_time]
    split <;> omega

/-!
### `SolvesWithin` quantifies over more than oracles

`SolvesWithin P problem bound` quantifies over every `Model Q Cost`, including arbitrary `cost`
fields. A finite natural-number bound is generally not derivable merely because each intended
`Lookup.unitCost oracle` charges one. Use:

- `Solves` for correctness under every model's functional semantics; and
- `SolvesWithinModel` for each member of a normalized model family.

## 7. Scale functional proofs with weakest preconditions

For stateful or looping programs, use the weakest-precondition interface:

- `HasModel` selects the default functional model;
- `mvcgen` proves a Hoare triple, usually from loop invariants; and
- `eval_of_triple` turns the triple into an evaluation theorem.

Weakest-precondition proofs do not prove cost. Keep a separate `Prog.time` theorem. Small examples
are in `AlgoleanTests/FreeMonadWP.lean`; `Algolean/Algorithms/VecBubbleSort.lean` shows loop
invariants, while `Algolean/Algorithms/ListInsertionSort.lean` shows direct recursive evaluation
and complexity proofs.

## 8. Use `Machine.Program` for an independent algorithm witness

An arbitrary `Prog` contains Lean continuation functions, and pure terms may perform unrecorded
work. For an independent existence statement, use the finite first-order source language:

```text
Machine.Program
    -- Program.compile input -->
Prog (Machine.Query ...)
    -- Prog.reduceProg implementation -->
Prog TargetQuery
    -- eval / time targetModel -->
result and cost
```

The important quantifier order is:

```lean
∃ program : Machine.Program language Exit,
  ∀ oracle input,
    SolvesWithinModel (run program input) (problem input) (model oracle) (bound input)
```

The witness is chosen before the runtime input and oracle. `Machine.Program` is a finite execution
tree: runtime results select only already stored successors. Public size- or fuel-indexed
algorithms can be families of finite trees. Runtime-dependent unbounded loops require a separate
control-flow-graph or transition-system representation.

`Program.compileFrom` exposes the same fixed structural translation starting from an existing
state. It is useful when a surrounding development already has a machine state, but that caller
then owns the state's input encoding, provenance, and cost. Because `Input` occurs only in the
resulting query type, a call may need an explicit `(Input := ...)` argument.

`RealRAMMachine` is the standard address-level adapter currently provided. It contains rational
literals and register addresses, lowers memory/arithmetic operations to primitive `RealRAM`
queries, and supplies an independently stated source model plus `Reduction.IsExact` proof. Its
default input contract is pre-encoded `RealRAM.Memory`; clients with another input type must make
their initializer and its cost explicit. A client changing the result representation likewise
needs an explicit finalizer and output-decoding cost.

Circuits, fan-in-two circuits, quantum circuits, and single-tape Turing machines already have
native first-order syntax or transition data, so wrapping them in `Machine.Program` usually would
duplicate their representation. The comparison, vector, sampling, Robertson--Webb, and
quantum-oracle modules are query effects; they have no canonical private-state layout and
therefore no standard machine adapter.

## 9. Add an oracle

An oracle is an ordinary indexed query type. Compose it with the base machine using
`compositeQuery`:

- `Model.combine` uses one shared cost type;
- `Model.compose` keeps costs in separate product components; and
- a `Reduction` lowers source machine operations to the composed target.

The dependent example in `AlgoleanTests/MachineExamples.lean` uses a request-indexed vector
response. Its reduction writes every returned coordinate into private RAM through charged queries,
then exposes only a `Choice2` success status to source control flow. The input-independent theorem
quantifies over every implementation of that dependent oracle.

An ordinary reduction is not automatically correct or cost preserving. `Reduction.IsExact`
collects two local obligations for each source query: equality of the result and equality of the
complete lowered cost. Its `reduceProg_eval` and `reduceProg_time` theorems lift those facts to
every source program. Reductions that have overhead or only upper bounds should instead use the
more general reduction theorems and prove the relevant inequality.

## 10. Audit the trust boundary

Before treating a theorem as an algorithmic guarantee, check:

- `Model.evalQuery` defines what the primitive operations mean.
- `Model.cost` defines exactly what is counted.
- `QueryProblem.spec` independently states the intended mathematical problem rather than merely
  restating the program's evaluation.
- Pure Lean work outside emitted queries is uncharged.
- Weakest preconditions prove functional behavior, not cost.
- Instruction payloads, target query types, models, and reductions are specification components.
- A reduction must not hide numeric work or memory access in `pure`.
- Initialization and finalization are charged, or the input/output encoding contract says
  explicitly that they are external.
- `Machine.Program.compile` and `compileFrom` protect source programs translated through those
  routes, not arbitrary `Prog` values; `compileFrom` leaves initial-state obligations to its caller.
- Program construction is outside runtime input and oracle quantifiers.
- Oracle robustness extends only over the functions or models actually quantified in the theorem.
- The Lean kernel and any axioms used by imported mathematics remain foundational assumptions.

The small lookup development above is the direct `Prog` route. For auditable independent machine
code with a dependent oracle, continue with `AlgoleanTests/MachineExamples.lean`; for the standard
address language and all three comparison branches, see
`AlgoleanTests/MachineRealRAMExamples.lean`.
-/

end Algolean.Tutorial
