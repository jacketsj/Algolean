/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.Basic
public import Algolean.Audit.Algorithm
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

## 8. Use a fixed RAM claim when uniform machine code matters

An arbitrary `Prog` contains Lean continuations and may perform uncharged pure work. The compact
`RAM` model instead uses an ordinary finite instruction list with numeric jumps. Backward jumps
give one fixed program input-dependent loops. `IntegerRAM`, `WordRAM`, and `RealRAM.Program` share
the same instruction semantics; only their literal and arithmetic operations differ.

`RAM.runFor` observes a program for a given number of unit-cost instructions and reports halt,
timeout, or an invalid program counter. `RAM.Reaches` gives the corresponding unbounded
small-step semantics. `RAM.CostedSemantics` and `RAM.HaltingTrace` additionally couple behavior
and accumulated cost in the same execution.

For an end-to-end structured exact-real claim, use `MachineProblem.HasFixedMachineAlgorithm`.
Its witness is one `StructuredRealRAM.Program`; the program existential is outside every input.
The machine has random-access real and natural banks, so exact weights and discrete lengths,
indices, and tags do not require hidden conversions. Inputs and outputs use the closed inductive
`StructuredRealRAM.Layout` constructors (`unit`, `bool`, `nat`, `int`, `rat`, `real`, `fin`,
`bitVec`, `prod`, `sum`, `option`, `array`, and `subtype`). Its encoder and decoder are fixed
recursive interpreters; there is no custom-codec or arbitrary-equivalence constructor. Input size
is derived from the layout footprint,
unused memory and registers start at zero, and output is a functional `Layout.RepAt` relation.

Ordinary integer RAM and fixed-width word RAM use
`IntegerRAM.Problem.HasFixedMachineAlgorithm` and `WordRAM.Problem.HasFixedMachineAlgorithm`.
Their basic input route is a canonical native cell array with a length header. The stronger
`WordRAM.StructuredProblem` route stores a closed `WordLayout`; its model-specific canonical
instances cover words, bounded indices, proof-erased refinements, containers, finite tables, and
named physical sparse/graph formats. Raw `Nat`, `Int`, `Rat`, and `Real` are not one-word values.
Every admissible structured input proves that its footprint fits the `2^w` address space.

A theorem ranging over word widths is a family theorem and should say so. The width-uniform API
uses one finite `UniformProgram` template before every width and input, not an arbitrary function
from widths to programs. Callable `ProcedureCertificate`s can be proved independently and linked
into a `RelativeAlgorithmCertificate`: the shared-body linker executes all callee instructions,
records actual typed calls, and charges their complete same-trace cost. `WordRAM.RandomBit` is a
separate hidden lengthless iid-bit profile for randomized ordinary Word-RAM claims. Uniform links
are themselves finite templates, and randomized relative links must refine the same hidden source
to an ordinary closed randomized program. Exact-uniform real sampling remains an explicitly
stronger exact-real profile.

The ordinary Word RAM's data and address banks are connected only through sealed instructions.
A loaded word becomes an address in one charged step; address multiplication is also explicit.
Typed fixed-stride accessors compile to multiply-and-add instructions and require a no-wrap proof.
Callable ABIs prove their regions realizable. A general `ProcedureCertificate` may retain changes
in declared scratch, while `RestoringProcedureCertificate` states that the final memory is exactly
the canonical output overwrite. Neither certificate hides a subroutine in one host-language step.

For reusable structured exact-real code, `StructuredRealRAM.CanonicalLayout` contains only a closed
layout term. Compact real/natural arrays and named dense, sparse, indexed, and graph formats expose
their physical representations. `MachineProblem.HasAlgorithmBy` permits an exact bound over the
structured input. Structured procedure contracts, relative call traces, and the shared-body linker
produce a finite core program; external oracle profiles remain visibly different dependencies.

Use `MachineProblem.HasNonuniformFamily` only for size-indexed code and provide separate
instruction-count and full-description-size bounds. Full description size charges natural and
rational literals, register indices, and jump targets.
`MachineProblem.HasUniformlyGeneratedFamily` quantifies one sealed structured-real-RAM generator,
ties the generated target's canonical binary serialization to the generator's final memory, and
charges output materialization in the same trace. This is explicitly unit-cost unbounded-Nat
generation, not word-RAM or bit generation. The caller-defined abstraction is named
`MachineProblem.HasFamilyRelativeToGeneratorSpecification`; it is relative to those supplied
semantics and must not be described as ordinary uniform generation.
`MachineProblem.HasCompiledAlgorithm` accepts a first-order `CFG.Program`; the assembler shares join
labels, `CFG.compile_length` reports exact target instruction count, and
`CFG.compile_descriptionSize` includes generated numeric targets.

Preferred randomized statements use `BitRandomizedMachineProblem.HasMonteCarloAlgorithm` and
`HasEverySourceLasVegasStepAlgorithm`. The library fixes a hidden, lengthless iid fair-bit product
source. The closed `randBit` instruction consumes one coordinate, advances an inaccessible cursor,
and charges the draw in the same trace; failure values carry a proof that they are at most one.
The legacy `InputDependentTapeProblem` is explicitly relative to its tape law and can model
input-dependent advice. `ScheduledBitTapeProblem` is likewise explicitly relative to its
observable size-indexed tape-length schedule.

Applications needing exact continuous randomness should use the separately named
`UniformRealRandomizedMachineProblem.HasMonteCarloAlgorithm`. Its `sampleUniform` instruction
draws from a hidden product source of exact uniform `[0,1]` values. This is explicitly a stronger
machine than the random-bit RAM; a Gaussian or other distribution is not silently treated as the
same primitive. Its certificate proves that the success event is measurable. The core structured
profile has no floor, real-to-natural, or real-to-address operation; these belong only to separately
named stronger profiles with explicitly documented domain behavior.

`OracleMachineProblem.HasOracleAlgorithm` fixes an `OracleInterface` before the program witness:
typed queries and dependent answers, canonical layouts, answer validity, and named query cost.
The closed `oracleCall` instruction decodes the query structurally, uses one responder fixed for
the whole run, writes the answer with a layout-derived transfer charge, and records all costs in
the output trace. The preferred certificate proves the interface non-vacuous and works for every
admissible responder.

## 9. Audit the trust boundary

Before treating a theorem as an algorithmic guarantee, check:

- `Model.evalQuery` defines what the primitive operations mean.
- `Model.cost` defines exactly what is counted.
- `QueryProblem.spec` independently states the intended mathematical problem rather than merely
  restating the program's evaluation.
- Pure Lean work outside emitted queries is uncharged.
- Weakest preconditions prove functional behavior, not cost.
- Instruction payloads, query types, models, and reductions are specification components.
- A reduction must not hide numeric work or memory access in `pure`.
- Initialization and finalization are charged, or the input/output encoding contract says
  explicitly that they are external.
- For the strongest structured claim, input size comes from `Layout.footprint`, output meaning
  comes from `Layout.RepAt`, and both result and cost come from one `HaltingTrace`.
- RAM fuel bounds an observation of cyclic code. A successful theorem must prove a halted result
  rather than treating `outOfFuel` as an answer.
- For program families (including varying word widths), state and justify the uniformity and source
  code size conditions needed by the intended complexity model.
- Program construction is outside runtime input and oracle quantifiers.
- Oracle robustness extends only over the functions or models actually quantified in the theorem.
- The Lean kernel and any axioms used by imported mathematics remain foundational assumptions.

The small lookup development above is the direct `Prog` route. Cyclic machine examples are in
`AlgoleanTests/RAMExamples.lean`; fixed-claim, structured-layout, CFG shared-join, integer-RAM,
and word-RAM checks are in `AlgoleanTests/ExistentialAlgorithms.lean`.
-/

end Algolean.Tutorial
