/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RandomSample
public import Mathlib.Data.Real.Basic

/-!
# The real RAM model

This file defines a unit-cost random-access machine whose memory cells contain exact real numbers.
The core instruction set consists of random-access reads and writes, addition, subtraction,
multiplication, division, negation, and comparison. More powerful operations sometimes included in
real-RAM variants are deliberately not primitive here. Independent roots, powers, floor, and
transcendental effects are provided by `Algolean.Models.RealRAM.Extensions`.

The model is intentionally hypothetical: Lean's `ℝ` gives the instructions exact real-number
semantics, and each instruction has unit cost regardless of the values involved. Division uses the
totalized division on `ℝ`, so division by zero evaluates to zero.

`RandomizedRealRAM α` composes the real RAM with Algolean's sampling oracle. The parameter `α` is
the sampled type, allowing both random-bit machines (`α = Bool`) and machines sampling from a
discrete distribution on real numbers (`α = ℝ`). A primitive continuous-uniform oracle is provided
by `Algolean.Models.RealRAM.ContinuousRandom`, and `Algolean.Algorithms.GaussianSampling` derives a
Gaussian sampler from it. Continuous laws are not `PMF`s.

## Main definitions

- `RealRAM.Memory`: unbounded, zero-initialized, real-valued random-access memory.
- `RealRAM`: the query type of primitive real-RAM instructions.
- `RealRAM.natCost`: the usual unit-cost model.
- `RealRAM.operationCost`: a model that counts each kind of operation separately.
- `RandomizedRealRAM`: a real RAM extended with a sampling query.
- `RandomizedRealRAM.natCost`: the unit-cost randomized model.
- `RandomizedRealRAM.operationCost`: the detailed randomized model, including sample count.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

/-- An unbounded memory whose addresses are natural numbers and whose cells contain real numbers. -/
abbrev RealRAM.Memory : Type := ℕ → ℝ

namespace RealRAM.Memory

/-- Real-RAM memory with every cell initialized to zero. -/
def empty : RealRAM.Memory := fun _ ↦ 0

/-- Read a cell of real-RAM memory. -/
def read (memory : RealRAM.Memory) (address : ℕ) : ℝ := memory address

/-- Return the memory obtained by writing `value` at `address`. -/
def write (memory : RealRAM.Memory) (address : ℕ) (value : ℝ) : RealRAM.Memory :=
  Function.update memory address value

@[simp]
theorem empty_apply (address : ℕ) : empty address = 0 := rfl

@[simp]
theorem write_same (memory : RealRAM.Memory) (address : ℕ) (value : ℝ) :
    (write memory address value) address = value := by
  simp [write]

@[simp]
theorem write_of_ne (memory : RealRAM.Memory) {writtenAddress address : ℕ} (value : ℝ)
    (h : address ≠ writtenAddress) :
    (write memory writtenAddress value) address = memory address := by
  simp [write, h]

end RealRAM.Memory

/--
Primitive instructions of the core real RAM.

Memory addresses are natural numbers, while memory cells and arithmetic registers contain exact
real numbers. `compare` returns all three possible comparison outcomes in one unit-cost instruction.
-/
inductive RealRAM : Type → Type where
  /-- Read the real number stored at `address`. -/
  | read (memory : RealRAM.Memory) (address : ℕ) : RealRAM ℝ
  /-- Write a real number at `address` and return the updated memory. -/
  | write (memory : RealRAM.Memory) (address : ℕ) (value : ℝ) : RealRAM RealRAM.Memory
  /-- Exact real addition. -/
  | add (x y : ℝ) : RealRAM ℝ
  /-- Exact real subtraction. -/
  | sub (x y : ℝ) : RealRAM ℝ
  /-- Exact real multiplication. -/
  | mul (x y : ℝ) : RealRAM ℝ
  /-- Exact, totalized real division; in particular, `x / 0 = 0`. -/
  | div (x y : ℝ) : RealRAM ℝ
  /-- Exact real negation. -/
  | neg (x : ℝ) : RealRAM ℝ
  /-- Compare two real numbers. -/
  | compare (x y : ℝ) : RealRAM Ordering

namespace RealRAM

/-- The exact functional semantics of one real-RAM instruction. -/
@[simp]
noncomputable def eval : RealRAM α → α
  | .read memory address => Memory.read memory address
  | .write memory address value => Memory.write memory address value
  | .add x y => x + y
  | .sub x y => x - y
  | .mul x y => x * y
  | .div x y => x / y
  | .neg x => -x
  | .compare x y => if x < y then .lt else if x = y then .eq else .gt

/-- A real-RAM model in which every primitive instruction has unit cost. -/
@[simps]
noncomputable def natCost : Model RealRAM ℕ where
  evalQuery := eval
  cost _ := 1

/-- Register the unit-cost semantics as the default model for real-RAM programs. -/
noncomputable instance : HasModel RealRAM ℕ where
  model := natCost

/-- The default real-RAM model is `RealRAM.natCost`. -/
@[simp]
theorem hasModel_model : (HasModel.model : Model RealRAM ℕ) = natCost := rfl

end RealRAM

/--
A detailed cost for real-RAM programs.

The `samples` field is zero for deterministic `RealRAM` instructions and is used by
`RandomizedRealRAM.operationCost` for sampling queries.
-/
@[ext, grind]
structure RealRAMCost where
  /-- Number of random-access memory reads. -/
  reads : ℕ
  /-- Number of random-access memory writes. -/
  writes : ℕ
  /-- Number of arithmetic operations. -/
  arithmetic : ℕ
  /-- Number of real-number comparisons. -/
  comparisons : ℕ
  /-- Number of random sampling queries. -/
  samples : ℕ

/-- Equivalence used to transport algebraic structure to `RealRAMCost`. -/
def RealRAMCost.equivProd : RealRAMCost ≃ (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) where
  toFun cost := (((cost.reads, cost.writes), (cost.arithmetic, cost.comparisons)), cost.samples)
  invFun cost := ⟨cost.1.1.1, cost.1.1.2, cost.1.2.1, cost.1.2.2, cost.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RealRAMCost

@[simps, grind]
instance : Zero RealRAMCost := ⟨0, 0, 0, 0, 0⟩

@[simps]
instance : LE RealRAMCost where
  le x y := x.reads ≤ y.reads ∧ x.writes ≤ y.writes ∧ x.arithmetic ≤ y.arithmetic ∧
    x.comparisons ≤ y.comparisons ∧ x.samples ≤ y.samples

instance : LT RealRAMCost where
  lt x y := x ≤ y ∧ ¬y ≤ x

@[grind]
instance : PartialOrder RealRAMCost where
  le_refl _ := ⟨by rfl, by rfl, by rfl, by rfl, by rfl⟩
  le_trans _ _ _ hxy hyz :=
    ⟨hxy.1.trans hyz.1, hxy.2.1.trans hyz.2.1, hxy.2.2.1.trans hyz.2.2.1,
      hxy.2.2.2.1.trans hyz.2.2.2.1, hxy.2.2.2.2.trans hyz.2.2.2.2⟩
  le_antisymm x y hxy hyx := by
    apply RealRAMCost.ext
    · exact Nat.le_antisymm hxy.1 hyx.1
    · exact Nat.le_antisymm hxy.2.1 hyx.2.1
    · exact Nat.le_antisymm hxy.2.2.1 hyx.2.2.1
    · exact Nat.le_antisymm hxy.2.2.2.1 hyx.2.2.2.1
    · exact Nat.le_antisymm hxy.2.2.2.2 hyx.2.2.2.2

@[simps]
instance : Add RealRAMCost where
  add x y := ⟨x.reads + y.reads, x.writes + y.writes, x.arithmetic + y.arithmetic,
    x.comparisons + y.comparisons, x.samples + y.samples⟩

@[simps]
instance : SMul ℕ RealRAMCost where
  smul n cost := ⟨n • cost.reads, n • cost.writes, n • cost.arithmetic,
    n • cost.comparisons, n • cost.samples⟩

instance : AddCommMonoid RealRAMCost :=
  fast_instance%
    RealRAMCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end RealRAMCost

namespace RealRAM

/--
A real-RAM model that counts memory, arithmetic, comparison, and sampling operations separately.
-/
@[simps, grind]
noncomputable def operationCost : Model RealRAM RealRAMCost where
  evalQuery := eval
  cost
    | .read _ _ => ⟨1, 0, 0, 0, 0⟩
    | .write _ _ _ => ⟨0, 1, 0, 0, 0⟩
    | .add _ _ | .sub _ _ | .mul _ _ | .div _ _ | .neg _ => ⟨0, 0, 1, 0, 0⟩
    | .compare _ _ => ⟨0, 0, 0, 1, 0⟩

end RealRAM

/-- A real RAM extended with a sampling oracle on `α`. -/
abbrev RandomizedRealRAM (α : Type) : Type → Type := RandomizeQuery RealRAM α

namespace RandomizedRealRAM

/-- Inject a deterministic real-RAM instruction into a randomized real RAM. -/
def ofRealRAM (query : RealRAM β) : RandomizedRealRAM α β := .inl query

/-- The raw sampling query of a randomized real RAM. -/
def sampleQuery : RandomizedRealRAM α (PMF α) := .inr .sample

/-- Lift a deterministic instruction into a randomized real-RAM program. -/
def liftRealRAM (query : RealRAM β) : Prog (RandomizedRealRAM α) β :=
  Cslib.FreeM.lift (ofRealRAM query)

/-- Make one sampling query in a randomized real-RAM program. -/
def sample : Prog (RandomizedRealRAM α) (PMF α) :=
  Cslib.FreeM.lift sampleQuery

@[simp]
theorem liftRealRAM_eval (query : RealRAM β) (M : Model RealRAM Cost)
    (S : Model (RandomSample α) Cost) :
    (liftRealRAM (α := α) query).eval (RandomizeQuery.model M S) = M.evalQuery query :=
  rfl

@[simp]
theorem sample_eval (M : Model RealRAM Cost) (S : Model (RandomSample α) Cost) :
    (sample (α := α)).eval (RandomizeQuery.model M S) = S.evalQuery .sample :=
  rfl

@[simp]
theorem liftRealRAM_time [AddZeroClass Cost] (query : RealRAM β) (M : Model RealRAM Cost)
    (S : Model (RandomSample α) Cost) :
    (liftRealRAM (α := α) query).time (RandomizeQuery.model M S) = M.cost query := by
  simp [liftRealRAM, ofRealRAM]

@[simp]
theorem sample_time [AddZeroClass Cost] (M : Model RealRAM Cost)
    (S : Model (RandomSample α) Cost) :
    (sample (α := α)).time (RandomizeQuery.model M S) = S.cost .sample := by
  simp [sample, sampleQuery]

/--
The unit-cost randomized real-RAM model using `dist` as its sampling distribution.

Both deterministic instructions and sampling queries cost one.
-/
@[simps!]
noncomputable def natCost (dist : PMF α) : Model (RandomizedRealRAM α) ℕ :=
  RandomizeQuery.model RealRAM.natCost (RandomSample.natCost dist)

/-- A sampling model whose detailed cost is one sample and no deterministic operations. -/
@[simps]
def sampleOperationCost (dist : PMF α) : Model (RandomSample α) RealRAMCost where
  evalQuery
    | .sample => dist
  cost _ := ⟨0, 0, 0, 0, 1⟩

/--
The detailed randomized real-RAM model using `dist` as its sampling distribution.

Deterministic instructions are interpreted by `RealRAM.operationCost`, while sampling queries
increment only `RealRAMCost.samples`.
-/
@[simps!]
noncomputable def operationCost (dist : PMF α) :
    Model (RandomizedRealRAM α) RealRAMCost :=
  RandomizeQuery.model RealRAM.operationCost (sampleOperationCost dist)

end RandomizedRealRAM

end Algorithms

end Algolean
