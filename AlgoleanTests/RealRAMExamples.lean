/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM

/-!
# Real-RAM examples

Small programs exercising deterministic real arithmetic, random-access memory, and the randomized
real-RAM composition.
-/

@[expose] public section

namespace AlgoleanTests

open Algolean Algorithms Prog

noncomputable section

/-- Compute `x * y + z` and store the result at `address`. -/
def multiplyAddStore (memory : RealRAM.Memory) (address : ℕ) (x y z : ℝ) :
    Prog RealRAM RealRAM.Memory := do
  let product : ℝ ← RealRAM.mul x y
  let result : ℝ ← RealRAM.add product z
  RealRAM.write memory address result

@[simp]
theorem multiplyAddStore_eval (memory : RealRAM.Memory) (address : ℕ) (x y z : ℝ) :
    ((multiplyAddStore memory address x y z).eval RealRAM.natCost) address = x * y + z := by
  simp [multiplyAddStore, RealRAM.natCost]

@[simp]
theorem multiplyAddStore_time (memory : RealRAM.Memory) (address : ℕ) (x y z : ℝ) :
    (multiplyAddStore memory address x y z).time RealRAM.natCost = 3 := by
  simp [multiplyAddStore, RealRAM.natCost]

@[simp]
theorem multiplyAddStore_operationCost
    (memory : RealRAM.Memory) (address : ℕ) (x y z : ℝ) :
    (multiplyAddStore memory address x y z).time RealRAM.operationCost =
      ⟨0, 1, 2, 0, 0⟩ := by
  simp [multiplyAddStore, RealRAM.operationCost]
  rfl

/-- Read two arbitrary memory cells and compare their exact real values. -/
def readAndCompare (memory : RealRAM.Memory) (first second : ℕ) : Prog RealRAM Ordering := do
  let x : ℝ ← RealRAM.read memory first
  let y : ℝ ← RealRAM.read memory second
  RealRAM.compare x y

@[simp]
theorem readAndCompare_eval (memory : RealRAM.Memory) (first second : ℕ) :
    (readAndCompare memory first second).eval RealRAM.natCost =
      if memory first < memory second then .lt
      else if memory first = memory second then .eq else .gt := by
  simp [readAndCompare, RealRAM.natCost, RealRAM.Memory.read]

@[simp]
theorem readAndCompare_operationCost (memory : RealRAM.Memory) (first second : ℕ) :
    (readAndCompare memory first second).time RealRAM.operationCost =
      ⟨2, 0, 0, 1, 0⟩ := by
  simp [readAndCompare, RealRAM.operationCost]
  rfl

/-- Add two exact real numbers, then make one random-bit sampling query. -/
def addThenSample (x y : ℝ) : Prog (RandomizedRealRAM Bool) (ℝ × PMF Bool) := do
  let sum : ℝ ← RandomizedRealRAM.liftRealRAM (RealRAM.add x y)
  let draw : PMF Bool ← RandomizedRealRAM.sample
  return (sum, draw)

@[simp]
theorem addThenSample_eval (dist : PMF Bool) (x y : ℝ) :
    (addThenSample x y).eval (RandomizedRealRAM.natCost dist) = (x + y, dist) := by
  simp [addThenSample, RandomizedRealRAM.natCost, RandomizedRealRAM.liftRealRAM,
    RandomizedRealRAM.sample, RandomizedRealRAM.sampleQuery, RandomizedRealRAM.ofRealRAM]

@[simp]
theorem addThenSample_time (dist : PMF Bool) (x y : ℝ) :
    (addThenSample x y).time (RandomizedRealRAM.natCost dist) = 2 := by
  simp [addThenSample, RandomizedRealRAM.natCost, RandomizedRealRAM.liftRealRAM,
    RandomizedRealRAM.sample, RandomizedRealRAM.sampleQuery, RandomizedRealRAM.ofRealRAM]

@[simp]
theorem addThenSample_operationCost (dist : PMF Bool) (x y : ℝ) :
    (addThenSample x y).time (RandomizedRealRAM.operationCost dist) =
      ⟨0, 0, 1, 0, 1⟩ := by
  simp [addThenSample, RandomizedRealRAM.operationCost, RandomizedRealRAM.liftRealRAM,
    RandomizedRealRAM.sample, RandomizedRealRAM.sampleQuery, RandomizedRealRAM.ofRealRAM,
    RandomizedRealRAM.sampleOperationCost, RealRAM.operationCost]
  rfl

/-- A randomized real RAM may also use a discrete sampling distribution on `ℝ`. -/
example (dist : PMF ℝ) : Model (RandomizedRealRAM ℝ) ℕ :=
  RandomizedRealRAM.natCost dist

end

end AlgoleanTests
