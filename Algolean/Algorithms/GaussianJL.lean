/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Algorithms.GaussianSampling
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Batteries.Data.Vector.Lemmas

/-!
# Gaussian Johnson--Lindenstrauss projection

This module implements the computational core of a Gaussian Johnson--Lindenstrauss map. For an
input `x : Fin d → ℝ`, `GaussianJL.project rows x firstSample` samples a `rows × d` standard-
Gaussian matrix `G` in row-major order and returns `Gx / √rows`.

The implementation uses `GaussianSampling.standard`, so its only random primitive is uniform
sampling from `[0, 1]`. The main correctness theorem identifies the evaluated program exactly with
Mathlib's matrix-vector product. Exact unit and detailed costs are also proved. The usual finite-set
distance-preservation theorem and its quantitative probability bound are in
`Algolean.Algorithms.GaussianJLProbability`.
-/

@[expose] public section

namespace Algolean.Algorithms

open scoped BigOperators

namespace GaussianJL

/-- The Gaussian coefficient matrix determined by a continuous-oracle realization. -/
noncomputable def matrix (oracle : ContinuousRealSample.Oracle) (firstSample : ℕ) :
    Matrix (Fin rows) (Fin d) ℝ :=
  fun i j => GaussianSampling.standardValue oracle
    (firstSample + 2 * (i.val * d + j.val))

/-- The mathematical normalized Gaussian projection computed by `project`. -/
noncomputable def value (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) : Vector ℝ rows :=
  Vector.ofFn fun i => Matrix.mulVec (matrix (rows := rows) oracle firstSample) x i /
    Real.sqrt rows

/-- The dot product of one sampled Gaussian row with `x`. -/
noncomputable def dot : {d : ℕ} → (Fin d → ℝ) → ℕ → Prog GaussianSampling.Machine ℝ
  | 0, _, _ => pure 0
  | d + 1, x, firstSample => do
      let accumulator ← dot (fun j : Fin d => x j.castSucc) firstSample
      let coefficient ← GaussianSampling.standard (firstSample + 2 * d)
      let term ← GaussianSampling.liftCore (.mul coefficient (x (Fin.last d)))
      GaussianSampling.liftCore (.add accumulator term)

/-- The pure row-dot-product value corresponding to `dot`. -/
noncomputable def dotValue (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) : ℝ :=
  ∑ j, GaussianSampling.standardValue oracle (firstSample + 2 * j.val) * x j

@[simp]
theorem dot_eval (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) :
    (dot x firstSample).eval (GaussianSampling.natCost oracle) =
      dotValue oracle x firstSample := by
  induction d with
  | zero => simp [dot, dotValue]
  | succ d ih =>
      rw [dotValue, Fin.sum_univ_castSucc]
      simp [dot, dotValue, ih]

@[simp]
theorem dot_time (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) :
    (dot x firstSample).time (GaussianSampling.natCost oracle) = 10 * d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [dot, ih, Nat.mul_succ]

@[simp]
theorem dot_operationCost (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) :
    (dot x firstSample).time (GaussianSampling.operationCost oracle) =
      ⟨0, 0, 8 * d, 0, 2 * d⟩ := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [dot, ih, RealRAM.operationCost, Nat.mul_succ]
      rfl

/-- Compute the first `rows` normalized projected coordinates, appending each new row. -/
noncomputable def projectRows (x : Fin d → ℝ) (denominator : ℝ) (firstSample : ℕ) :
    (rows : ℕ) → Prog GaussianSampling.Machine (Vector ℝ rows)
  | 0 => pure #v[]
  | rows + 1 => do
      let previous ← projectRows x denominator firstSample rows
      let row ← dot x (firstSample + 2 * (rows * d))
      let normalized ← GaussianSampling.liftCore (.div row denominator)
      return previous.push normalized

/-- Pure recursive specification of `projectRows`. -/
noncomputable def projectRowsValue (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (denominator : ℝ) (firstSample : ℕ) : (rows : ℕ) → Vector ℝ rows
  | 0 => #v[]
  | rows + 1 =>
      (projectRowsValue oracle x denominator firstSample rows).push
        (dotValue oracle x (firstSample + 2 * (rows * d)) / denominator)

@[simp]
theorem projectRows_eval (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (denominator : ℝ) (firstSample rows : ℕ) :
    (projectRows x denominator firstSample rows).eval (GaussianSampling.natCost oracle) =
      projectRowsValue oracle x denominator firstSample rows := by
  induction rows with
  | zero => simp [projectRows]
  | succ rows ih => simp [projectRows, projectRowsValue, ih]

@[simp]
theorem projectRows_time (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (denominator : ℝ) (firstSample rows : ℕ) :
    (projectRows x denominator firstSample rows).time (GaussianSampling.natCost oracle) =
      rows * (10 * d + 1) := by
  induction rows with
  | zero =>
      rw [show projectRows x denominator firstSample 0 = pure #v[] from rfl,
        Prog.time_pure]
      simp
  | succ rows ih =>
      simp [projectRows, ih, Nat.succ_mul]

@[simp]
theorem projectRows_operationCost (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (denominator : ℝ) (firstSample rows : ℕ) :
    (projectRows x denominator firstSample rows).time
        (GaussianSampling.operationCost oracle) =
      ⟨0, 0, rows * (8 * d + 1), 0, rows * (2 * d)⟩ := by
  induction rows with
  | zero =>
      rw [show projectRows x denominator firstSample 0 = pure #v[] from rfl,
        Prog.time_pure]
      simp only [zero_mul]
      rfl
  | succ rows ih =>
      simp [projectRows, ih, RealRAM.operationCost, Nat.succ_mul]
      rfl

/-- Apply a normalized `rows × d` Gaussian matrix to `x`. -/
noncomputable def project (rows : ℕ) (x : Fin d → ℝ) (firstSample : ℕ) :
    Prog GaussianSampling.Machine (Vector ℝ rows) := do
  let denominator ← GaussianSampling.liftExtension (.inl (.sqrt rows))
  projectRows x denominator firstSample rows

theorem projectRowsValue_get (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (denominator : ℝ) (firstSample : ℕ) (i : Fin rows) :
    (projectRowsValue oracle x denominator firstSample rows).get i =
      dotValue oracle x (firstSample + 2 * (i.val * d)) / denominator := by
  induction rows with
  | zero => exact Fin.elim0 i
  | succ rows ih =>
      cases i using Fin.lastCases with
      | last => simp [projectRowsValue]
      | cast i => simp [projectRowsValue, ih]

theorem dotValue_eq_matrix_mulVec (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) (i : Fin rows) :
    dotValue oracle x (firstSample + 2 * (i.val * d)) =
      Matrix.mulVec (matrix (d := d) oracle firstSample) x i := by
  simp only [dotValue, Matrix.mulVec, dotProduct, matrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

theorem projectRowsValue_eq_value (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (rows : ℕ)
    (firstSample : ℕ) :
    projectRowsValue oracle x (Real.sqrt rows) firstSample rows =
      value oracle x firstSample := by
  apply Vector.ext
  intro i hi
  let j : Fin rows := ⟨i, hi⟩
  change (projectRowsValue oracle x (Real.sqrt rows) firstSample rows).get j =
    (value oracle x firstSample).get j
  rw [projectRowsValue_get, dotValue_eq_matrix_mulVec]
  simp [value]

@[simp]
theorem project_eval (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample rows : ℕ) :
    (project rows x firstSample).eval (GaussianSampling.natCost oracle) =
      value oracle x firstSample := by
  simp [project, projectRowsValue_eq_value]

/-- Every realization of the Gaussian projection sends the zero vector to zero. -/
@[simp]
theorem value_zero (oracle : ContinuousRealSample.Oracle) (firstSample : ℕ) :
    value (rows := rows) oracle (0 : Fin d → ℝ) firstSample = Vector.replicate rows 0 := by
  apply Vector.ext
  intro i hi
  let j : Fin rows := ⟨i, hi⟩
  change (value (rows := rows) oracle (0 : Fin d → ℝ) firstSample).get j =
    (Vector.replicate rows 0).get j
  simp [value]

/-- The executable projection therefore returns zero on the zero vector. -/
theorem project_zero_eval (oracle : ContinuousRealSample.Oracle) (firstSample rows d : ℕ) :
    (project rows (0 : Fin d → ℝ) firstSample).eval (GaussianSampling.natCost oracle) =
      Vector.replicate rows 0 := by
  rw [project_eval, value_zero]

@[simp]
theorem project_time (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample rows : ℕ) :
    (project rows x firstSample).time (GaussianSampling.natCost oracle) =
      1 + rows * (10 * d + 1) := by
  simp [project]

@[simp]
theorem project_operationCost (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample rows : ℕ) :
    (project rows x firstSample).time (GaussianSampling.operationCost oracle) =
      ⟨0, 0, 1 + rows * (8 * d + 1), 0, rows * (2 * d)⟩ := by
  rw [show project rows x firstSample =
      GaussianSampling.liftExtension (.inl (.sqrt rows)) >>= fun denominator =>
        projectRows x denominator firstSample rows from rfl,
    Prog.time_bind, GaussianSampling.liftExtension_operationCost,
    GaussianSampling.sqrt_operation_eval, projectRows_operationCost]
  change (⟨0, 0, 1, 0, 0⟩ : RealRAMCost) +
    (⟨0, 0, rows * (8 * d + 1), 0, rows * (2 * d)⟩ : RealRAMCost) = _
  apply RealRAMCost.ext <;> simp

end GaussianJL

end Algolean.Algorithms
