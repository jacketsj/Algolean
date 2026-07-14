/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Algorithms.GaussianJLProbability

/-!
# Gaussian algorithm examples

Examples for the derived Box--Muller sampler and its use in a Gaussian Johnson--Lindenstrauss
projection.
-/

@[expose] public section

namespace AlgoleanTests

open Algolean Algorithms Prog

noncomputable section

/-- A concrete endpoint-valued oracle used only to evaluate deterministic realizations. -/
def gaussianExampleOracle : ContinuousRealSample.Oracle :=
  fun _ => ⟨1, by norm_num⟩

/-- One Gaussian sample is an eight-query algorithm, including its two uniform draws. -/
example :
    (GaussianSampling.standard 12).time (GaussianSampling.natCost gaussianExampleOracle) = 8 := by
  simp

/-- A two-dimensional projection of a three-dimensional vector. -/
def jlExample (x : Fin 3 → ℝ) : Prog GaussianSampling.Machine (Vector ℝ 2) :=
  GaussianJL.project 2 x 0

/-- The program evaluates exactly to the normalized Mathlib matrix-vector product. -/
example (x : Fin 3 → ℝ) :
    (jlExample x).eval (GaussianSampling.natCost gaussianExampleOracle) =
      GaussianJL.value gaussianExampleOracle x 0 := by
  simp [jlExample]

/-- The verified realization sends the zero vector to zero. -/
example :
    (jlExample (0 : Fin 3 → ℝ)).eval (GaussianSampling.natCost gaussianExampleOracle) =
      Vector.replicate 2 0 := by
  simp [jlExample]

/-- The `2 × 3` example performs 63 unit-cost queries. -/
example (x : Fin 3 → ℝ) :
    (jlExample x).time (GaussianSampling.natCost gaussianExampleOracle) = 63 := by
  norm_num [jlExample]

/-- Detailed accounting exposes 51 arithmetic instructions and 12 uniform samples. -/
example (x : Fin 3 → ℝ) :
    (jlExample x).time (GaussianSampling.operationCost gaussianExampleOracle) =
      ⟨0, 0, 51, 0, 12⟩ := by
  norm_num [jlExample]

/-- The probability layer identifies the program specification with the ideal Gaussian map. -/
example (oracle : ContinuousRealSample.Oracle) (x : Fin 3 → ℝ) :
    GaussianJL.value (rows := 2) oracle x 0 =
      Vector.ofFn (GaussianJL.idealProject (GaussianJL.matrix (rows := 2) oracle 0) x) := by
  exact GaussianJL.value_eq_idealProject oracle x 0

/-- Box--Muller sampling from the canonical uniform oracle has the standard Gaussian law. -/
example :
    ProbabilityTheory.HasLaw
      (fun oracle : ContinuousRealSample.Oracle => GaussianSampling.standardValue oracle 12)
      (ProbabilityTheory.gaussianReal 0 1) ContinuousRealSample.oracleLaw := by
  exact GaussianSampling.standardValue_hasLaw 12

/-- The usual JL application: all distances in a finite family are preserved simultaneously. -/
example {ι : Type} [Fintype ι] (points : ι → Fin 3 → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 2 * (Fintype.card ι : ℝ) ^ 2 * Real.exp (-(2 : ℝ) * ε ^ 2 / 16) ≤
      (GaussianJL.gaussianMatrixMeasure 2 3).real
        {A | GaussianJL.preservesDistances ε A points} := by
  exact GaussianJL.success_probability (by norm_num) hε0 hε1 points

/-- The same JL bound holds directly for the matrix computed from the canonical uniform oracle. -/
example {ι : Type} [Fintype ι] (points : ι → Fin 3 → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - 2 * (Fintype.card ι : ℝ) ^ 2 * Real.exp (-(2 : ℝ) * ε ^ 2 / 16) ≤
      ContinuousRealSample.oracleLaw.real
        {oracle | GaussianJL.preservesDistances ε
          (GaussianJL.matrix (rows := 2) oracle 0) points} := by
  exact GaussianJL.algorithm_success_probability
    (d := 3) (firstSample := 0) (by norm_num) hε0 hε1 points

end

end AlgoleanTests
