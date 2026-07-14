/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Algorithms.GaussianJL
public import Algolean.Algorithms.GaussianSamplingProbability
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Probability guarantee for Gaussian Johnson--Lindenstrauss projections

This module proves the usual finite-set Johnson--Lindenstrauss guarantee for the Gaussian
projection implemented in `Algolean.Algorithms.GaussianJL`. If `A` is a `k × d` matrix of
independent standard Gaussians, then, for any finite family of `n` points and `0 ≤ ε ≤ 1`, all
squared pairwise distances are simultaneously preserved within factors `1 - ε` and `1 + ε` with
probability at least

`1 - 2 * n^2 * exp (-k * ε^2 / 16)`.

The proof is self-contained apart from Mathlib's Gaussian density, Gaussian integral, product
measure, and Chernoff bound. It first computes the exact moment-generating function of `Z^2`, then
proves a two-sided chi-square tail bound, the fixed-vector projection bound, and finally the finite
union bound.

`canonical_hasGaussianMatrixLaw` proves that the matrix produced by `GaussianJL.matrix` from the
canonical independent-uniform oracle has exactly the required iid Gaussian law.
`algorithm_success_probability` therefore states the probability guarantee directly for the
implemented sampler. `algorithm_success_probability_of_hasLaw` retains the more general transfer
form for alternate oracle laws.
-/

@[expose] public section

namespace Algolean.Algorithms.GaussianJL

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

noncomputable section

/-- The sample space of `k` independent real Gaussian coordinates. -/
abbrev GaussianSpace (k : ℕ) := Fin k → ℝ

/-- The product law of `k` independent standard real Gaussians. -/
def standardGaussianMeasure (k : ℕ) : Measure (GaussianSpace k) :=
  Measure.pi fun _ : Fin k => gaussianReal 0 1

instance (k : ℕ) : IsProbabilityMeasure (standardGaussianMeasure k) := by
  unfold standardGaussianMeasure
  infer_instance

/-- Squared Euclidean norm on a finite real coordinate space. -/
def normSq (x : Fin d → ℝ) : ℝ :=
  ∑ i, x i ^ 2

@[simp]
theorem normSq_zero : normSq (0 : Fin d → ℝ) = 0 := by
  simp [normSq]

theorem normSq_nonneg (x : Fin d → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem normSq_pos {x : Fin d → ℝ} (hx : x ≠ 0) : 0 < normSq x := by
  apply lt_of_le_of_ne (normSq_nonneg x)
  intro h
  apply hx
  rw [← dotProduct_self_eq_zero]
  simpa [normSq, dotProduct, pow_two] using h.symm

/-- Exact moment-generating function of the square of a standard Gaussian. -/
theorem gaussian_square_mgf {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  unfold mgf
  rw [integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := (0 : ℝ))
    (v := (1 : NNReal)) (f := fun x : ℝ => Real.exp (t * x ^ 2)) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hb : 0 < 1 / 2 - t := by linarith
  have hfun : (fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (t * x ^ 2)) =
      fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(1 / 2 - t) * x ^ 2) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian]
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.sqrt_div (by positivity), inv_mul_eq_div]
  have ha : 1 - 2 * t = 2 * (1 / 2 - t) := by ring
  rw [ha, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr htwo
  have hsb : Real.sqrt (1 / 2 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr hb
  have hsp : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr hpi
  field_simp [hs2, hsb, hsp]

private theorem coordinateSquare_identDistrib (i : Fin k) :
    IdentDistrib (fun z : GaussianSpace k => z i ^ 2) (fun x : ℝ => x ^ 2)
      (standardGaussianMeasure k) (gaussianReal 0 1) := by
  have h := (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) i).hasLaw
  simpa [GaussianSpace, standardGaussianMeasure, Function.comp_def] using
    (h.identDistrib HasLaw.id).comp (measurable_id.pow_const 2)

private theorem independent_coordinateSquares :
    iIndepFun (fun i (z : GaussianSpace k) => z i ^ 2) (standardGaussianMeasure k) := by
  have h := iIndepFun_pi (μ := fun _ : Fin k => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  simpa [GaussianSpace, standardGaussianMeasure, Function.comp_def] using
    h.comp (fun _ => fun x : ℝ => x ^ 2) (fun _ => measurable_id.pow_const 2)

/-- Exact MGF of the squared norm of `k` independent standard Gaussians. -/
theorem normSq_mgf {t : ℝ} (ht : t < 1 / 2) :
    mgf (normSq (d := k)) (standardGaussianMeasure k) t =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ k := by
  unfold normSq
  rw [show (fun z : GaussianSpace k => ∑ i, z i ^ 2) =
      ∑ i ∈ Finset.univ, fun z : GaussianSpace k => z i ^ 2 by
    ext z
    simp]
  rw [independent_coordinateSquares.mgf_sum
    (fun _ => (measurable_pi_apply _).pow_const 2)]
  calc
    ∏ i : Fin k,
        mgf (fun z : GaussianSpace k => z i ^ 2) (standardGaussianMeasure k) t =
        ∏ _i : Fin k, (Real.sqrt (1 - 2 * t))⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [mgf_congr_identDistrib (coordinateSquare_identDistrib i)]
      exact gaussian_square_mgf ht
    _ = _ := by simp

private theorem invSqrt_pow_eq_exp {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ((Real.sqrt a)⁻¹) ^ k =
      Real.exp (-(k : ℝ) / 2 * Real.log a) := by
  calc
    ((Real.sqrt a)⁻¹) ^ k = (Real.exp (-Real.log (Real.sqrt a))) ^ k := by
      rw [Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 ha)]
    _ = Real.exp ((k : ℝ) * (-Real.log (Real.sqrt a))) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(k : ℝ) / 2 * Real.log a) := by
      rw [Real.log_sqrt ha.le]
      congr 1
      ring

private theorem integrable_exp_normSq {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun z : GaussianSpace k => Real.exp (t * normSq z))
      (standardGaussianMeasure k) := by
  rw [← mgf_pos_iff]
  rw [normSq_mgf ht]
  have : 0 < 1 - 2 * t := by linarith
  positivity

private theorem upperTail {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (standardGaussianMeasure k).real
        {z | (k : ℝ) * (1 + ε) ≤ normSq z} ≤
      Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
  let t := ε / 8
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t < 1 / 2 := by dsimp [t]; linarith
  have ha : 0 < 1 - ε / 4 := by linarith
  have hlog : -Real.log (1 - ε / 4) ≤ (1 - ε / 4)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos ha]
  have hscalar :
      -(ε / 8) * (1 + ε) - 1 / 2 * Real.log (1 - ε / 4) ≤
        -ε ^ 2 / 16 := by
    calc
      -(ε / 8) * (1 + ε) - 1 / 2 * Real.log (1 - ε / 4) ≤
          -(ε / 8) * (1 + ε) + 1 / 2 * ((1 - ε / 4)⁻¹ - 1) := by
        linarith
      _ = -ε ^ 2 * (3 - ε) / (32 * (1 - ε / 4)) := by
        have h4 : 4 - ε ≠ 0 := by linarith
        field_simp [ha.ne', h4]
        ring
      _ ≤ -ε ^ 2 / 16 := by
        rw [div_le_iff₀ (by positivity : 0 < 32 * (1 - ε / 4))]
        nlinarith [sq_nonneg ε]
  calc
    (standardGaussianMeasure k).real {z | (k : ℝ) * (1 + ε) ≤ normSq z} ≤
        Real.exp (-t * ((k : ℝ) * (1 + ε))) *
          mgf (normSq (d := k)) (standardGaussianMeasure k) t :=
      measure_ge_le_exp_mul_mgf _ ht0 (integrable_exp_normSq ht)
    _ = Real.exp ((k : ℝ) *
        (-(ε / 8) * (1 + ε) - 1 / 2 * Real.log (1 - ε / 4))) := by
      rw [normSq_mgf ht]
      dsimp [t]
      rw [show 1 - 2 * (ε / 8) = 1 - ε / 4 by ring]
      rw [invSqrt_pow_eq_exp ha, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg k)]

private theorem lowerTail {ε : ℝ} (hε0 : 0 ≤ ε) :
    (standardGaussianMeasure k).real
        {z | normSq z ≤ (k : ℝ) * (1 - ε)} ≤
      Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
  let t := -ε / 4
  have ht0 : t ≤ 0 := by dsimp [t]; linarith
  have ht : t < 1 / 2 := by dsimp [t]; linarith
  have ha : 0 < 1 + ε / 2 := by linarith
  have hlog : 1 - (1 + ε / 2)⁻¹ ≤ Real.log (1 + ε / 2) :=
    Real.one_sub_inv_le_log_of_pos ha
  have hscalar :
      ε / 4 * (1 - ε) - 1 / 2 * Real.log (1 + ε / 2) ≤
        -ε ^ 2 / 16 := by
    calc
      ε / 4 * (1 - ε) - 1 / 2 * Real.log (1 + ε / 2) ≤
          ε / 4 * (1 - ε) - 1 / 2 * (1 - (1 + ε / 2)⁻¹) := by
        linarith
      _ = -ε ^ 2 * (1 + ε) / (4 * (2 + ε)) := by
        have h2 : 2 + ε ≠ 0 := by linarith
        field_simp [ha.ne', h2]
        ring
      _ ≤ -ε ^ 2 / 16 := by
        rw [div_le_iff₀ (by positivity : 0 < 4 * (2 + ε))]
        nlinarith [sq_nonneg ε]
  calc
    (standardGaussianMeasure k).real {z | normSq z ≤ (k : ℝ) * (1 - ε)} ≤
        Real.exp (-t * ((k : ℝ) * (1 - ε))) *
          mgf (normSq (d := k)) (standardGaussianMeasure k) t :=
      measure_le_le_exp_mul_mgf _ ht0 (integrable_exp_normSq ht)
    _ = Real.exp ((k : ℝ) *
        (ε / 4 * (1 - ε) - 1 / 2 * Real.log (1 + ε / 2))) := by
      rw [normSq_mgf ht]
      dsimp [t]
      rw [show 1 - 2 * (-ε / 4) = 1 + ε / 2 by ring]
      rw [invSqrt_pow_eq_exp ha, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg k)]

/-- Two-sided chi-square concentration for `k` independent standard Gaussians. -/
theorem normSq_two_sided_tail {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (standardGaussianMeasure k).real
        ({z | normSq z ≤ (k : ℝ) * (1 - ε)} ∪
          {z | (k : ℝ) * (1 + ε) ≤ normSq z}) ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
  calc
    _ ≤ (standardGaussianMeasure k).real {z | normSq z ≤ (k : ℝ) * (1 - ε)} +
        (standardGaussianMeasure k).real {z | (k : ℝ) * (1 + ε) ≤ normSq z} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(k : ℝ) * ε ^ 2 / 16) +
        Real.exp (-(k : ℝ) * ε ^ 2 / 16) :=
      add_le_add (lowerTail hε0) (upperTail hε0 hε1)
    _ = _ := by ring

section GaussianDotLaw

/-- Mathlib's real inner-product module, used locally by `HasGaussianLaw.map`. -/
noncomputable local instance realModuleForGaussian : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

private theorem coordinate_hasGaussianLaw (i : Fin d) :
    HasGaussianLaw (fun z : GaussianSpace d => z i) (standardGaussianMeasure d) :=
  (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).hasLaw.hasGaussianLaw

private theorem vector_hasGaussianLaw :
    HasGaussianLaw (fun z : GaussianSpace d => z) (standardGaussianMeasure d) := by
  have hindep := iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  simpa [GaussianSpace, standardGaussianMeasure] using
    hindep.hasGaussianLaw (coordinate_hasGaussianLaw (d := d))

private theorem integral_dotProduct (v : Fin d → ℝ) :
    ∫ z, v ⬝ᵥ z ∂standardGaussianMeasure d = 0 := by
  unfold dotProduct standardGaussianMeasure
  rw [integral_finsetSum]
  · simp [integral_const_mul, integral_eval]
  · intro i _
    exact (integrable_eval IsGaussian.integrable_id).const_mul _

private theorem variance_dotProduct (v : Fin d → ℝ) :
    Var[(v ⬝ᵥ ·); standardGaussianMeasure d] = normSq v := by
  unfold dotProduct standardGaussianMeasure normSq
  rw [show (fun z : Fin d → ℝ => ∑ i, v i * z i) =
      ∑ i, fun z : Fin d → ℝ => v i * z i by
    ext z
    simp]
  rw [variance_sum_pi (X := fun i (x : ℝ) => v i * x)
    (fun i => IsGaussian.memLp_two_id.const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_const_mul, variance_fun_id_gaussianReal]
  norm_num

/-- A fixed linear functional of a standard Gaussian vector is Gaussian with variance `‖v‖²`. -/
theorem dotProduct_hasLaw (v : Fin d → ℝ) :
    HasLaw (fun z => v ⬝ᵥ z)
      (gaussianReal 0 (⟨normSq v, normSq_nonneg v⟩ : NNReal))
      (standardGaussianMeasure d) := by
  let L : (Fin d → ℝ) →L[ℝ] ℝ :=
    ∑ i, v i • ContinuousLinearMap.proj i
  have h := (vector_hasGaussianLaw (d := d)).map L
  have hfun : L ∘ (fun z : GaussianSpace d => z) = fun z => v ⬝ᵥ z := by
    funext z
    simp [L, dotProduct]
  rw [hfun] at h
  refine ⟨h.aemeasurable, ?_⟩
  rw [h.map_eq_gaussianReal, integral_dotProduct, variance_dotProduct]
  congr 2
  ext
  exact Real.coe_toNNReal _ (normSq_nonneg v)

end GaussianDotLaw

private def normalizedDot (v z : Fin d → ℝ) : ℝ :=
  (v ⬝ᵥ z) / Real.sqrt (normSq v)

private theorem normalizedDot_hasLaw {v : Fin d → ℝ} (hv : v ≠ 0) :
    HasLaw (normalizedDot v) (gaussianReal 0 1) (standardGaussianMeasure d) := by
  let s := normSq v
  have hs : 0 < s := normSq_pos hv
  let u : Fin d → ℝ := fun i => v i / Real.sqrt s
  have hu : normSq u = 1 := by
    calc
      normSq u = (∑ i, v i ^ 2) / (Real.sqrt s) ^ 2 := by
        simp only [normSq, u, div_pow]
        rw [Finset.sum_div]
      _ = s / s := by rw [Real.sq_sqrt hs.le]; rfl
      _ = 1 := div_self hs.ne'
  have h := dotProduct_hasLaw u
  have huNN : (⟨normSq u, normSq_nonneg u⟩ : NNReal) = 1 := by
    ext
    exact hu
  have hlaw : gaussianReal 0 (⟨normSq u, normSq_nonneg u⟩ : NNReal) =
      gaussianReal 0 1 := by
    rw [huNN]
    rfl
  rw [hlaw] at h
  have hfun : (fun z => u ⬝ᵥ z) = normalizedDot v := by
    funext z
    simp only [dotProduct, u, normalizedDot, s]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun] at h
  exact h

/-- The sample space of `k × d` real matrices. -/
abbrev GaussianMatrixSpace (k d : ℕ) := Fin k → GaussianSpace d

/-- Product law of a `k × d` matrix of independent standard Gaussians. -/
def gaussianMatrixMeasure (k d : ℕ) : Measure (GaussianMatrixSpace k d) :=
  Measure.pi fun _ : Fin k => standardGaussianMeasure d

instance (k d : ℕ) : IsProbabilityMeasure (gaussianMatrixMeasure k d) := by
  unfold gaussianMatrixMeasure
  infer_instance

private def normalizedDots (v : Fin d → ℝ) (A : GaussianMatrixSpace k d) :
    GaussianSpace k :=
  fun i => normalizedDot v (A i)

private theorem normalizedDots_hasLaw {v : Fin d → ℝ} (hv : v ≠ 0) :
    HasLaw (normalizedDots (k := k) v) (standardGaussianMeasure k)
      (gaussianMatrixMeasure k d) := by
  have hm : Measurable (normalizedDot v) := by
    unfold normalizedDot dotProduct
    fun_prop
  refine ⟨(measurable_pi_lambda _ fun i => hm.comp (measurable_pi_apply i)).aemeasurable, ?_⟩
  unfold normalizedDots gaussianMatrixMeasure
  rw [Measure.pi_map_pi (fun _ => (normalizedDot_hasLaw hv).aemeasurable)]
  unfold standardGaussianMeasure
  apply congrArg Measure.pi
  funext i
  exact (normalizedDot_hasLaw hv).map_eq

/-- The normalized Gaussian matrix projection `x ↦ Ax / √k`. -/
def idealProject (A : GaussianMatrixSpace k d) (x : Fin d → ℝ) : Fin k → ℝ :=
  fun i => (x ⬝ᵥ A i) / Real.sqrt k

theorem idealProject_sub (A : GaussianMatrixSpace k d) (x y : Fin d → ℝ) :
    idealProject A (x - y) = idealProject A x - idealProject A y := by
  funext i
  unfold idealProject dotProduct
  simp only [Pi.sub_apply]
  rw [show (∑ j, (x j - y j) * A i j) =
      (∑ j, x j * A i j) - ∑ j, y j * A i j by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  ring

private theorem normSq_idealProject {v : Fin d → ℝ} (hk : 0 < k) (hv : v ≠ 0)
    (A : GaussianMatrixSpace k d) :
    normSq (idealProject A v) =
      normSq v / k * normSq (normalizedDots v A) := by
  have hkr : 0 < (k : ℝ) := by positivity
  have hsv : 0 < normSq v := normSq_pos hv
  unfold normSq idealProject normalizedDots normalizedDot dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, div_pow, Real.sq_sqrt hkr.le, Real.sq_sqrt hsv.le]
  field_simp [hkr.ne', hsv.ne']
  rfl

private def badNorm (ε : ℝ) (A : GaussianMatrixSpace k d) (v : Fin d → ℝ) : Prop :=
  normSq (idealProject A v) < (1 - ε) * normSq v ∨
    (1 + ε) * normSq v < normSq (idealProject A v)

private theorem badNorm_subset_normalizedTails {ε : ℝ} (hk : 0 < k)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    {A : GaussianMatrixSpace k d | badNorm ε A v} ⊆
      {A | normSq (normalizedDots v A) ≤ (k : ℝ) * (1 - ε)} ∪
        {A | (k : ℝ) * (1 + ε) ≤ normSq (normalizedDots v A)} := by
  intro A hA
  have hkr : 0 < (k : ℝ) := by positivity
  have hsv : 0 < normSq v := normSq_pos hv
  have hfactor : 0 < normSq v / (k : ℝ) := div_pos hsv hkr
  have hnorm := normSq_idealProject hk hv A
  rcases hA with hlower | hupper
  · left
    change normSq (normalizedDots v A) ≤ (k : ℝ) * (1 - ε)
    apply le_of_lt
    apply lt_of_mul_lt_mul_left _ hfactor.le
    rw [← hnorm]
    calc
      normSq (idealProject A v) < (1 - ε) * normSq v := hlower
      _ = normSq v / (k : ℝ) * ((k : ℝ) * (1 - ε)) := by
        field_simp [hkr.ne']
  · right
    change (k : ℝ) * (1 + ε) ≤ normSq (normalizedDots v A)
    apply le_of_lt
    apply lt_of_mul_lt_mul_left _ hfactor.le
    rw [← hnorm]
    calc
      normSq v / (k : ℝ) * ((k : ℝ) * (1 + ε)) =
          (1 + ε) * normSq v := by
        field_simp [hkr.ne']
      _ < normSq (idealProject A v) := hupper

private theorem badNorm_probability {ε : ℝ} (hk : 0 < k)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (v : Fin d → ℝ) :
    (gaussianMatrixMeasure k d).real {A | badNorm ε A v} ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
  by_cases hv : v = 0
  · subst v
    have hempty : {A : GaussianMatrixSpace k d | badNorm ε A 0} = ∅ := by
      ext A
      simp [badNorm, idealProject, dotProduct, normSq]
    rw [hempty]
    simp only [measureReal_empty]
    positivity
  · have hmeas : MeasurableSet
        ({z : GaussianSpace k | normSq z ≤ (k : ℝ) * (1 - ε)} ∪
          {z | (k : ℝ) * (1 + ε) ≤ normSq z}) := by
      have hn : Measurable (normSq (d := k)) := by
        unfold normSq
        fun_prop
      exact (measurableSet_le hn measurable_const).union
        (measurableSet_le measurable_const hn)
    calc
      (gaussianMatrixMeasure k d).real {A | badNorm ε A v} ≤
          (gaussianMatrixMeasure k d).real
            ((normalizedDots v) ⁻¹'
              ({z : GaussianSpace k | normSq z ≤ (k : ℝ) * (1 - ε)} ∪
                {z | (k : ℝ) * (1 + ε) ≤ normSq z})) := by
        exact measureReal_mono (badNorm_subset_normalizedTails hk hv) (by finiteness)
      _ = (standardGaussianMeasure k).real
          ({z : GaussianSpace k | normSq z ≤ (k : ℝ) * (1 - ε)} ∪
            {z | (k : ℝ) * (1 + ε) ≤ normSq z}) :=
        (normalizedDots_hasLaw hv).measureReal_eq hmeas
      _ ≤ _ := normSq_two_sided_tail hε0 hε1

/--
`A` preserves all squared distances among `points` within multiplicative factors `1 ± ε`.
-/
def preservesDistances (ε : ℝ) (A : GaussianMatrixSpace k d)
    (points : ι → Fin d → ℝ) : Prop :=
  ∀ i j,
    (1 - ε) * normSq (points i - points j) ≤
        normSq (idealProject A (points i) - idealProject A (points j)) ∧
      normSq (idealProject A (points i) - idealProject A (points j)) ≤
        (1 + ε) * normSq (points i - points j)

private theorem not_pairPreserved_iff_badNorm (ε : ℝ) (A : GaussianMatrixSpace k d)
    (x y : Fin d → ℝ) :
    ¬((1 - ε) * normSq (x - y) ≤ normSq (idealProject A x - idealProject A y) ∧
      normSq (idealProject A x - idealProject A y) ≤ (1 + ε) * normSq (x - y)) ↔
      badNorm ε A (x - y) := by
  simp only [badNorm, not_and_or, not_le]
  rw [idealProject_sub]

/--
The usual finite-set Gaussian JL failure bound. With probability at least the complement of the
right-hand side, every squared pairwise distance among the `n = Fintype.card ι` input points is
preserved within factors `1 - ε` and `1 + ε`.
-/
theorem failure_probability [Fintype ι] {ε : ℝ} (hk : 0 < k)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (points : ι → Fin d → ℝ) :
    (gaussianMatrixMeasure k d).real {A | ¬preservesDistances ε A points} ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
  classical
  have hfailure : {A : GaussianMatrixSpace k d | ¬preservesDistances ε A points} =
      ⋃ i, ⋃ j, {A | badNorm ε A (points i - points j)} := by
    ext A
    simp only [Set.mem_setOf_eq, preservesDistances, not_forall, Set.mem_iUnion]
    constructor
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, (not_pairPreserved_iff_badNorm ε A _ _).mp hij⟩
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, (not_pairPreserved_iff_badNorm ε A _ _).mpr hij⟩
  rw [hfailure]
  calc
    (gaussianMatrixMeasure k d).real (⋃ i, ⋃ j,
        {A | badNorm ε A (points i - points j)}) ≤
        ∑ i, (gaussianMatrixMeasure k d).real
          (⋃ j, {A | badNorm ε A (points i - points j)}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, ∑ j, (gaussianMatrixMeasure k d).real
          {A | badNorm ε A (points i - points j)} := by
      gcongr with i
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, ∑ _j : ι,
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
      gcongr with i j
      exact badNorm_probability hk hε0 hε1 _
    _ = 2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-(k : ℝ) * ε ^ 2 / 16) := by
      simp
      ring

theorem measurableSet_preservesDistances [Finite ι] (ε : ℝ)
    (points : ι → Fin d → ℝ) :
    MeasurableSet {A : GaussianMatrixSpace k d | preservesDistances ε A points} := by
  unfold preservesDistances normSq idealProject dotProduct
  measurability

/-- The finite-set Gaussian JL theorem, stated directly as a lower bound on success probability. -/
theorem success_probability [Fintype ι] {k : ℕ} {ε : ℝ} (hk : 0 < k)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (points : ι → Fin d → ℝ) :
    1 - 2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-(k : ℝ) * ε ^ 2 / 16) ≤
      (gaussianMatrixMeasure k d).real {A | preservesDistances ε A points} := by
  have hfail := failure_probability hk hε0 hε1 points
  have hgood := measurableSet_preservesDistances (k := k) ε points
  have hset : {A : GaussianMatrixSpace k d | ¬preservesDistances ε A points} =
      {A | preservesDistances ε A points}ᶜ := by rfl
  rw [hset, measureReal_compl hgood, probReal_univ] at hfail
  linarith

/-- The program's matrix-vector specification is exactly the ideal Gaussian projection. -/
theorem value_eq_idealProject (oracle : ContinuousRealSample.Oracle) (x : Fin d → ℝ)
    (firstSample : ℕ) :
    value (rows := k) oracle x firstSample =
      Vector.ofFn (idealProject (matrix (rows := k) oracle firstSample) x) := by
  apply Vector.ext
  intro i hi
  let row : Fin k := ⟨i, hi⟩
  change (value (rows := k) oracle x firstSample).get row =
    (Vector.ofFn (idealProject (matrix (rows := k) oracle firstSample) x)).get row
  simp only [value, Vector.get_ofFn, idealProject]
  congr 1
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro j _
  ring

private abbrev MatrixEntry (k d : ℕ) := Fin k × Fin d

/-- The two uniform-tape coordinates assigned to one row-major matrix entry. -/
private def matrixSampleIndex (firstSample : ℕ)
    (p : MatrixEntry k d × Fin 2) : ℕ :=
  firstSample + 2 * (finProdFinEquiv p.1).val + p.2.val

private theorem matrixSampleIndex_injective (firstSample k d : ℕ) :
    Function.Injective (matrixSampleIndex (k := k) (d := d) firstSample) := by
  intro p q hpq
  simp only [matrixSampleIndex] at hpq
  have hbit : p.2.val = q.2.val := by omega
  have hentry : (finProdFinEquiv p.1).val = (finProdFinEquiv q.1).val := by omega
  apply Prod.ext
  · exact finProdFinEquiv.injective (Fin.ext hentry)
  · exact Fin.ext hbit

/-- The matrix generated from a random oracle has the ideal independent-Gaussian matrix law. -/
def HasGaussianMatrixLaw (P : Measure ContinuousRealSample.Oracle)
    (firstSample k d : ℕ) : Prop :=
  HasLaw (fun oracle => matrix (rows := k) (d := d) oracle firstSample)
    (gaussianMatrixMeasure k d) P

/-- Under the canonical uniform-oracle law, the algorithm generates an iid Gaussian matrix. -/
theorem canonical_hasGaussianMatrixLaw (firstSample k d : ℕ) :
    HasGaussianMatrixLaw ContinuousRealSample.oracleLaw firstSample k d := by
  let Entry := MatrixEntry k d
  let selected : ContinuousRealSample.Oracle → Entry × Fin 2 → ℝ :=
    fun oracle p => oracle (matrixSampleIndex firstSample p)
  have hselectedIndep : iIndepFun (fun p oracle => selected oracle p)
      ContinuousRealSample.oracleLaw := by
    simpa [selected, Function.comp_def] using
      ContinuousRealSample.coordinates_iIndep.precomp
        (matrixSampleIndex_injective firstSample k d)
  have hselected : HasLaw selected
      (Measure.infinitePi fun _ : Entry × Fin 2 => ContinuousRealSample.uniformLaw)
      ContinuousRealSample.oracleLaw := by
    exact hselectedIndep.hasLaw_infinitePi
      (fun p => ContinuousRealSample.coordinate_hasLaw (matrixSampleIndex firstSample p))
      ((measurable_pi_lambda _ fun p =>
        measurable_subtype_coe.comp
          (measurable_pi_apply (matrixSampleIndex firstSample p))).aemeasurable)
  let grouped : ContinuousRealSample.Oracle → Entry → Fin 2 → ℝ :=
    fun oracle => MeasurableEquiv.curry Entry (Fin 2) ℝ (selected oracle)
  have hgroupTransform : HasLaw (MeasurableEquiv.curry Entry (Fin 2) ℝ)
      (Measure.infinitePi fun _ : Entry =>
        Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw)
      (Measure.infinitePi fun _ : Entry × Fin 2 => ContinuousRealSample.uniformLaw) := by
    exact ⟨by fun_prop, Measure.infinitePi_map_curry
      (fun _ : Entry => fun _ : Fin 2 => ContinuousRealSample.uniformLaw)⟩
  have hgrouped : HasLaw grouped
      (Measure.infinitePi fun _ : Entry =>
        Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw)
      ContinuousRealSample.oracleLaw := by
    simpa [grouped, Function.comp_def] using hgroupTransform.comp hselected
  let pairs : ContinuousRealSample.Oracle → Entry → ℝ × ℝ :=
    fun oracle e => MeasurableEquiv.finTwoArrow (grouped oracle e)
  have hfinTwo :
      (Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw).map
          MeasurableEquiv.finTwoArrow =
        ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw := by
    rw [Measure.infinitePi_eq_pi]
    exact (measurePreserving_finTwoArrow ContinuousRealSample.uniformLaw).map_eq
  have hpairTransform : HasLaw
      (fun x : Entry → Fin 2 → ℝ => fun e => MeasurableEquiv.finTwoArrow (x e))
      (Measure.infinitePi fun _ : Entry =>
        ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw)
      (Measure.infinitePi fun _ : Entry =>
        Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw) := by
    refine ⟨(measurable_pi_lambda _ fun e =>
      MeasurableEquiv.finTwoArrow.measurable.comp (measurable_pi_apply e)).aemeasurable, ?_⟩
    calc
      Measure.map (fun x : Entry → Fin 2 → ℝ =>
          fun e => MeasurableEquiv.finTwoArrow (x e))
          (Measure.infinitePi fun _ : Entry =>
            Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw) =
          Measure.infinitePi fun _ : Entry =>
            (Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw).map
              MeasurableEquiv.finTwoArrow :=
        Measure.infinitePi_map_pi
          (fun _ : Entry =>
            Measure.infinitePi fun _ : Fin 2 => ContinuousRealSample.uniformLaw)
          (f := fun _ : Entry => MeasurableEquiv.finTwoArrow) (fun _ => by fun_prop)
      _ = Measure.infinitePi fun _ : Entry =>
          ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw := by
        congrm Measure.infinitePi fun e => ?_
        exact hfinTwo
  have hpairs : HasLaw pairs
      (Measure.infinitePi fun _ : Entry =>
        ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw)
      ContinuousRealSample.oracleLaw := by
    simpa [pairs, grouped, Function.comp_def] using hpairTransform.comp hgrouped
  let coefficients : ContinuousRealSample.Oracle → Entry → ℝ :=
    fun oracle e =>
      Real.sqrt (-2 * Real.log (pairs oracle e).1) *
        Real.cos ((2 * Real.pi) * (pairs oracle e).2)
  have hcoefficientTransform : HasLaw
      (fun x : Entry → ℝ × ℝ => fun e =>
        Real.sqrt (-2 * Real.log (x e).1) * Real.cos ((2 * Real.pi) * (x e).2))
      (Measure.infinitePi fun _ : Entry => gaussianReal 0 1)
      (Measure.infinitePi fun _ : Entry =>
        ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) := by
    refine ⟨(measurable_pi_lambda _ fun e => by
      change Measurable (fun x : Entry → ℝ × ℝ =>
        Real.sqrt (-2 * Real.log (x e).1) * Real.cos ((2 * Real.pi) * (x e).2))
      fun_prop).aemeasurable, ?_⟩
    calc
      Measure.map
          (fun x : Entry → ℝ × ℝ => fun e =>
            Real.sqrt (-2 * Real.log (x e).1) * Real.cos ((2 * Real.pi) * (x e).2))
          (Measure.infinitePi fun _ : Entry =>
            ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) =
          Measure.infinitePi fun _ : Entry =>
            (ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw).map
              (fun uv : ℝ × ℝ =>
                Real.sqrt (-2 * Real.log uv.1) * Real.cos ((2 * Real.pi) * uv.2)) :=
        Measure.infinitePi_map_pi
          (fun _ : Entry =>
            ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw)
          (f := fun _ : Entry => fun uv : ℝ × ℝ =>
            Real.sqrt (-2 * Real.log uv.1) * Real.cos ((2 * Real.pi) * uv.2))
          (fun _ => by fun_prop)
      _ = Measure.infinitePi fun _ : Entry => gaussianReal 0 1 := by
        congrm Measure.infinitePi fun e => ?_
        exact GaussianSampling.boxMuller_hasLaw.map_eq
  have hcoefficients : HasLaw coefficients
      (Measure.infinitePi fun _ : Entry => gaussianReal 0 1)
      ContinuousRealSample.oracleLaw := by
    simpa [coefficients, Function.comp_def] using hcoefficientTransform.comp hpairs
  have hmatrixTransform : HasLaw (MeasurableEquiv.curry (Fin k) (Fin d) ℝ)
      (gaussianMatrixMeasure k d)
      (Measure.infinitePi fun _ : Fin k × Fin d => gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    calc
      (Measure.infinitePi fun _ : Fin k × Fin d => gaussianReal 0 1).map
          (MeasurableEquiv.curry (Fin k) (Fin d) ℝ) =
          Measure.infinitePi fun _ : Fin k =>
            Measure.infinitePi fun _ : Fin d => gaussianReal 0 1 :=
        Measure.infinitePi_map_curry
          (fun _ : Fin k => fun _ : Fin d => gaussianReal 0 1)
      _ = gaussianMatrixMeasure k d := by
        simp_rw [Measure.infinitePi_eq_pi]
        rfl
  have hmatrix := hmatrixTransform.comp hcoefficients
  unfold HasGaussianMatrixLaw
  have hfun : (fun oracle =>
      MeasurableEquiv.curry (Fin k) (Fin d) ℝ (coefficients oracle)) =
      fun oracle => matrix (rows := k) (d := d) oracle firstSample := by
    funext oracle i j
    have hflat : (finProdFinEquiv (i, j)).val = i.val * d + j.val := by
      change j.val + d * i.val = i.val * d + j.val
      rw [Nat.mul_comm d i.val, Nat.add_comm]
    unfold coefficients pairs grouped selected matrixSampleIndex matrix
    simp only [MeasurableEquiv.curry_apply, MeasurableEquiv.finTwoArrow_apply]
    rw [hflat]
    unfold GaussianSampling.standardValue
    congr 2
  rw [← hfun]
  change HasLaw (fun oracle =>
    MeasurableEquiv.curry (Fin k) (Fin d) ℝ (coefficients oracle))
      (gaussianMatrixMeasure k d) ContinuousRealSample.oracleLaw
  exact hmatrix.congr (Filter.Eventually.of_forall fun _ => rfl)

/--
Transfer the finite-set JL theorem to the matrix actually generated by the Box--Muller real-RAM
algorithm. The sole hypothesis is its explicit matrix-law contract.
-/
theorem algorithm_success_probability_of_hasLaw [Fintype ι]
    {P : Measure ContinuousRealSample.Oracle} [IsProbabilityMeasure P]
    {k : ℕ} {ε : ℝ} (hLaw : HasGaussianMatrixLaw P firstSample k d)
    (hk : 0 < k) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (points : ι → Fin d → ℝ) :
    1 - 2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-(k : ℝ) * ε ^ 2 / 16) ≤
      P.real {oracle | preservesDistances (k := k) ε
        (matrix (rows := k) oracle firstSample) points} := by
  rw [hLaw.measureReal_eq (measurableSet_preservesDistances ε points)]
  exact success_probability hk hε0 hε1 points

/--
The implemented Box--Muller projection preserves all pairwise squared distances in a finite family
within factors `1 - ε` and `1 + ε`, with the usual Gaussian JL probability bound.
-/
theorem algorithm_success_probability [Fintype ι]
    {k : ℕ} {ε : ℝ} (hk : 0 < k) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (points : ι → Fin d → ℝ) :
    1 - 2 * (Fintype.card ι : ℝ) ^ 2 *
        Real.exp (-(k : ℝ) * ε ^ 2 / 16) ≤
      ContinuousRealSample.oracleLaw.real {oracle | preservesDistances (k := k) ε
        (matrix (rows := k) oracle firstSample) points} :=
  algorithm_success_probability_of_hasLaw
    (canonical_hasGaussianMatrixLaw firstSample k d) hk hε0 hε1 points

end

end Algolean.Algorithms.GaussianJL
