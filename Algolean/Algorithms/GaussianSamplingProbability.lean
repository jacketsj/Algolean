/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Algorithms.GaussianSampling
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Probability.Independence.InfinitePi

/-!
# Probability law of the Box--Muller sampler

This module proves that `GaussianSampling.standardValue`, evaluated on the canonical independent
uniform oracle, has Mathlib's standard Gaussian law.  The proof uses the change-of-variables
formula through polar coordinates; no Gaussian randomness is postulated as a machine primitive.
-/

@[expose] public section

namespace Algolean.Algorithms.GaussianSampling

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

noncomputable section

/--
The real additive structure used by Mathlib's Gaussian derivative lemmas. It is extensionally the
canonical one and is kept local to this proof module.
-/
local instance (priority := 2000) realAddCommGroup : AddCommGroup ℝ :=
  normedAddCommGroup.toAddCommGroup

/-- The corresponding local real module structure used by those derivative lemmas. -/
local instance (priority := 2000) realModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

private def radial (u : ℝ) : ℝ :=
  Real.sqrt (-2 * Real.log u)

private def centeredAngle (v : ℝ) : ℝ :=
  2 * Real.pi * v - Real.pi

private def parameters (uv : ℝ × ℝ) : ℝ × ℝ :=
  (radial uv.1, centeredAngle uv.2)

private def parameterFDeriv (uv : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (-1 / (uv.1 * radial uv.1))).prodMap
    (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi))

private theorem radial_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < radial u := by
  rw [radial, Real.sqrt_pos]
  nlinarith [Real.log_neg hu.1 hu.2]

private theorem radial_sq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    radial u ^ 2 = -2 * Real.log u := by
  rw [radial, Real.sq_sqrt]
  nlinarith [Real.log_neg hu.1 hu.2]

private theorem radial_injOn : Set.InjOn radial (Ioo (0 : ℝ) 1) := by
  intro u hu v hv huv
  have hsq := congrArg (fun x : ℝ => x ^ 2) huv
  rw [radial_sq hu, radial_sq hv] at hsq
  apply Real.strictMonoOn_log.injOn hu.1 hv.1
  linarith

private theorem radial_surjOn : Set.SurjOn radial (Ioo (0 : ℝ) 1) (Ioi 0) := by
  intro r hr
  change 0 < r at hr
  let u := Real.exp (-r ^ 2 / 2)
  have hu0 : 0 < u := Real.exp_pos _
  have huexp : -r ^ 2 / 2 < 0 := by nlinarith [sq_pos_of_pos hr]
  have hu1 : u < 1 := by
    simpa [u, ← Real.exp_zero] using Real.exp_lt_exp.mpr huexp
  refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
  dsimp [radial, u]
  rw [Real.log_exp]
  have hr0 : 0 ≤ r := hr.le
  convert Real.sqrt_sq hr0 using 1
  ring_nf

private theorem centeredAngle_injOn :
    Set.InjOn centeredAngle (Ioo (0 : ℝ) 1) := by
  intro u _ v _ huv
  unfold centeredAngle at huv
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hpi)
  linarith

private theorem centeredAngle_surjOn :
    Set.SurjOn centeredAngle (Ioo (0 : ℝ) 1) (Ioo (-Real.pi) Real.pi) := by
  intro theta htheta
  change -Real.pi < theta ∧ theta < Real.pi at htheta
  let v := (theta + Real.pi) / (2 * Real.pi)
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨v, ?_, ?_⟩
  · constructor
    · dsimp [v]
      exact div_pos (by linarith) (by positivity)
    · dsimp [v]
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
      linarith
  · dsimp [centeredAngle, v]
    field_simp [ne_of_gt hpi]
    ring

private theorem parameters_image :
    parameters '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = polarCoord.target := by
  rw [polarCoord_target]
  ext p
  constructor
  · rintro ⟨uv, huv, rfl⟩
    exact ⟨radial_pos huv.1,
      ⟨by change -Real.pi < centeredAngle uv.2
          unfold centeredAngle
          nlinarith [huv.2.1, Real.pi_pos],
        by change centeredAngle uv.2 < Real.pi
           unfold centeredAngle
           nlinarith [huv.2.2, Real.pi_pos]⟩⟩
  · intro hp
    obtain ⟨u, hu, hru⟩ := radial_surjOn hp.1
    obtain ⟨v, hv, hav⟩ := centeredAngle_surjOn hp.2
    exact ⟨(u, v), ⟨hu, hv⟩, Prod.ext hru hav⟩

private theorem parameters_injOn :
    Set.InjOn parameters (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [parameters, Prod.mk.injEq] at h
  exact Prod.ext (radial_injOn huv.1 huv'.1 h.1)
    (centeredAngle_injOn huv.2 huv'.2 h.2)

private theorem radial_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt radial (-1 / (u * radial u)) u := by
  have harg : -2 * Real.log u ≠ 0 := ne_of_gt (by nlinarith [Real.log_neg hu.1 hu.2])
  have h := ((Real.hasDerivAt_log hu.1.ne').const_mul (-2)).sqrt harg
  have hsqrt : Real.sqrt (-2 * Real.log u) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [Real.log_neg hu.1 hu.2])
  change HasDerivAt (fun x => Real.sqrt (-2 * Real.log x))
    (-1 / (u * Real.sqrt (-2 * Real.log u))) u
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hu.1.ne', hsqrt]

private theorem centeredAngle_hasDerivAt (v : ℝ) :
    HasDerivAt centeredAngle (2 * Real.pi) v := by
  convert (hasDerivAt_const_mul (x := v) (2 * Real.pi)).sub_const Real.pi using 1
  all_goals try with_reducible_and_instances rfl
  rfl

private theorem parameters_hasFDerivAt {uv : ℝ × ℝ}
    (huv : uv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    HasFDerivAt parameters (parameterFDeriv uv) uv := by
  exact (radial_hasDerivAt huv.1).hasFDerivAt.prodMap uv
    (centeredAngle_hasDerivAt uv.2).hasFDerivAt

private theorem det_parameterFDeriv (uv : ℝ × ℝ) :
    (parameterFDeriv uv).det =
      (-1 / (uv.1 * radial uv.1)) * (2 * Real.pi) := by
  have hlin : (parameterFDeriv uv).toLinearMap =
      LinearMap.prodMap
        (ContinuousLinearMap.toSpanSingleton ℝ (-1 / (uv.1 * radial uv.1))).toLinearMap
        (ContinuousLinearMap.toSpanSingleton ℝ (2 * Real.pi)).toLinearMap := rfl
  rw [ContinuousLinearMap.det, hlin, LinearMap.det_prodMap]
  simp

private theorem lintegral_parameters (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p in polarCoord.target, f p =
      ∫⁻ uv in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        ENNReal.ofReal |(parameterFDeriv uv).det| * f (parameters uv) := by
  rw [← parameters_image]
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun uv huv => (parameters_hasFDerivAt huv).hasFDerivWithinAt)
    parameters_injOn f

private theorem gaussianPDFReal_polar (r theta : ℝ) :
    gaussianPDFReal 0 1 (r * Real.cos theta) *
        gaussianPDFReal 0 1 (r * Real.sin theta) =
      (2 * Real.pi)⁻¹ * Real.exp (-r ^ 2 / 2) := by
  have htwoPi : 0 ≤ (2 * Real.pi : ℝ) := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt htwoPi
  rw [gaussianPDFReal, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r * Real.sin theta) ^ 2 / 2)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
        (Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
          Real.exp (-(r * Real.sin theta) ^ 2 / 2)) by ring]
  rw [← Real.exp_add]
  have hexp : -(r * Real.cos theta) ^ 2 / 2 + -(r * Real.sin theta) ^ 2 / 2 =
      -r ^ 2 / 2 := by
    calc
      _ = (-r ^ 2 / 2) * (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
      _ = -r ^ 2 / 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [hexp]
  congr 1
  rw [← pow_two, inv_pow, hsqrt]

private theorem uniformLaw_prod :
    ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw =
      volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  rw [ContinuousRealSample.uniformLaw, Measure.prod_restrict]
  exact Measure.restrict_congr_set
    (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm

private def centeredBoxMullerPair (uv : ℝ × ℝ) : ℝ × ℝ :=
  polarCoord.symm (parameters uv)

private theorem exp_neg_radial_sq {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    Real.exp (-radial u ^ 2 / 2) = u := by
  rw [radial_sq hu]
  convert Real.exp_log hu.1 using 1
  ring_nf

private theorem jacobian_gaussianPDFReal_cancel (uv : ℝ × ℝ)
    (huv : uv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    |(parameterFDeriv uv).det| * (parameters uv).1 *
        (gaussianPDFReal 0 1 (centeredBoxMullerPair uv).1 *
          gaussianPDFReal 0 1 (centeredBoxMullerPair uv).2) = 1 := by
  have hu : 0 < uv.1 := huv.1.1
  have hr : 0 < radial uv.1 := radial_pos huv.1
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [centeredBoxMullerPair, polarCoord_symm_apply]
  simp only [parameters]
  rw [gaussianPDFReal_polar, det_parameterFDeriv, exp_neg_radial_sq huv.1]
  have hneg : -1 / (uv.1 * radial uv.1) * (2 * Real.pi) < 0 :=
    mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by norm_num) (mul_pos hu hr))
      (by positivity)
  rw [abs_of_neg hneg]
  field_simp [hu.ne', hr.ne', hpi.ne']

private theorem jacobian_gaussianPDF_cancel (uv : ℝ × ℝ)
    (huv : uv ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal |(parameterFDeriv uv).det| *
        (ENNReal.ofReal (parameters uv).1 *
          (gaussianPDF 0 1 (centeredBoxMullerPair uv).1 *
            gaussianPDF 0 1 (centeredBoxMullerPair uv).2)) = 1 := by
  have hparam : 0 ≤ (parameters uv).1 := (radial_pos huv.1).le
  rw [← ENNReal.toReal_eq_one_iff]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal hparam, toReal_gaussianPDF]
  simpa [mul_assoc] using jacobian_gaussianPDFReal_cancel uv huv

private theorem measurable_centeredBoxMullerPair : Measurable centeredBoxMullerPair := by
  unfold centeredBoxMullerPair parameters radial centeredAngle
  fun_prop

private theorem centeredBoxMullerPair_hasLaw :
    HasLaw centeredBoxMullerPair ((gaussianReal 0 1).prod (gaussianReal 0 1))
      (ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) := by
  refine ⟨measurable_centeredBoxMullerPair.aemeasurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_centeredBoxMullerPair, uniformLaw_prod]
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  rw [lintegral_withDensity_eq_lintegral_mul (volume.prod volume) (by fun_prop) hf]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  rw [← lintegral_comp_polarCoord_symm]
  rw [lintegral_parameters]
  apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro uv huv
  change f (centeredBoxMullerPair uv) =
    ENNReal.ofReal |(parameterFDeriv uv).det| *
      (ENNReal.ofReal (parameters uv).1 *
        ((gaussianPDF 0 1 (centeredBoxMullerPair uv).1 *
          gaussianPDF 0 1 (centeredBoxMullerPair uv).2) *
            f (centeredBoxMullerPair uv)))
  rw [show ENNReal.ofReal |(parameterFDeriv uv).det| *
      (ENNReal.ofReal (parameters uv).1 *
        (gaussianPDF 0 1 (centeredBoxMullerPair uv).1 *
          gaussianPDF 0 1 (centeredBoxMullerPair uv).2 *
            f (centeredBoxMullerPair uv))) =
      (ENNReal.ofReal |(parameterFDeriv uv).det| *
        (ENNReal.ofReal (parameters uv).1 *
          (gaussianPDF 0 1 (centeredBoxMullerPair uv).1 *
            gaussianPDF 0 1 (centeredBoxMullerPair uv).2))) *
        f (centeredBoxMullerPair uv) by ac_rfl,
    jacobian_gaussianPDF_cancel uv huv, one_mul]

private theorem centeredFirst_hasLaw :
    HasLaw (fun uv => (centeredBoxMullerPair uv).1) (gaussianReal 0 1)
      (ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) := by
  exact (measurePreserving_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw.comp
    centeredBoxMullerPair_hasLaw

private def boxMullerValue (uv : ℝ × ℝ) : ℝ :=
  radial uv.1 * Real.cos ((2 * Real.pi) * uv.2)

private theorem boxMullerValue_eq_neg_centeredFirst (uv : ℝ × ℝ) :
    boxMullerValue uv = -(centeredBoxMullerPair uv).1 := by
  rw [centeredBoxMullerPair, polarCoord_symm_apply]
  simp only [parameters, centeredAngle, boxMullerValue]
  rw [Real.cos_sub_pi]
  ring

private theorem boxMullerValue_hasLaw :
    HasLaw boxMullerValue (gaussianReal 0 1)
      (ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) := by
  have h := gaussianReal_neg centeredFirst_hasLaw
  have hfun : boxMullerValue = -(fun uv => (centeredBoxMullerPair uv).1) := by
    funext uv
    exact boxMullerValue_eq_neg_centeredFirst uv
  rw [hfun]
  simpa using h

/-- The scalar Box--Muller transform sends two independent uniforms to a standard Gaussian. -/
theorem boxMuller_hasLaw :
    HasLaw (fun uv : ℝ × ℝ =>
      Real.sqrt (-2 * Real.log uv.1) * Real.cos ((2 * Real.pi) * uv.2))
      (gaussianReal 0 1)
      (ContinuousRealSample.uniformLaw.prod ContinuousRealSample.uniformLaw) := by
  have hfun : (fun uv : ℝ × ℝ =>
      Real.sqrt (-2 * Real.log uv.1) * Real.cos ((2 * Real.pi) * uv.2)) =
      boxMullerValue := by
    funext uv
    simp only [boxMullerValue, radial]
  rw [hfun]
  exact boxMullerValue_hasLaw

/-- One Box--Muller output from the canonical independent-uniform oracle is standard Gaussian. -/
theorem standardValue_hasLaw (firstSample : ℕ) :
    HasLaw (fun oracle : ContinuousRealSample.Oracle => standardValue oracle firstSample)
      (gaussianReal 0 1) ContinuousRealSample.oracleLaw := by
  have hne : firstSample ≠ firstSample + 1 := by omega
  have hpair :=
    (ContinuousRealSample.coordinates_iIndep.indepFun hne).hasLaw_prod
      (ContinuousRealSample.coordinate_hasLaw firstSample)
      (ContinuousRealSample.coordinate_hasLaw (firstSample + 1))
  simpa [boxMullerValue, radial, standardValue, Function.comp_def] using
    boxMullerValue_hasLaw.comp hpair

end

end Algolean.Algorithms.GaussianSampling
