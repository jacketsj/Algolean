/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Algorithms.GaussianSampling

/-!
# Modular extended and continuously randomized real-RAM examples

These examples check that optional operations form independent machine instances, arbitrary
extension effects compose, and a Gaussian value is computed from primitive continuous-uniform
samples on a suitably extended real RAM.
-/

@[expose] public section

namespace AlgoleanTests

open Algolean Algorithms Prog

noncomputable section

/-- A real RAM with square root as its only optional primitive. -/
def sqrtOnlyModel : Model SqrtRealRAM ℕ :=
  ExtendedRealRAM.natCost RealRAM.Sqrt.natCost

/-- A distinct real RAM with general real power as its only optional primitive. -/
def realPowOnlyModel : Model RealPowRAM ℕ :=
  ExtendedRealRAM.natCost RealRAM.RealPow.natCost

example : sqrtOnlyModel.evalQuery (ExtendedRealRAM.ofExtension (.sqrt 9)) = 3 := by
  change √(9 : ℝ) = 3
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

example : realPowOnlyModel.evalQuery (ExtendedRealRAM.ofExtension (.pow 4 (3 : ℝ))) = 64 := by
  norm_num [realPowOnlyModel, ExtendedRealRAM.natCost, ExtendedRealRAM.model,
    ExtendedRealRAM.ofExtension, Model.combine, RealRAM.RealPow.natCost,
    RealRAM.RealPow.eval, Real.rpow_natCast]

/-- Independently selected root, logarithm, and exponential effects. -/
abbrev RootLogExp :=
  RealRAM.ExtensionSum RealRAM.NthRoot (RealRAM.ExtensionSum RealRAM.Log RealRAM.Exp)

def rootLogExpExtensionModel : Model RootLogExp ℕ :=
  RealRAM.NthRoot.natCost.combine (RealRAM.Log.natCost.combine RealRAM.Exp.natCost)

def rootLogExpModel : Model (ExtendedRealRAM RootLogExp) ℕ :=
  ExtendedRealRAM.natCost rootLogExpExtensionModel

/-- Use two independently composed extension effects in one program. -/
def rootThenExp (degree : ℕ) (x : ℝ) : Prog (ExtendedRealRAM RootLogExp) ℝ := do
  let root : ℝ ← ExtendedRealRAM.liftExtension (.inl (.nthRoot degree x))
  ExtendedRealRAM.liftExtension (.inr (.inr (.exp root)))

@[simp]
theorem rootThenExp_eval (degree : ℕ) (x : ℝ) :
    (rootThenExp degree x).eval rootLogExpModel =
      Real.exp (RealRAM.NthRoot.value degree x) := by
  simp [rootThenExp, rootLogExpModel, rootLogExpExtensionModel, ExtendedRealRAM.natCost,
    ExtendedRealRAM.model, ExtendedRealRAM.liftExtension, ExtendedRealRAM.ofExtension,
    Model.combine, RealRAM.NthRoot.natCost, RealRAM.Exp.natCost]

@[simp]
theorem rootThenExp_time (degree : ℕ) (x : ℝ) :
    (rootThenExp degree x).time rootLogExpModel = 2 := by
  simp [rootThenExp, rootLogExpModel, rootLogExpExtensionModel, ExtendedRealRAM.natCost,
    ExtendedRealRAM.model, ExtendedRealRAM.liftExtension, ExtendedRealRAM.ofExtension,
    Model.combine, RealRAM.NthRoot.natCost, RealRAM.Exp.natCost]

/-- A concrete realization of the primitive continuous oracle, useful for evaluation examples. -/
def unitOracle : ContinuousRealSample.Oracle :=
  fun _ => ⟨1, by norm_num⟩

/-- Continuous uniform sampling composes with any independently selected extension effects. -/
def continuousRootLogExpModel :
    Model (ContinuousRandomizedExtendedRealRAM RootLogExp) ℕ :=
  ContinuousRandomizedExtendedRealRAM.natCost rootLogExpExtensionModel unitOracle

example :
    (WithContinuousRealRandomness.uniformIcc01 (Q := ExtendedRealRAM RootLogExp) 7).eval
      continuousRootLogExpModel = 1 := by
  rfl

/-- A standard-Gaussian value computed from two primitive interval samples by Box--Muller. -/
def standardGaussian : Prog GaussianSampling.Machine ℝ :=
  GaussianSampling.standard 0

@[simp]
theorem standardGaussian_eval :
    standardGaussian.eval (GaussianSampling.natCost unitOracle) = 0 := by
  simp [standardGaussian, GaussianSampling.standardValue, unitOracle]

@[simp]
theorem standardGaussian_time :
    standardGaussian.time (GaussianSampling.natCost unitOracle) = 8 := by
  simp [standardGaussian]

@[simp]
theorem standardGaussian_operationCost :
    standardGaussian.time (GaussianSampling.operationCost unitOracle) =
      ⟨0, 0, 6, 0, 2⟩ := by
  simp [standardGaussian]

end

end AlgoleanTests
