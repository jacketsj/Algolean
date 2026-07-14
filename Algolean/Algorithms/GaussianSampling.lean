/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM.ContinuousRandom

/-!
# Gaussian sampling on a real RAM

This module implements standard-Gaussian sampling as an algorithm, not a machine primitive. The
Box--Muller transform consumes two coordinates of the primitive uniform `[0, 1]` oracle and uses
independently selected `Sqrt`, `Log`, and `Cos` real-RAM extensions.

The operational theorems below expose the exact Box--Muller value and prove that one run costs two
random samples and six deterministic arithmetic operations. Its standard-Gaussian law under the
canonical independent-uniform oracle is proved in
`Algolean.Algorithms.GaussianSamplingProbability`.
-/

@[expose] public section

namespace Algolean.Algorithms

namespace GaussianSampling

/-- The independent deterministic effects used by the Box--Muller transform. -/
abbrev Operations :=
  RealRAM.ExtensionSum RealRAM.Sqrt (RealRAM.ExtensionSum RealRAM.Log RealRAM.Cos)

/-- Unit-cost model for the deterministic Box--Muller extensions. -/
noncomputable def operationsNatCost : Model Operations ℕ :=
  RealRAM.Sqrt.natCost.combine (RealRAM.Log.natCost.combine RealRAM.Cos.natCost)

/-- Detailed-cost model for the deterministic Box--Muller extensions. -/
noncomputable def operationsCost : Model Operations RealRAMCost :=
  RealRAM.Sqrt.operationCost.combine
    (RealRAM.Log.operationCost.combine RealRAM.Cos.operationCost)

/-- The Box--Muller real RAM with primitive continuous-uniform randomness. -/
abbrev Machine := WithContinuousRealRandomness (ExtendedRealRAM Operations)

/-- Unit-cost Box--Muller machine for the supplied uniform-oracle realization. -/
noncomputable def natCost (oracle : ContinuousRealSample.Oracle) : Model Machine ℕ :=
  ContinuousRandomizedExtendedRealRAM.natCost operationsNatCost oracle

/-- Detailed-cost Box--Muller machine for the supplied uniform-oracle realization. -/
noncomputable def operationCost (oracle : ContinuousRealSample.Oracle) :
    Model Machine RealRAMCost :=
  ContinuousRandomizedExtendedRealRAM.operationCost operationsCost oracle

/-- Lift a core real-RAM instruction into the Gaussian-sampling machine. -/
def liftCore (query : RealRAM α) : Prog Machine α :=
  WithContinuousRealRandomness.liftMachine (ExtendedRealRAM.ofCore query)

/-- Lift a selected Box--Muller extension instruction into the Gaussian-sampling machine. -/
def liftExtension (query : Operations α) : Prog Machine α :=
  WithContinuousRealRandomness.liftMachine (ExtendedRealRAM.ofExtension query)

@[simp]
theorem liftCore_eval (oracle : ContinuousRealSample.Oracle)
    (query : RealRAM α) :
    (liftCore query).eval (natCost oracle) = RealRAM.eval query :=
  rfl

theorem liftExtension_eval (oracle : ContinuousRealSample.Oracle) (query : Operations α) :
    (liftExtension query).eval (natCost oracle) = operationsNatCost.evalQuery query :=
  rfl

@[simp]
theorem sqrt_eval (oracle : ContinuousRealSample.Oracle) (x : ℝ) :
    (liftExtension (.inl (.sqrt x))).eval (natCost oracle) = Real.sqrt x := by
  rfl

@[simp]
theorem sqrt_operation_eval (oracle : ContinuousRealSample.Oracle) (x : ℝ) :
    (liftExtension (.inl (.sqrt x))).eval (operationCost oracle) = Real.sqrt x := by
  rfl

@[simp]
theorem liftCore_time (oracle : ContinuousRealSample.Oracle)
    (query : RealRAM α) :
    (liftCore query).time (natCost oracle) = 1 := by
  simp [liftCore, natCost, ContinuousRandomizedExtendedRealRAM.natCost,
    WithContinuousRealRandomness.natCost, ExtendedRealRAM.natCost, ExtendedRealRAM.model,
    ExtendedRealRAM.ofCore, Model.combine, RealRAM.natCost]

@[simp]
theorem liftCore_operationCost (oracle : ContinuousRealSample.Oracle)
    (query : RealRAM α) :
    (liftCore query).time (operationCost oracle) = RealRAM.operationCost.cost query := by
  simp [liftCore, operationCost, ContinuousRandomizedExtendedRealRAM.operationCost,
    WithContinuousRealRandomness.operationCost, ExtendedRealRAM.operationCost,
    ExtendedRealRAM.model, ExtendedRealRAM.ofCore, Model.combine]

@[simp]
theorem liftExtension_time (oracle : ContinuousRealSample.Oracle) (query : Operations α) :
    (liftExtension query).time (natCost oracle) = 1 := by
  rcases query with query | query
  · simp [liftExtension, natCost, ContinuousRandomizedExtendedRealRAM.natCost,
      WithContinuousRealRandomness.natCost, ExtendedRealRAM.natCost, operationsNatCost,
      ExtendedRealRAM.model, ExtendedRealRAM.ofExtension, Model.combine,
      RealRAM.Sqrt.natCost]
  · rcases query with query | query <;>
      simp [liftExtension, natCost, ContinuousRandomizedExtendedRealRAM.natCost,
        WithContinuousRealRandomness.natCost, ExtendedRealRAM.natCost, operationsNatCost,
        ExtendedRealRAM.model, ExtendedRealRAM.ofExtension, Model.combine,
        RealRAM.Log.natCost, RealRAM.Cos.natCost]

@[simp]
theorem liftExtension_operationCost (oracle : ContinuousRealSample.Oracle)
    (query : Operations α) :
    (liftExtension query).time (operationCost oracle) = operationsCost.cost query := by
  simp [liftExtension, operationCost, ContinuousRandomizedExtendedRealRAM.operationCost,
    WithContinuousRealRandomness.operationCost, ExtendedRealRAM.operationCost,
    ExtendedRealRAM.model, ExtendedRealRAM.ofExtension, Model.combine]

/-- The pure Box--Muller value determined by two coordinates of an oracle realization. -/
noncomputable def standardValue (oracle : ContinuousRealSample.Oracle)
    (firstSample : ℕ) : ℝ :=
  Real.sqrt (-2 * Real.log (oracle firstSample)) *
    Real.cos ((2 * Real.pi) * oracle (firstSample + 1))

/--
Generate one standard-Gaussian value with the Box--Muller transform.

The program reads oracle coordinates `firstSample` and `firstSample + 1`. At the measure-zero
endpoint `u₁ = 0`, Mathlib's totalized logarithm gives the program a total value.
-/
noncomputable def standard (firstSample : ℕ) : Prog Machine ℝ := do
  let u₁ : ℝ ← WithContinuousRealRandomness.uniformIcc01 firstSample
  let u₂ : ℝ ← WithContinuousRealRandomness.uniformIcc01 (firstSample + 1)
  let logU₁ : ℝ ← liftExtension (.inr (.inl (.log u₁)))
  let radiusSquared : ℝ ← liftCore (.mul (-2) logU₁)
  let radius : ℝ ← liftExtension (.inl (.sqrt radiusSquared))
  let angle : ℝ ← liftCore (.mul (2 * Real.pi) u₂)
  let direction : ℝ ← liftExtension (.inr (.inr (.cos angle)))
  liftCore (.mul radius direction)

@[simp]
theorem standard_eval (oracle : ContinuousRealSample.Oracle) (firstSample : ℕ) :
    (standard firstSample).eval (natCost oracle) = standardValue oracle firstSample := by
  rfl

@[simp]
theorem standard_time (oracle : ContinuousRealSample.Oracle) (firstSample : ℕ) :
    (standard firstSample).time (natCost oracle) = 8 := by
  simp [standard, natCost, ContinuousRandomizedExtendedRealRAM.natCost,
    WithContinuousRealRandomness.natCost, WithContinuousRealRandomness.model,
    WithContinuousRealRandomness.uniformIcc01, WithContinuousRealRandomness.liftMachine,
    WithContinuousRealRandomness.liftRandomness, WithContinuousRealRandomness.ofMachine,
    WithContinuousRealRandomness.ofRandomness, operationsNatCost, liftCore, liftExtension,
    ExtendedRealRAM.natCost, ExtendedRealRAM.model, ExtendedRealRAM.ofCore,
    ExtendedRealRAM.ofExtension, Model.combine, RealRAM.natCost, RealRAM.Sqrt.natCost,
    RealRAM.Log.natCost, RealRAM.Cos.natCost, ContinuousRealSample.natCost]

@[simp]
theorem standard_operationCost (oracle : ContinuousRealSample.Oracle) (firstSample : ℕ) :
    (standard firstSample).time (operationCost oracle) = ⟨0, 0, 6, 0, 2⟩ := by
  simp [standard, operationCost, ContinuousRandomizedExtendedRealRAM.operationCost,
    WithContinuousRealRandomness.operationCost, WithContinuousRealRandomness.model,
    WithContinuousRealRandomness.uniformIcc01, WithContinuousRealRandomness.liftMachine,
    WithContinuousRealRandomness.liftRandomness, WithContinuousRealRandomness.ofMachine,
    WithContinuousRealRandomness.ofRandomness, operationsCost, liftCore, liftExtension,
    ExtendedRealRAM.operationCost, ExtendedRealRAM.model, ExtendedRealRAM.ofCore,
    ExtendedRealRAM.ofExtension, Model.combine, RealRAM.operationCost,
    RealRAM.Sqrt.operationCost, RealRAM.Log.operationCost, RealRAM.Cos.operationCost,
    ContinuousRealSample.operationCost]
  rfl

end GaussianSampling

end Algolean.Algorithms
