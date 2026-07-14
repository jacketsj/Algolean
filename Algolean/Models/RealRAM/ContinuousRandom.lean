/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM.Extensions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure

/-!
# Continuous randomness for real RAMs

The primitive continuous random source is an indexed oracle of real values in `[0, 1]`. A concrete
`Model` supplies one realization of that oracle. `ContinuousRealSample.oracleLaw` is the canonical
probability measure under which its coordinates are independent and uniform on `[0, 1]`.

There is deliberately no primitive Gaussian query. Gaussian generation is implemented as an
ordinary algorithm in `Algolean.Algorithms.GaussianSampling`, so it is charged for all randomness
and arithmetic it actually uses.

The indexed-oracle presentation fits Algolean's pure `Model.evalQuery` interface: algorithms obtain
actual real values and may use them in later queries, while different models can supply different
oracle realizations. Probabilistic theorems can use `oracleLaw` directly or quantify over another
law when a different coupling is wanted.
-/

@[expose] public section

namespace Algolean.Algorithms

open MeasureTheory
open ProbabilityTheory

/-- Queries to an indexed continuous real-randomness oracle. -/
inductive ContinuousRealSample : Type → Type where
  /-- Read coordinate `index`, intended to be an independent uniform sample from `[0, 1]`. -/
  | uniformIcc01 (index : ℕ) : ContinuousRealSample ℝ

namespace ContinuousRealSample

/-- The closed unit interval as a subtype of the reals. -/
abbrev UnitInterval : Type := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}

/-- One realization of the continuous oracle, with every coordinate constrained to `[0, 1]`. -/
abbrev Oracle : Type := ℕ → UnitInterval

/-- The probability law intended for each coordinate of a continuous oracle. -/
noncomputable def uniformLaw : Measure ℝ :=
  volume.restrict (Set.Icc 0 1)

/-- The uniform law on `[0, 1]` has total mass one. -/
instance : IsProbabilityMeasure uniformLaw where
  measure_univ := by
    simp [uniformLaw, Real.volume_Icc]

/-- Uniform probability measure on the subtype `[0, 1]` used by an oracle coordinate. -/
noncomputable def coordinateLaw : Measure UnitInterval :=
  uniformLaw.comap Subtype.val

instance : IsProbabilityMeasure coordinateLaw := by
  unfold coordinateLaw
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
  simpa [uniformLaw] using
    (ae_restrict_mem measurableSet_Icc : ∀ᵐ x ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      x ∈ Set.Icc (0 : ℝ) 1)

/-- Coercing a subtype-valued uniform coordinate recovers `uniformLaw` on `ℝ`. -/
theorem coordinateLaw_map_subtypeVal :
    coordinateLaw.map ((↑) : UnitInterval → ℝ) = uniformLaw := by
  rw [coordinateLaw, map_comap_subtype_coe measurableSet_Icc]
  simp [uniformLaw, Measure.restrict_restrict, measurableSet_Icc]

/-- Canonical law of an oracle tape: countably many independent uniform `[0, 1]` coordinates. -/
noncomputable def oracleLaw : Measure Oracle :=
  Measure.infinitePi fun _ : ℕ => coordinateLaw

instance : IsProbabilityMeasure oracleLaw := by
  unfold oracleLaw
  infer_instance

/-- Every coordinate of the canonical oracle is uniform on `[0, 1]` as a real variable. -/
theorem coordinate_hasLaw (index : ℕ) :
    HasLaw (fun oracle : Oracle => (oracle index : ℝ)) uniformLaw oracleLaw := by
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => coordinateLaw) index).hasLaw
  have hcoe : HasLaw ((↑) : UnitInterval → ℝ) uniformLaw coordinateLaw :=
    ⟨measurable_subtype_coe.aemeasurable, coordinateLaw_map_subtypeVal⟩
  simpa [oracleLaw, Function.comp_def] using hcoe.comp h

/-- The real-valued coordinates of the canonical oracle are mutually independent. -/
theorem coordinates_iIndep :
    iIndepFun (fun index (oracle : Oracle) => (oracle index : ℝ)) oracleLaw := by
  unfold oracleLaw
  exact iIndepFun_infinitePi
    (X := fun _ : ℕ => ((↑) : UnitInterval → ℝ)) (fun _ => measurable_subtype_coe)

/-- Evaluate a sampling query against a fixed oracle realization. -/
@[simp]
def eval (oracle : Oracle) : ContinuousRealSample α → α
  | .uniformIcc01 index => oracle index

/-- Each interval-sampling query has unit cost. -/
@[simps]
def natCost (oracle : Oracle) : Model ContinuousRealSample ℕ where
  evalQuery := eval oracle
  cost _ := 1

/-- An interval-sampling query increments the existing random-sample counter. -/
@[simps]
def operationCost (oracle : Oracle) : Model ContinuousRealSample RealRAMCost where
  evalQuery := eval oracle
  cost _ := ⟨0, 0, 0, 0, 1⟩

end ContinuousRealSample

/-- Add continuous real randomness to an arbitrary query machine `Q`. -/
abbrev WithContinuousRealRandomness (Q : Type → Type) : Type → Type :=
  compositeQuery Q ContinuousRealSample

namespace WithContinuousRealRandomness

/-- Inject a deterministic machine query into the continuously randomized machine. -/
def ofMachine (query : Q α) : WithContinuousRealRandomness Q α := .inl query

/-- Inject a continuous-randomness query into the continuously randomized machine. -/
def ofRandomness (query : ContinuousRealSample α) : WithContinuousRealRandomness Q α := .inr query

/-- Lift a deterministic machine query into a continuously randomized program. -/
def liftMachine (query : Q α) : Prog (WithContinuousRealRandomness Q) α :=
  Cslib.FreeM.lift (ofMachine query)

/-- Lift a continuous-randomness query into a continuously randomized program. -/
def liftRandomness (query : ContinuousRealSample α) :
    Prog (WithContinuousRealRandomness Q) α :=
  Cslib.FreeM.lift (ofRandomness query)

/-- Combine a machine model with a continuous-randomness model using a shared cost type. -/
def model (machineModel : Model Q Cost) (randomModel : Model ContinuousRealSample Cost) :
    Model (WithContinuousRealRandomness Q) Cost :=
  machineModel.combine randomModel

/-- Unit-cost continuously randomized machine for the supplied oracle realization. -/
noncomputable def natCost (machineModel : Model Q ℕ) (oracle : ContinuousRealSample.Oracle) :
    Model (WithContinuousRealRandomness Q) ℕ :=
  model machineModel (ContinuousRealSample.natCost oracle)

/-- Detailed-cost continuously randomized machine for the supplied oracle realization. -/
noncomputable def operationCost (machineModel : Model Q RealRAMCost)
    (oracle : ContinuousRealSample.Oracle) :
    Model (WithContinuousRealRandomness Q) RealRAMCost :=
  model machineModel (ContinuousRealSample.operationCost oracle)

/-- Read one coordinate from the primitive continuous uniform oracle. -/
def uniformIcc01 (index : ℕ) : Prog (WithContinuousRealRandomness Q) ℝ :=
  liftRandomness (.uniformIcc01 index)

@[simp]
theorem liftMachine_eval (query : Q α) (machineModel : Model Q Cost)
    (randomModel : Model ContinuousRealSample Cost) :
    (liftMachine query).eval (model machineModel randomModel) = machineModel.evalQuery query :=
  rfl

@[simp]
theorem uniformIcc01_eval (index : ℕ) (machineModel : Model Q Cost)
    (randomModel : Model ContinuousRealSample Cost) :
    (uniformIcc01 (Q := Q) index).eval (model machineModel randomModel) =
      randomModel.evalQuery (.uniformIcc01 index) :=
  rfl

@[simp]
theorem liftMachine_time [AddZeroClass Cost] (query : Q α) (machineModel : Model Q Cost)
    (randomModel : Model ContinuousRealSample Cost) :
    (liftMachine query).time (model machineModel randomModel) = machineModel.cost query := by
  simp [liftMachine, ofMachine, model]

@[simp]
theorem uniformIcc01_time [AddZeroClass Cost] (index : ℕ) (machineModel : Model Q Cost)
    (randomModel : Model ContinuousRealSample Cost) :
    (uniformIcc01 (Q := Q) index).time (model machineModel randomModel) =
      randomModel.cost (.uniformIcc01 index) := by
  simp [uniformIcc01, liftRandomness, ofRandomness, model]

end WithContinuousRealRandomness

/-- The core real RAM with a continuous uniform random oracle. -/
abbrev ContinuousRandomizedRealRAM := WithContinuousRealRandomness RealRAM

namespace ContinuousRandomizedRealRAM

/-- Unit-cost core real RAM with a supplied continuous oracle realization. -/
noncomputable def natCost (oracle : ContinuousRealSample.Oracle) :
    Model ContinuousRandomizedRealRAM ℕ :=
  WithContinuousRealRandomness.natCost RealRAM.natCost oracle

/-- Detailed-cost core real RAM with a supplied continuous oracle realization. -/
noncomputable def operationCost (oracle : ContinuousRealSample.Oracle) :
    Model ContinuousRandomizedRealRAM RealRAMCost :=
  WithContinuousRealRandomness.operationCost RealRAM.operationCost oracle

end ContinuousRandomizedRealRAM

/-- A modularly extended real RAM with a continuous uniform random oracle. -/
abbrev ContinuousRandomizedExtendedRealRAM (Extension : Type → Type) :=
  WithContinuousRealRandomness (ExtendedRealRAM Extension)

namespace ContinuousRandomizedExtendedRealRAM

/-- Unit-cost continuously randomized extended real RAM. -/
noncomputable def natCost (extensionModel : Model Extension ℕ)
    (oracle : ContinuousRealSample.Oracle) :
    Model (ContinuousRandomizedExtendedRealRAM Extension) ℕ :=
  WithContinuousRealRandomness.natCost (ExtendedRealRAM.natCost extensionModel) oracle

/-- Detailed-cost continuously randomized extended real RAM. -/
noncomputable def operationCost (extensionModel : Model Extension RealRAMCost)
    (oracle : ContinuousRealSample.Oracle) :
    Model (ContinuousRandomizedExtendedRealRAM Extension) RealRAMCost :=
  WithContinuousRealRandomness.operationCost
    (ExtendedRealRAM.operationCost extensionModel) oracle

end ContinuousRandomizedExtendedRealRAM

end Algolean.Algorithms
