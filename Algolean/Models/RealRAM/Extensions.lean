/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RealRAM
public import Algolean.QueryComposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Modular extensions of the real RAM

Real-RAM variants differ in which non-core real operations they treat as primitive unit-cost
instructions. This file models every optional operation as an independent query effect. An
`ExtendedRealRAM E` is the core `RealRAM` extended by `E`, and `RealRAM.ExtensionSum` combines any
number of extension effects.

In particular, square root and general real exponentiation are intentionally different effects.
Although the latter can express square root mathematically, selecting `RealRAM.Sqrt` does not add
`RealRAM.RealPow`, and selecting `RealRAM.RealPow` does not add a primitive square-root query.

The supplied effects are:

- `RealRAM.Sqrt`: square root.
- `RealRAM.NthRoot`: real `n`th roots.
- `RealRAM.RealPow`: a real base raised to a real exponent.
- `RealRAM.Exp` and `RealRAM.Log`: exponential and logarithm.
- `RealRAM.Sin` and `RealRAM.Cos`: trigonometric operations.
- `RealRAM.Floor`: integer floor.

Users can define another query effect and plug it into `ExtendedRealRAM` without modifying the core
model or this file.
-/

@[expose] public section

namespace Algolean.Algorithms

/-- A square-root primitive for an extended real RAM. -/
inductive RealRAM.Sqrt : Type → Type where
  /-- Exact square root, with Mathlib's totalized semantics on negative inputs. -/
  | sqrt (x : ℝ) : RealRAM.Sqrt ℝ

namespace RealRAM.Sqrt

/-- Exact semantics of the square-root extension. -/
@[simp]
noncomputable def eval : RealRAM.Sqrt α → α
  | .sqrt x => Real.sqrt x

/-- Unit-cost model of the square-root extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Sqrt ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; a square root counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Sqrt RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Sqrt

/-- An arbitrary-degree real-root primitive for an extended real RAM. -/
inductive RealRAM.NthRoot : Type → Type where
  /-- The real `degree`th root of `x`. -/
  | nthRoot (degree : ℕ) (x : ℝ) : RealRAM.NthRoot ℝ

namespace RealRAM.NthRoot

/--
The totalized real `degree`th-root function used by the model.

Degree zero and even roots of negative numbers return zero. Odd roots of negative numbers have the
expected negative sign; all remaining cases use Mathlib's real power.
-/
noncomputable def value (degree : ℕ) (x : ℝ) : ℝ :=
  if degree = 0 then 0
  else if x < 0 then
    if Odd degree then -((-x) ^ ((degree : ℝ)⁻¹)) else 0
  else x ^ ((degree : ℝ)⁻¹)

/-- Exact semantics of the arbitrary-root extension. -/
@[simp]
noncomputable def eval : RealRAM.NthRoot α → α
  | .nthRoot degree x => value degree x

/-- Unit-cost model of the arbitrary-root extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.NthRoot ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; an arbitrary root counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.NthRoot RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.NthRoot

/-- A general real-exponentiation primitive for an extended real RAM. -/
inductive RealRAM.RealPow : Type → Type where
  /-- Raise the real base `x` to the real exponent `y`. -/
  | pow (x y : ℝ) : RealRAM.RealPow ℝ

namespace RealRAM.RealPow

/-- Exact semantics of the real-exponentiation extension, using Mathlib's `Real.rpow`. -/
@[simp]
noncomputable def eval : RealRAM.RealPow α → α
  | .pow x y => x ^ y

/-- Unit-cost model of the real-exponentiation extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.RealPow ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; real exponentiation counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.RealPow RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.RealPow

/-- An exact real-exponential primitive for an extended real RAM. -/
inductive RealRAM.Exp : Type → Type where
  /-- Compute `exp x`. -/
  | exp (x : ℝ) : RealRAM.Exp ℝ

namespace RealRAM.Exp

/-- Exact semantics of the exponential extension. -/
@[simp]
noncomputable def eval : RealRAM.Exp α → α
  | .exp x => Real.exp x

/-- Unit-cost model of the exponential extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Exp ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; exponential counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Exp RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Exp

/-- An exact real-logarithm primitive for an extended real RAM. -/
inductive RealRAM.Log : Type → Type where
  /-- Compute Mathlib's totalized real logarithm. -/
  | log (x : ℝ) : RealRAM.Log ℝ

namespace RealRAM.Log

/-- Exact semantics of the totalized-logarithm extension. -/
@[simp]
noncomputable def eval : RealRAM.Log α → α
  | .log x => Real.log x

/-- Unit-cost model of the logarithm extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Log ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; logarithm counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Log RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Log

/-- An exact real-sine primitive for an extended real RAM. -/
inductive RealRAM.Sin : Type → Type where
  /-- Compute `sin x`. -/
  | sin (x : ℝ) : RealRAM.Sin ℝ

namespace RealRAM.Sin

/-- Exact semantics of the sine extension. -/
@[simp]
noncomputable def eval : RealRAM.Sin α → α
  | .sin x => Real.sin x

/-- Unit-cost model of the sine extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Sin ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; sine counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Sin RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Sin

/-- An exact real-cosine primitive for an extended real RAM. -/
inductive RealRAM.Cos : Type → Type where
  /-- Compute `cos x`. -/
  | cos (x : ℝ) : RealRAM.Cos ℝ

namespace RealRAM.Cos

/-- Exact semantics of the cosine extension. -/
@[simp]
noncomputable def eval : RealRAM.Cos α → α
  | .cos x => Real.cos x

/-- Unit-cost model of the cosine extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Cos ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; cosine counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Cos RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Cos

/-- An integer-floor primitive for an extended real RAM. -/
inductive RealRAM.Floor : Type → Type where
  /-- Compute the greatest integer at most `x`. -/
  | floor (x : ℝ) : RealRAM.Floor ℤ

namespace RealRAM.Floor

/-- Exact semantics of the integer-floor extension. -/
@[simp]
noncomputable def eval : RealRAM.Floor α → α
  | .floor x => ⌊x⌋

/-- Unit-cost model of the integer-floor extension. -/
@[simps]
noncomputable def natCost : Model RealRAM.Floor ℕ where
  evalQuery := eval
  cost _ := 1

/-- Detailed model; floor counts as one arithmetic operation. -/
@[simps]
noncomputable def operationCost : Model RealRAM.Floor RealRAMCost where
  evalQuery := eval
  cost _ := ⟨0, 0, 1, 0, 0⟩

end RealRAM.Floor

/-- Combine two independent real-RAM extension effects. This operator may be nested. -/
abbrev RealRAM.ExtensionSum (E₁ E₂ : Type → Type) : Type → Type :=
  compositeQuery E₁ E₂

/-- The core real RAM extended with the independently selected query effect `Extension`. -/
abbrev ExtendedRealRAM (Extension : Type → Type) : Type → Type :=
  compositeQuery RealRAM Extension

namespace ExtendedRealRAM

/-- Inject a core real-RAM query into an extended real RAM. -/
def ofCore (query : RealRAM α) : ExtendedRealRAM Extension α := .inl query

/-- Inject an extension query into an extended real RAM. -/
def ofExtension (query : Extension α) : ExtendedRealRAM Extension α := .inr query

/-- Lift a core instruction into an extended real-RAM program. -/
def liftCore (query : RealRAM α) : Prog (ExtendedRealRAM Extension) α :=
  Cslib.FreeM.lift (ofCore query)

/-- Lift an optional instruction into an extended real-RAM program. -/
def liftExtension (query : Extension α) : Prog (ExtendedRealRAM Extension) α :=
  Cslib.FreeM.lift (ofExtension query)

/-- Combine arbitrary core and extension models that use the same cost type. -/
def model (coreModel : Model RealRAM Cost) (extensionModel : Model Extension Cost) :
    Model (ExtendedRealRAM Extension) Cost :=
  coreModel.combine extensionModel

/-- Unit-cost extended real RAM, given a unit-cost model for its selected extensions. -/
noncomputable def natCost (extensionModel : Model Extension ℕ) :
    Model (ExtendedRealRAM Extension) ℕ :=
  model RealRAM.natCost extensionModel

/-- Detailed extended real RAM, given a detailed model for its selected extensions. -/
noncomputable def operationCost (extensionModel : Model Extension RealRAMCost) :
    Model (ExtendedRealRAM Extension) RealRAMCost :=
  model RealRAM.operationCost extensionModel

@[simp]
theorem liftCore_eval (query : RealRAM α) (coreModel : Model RealRAM Cost)
    (extensionModel : Model Extension Cost) :
    (liftCore (Extension := Extension) query).eval (model coreModel extensionModel) =
      coreModel.evalQuery query :=
  rfl

@[simp]
theorem liftExtension_eval (query : Extension α) (coreModel : Model RealRAM Cost)
    (extensionModel : Model Extension Cost) :
    (liftExtension query).eval (model coreModel extensionModel) = extensionModel.evalQuery query :=
  rfl

@[simp]
theorem liftCore_time [AddZeroClass Cost] (query : RealRAM α)
    (coreModel : Model RealRAM Cost) (extensionModel : Model Extension Cost) :
    (liftCore (Extension := Extension) query).time (model coreModel extensionModel) =
      coreModel.cost query := by
  simp [liftCore, ofCore, model]

@[simp]
theorem liftExtension_time [AddZeroClass Cost] (query : Extension α)
    (coreModel : Model RealRAM Cost) (extensionModel : Model Extension Cost) :
    (liftExtension query).time (model coreModel extensionModel) = extensionModel.cost query := by
  simp [liftExtension, ofExtension, model]

end ExtendedRealRAM

/-- Core real RAM plus a primitive square root, but no other optional operation. -/
abbrev SqrtRealRAM := ExtendedRealRAM RealRAM.Sqrt

/-- Core real RAM plus arbitrary-degree roots, independently of square root and real powers. -/
abbrev NthRootRealRAM := ExtendedRealRAM RealRAM.NthRoot

/-- Core real RAM plus general real exponentiation, but no separate square-root primitive. -/
abbrev RealPowRAM := ExtendedRealRAM RealRAM.RealPow

/-- Core real RAM plus exact exponential. -/
abbrev ExpRealRAM := ExtendedRealRAM RealRAM.Exp

/-- Core real RAM plus exact logarithm. -/
abbrev LogRealRAM := ExtendedRealRAM RealRAM.Log

namespace SqrtRealRAM

/--
Reduce a square-root real RAM to a real-power RAM.

This records the strength relationship without identifying the two instruction sets: `SqrtRealRAM`
still has a primitive square-root instruction, while `RealPowRAM` implements it through `rpow`.
-/
noncomputable def toRealPowRAM : Reduction SqrtRealRAM RealPowRAM where
  reduce
    | .inl query => ExtendedRealRAM.liftCore query
    | .inr (.sqrt x) => ExtendedRealRAM.liftExtension (.pow x (1 / (2 : ℝ)))

@[simp]
theorem toRealPowRAM_correct (query : SqrtRealRAM α) :
    (toRealPowRAM.reduce query).eval (ExtendedRealRAM.natCost RealRAM.RealPow.natCost) =
      (ExtendedRealRAM.natCost RealRAM.Sqrt.natCost).evalQuery query := by
  cases query with
  | inl query =>
    simp [toRealPowRAM, ExtendedRealRAM.liftCore, ExtendedRealRAM.ofCore,
      ExtendedRealRAM.natCost, ExtendedRealRAM.model, Model.combine]
  | inr query =>
    cases query with
    | sqrt x =>
      simp [toRealPowRAM, ExtendedRealRAM.liftExtension, ExtendedRealRAM.ofExtension,
        ExtendedRealRAM.natCost, ExtendedRealRAM.model, Model.combine, RealRAM.RealPow.natCost,
        RealRAM.Sqrt.natCost, Real.sqrt_eq_rpow]

@[simp]
theorem toRealPowRAM_time (query : SqrtRealRAM α) :
    (toRealPowRAM.reduce query).time (ExtendedRealRAM.natCost RealRAM.RealPow.natCost) = 1 := by
  cases query with
  | inl query =>
    simp [toRealPowRAM, ExtendedRealRAM.liftCore, ExtendedRealRAM.ofCore,
      ExtendedRealRAM.natCost, ExtendedRealRAM.model, Model.combine, RealRAM.natCost]
  | inr query =>
    cases query
    simp [toRealPowRAM, ExtendedRealRAM.liftExtension, ExtendedRealRAM.ofExtension,
      ExtendedRealRAM.natCost, ExtendedRealRAM.model, Model.combine, RealRAM.RealPow.natCost]

end SqrtRealRAM

end Algolean.Algorithms
