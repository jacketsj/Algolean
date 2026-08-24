/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMProcedure
public import Algolean.Models.WordRAM.Data.Physical

/-!
# Certified structural composition for Word-RAM procedures

Logical refinements are zero runtime.  Any physical handoff or representation conversion is
represented by finite procedure code and a same-trace certificate; there is no free Lean adapter.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- A conversion between physical formats is an ordinary charged structured problem. -/
def conversionProblem (w : Nat) (source target : Type)
    (sourceLayout : WordLayout w source) (targetLayout : WordLayout w target)
    (widthAtLeastTwo : 2 ≤ w) (outputRegion : Region w)
    (pre : source → Prop) (representsSame : source → target → Prop)
    (sourceFits : ∀ input, pre input → sourceLayout.FitsInput input) :
    StructuredProblem w where
  widthAtLeastTwo := widthAtLeastTwo
  Input := source
  Output := target
  inputLayout := sourceLayout
  outputLayout := targetLayout
  outputRegion := outputRegion
  pre := pre
  post := representsSame
  inputFits := sourceFits

/-- Contract obtained by sequentially feeding the first result to the second procedure. -/
def ProcedureContract.then (first : ProcedureContract w) (second : ProcedureContract w)
    (sameCarrier : first.Output = second.Input) : ProcedureContract w :=
  {
    widthAtLeastTwo := first.widthAtLeastTwo
    Input := first.Input
    Output := second.Output
    inputLayout := first.inputLayout
    outputLayout := second.outputLayout
    pre := first.pre
    post := fun input output ↦
      ∃ middle, first.post input middle ∧ second.pre (cast sameCarrier middle) ∧
        second.post (cast sameCarrier middle) output
    inputFits := first.inputFits
    outputFits := by
      intro input output valid
      rintro ⟨middle, firstCorrect, secondValid, secondCorrect⟩
      exact second.outputFits (cast sameCarrier middle) output secondValid secondCorrect }

/--
Evidence produced by the verified module linker for sequential composition.  The transfer charge
is explicit; an aliasing handoff may prove it zero, while copying or format conversion supplies a
certified nonzero bound.
-/
structure SequentialComposition
    (first : ProcedureCertificate firstContract firstBound)
    (second : ProcedureCertificate secondContract secondBound)
    (composed : ProcedureContract w)
    (bound : ProcedureBound composed) where
  composedInput_eq : composed.Input = firstContract.Input
  middle_eq : firstContract.Output = secondContract.Input
  transferCost : firstContract.Input → Nat
  module : ProcedureModule w
  calling : CallingConvention w
  callingRealizes : calling.Realizes composed
  valid : module.Valid
  output : composed.Input → composed.Output
  outputCorrect : ∀ input, composed.pre input → composed.post input (output input)
  correct : ∀ input, ∀ _validInput : composed.pre input,
    ∀ initial : Memory w,
      composed.inputLayout.RepAt calling.inputRegion input initial →
      ∃ run : ProcedureRun module initial,
        composed.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
        run.cost ≤ bound input ∧
        PreservesFrame composed calling input (output input) initial run.final
  boundIncludesComponents : ∀ input middle,
    firstContract.post (cast composedInput_eq input) middle →
      secondContract.pre (cast middle_eq middle) →
      firstBound (cast composedInput_eq input) + transferCost (cast composedInput_eq input) +
        secondBound (cast middle_eq middle) ≤ bound input

/-- Package a verified sequential link without rerunning either component correctness proof. -/
def ProcedureCertificate.then
    (first : ProcedureCertificate firstContract firstBound)
    (second : ProcedureCertificate secondContract secondBound)
    (composition : SequentialComposition first second composed bound) :
    ProcedureCertificate composed bound where
  module := composition.module
  calling := composition.calling
  callingRealizes := composition.callingRealizes
  valid := composition.valid
  output := composition.output
  outputCorrect := composition.outputCorrect
  correct := composition.correct

end Algolean.Algorithms.WordRAM
