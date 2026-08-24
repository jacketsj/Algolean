/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMStructured

/-!
# Callable Word-RAM procedure contracts and certificates

Contracts contain no implementation function.  Certificates contain finite RAM code and prove
correctness from arbitrary caller-owned memory, including a frame theorem and same-trace cost.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- A typed contract for a callable deterministic Word-RAM procedure. -/
structure ProcedureContract (w : ℕ) where
  widthAtLeastTwo : 2 ≤ w
  Input : Type
  Output : Type
  inputLayout : WordLayout w Input
  outputLayout : WordLayout w Output
  pre : Input → Prop
  post : Input → Output → Prop
  inputFits : ∀ input, pre input → inputLayout.Fits input
  /-- Every contract-permitted answer is representable somewhere in the word address space. -/
  outputFits : ∀ input output, pre input → post input output → outputLayout.Fits output

/-- Resolve canonical contract layouts once, outside execution semantics. -/
def ProcedureContract.ofCanonical (w : ℕ) (Input Output : Type)
    [CanonicalLayout w Input] [CanonicalLayout w Output]
    (widthAtLeastTwo : 2 ≤ w) (pre : Input → Prop) (post : Input → Output → Prop)
    (inputFits : ∀ input, pre input → (layoutOf w Input).Fits input)
    (outputFits : ∀ input output, pre input → post input output →
      (layoutOf w Output).Fits output) : ProcedureContract w where
  widthAtLeastTwo := widthAtLeastTwo
  Input := Input
  Output := Output
  inputLayout := layoutOf w Input
  outputLayout := layoutOf w Output
  pre := pre
  post := post
  inputFits := inputFits
  outputFits := outputFits

/-- Replace only the mathematical postcondition and its representation guarantee. -/
def ProcedureContract.withPost (contract : ProcedureContract w)
    (newPost : contract.Input → contract.Output → Prop)
    (newOutputFits : ∀ input output, contract.pre input → newPost input output →
      contract.outputLayout.Fits output) : ProcedureContract w where
  widthAtLeastTwo := contract.widthAtLeastTwo
  Input := contract.Input
  Output := contract.Output
  inputLayout := contract.inputLayout
  outputLayout := contract.outputLayout
  pre := contract.pre
  post := newPost
  inputFits := contract.inputFits
  outputFits := newOutputFits

/-- Replace only the mathematical precondition and its representation guarantees. -/
def ProcedureContract.withPre (contract : ProcedureContract w)
    (newPre : contract.Input → Prop)
    (stronger : ∀ input, newPre input → contract.pre input)
    (newFits : ∀ input, newPre input → contract.inputLayout.Fits input) : ProcedureContract w where
  widthAtLeastTwo := contract.widthAtLeastTwo
  Input := contract.Input
  Output := contract.Output
  inputLayout := contract.inputLayout
  outputLayout := contract.outputLayout
  pre := newPre
  post := contract.post
  inputFits := newFits
  outputFits input output valid correct :=
    contract.outputFits input output (stronger input valid) correct

/-- Exact input-dependent procedure resource bound. -/
abbrev ProcedureBound (contract : ProcedureContract w) := contract.Input → ℕ

/-- Explicit input/output aliasing policy of a callable ABI. -/
inductive AliasingPolicy where
  | disjoint
  | inPlace
deriving DecidableEq, Repr

/-- Explicit caller/callee region and register ownership. -/
structure CallingConvention (w : ℕ) where
  inputRegion : Region w
  outputRegion : Region w
  /-- Addresses the callee may modify in addition to its output region. -/
  scratchOwned : BitVec w → Prop
  /-- Address registers the callee may modify. -/
  registerOwned : ℕ → Prop
  /-- Constant charged setup/dispatch/return overhead. -/
  callOverhead : ℕ
  /-- Whether output storage must be separate or may intentionally alias the input. -/
  aliasingPolicy : AliasingPolicy := .disjoint

/-- A finite callable module in the same sealed core instruction language. -/
structure ProcedureModule (w : ℕ) where
  code : Program w
  entry : ℕ

namespace ProcedureModule

/-- All jumps and the entry point are within the finite module. -/
def Valid (module : ProcedureModule w) : Prop :=
  module.code.Valid ∧ module.entry < module.code.length

end ProcedureModule

/-- Data addresses occupied by a represented value. -/
def WordLayout.Occupies (layout : WordLayout w alpha) (region : Region w)
    (value : alpha) (address : BitVec w) : Prop :=
  ∃ index, index < layout.footprintWords value ∧
    address = BitVec.ofNat w (region.base.toNat + index)

/-- Two actual represented values occupy disjoint concrete word intervals. -/
def RepresentationsDisjoint (left : WordLayout w alpha) (leftRegion : Region w)
    (leftValue : alpha) (right : WordLayout w beta) (rightRegion : Region w)
    (rightValue : beta) : Prop :=
  ∀ address, ¬ (left.Occupies leftRegion leftValue address ∧
    right.Occupies rightRegion rightValue address)

/-- The concrete regions and ownership declarations realize a procedure contract. -/
structure CallingConvention.Realizes (contract : ProcedureContract w)
    (calling : CallingConvention w) : Prop where
  inputFitsAt : ∀ input, contract.pre input →
    contract.inputLayout.FitsAt calling.inputRegion input
  outputFitsAt : ∀ input output, contract.pre input → contract.post input output →
    contract.outputLayout.FitsAt calling.outputRegion output
  inputOutputPolicy : ∀ input output, contract.pre input → contract.post input output →
    match calling.aliasingPolicy with
    | .disjoint => RepresentationsDisjoint contract.inputLayout calling.inputRegion input
        contract.outputLayout calling.outputRegion output
    | .inPlace => True
  scratchDisjointOutput : ∀ input output, contract.pre input → contract.post input output →
    ∀ address, contract.outputLayout.Occupies calling.outputRegion output address →
      ¬ calling.scratchOwned address

/-- The callee preserves every caller-owned data cell and address register. -/
def PreservesFrame (contract : ProcedureContract w) (calling : CallingConvention w)
    (input : contract.Input) (output : contract.Output) (before after : Memory w) : Prop :=
  (∀ address,
      ¬ contract.inputLayout.Occupies calling.inputRegion input address →
      ¬ calling.scratchOwned address →
      ¬ contract.outputLayout.Occupies calling.outputRegion output address →
      after.data address = before.data address) ∧
    (∀ register, ¬ calling.registerOwned register →
      after.address register = before.address register)

/-- One concrete same-trace procedure execution from caller-owned memory. -/
structure ProcedureRun (module : ProcedureModule w) (initial : Memory w) where
  final : Memory w
  result : BitVec w
  cost : ℕ
  steps : ℕ
  trace : RAM.HaltingTrace (stepCosted module.code)
    ⟨module.entry, initial⟩ final result cost steps

/-- Callable finite code implementing one typed contract and exact bound. -/
structure ProcedureCertificate (contract : ProcedureContract w)
    (bound : ProcedureBound contract) where
  module : ProcedureModule w
  calling : CallingConvention w
  /-- The advertised fixed regions are usable for every contract-permitted call. -/
  callingRealizes : calling.Realizes contract
  valid : module.Valid
  /-- Deterministic structured result, independent of caller-owned memory and scratch contents. -/
  output : contract.Input → contract.Output
  outputCorrect : ∀ input, contract.pre input → contract.post input (output input)
  /-- Correct for any caller memory containing a valid structured input at the declared region. -/
  correct : ∀ input, ∀ _validInput : contract.pre input,
    ∀ initial : Memory w,
      contract.inputLayout.RepAt calling.inputRegion input initial →
      ∃ run : ProcedureRun module initial,
        contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
        run.cost ≤ bound input + calling.callOverhead ∧
        PreservesFrame contract calling input (output input) initial run.final

/-- Stronger convention restoring scratch and owned registers before return. -/
structure RestoringProcedureCertificate (contract : ProcedureContract w)
    (bound : ProcedureBound contract) extends ProcedureCertificate contract bound where
  restoringCorrect : ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory w,
    contract.inputLayout.RepAt calling.inputRegion input initial →
    ∃ run : ProcedureRun module initial,
      contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
      run.cost ≤ bound input + calling.callOverhead ∧
      run.final = contract.outputLayout.writeAt calling.outputRegion (output input) initial

/-- Existence of concrete callable code; retained separately from the inspectable certificate. -/
def HasProcedure (contract : ProcedureContract w) (bound : ProcedureBound contract) : Prop :=
  Nonempty (ProcedureCertificate contract bound)

/-- Existence of callable code satisfying the stronger restoring convention. -/
def HasRestoringProcedure (contract : ProcedureContract w)
    (bound : ProcedureBound contract) : Prop :=
  Nonempty (RestoringProcedureCertificate contract bound)

namespace ProcedureCertificate

/-- Logical postcondition weakening changes no instruction or runtime bound. -/
def weakenPost (certificate : ProcedureCertificate contract bound)
    (weaker : ∀ input output, contract.post input output → newPost input output)
    (newOutputFits : ∀ input output, contract.pre input → newPost input output →
      contract.outputLayout.Fits output)
    (newRealizes : certificate.calling.Realizes (contract.withPost newPost newOutputFits)) :
    ProcedureCertificate (contract.withPost newPost newOutputFits) bound where
  module := certificate.module
  calling := certificate.calling
  callingRealizes := newRealizes
  valid := certificate.valid
  output := certificate.output
  outputCorrect input validInput := weaker input _ (certificate.outputCorrect input validInput)
  correct input validInput initial represented := by
    rcases certificate.correct input validInput initial represented with
      ⟨run, outputRep, cost, frame⟩
    exact ⟨run, outputRep, cost, frame⟩

/-- Precondition strengthening changes no instruction or runtime bound. -/
def restrictPre (certificate : ProcedureCertificate contract bound)
    (stronger : ∀ input, newPre input → contract.pre input)
    (newFits : ∀ input, newPre input → contract.inputLayout.Fits input)
    : ProcedureCertificate (contract.withPre newPre stronger newFits) bound where
  module := certificate.module
  calling := certificate.calling
  callingRealizes := {
    inputFitsAt := fun input valid ↦
      certificate.callingRealizes.inputFitsAt input (stronger input valid)
    outputFitsAt := fun input output valid correct ↦
      certificate.callingRealizes.outputFitsAt input output (stronger input valid) correct
    inputOutputPolicy := fun input output valid correct ↦
      certificate.callingRealizes.inputOutputPolicy input output (stronger input valid) correct
    scratchDisjointOutput := fun input output valid correct ↦
      certificate.callingRealizes.scratchDisjointOutput input output
        (stronger input valid) correct }
  valid := certificate.valid
  output := certificate.output
  outputCorrect input validInput := certificate.outputCorrect input (stronger input validInput)
  correct input validInput initial represented :=
    certificate.correct input (stronger input validInput) initial represented

/-- Weaken a procedure's theorem-side cost without changing code or calling convention. -/
def weakenBound (certificate : ProcedureCertificate contract oldBound)
    (larger : ∀ input, oldBound input ≤ newBound input) :
    ProcedureCertificate contract newBound where
  module := certificate.module
  calling := certificate.calling
  callingRealizes := certificate.callingRealizes
  valid := certificate.valid
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct input validInput initial represented := by
    rcases certificate.correct input validInput initial represented with
      ⟨run, outputRep, cost, frame⟩
    refine ⟨run, outputRep, ?_, frame⟩
    exact cost.trans (Nat.add_le_add_right (larger input) certificate.calling.callOverhead)

end ProcedureCertificate

end

end Algolean.Algorithms.WordRAM
