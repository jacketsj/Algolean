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

/-- Resolve canonical contract layouts once, outside execution semantics. -/
def ProcedureContract.ofCanonical (w : ℕ) (Input Output : Type)
    [CanonicalLayout w Input] [CanonicalLayout w Output]
    (widthAtLeastTwo : 2 ≤ w) (pre : Input → Prop) (post : Input → Output → Prop)
    (inputFits : ∀ input, pre input → (layoutOf w Input).Fits input) : ProcedureContract w where
  widthAtLeastTwo := widthAtLeastTwo
  Input := Input
  Output := Output
  inputLayout := layoutOf w Input
  outputLayout := layoutOf w Output
  pre := pre
  post := post
  inputFits := inputFits

/-- Exact input-dependent procedure resource bound. -/
abbrev ProcedureBound (contract : ProcedureContract w) := contract.Input → ℕ

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

/-- The callee preserves every caller-owned data cell and address register. -/
def PreservesFrame (contract : ProcedureContract w) (calling : CallingConvention w)
    (input : contract.Input) (before after : Memory w) : Prop :=
  (∀ address,
      ¬ contract.inputLayout.Occupies calling.inputRegion input address →
      ¬ calling.scratchOwned address →
      ¬ (∃ output, contract.outputLayout.Occupies calling.outputRegion output address) →
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
        PreservesFrame contract calling input initial run.final ∧
        run.final = contract.outputLayout.writeAt calling.outputRegion (output input) initial

/-- Existence of concrete callable code; retained separately from the inspectable certificate. -/
def HasProcedure (contract : ProcedureContract w) (bound : ProcedureBound contract) : Prop :=
  Nonempty (ProcedureCertificate contract bound)

namespace ProcedureCertificate

/-- Logical postcondition weakening changes no instruction or runtime bound. -/
def weakenPost (certificate : ProcedureCertificate contract bound)
    (weaker : ∀ input output, contract.post input output → newPost input output) :
    ProcedureCertificate { contract with post := newPost } bound where
  module := certificate.module
  calling := certificate.calling
  valid := certificate.valid
  output := certificate.output
  outputCorrect input validInput := weaker input _ (certificate.outputCorrect input validInput)
  correct input validInput initial represented := by
    rcases certificate.correct input validInput initial represented with
      ⟨run, outputRep, cost, frame, effect⟩
    exact ⟨run, outputRep, cost, frame, effect⟩

/-- Precondition strengthening changes no instruction or runtime bound. -/
def restrictPre (certificate : ProcedureCertificate contract bound)
    (stronger : ∀ input, newPre input → contract.pre input)
    (newFits : ∀ input, newPre input → contract.inputLayout.Fits input) :
    ProcedureCertificate { contract with pre := newPre, inputFits := newFits } bound where
  module := certificate.module
  calling := certificate.calling
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
  valid := certificate.valid
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct input validInput initial represented := by
    rcases certificate.correct input validInput initial represented with
      ⟨run, outputRep, cost, frame, effect⟩
    refine ⟨run, outputRep, ?_, frame, effect⟩
    exact cost.trans (Nat.add_le_add_right (larger input) certificate.calling.callOverhead)

end ProcedureCertificate

end

end Algolean.Algorithms.WordRAM
