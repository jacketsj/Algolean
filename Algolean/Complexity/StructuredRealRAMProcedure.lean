/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem
public import Algolean.Models.StructuredRealRAM.TypedRegion

/-!
# Callable structured exact-real/natural procedures

The ABI is proved realizable before code correctness.  General procedures may leave owned
scratch changed; `RestoringProcedureCertificate` states the stronger canonical-effect convention
used by the initial shared-body linker.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

noncomputable section

/-- Typed implementation-independent callable contract. -/
structure ProcedureContract where
  Input : Type
  Output : Type
  inputLayout : Layout Input
  outputLayout : Layout Output
  pre : Input → Prop
  post : Input → Output → Prop

/-- Resolve model-specific canonical syntax once at contract construction. -/
def ProcedureContract.ofCanonical (Input Output : Type)
    [CanonicalLayout Input] [CanonicalLayout Output]
    (pre : Input → Prop) (post : Input → Output → Prop) : ProcedureContract where
  Input := Input
  Output := Output
  inputLayout := layoutOf Input
  outputLayout := layoutOf Output
  pre := pre
  post := post

abbrev ProcedureBound (contract : ProcedureContract) := contract.Input → Cost

/-- Explicit input/output aliasing policy of a structured-real callable ABI. -/
inductive AliasingPolicy where
  | disjoint
  | inPlace
deriving DecidableEq, Repr

/-- Concrete two-bank caller/callee ownership convention. -/
structure CallingConvention where
  inputRegion : Region
  outputRegion : Region
  scratchRealOwned : Nat → Prop
  scratchNatOwned : Nat → Prop
  natRegisterOwned : Nat → Prop
  /-- Whether output storage must be separate or may intentionally alias the input. -/
  aliasingPolicy : AliasingPolicy := .disjoint

/-- Real-bank addresses occupied by the actual represented value. -/
def Layout.OccupiesReal (layout : Layout alpha) (region : Region)
    (value : alpha) (address : Nat) : Prop :=
  region.realBase ≤ address ∧ address < region.realBase + (layout.footprint value).realCells

/-- Natural-bank addresses occupied by the actual represented value. -/
def Layout.OccupiesNat (layout : Layout alpha) (region : Region)
    (value : alpha) (address : Nat) : Prop :=
  region.natBase ≤ address ∧ address < region.natBase + (layout.footprint value).natCells

/-- Concrete ABI regions are disjoint for every contract-permitted input/output pair. -/
structure CallingConvention.Realizes (contract : ProcedureContract)
    (calling : CallingConvention) : Prop where
  inputOutputPolicy : ∀ input output, contract.pre input → contract.post input output →
    match calling.aliasingPolicy with
    | .disjoint =>
        (∀ address, ¬(contract.inputLayout.OccupiesReal calling.inputRegion input address ∧
          contract.outputLayout.OccupiesReal calling.outputRegion output address)) ∧
        (∀ address, ¬(contract.inputLayout.OccupiesNat calling.inputRegion input address ∧
          contract.outputLayout.OccupiesNat calling.outputRegion output address))
    | .inPlace => True
  scratchRealDisjointOutput : ∀ input output, contract.pre input → contract.post input output →
    ∀ address, contract.outputLayout.OccupiesReal calling.outputRegion output address →
      ¬ calling.scratchRealOwned address
  scratchNatDisjointOutput : ∀ input output, contract.pre input → contract.post input output →
    ∀ address, contract.outputLayout.OccupiesNat calling.outputRegion output address →
      ¬ calling.scratchNatOwned address

/-- Finite callable code in the sealed core structured-machine syntax. -/
structure ProcedureModule where
  code : Program
  entry : Nat

def ProcedureModule.Valid (module : ProcedureModule) : Prop :=
  module.code.Valid ∧ module.entry < module.code.length

/-- Frame preservation exempts only the actual input, output, and declared scratch footprints. -/
def PreservesFrame (contract : ProcedureContract) (calling : CallingConvention)
    (input : contract.Input) (output : contract.Output) (before after : Memory) : Prop :=
  (∀ address, ¬ contract.inputLayout.OccupiesReal calling.inputRegion input address →
      ¬ contract.outputLayout.OccupiesReal calling.outputRegion output address →
      ¬ calling.scratchRealOwned address → after.realMem address = before.realMem address) ∧
  (∀ address, ¬ contract.inputLayout.OccupiesNat calling.inputRegion input address →
      ¬ contract.outputLayout.OccupiesNat calling.outputRegion output address →
      ¬ calling.scratchNatOwned address → after.natMem address = before.natMem address) ∧
  (∀ register, ¬ calling.natRegisterOwned register →
      after.natReg register = before.natReg register)

/-- One same-trace call execution from arbitrary caller memory. -/
structure ProcedureRun (module : ProcedureModule) (initial : Memory) where
  final : Memory
  result : Real
  cost : Cost
  steps : Nat
  trace : HaltingTrace module.code ⟨module.entry, initial⟩ final result cost steps

/-- General frame-safe callable procedure; owned scratch need not be restored. -/
structure ProcedureCertificate (contract : ProcedureContract)
    (bound : ProcedureBound contract) where
  module : ProcedureModule
  calling : CallingConvention
  callingRealizes : calling.Realizes contract
  valid : module.Valid
  output : contract.Input → contract.Output
  outputCorrect : ∀ input, contract.pre input → contract.post input (output input)
  correct : ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory,
    contract.inputLayout.RepAt calling.inputRegion input initial →
    ∃ run : ProcedureRun module initial,
      contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
      run.cost ≤ bound input ∧
      PreservesFrame contract calling input (output input) initial run.final

/-- Stronger restoring procedure used by the initial exact-state linker. -/
structure RestoringProcedureCertificate (contract : ProcedureContract)
    (bound : ProcedureBound contract) extends ProcedureCertificate contract bound where
  restoringCorrect : ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory,
    contract.inputLayout.RepAt calling.inputRegion input initial →
    ∃ run : ProcedureRun module initial,
      contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
      run.cost ≤ bound input ∧
      run.final = contract.outputLayout.writeAt calling.outputRegion (output input) initial

/-- One sealed module proved callable at every concrete ABI realizing the contract. -/
structure ParametricProcedureCertificate (contract : ProcedureContract)
    (bound : ProcedureBound contract) where
  module : ProcedureModule
  valid : module.Valid
  output : contract.Input → contract.Output
  outputCorrect : ∀ input, contract.pre input → contract.post input (output input)
  correct : ∀ calling : CallingConvention, calling.Realizes contract →
    ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory,
      contract.inputLayout.RepAt calling.inputRegion input initial →
      ∃ run : ProcedureRun module initial,
        contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
        run.cost ≤ bound input ∧
        PreservesFrame contract calling input (output input) initial run.final

namespace ParametricProcedureCertificate

def forConvention (certificate : ParametricProcedureCertificate contract bound)
    (calling : CallingConvention) (realizes : calling.Realizes contract) :
    ProcedureCertificate contract bound where
  module := certificate.module
  calling := calling
  callingRealizes := realizes
  valid := certificate.valid
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct := certificate.correct calling realizes

end ParametricProcedureCertificate

/-- A structural representation adapter is an ordinary charged procedure certificate. -/
abbrev RepresentationAdapterCertificate (contract : ProcedureContract)
    (bound : ProcedureBound contract) := ProcedureCertificate contract bound

def HasProcedure (contract : ProcedureContract) (bound : ProcedureBound contract) : Prop :=
  Nonempty (ProcedureCertificate contract bound)

def HasRestoringProcedure (contract : ProcedureContract)
    (bound : ProcedureBound contract) : Prop :=
  Nonempty (RestoringProcedureCertificate contract bound)

namespace ProcedureCertificate

/-- Logical bound weakening changes neither code nor execution. -/
def weakenBound (certificate : ProcedureCertificate contract oldBound)
    (larger : ∀ input, oldBound input ≤ newBound input) :
    ProcedureCertificate contract newBound where
  module := certificate.module
  calling := certificate.calling
  callingRealizes := certificate.callingRealizes
  valid := certificate.valid
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct input valid initial represented := by
    rcases certificate.correct input valid initial represented with
      ⟨run, outputRep, cost, frame⟩
    exact ⟨run, outputRep, cost.trans (larger input), frame⟩

end ProcedureCertificate

end

end Algolean.Algorithms.StructuredRealRAM
