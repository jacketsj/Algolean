/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.StructuredRealRAMProfiled
public import Algolean.Complexity.StructuredRealRAMProcedure

/-! # Callable procedures in closed arithmetic/randomness profiles -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

noncomputable section

abbrev ProfiledProcedureBound (contract : ProcedureContract) :=
  contract.Input → ProfiledCost

/-- Finite callable code in exactly one closed profile. -/
structure ProfiledProcedureModule (profile : ClosedMachineProfile) where
  code : ProfiledProgram profile
  entry : Nat

def ProfiledProcedureModule.Valid (module : ProfiledProcedureModule profile) : Prop :=
  module.code.Valid ∧ module.entry < module.code.length

/-- Same-source, arbitrary-cursor procedure execution from caller-owned memory. -/
structure ProfiledProcedureRun (module : ProfiledProcedureModule profile)
    (source : profile.randomness.Source) (initialCursor : Nat) (initial : Memory) where
  final : Memory
  result : Real
  cost : ProfiledCost
  steps : Nat
  draws : Nat
  trace : ProfiledHaltingTrace module.code source
    ⟨module.entry, initial, initialCursor⟩ final result cost steps draws

/-- Profile-aware callable procedure with canonical I/O and frame preservation. -/
structure ProfiledProcedureCertificate (profile : ClosedMachineProfile)
    (contract : ProcedureContract) (bound : ProfiledProcedureBound contract) where
  module : ProfiledProcedureModule profile
  calling : CallingConvention
  callingRealizes : calling.Realizes contract
  valid : module.Valid
  output : contract.Input → contract.Output
  outputCorrect : ∀ input, contract.pre input → contract.post input (output input)
  correct : ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory,
    contract.inputLayout.RepAt calling.inputRegion input initial →
    ∀ source cursor,
    ∃ run : ProfiledProcedureRun module source cursor initial,
      contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
      run.cost ≤ bound input ∧
      PreservesFrame contract calling input (output input) initial run.final

/-- Exact-state restoring procedure used by the concrete shared-body linker. -/
structure ProfiledRestoringProcedureCertificate (profile : ClosedMachineProfile)
    (contract : ProcedureContract) (bound : ProfiledProcedureBound contract)
    extends ProfiledProcedureCertificate profile contract bound where
  restoringCorrect : ∀ input, ∀ _validInput : contract.pre input, ∀ initial : Memory,
    contract.inputLayout.RepAt calling.inputRegion input initial →
    ∀ source cursor,
    ∃ run : ProfiledProcedureRun module source cursor initial,
      contract.outputLayout.RepAt calling.outputRegion (output input) run.final ∧
      run.cost ≤ bound input ∧
      run.final = contract.outputLayout.writeAt calling.outputRegion (output input) initial

def HasProfiledProcedure (profile : ClosedMachineProfile) (contract : ProcedureContract)
    (bound : ProfiledProcedureBound contract) : Prop :=
  Nonempty (ProfiledProcedureCertificate profile contract bound)

namespace ProfiledProcedureCertificate

def weakenBound (certificate : ProfiledProcedureCertificate profile contract oldBound)
    (larger : ∀ input, oldBound input ≤ newBound input) :
    ProfiledProcedureCertificate profile contract newBound where
  module := certificate.module
  calling := certificate.calling
  callingRealizes := certificate.callingRealizes
  valid := certificate.valid
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct input validInput initial represented source cursor := by
    rcases certificate.correct input validInput initial represented source cursor with
      ⟨run, outputRep, costBound, frame⟩
    exact ⟨run, outputRep, costBound.trans (larger input), frame⟩

end ProfiledProcedureCertificate

/-- Lift a deterministic procedure into stronger arithmetic and any selected hidden source. -/
def ProfiledRestoringProcedureCertificate.embedDeterministic
    {sourceArithmetic targetArithmetic : ArithmeticProfile}
    (arithmetic : sourceArithmetic.Includes targetArithmetic)
    (randomness : RandomnessProfile)
    (certificate : ProfiledRestoringProcedureCertificate
      (ClosedMachineProfile.deterministic sourceArithmetic) contract bound) :
    ProfiledRestoringProcedureCertificate
      ⟨targetArithmetic, randomness⟩ contract bound where
  module :=
    { code := certificate.module.code.lift
        (ClosedMachineProfile.Embedding.deterministicInto arithmetic randomness)
      entry := certificate.module.entry }
  calling := certificate.calling
  callingRealizes := certificate.callingRealizes
  valid := ⟨certificate.module.code.lift_valid _ certificate.valid.1, by
    simpa using certificate.valid.2⟩
  output := certificate.output
  outputCorrect := certificate.outputCorrect
  correct input validInput initial represented source cursor := by
    rcases certificate.correct input validInput initial represented () cursor with
      ⟨run, outputRep, costBound, frame⟩
    let liftedRun : ProfiledProcedureRun
        { code := certificate.module.code.lift
            (ClosedMachineProfile.Embedding.deterministicInto arithmetic randomness)
          entry := certificate.module.entry }
        source cursor initial :=
      { final := run.final
        result := run.result
        cost := run.cost
        steps := run.steps
        draws := run.draws
        trace := run.trace.liftDeterministic arithmetic source }
    exact ⟨liftedRun, outputRep, costBound, frame⟩
  restoringCorrect input validInput initial represented source cursor := by
    rcases certificate.restoringCorrect input validInput initial represented () cursor with
      ⟨run, outputRep, costBound, finalEq⟩
    let liftedRun : ProfiledProcedureRun
        { code := certificate.module.code.lift
            (ClosedMachineProfile.Embedding.deterministicInto arithmetic randomness)
          entry := certificate.module.entry }
        source cursor initial :=
      { final := run.final
        result := run.result
        cost := run.cost
        steps := run.steps
        draws := run.draws
        trace := run.trace.liftDeterministic arithmetic source }
    exact ⟨liftedRun, outputRep, costBound, finalEq⟩

end

end Algolean.Algorithms.StructuredRealRAM
