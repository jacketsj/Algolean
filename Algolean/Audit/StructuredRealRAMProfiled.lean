/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.StructuredRealRAM
public import Algolean.Compiler.StructuredRealRAMProfiledLinker

/-! # Typed audits for closed arithmetic/randomness product profiles -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.ProfiledAudit

open MeasureTheory

def stringList (values : List String) : String :=
  if values.isEmpty then "none" else String.intercalate ", " values

/-- The input-distribution axis is independent of internal machine randomness. -/
inductive InputModel where
  | worstCaseValid
  | averageCase (distributionName : String)
  | randomOrder (distributionName : String)
  | smoothed (distributionName : String)
deriving DecidableEq, Repr

def InputModel.summary : InputModel → String
  | .worstCaseValid => "worst case over every input satisfying the precondition"
  | .averageCase name => "average case under external input law " ++ name
  | .randomOrder name => "random order under external input law " ++ name
  | .smoothed name => "smoothed analysis under external input law " ++ name

/-- Profile text is computed from the actual type index carried by a certificate. -/
def profileSummary (profile : ClosedMachineProfile) : String :=
  "Storage architecture: exact Real bank + unbounded mathematical Nat bank\n" ++
  "Arithmetic profile: " ++ profile.arithmetic.name ++ "\n" ++
  "Comparison: exact three-way order comparison\n" ++
  "Core division: totalized according to Lean field division\n" ++
  "Partial-operation domains: " ++ stringList profile.arithmetic.domainRules ++ "\n" ++
  "Named constants: " ++ stringList profile.arithmetic.constantNames ++
    " (finite tags only; arbitrary Real literals absent)\n" ++
  "Real-to-Nat bridge: " ++
    (if "floor-to-Nat" ∈ profile.arithmetic.primitiveNames then
      "exact nonnegative floor is present and separately charged"
    else "absent") ++ "\n" ++
  "Random source: " ++ profile.randomness.name ++ "\n" ++
  "Random-source length observable: no\n" ++
  "Cost coordinates: core machine vector, one coordinate per optional primitive, random draws"

/-- Typed fixed-program publication in one exact closed profile. -/
structure FixedPublication (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) where
  certificate : ProfiledMachineProblem.FixedAlgorithmCertificateBy problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  primitiveBoundTheorems : List Lean.Name := []
  inputModel : InputModel := .worstCaseValid
  warnings : List String := []

/-- Typed callable-procedure publication in the same closed product profile. -/
structure ProcedurePublication (profile : ClosedMachineProfile) (contract : ProcedureContract)
    (bound : ProfiledProcedureBound contract) where
  certificate : ProfiledProcedureCertificate profile contract bound
  certificateName : Lean.Name
  contractName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  primitiveBoundTheorems : List Lean.Name := []
  warnings : List String := []

/-- An unresolved client is deliberately a different publication type. -/
structure RelativePublication (signature : ProfiledDependencySignature profile)
    (problem : ProfiledMachineProblem profile) (bound : problem.Input → ProfiledCost) where
  certificate : ProfiledRelativeAlgorithmCertificate signature problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Fully linked shared-body publication; every runtime call executes profiled machine code. -/
structure LinkedPublication (signature : ProfiledDependencySignature profile)
    (problem : ProfiledMachineProblem profile)
    (relativeBound linkedBound : problem.Input → ProfiledCost) where
  client : ProfiledRelativeAlgorithmCertificate signature problem relativeBound
  implementations : ProfiledImplementationEnvironment signature
  configuration : ProfiledLinker.Configuration
  refinement : ProfiledLinker.Refinement client implementations configuration linkedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  primitiveBoundTheorems : List Lean.Name := []
  warnings : List String := []

/-- Every-source-time Monte Carlo publication in an explicit random-source profile. -/
structure BoundedTimeMonteCarloPublication (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (failure : problem.Input → Probability) where
  certificate : ProfiledMachineProblem.BoundedTimeMonteCarloCertificate problem bound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  primitiveBoundTheorems : List Lean.Name := []
  inputModel : InputModel := .worstCaseValid
  warnings : List String := []

/-- Finite-expected-time Las Vegas publication; finiteness is a certificate field. -/
structure LasVegasExpectedTimePublication (problem : ProfiledMachineProblem profile)
    (expectedBound : problem.Input → ENNReal) where
  certificate : ProfiledMachineProblem.LasVegasExpectedTimeCertificate problem expectedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  expectedBoundName : Lean.Name
  correctnessTheorem : Lean.Name
  terminationTheorem : Lean.Name
  runtimeMeasurabilityTheorem : Lean.Name
  finitenessTheorem : Lean.Name
  warnings : List String := []

/-- Strong a.s.-terminating high-probability-time Las Vegas publication. -/
structure LasVegasHighProbabilityTimePublication (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (timeout : problem.Input → Probability) where
  certificate :
    ProfiledMachineProblem.LasVegasHighProbabilityTimeCertificate problem bound timeout
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  timeoutName : Lean.Name
  correctnessTheorem : Lean.Name
  terminationTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

/-- Deliberately weaker publication which permits divergence outside its bounded event. -/
structure ZeroErrorBoundedTerminationPublication (problem : ProfiledMachineProblem profile)
    (bound : problem.Input → ProfiledCost) (timeout : problem.Input → Probability) where
  certificate : ProfiledMachineProblem.ZeroErrorHighProbabilityBoundedTerminationCertificate
    problem bound timeout
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  timeoutName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

def FixedPublication.summary {profile : ClosedMachineProfile}
    {problem : ProfiledMachineProblem profile}
    {bound : problem.Input → ProfiledCost}
    (publication : FixedPublication problem bound) : String :=
  profileSummary profile ++ "\n" ++
  "Claim: fixed finite first-order program\n" ++
  "Input model: " ++ publication.inputModel.summary ++ "\n" ++
  "Certificate/problem: " ++ toString publication.certificateName ++ " / " ++
    toString publication.problemName ++ "\n" ++
  "Input/output layouts: " ++ problem.inputLayout.syntaxName ++ " / " ++
    problem.outputLayout.syntaxName ++ "\n" ++
  "Instruction/description size: " ++ toString publication.certificate.program.length ++
    " / " ++ toString publication.certificate.program.descriptionSize ++ " bits\n" ++
  "Per-primitive bound theorems: " ++ stringList (publication.primitiveBoundTheorems.map toString) ++
    "\nBound: " ++ toString publication.boundName ++ "\n" ++
  "Output/cost/draws: one ProfiledHaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

def ProcedurePublication.summary
    (publication : ProcedurePublication profile contract bound) : String :=
  profileSummary profile ++ "\n" ++
  "Claim: callable frame-safe profiled procedure\n" ++
  "Certificate/contract: " ++ toString publication.certificateName ++ " / " ++
    toString publication.contractName ++ "\n" ++
  "ABI realizability: proof-carrying\nSource/cursor: one caller-owned source, arbitrary cursor\n" ++
  "Instruction/description size: " ++ toString publication.certificate.module.code.length ++
    " / " ++ toString publication.certificate.module.code.descriptionSize ++ " bits\n" ++
  "Per-primitive bound theorems: " ++ stringList (publication.primitiveBoundTheorems.map toString) ++
    "\nBound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def RelativePublication.summary
    {profile : ClosedMachineProfile} {signature : ProfiledDependencySignature profile}
    {problem : ProfiledMachineProblem profile}
    {bound : problem.Input → ProfiledCost}
    (publication : RelativePublication signature problem bound) : String :=
  "RELATIVE ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL PROFILED MACHINE ALGORITHM\n" ++
  profileSummary profile ++ "\n" ++
  "Certificate/problem: " ++ toString publication.certificateName ++ " / " ++
    toString publication.problemName ++ "\n" ++
  "Unresolved typed procedures: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Calls: finite first-order nodes; coherent responder required\n" ++
  "Bound/correctness: " ++ toString publication.boundName ++ " / " ++
    toString publication.correctnessTheorem

noncomputable def LinkedPublication.summary
    {profile : ClosedMachineProfile} {signature : ProfiledDependencySignature profile}
    {problem : ProfiledMachineProblem profile}
    {relativeBound linkedBound : problem.Input → ProfiledCost}
    (publication : LinkedPublication signature problem relativeBound linkedBound) : String :=
  let certificate := ProfiledLinker.ProfiledRelativeAlgorithmCertificate.link
    publication.client publication.implementations publication.configuration
      linkedBound publication.refinement
  profileSummary profile ++ "\n" ++
  "Claim: fully linked, unconditional profiled algorithm\n" ++
  "Certificate/problem: " ++ toString publication.certificateName ++ " / " ++
    toString publication.problemName ++ "\n" ++
  "Dependency status: " ++ toString (Fintype.card signature.Op) ++ " resolved\n" ++
  "Body sharing: one relocated body per operation\n" ++
  "Execution: callee instructions occur in the same concrete ProfiledHaltingTrace\n" ++
  "Instruction/description size: " ++ toString certificate.program.length ++ " / " ++
    toString certificate.program.descriptionSize ++ " bits\n" ++
  "Per-primitive bound theorems: " ++ stringList (publication.primitiveBoundTheorems.map toString) ++
    "\nBound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def BoundedTimeMonteCarloPublication.summary
    {profile : ClosedMachineProfile} {problem : ProfiledMachineProblem profile}
    {bound : problem.Input → ProfiledCost} {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloPublication problem bound failure) : String :=
  profileSummary profile ++ "\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Input model: " ++ publication.inputModel.summary ++ "\n" ++
  "Termination: every source within the full resource-vector bound\n" ++
  "Correctness: two-sided error at most " ++ toString publication.failureName ++ "\n" ++
  "Draw bound: randomDraws coordinate of " ++ toString publication.boundName ++ "\n" ++
  "Program instruction/description size: " ++ toString publication.certificate.program.length ++
    " / " ++ toString publication.certificate.program.descriptionSize ++ " bits\n" ++
  "Per-primitive bound theorems: " ++ stringList (publication.primitiveBoundTheorems.map toString) ++
    "\nMeasurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def LasVegasExpectedTimePublication.summary
    {profile : ClosedMachineProfile} {problem : ProfiledMachineProblem profile}
    {expectedBound : problem.Input → ENNReal}
    (publication : LasVegasExpectedTimePublication problem expectedBound) : String :=
  profileSummary profile ++ "\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.expectedTimeLasVegas.summary ++ "\n" ++
  "Expected bound: " ++ toString publication.expectedBoundName ++ "\n" ++
  "Almost-sure termination theorem: " ++ toString publication.terminationTheorem ++ "\n" ++
  "Runtime measurability theorem: " ++ toString publication.runtimeMeasurabilityTheorem ++ "\n" ++
  "Finite-bound theorem: " ++ toString publication.finitenessTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def LasVegasHighProbabilityTimePublication.summary
    {profile : ClosedMachineProfile} {problem : ProfiledMachineProblem profile}
    {bound : problem.Input → ProfiledCost} {timeout : problem.Input → Probability}
    (publication : LasVegasHighProbabilityTimePublication problem bound timeout) : String :=
  profileSummary profile ++ "\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.highProbabilityTimeLasVegas.summary ++ "\n" ++
  "Termination: almost surely; bounded envelope may fail with probability " ++
    toString publication.timeoutName ++ "\n" ++
  "Almost-sure theorem: " ++ toString publication.terminationTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def ZeroErrorBoundedTerminationPublication.summary
    {profile : ClosedMachineProfile} {problem : ProfiledMachineProblem profile}
    {bound : problem.Input → ProfiledCost} {timeout : problem.Input → Probability}
    (publication : ZeroErrorBoundedTerminationPublication problem bound timeout) : String :=
  profileSummary profile ++ "\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.summary
    Algolean.Algorithms.Audit.RandomGuaranteeAudit.zeroErrorHighProbabilityBoundedTermination ++
      "\n" ++
  "Almost-sure termination: NOT CLAIMED\n" ++
  "Divergence outside bounded event: permitted\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

end Algolean.Algorithms.StructuredRealRAM.ProfiledAudit

namespace Algolean.Algorithms.Audit

instance profiledFixedPublicationAuditable {profile : StructuredRealRAM.ClosedMachineProfile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {bound : problem.Input → StructuredRealRAM.ProfiledCost} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.FixedPublication problem bound) :=
  ⟨fun publication ↦ StructuredRealRAM.ProfiledAudit.FixedPublication.summary
    (profile := profile) publication⟩

instance profiledProcedurePublicationAuditable {profile : StructuredRealRAM.ClosedMachineProfile}
    {contract : StructuredRealRAM.ProcedureContract}
    {bound : StructuredRealRAM.ProfiledProcedureBound contract} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.ProcedurePublication profile contract bound) :=
  ⟨StructuredRealRAM.ProfiledAudit.ProcedurePublication.summary⟩

instance profiledRelativePublicationAuditable {profile : StructuredRealRAM.ClosedMachineProfile}
    {signature : StructuredRealRAM.ProfiledDependencySignature profile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {bound : problem.Input → StructuredRealRAM.ProfiledCost} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.RelativePublication signature problem bound) :=
  ⟨fun publication ↦ StructuredRealRAM.ProfiledAudit.RelativePublication.summary
    (profile := profile) publication⟩

noncomputable instance profiledLinkedPublicationAuditable
    {profile : StructuredRealRAM.ClosedMachineProfile}
    {signature : StructuredRealRAM.ProfiledDependencySignature profile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {relativeBound linkedBound : problem.Input → StructuredRealRAM.ProfiledCost} :
    AuditablePublication
    (StructuredRealRAM.ProfiledAudit.LinkedPublication
      signature problem relativeBound linkedBound) :=
  ⟨fun publication ↦ StructuredRealRAM.ProfiledAudit.LinkedPublication.summary
    (profile := profile) publication⟩

instance profiledMonteCarloPublicationAuditable
    {profile : StructuredRealRAM.ClosedMachineProfile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {bound : problem.Input → StructuredRealRAM.ProfiledCost}
    {failure : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.BoundedTimeMonteCarloPublication
      problem bound failure) :=
  ⟨StructuredRealRAM.ProfiledAudit.BoundedTimeMonteCarloPublication.summary⟩

instance profiledExpectedTimePublicationAuditable
    {profile : StructuredRealRAM.ClosedMachineProfile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {expectedBound : problem.Input → ENNReal} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.LasVegasExpectedTimePublication
      problem expectedBound) :=
  ⟨fun publication ↦ StructuredRealRAM.ProfiledAudit.LasVegasExpectedTimePublication.summary
    (profile := profile) publication⟩

instance profiledHighProbabilityTimePublicationAuditable
    {profile : StructuredRealRAM.ClosedMachineProfile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {bound : problem.Input → StructuredRealRAM.ProfiledCost}
    {timeout : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.LasVegasHighProbabilityTimePublication
      problem bound timeout) :=
  ⟨fun publication ↦
    StructuredRealRAM.ProfiledAudit.LasVegasHighProbabilityTimePublication.summary
      (profile := profile) publication⟩

instance profiledWeakBoundedTerminationPublicationAuditable
    {profile : StructuredRealRAM.ClosedMachineProfile}
    {problem : StructuredRealRAM.ProfiledMachineProblem profile}
    {bound : problem.Input → StructuredRealRAM.ProfiledCost}
    {timeout : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.ProfiledAudit.ZeroErrorBoundedTerminationPublication
      problem bound timeout) :=
  ⟨fun publication ↦
    StructuredRealRAM.ProfiledAudit.ZeroErrorBoundedTerminationPublication.summary
      (profile := profile) publication⟩

end Algolean.Algorithms.Audit
