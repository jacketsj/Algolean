/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.Algorithm
public import Algolean.Compiler.StructuredRealRAMLinkerCorrectness
public import Algolean.Compiler.StructuredRealRAMEmbedding
public import Algolean.Compiler.StructuredRealRAMRandomLinkerCorrectness
public import Algolean.Compiler.StructuredRealRAMUniformRealLinkerCorrectness
public import Algolean.Models.StructuredRealRAM.ArithmeticProfile
public import Algolean.Complexity.StructuredRealRAMRandomizedGuarantees

/-! # Typed audits for the two-bank structured exact-real/natural RAM -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.Audit

/-- Closed machine-profile disclosure independent of any theorem author callback. -/
structure ProfileAudit where
  name : String
  randomness : String
  extensions : String
  oracles : String

/-- Core two-bank exact-real/natural profile. -/
def coreProfileAudit : ProfileAudit where
  name := coreProfile.name
  randomness := "none"
  extensions := "none (closed core instruction syntax)"
  oracles := "none"

/-- Hidden lengthless iid-fair-bit profile. -/
def randomBitProfileAudit : ProfileAudit where
  name := RandomBit.profile.name
  randomness := "hidden lengthless iid fair bits; one charged randBit transition"
  extensions := "sealed randBit only"
  oracles := "none"

/-- Hidden lengthless exact-uniform-real profile. -/
def uniformRealProfileAudit : ProfileAudit where
  name := UniformReal.profile.name
  randomness := "hidden lengthless iid exact uniform [0,1] values; measurable success required"
  extensions := "sealed sampleUniform only; strictly stronger than random bits"
  oracles := "none"

/-- Typed external-oracle profile; the concrete interface is part of the certificate type. -/
def oracleProfileAudit : ProfileAudit where
  name := OracleMachine.profile.name
  randomness := "none"
  extensions := "sealed oracleCall only; no arbitrary memory transformer"
  oracles := "typed interface fixed before the program; non-vacuity required by publication"

/-- The closed profile index itself determines all audit text. -/
def sealedProfileAudit (profile : SealedProfile) : ProfileAudit where
  name := profile.summary
  randomness := profile.randomness
  extensions := match profile with
    | .deterministic => "none (closed core instruction syntax)"
    | .hiddenFairBits => "sealed randBit only"
    | .hiddenUniformReal => "sealed sampleUniform only; strictly stronger than random bits"
  oracles := "none; typed external-oracle claims use a separate relative API"

/-- Closed disclosure of the two certified core-profile embeddings. -/
def coreEmbeddingSummary (target : SealedProfile) : String :=
  match target with
  | .deterministic =>
      "Embedding: identity on deterministic structured exact-real/natural syntax"
  | .hiddenFairBits =>
      "Embedding: deterministic core -> hidden fair bits via fixed `.core`; " ++
        "trace/cost/cursor/description-size theorems certified"
  | .hiddenUniformReal =>
      "Embedding: deterministic core -> hidden exact uniform reals via fixed `.core`; " ++
        "trace/cost/cursor/description-size theorems certified"

/-- Render every convention affecting computational strength. -/
def ProfileAudit.summary (profile : ProfileAudit) : String :=
  "Machine: " ++ profile.name ++ "\n" ++
  "Banks: exact Real and unbounded mathematical Nat, separately random access\n" ++
  "Addressing: Nat registers address both banks; no Real-to-Nat or Nat-to-Real conversion\n" ++
  "Natural arithmetic: unit-cost +, truncating -, and multiplication\n" ++
  "Input size: represented real cells plus natural cells; not Nat bit length\n" ++
  "Real arithmetic/comparison: exact; source literals are rational\n" ++
  "Division by zero: Lean totalized field division\n" ++
  "Optional arithmetic: selected only by a closed ArithmeticProfile\n" ++
  "Real-to-discrete conversion: absent unless the named floor profile is selected\n" ++
  "Halt counted: yes\n" ++
  "Randomness: " ++ profile.randomness ++ "\n" ++
  "Extensions: " ++ profile.extensions ++ "\n" ++
  "External oracles: " ++ profile.oracles

def stringList (values : List String) : String :=
  if values.isEmpty then "none" else String.intercalate ", " values

/-- Audit data derived from one closed exact-real arithmetic capability term. -/
structure ArithmeticProfileAudit where
  profile : ArithmeticProfile
  embeddingTheorem : Option Lean.Name := none
  warnings : List String := []

/-- Print primitive strength, partial domains, constants, and operation-sensitive costs. -/
def ArithmeticProfileAudit.summary (audit : ArithmeticProfileAudit) : String :=
  "Storage model: structured exact-real/unbounded-Nat RAM\n" ++
  "Arithmetic profile: " ++ audit.profile.name ++ "\n" ++
  "Core primitives: exact +, -, *, / and exact comparison; division is totalized\n" ++
  "Optional closed primitives: " ++ stringList audit.profile.primitiveNames ++ "\n" ++
  "Domain semantics: " ++ stringList audit.profile.domainRules ++ "\n" ++
  "Named constants: " ++ stringList audit.profile.constantNames ++
    "; no arbitrary Real literal\n" ++
  "Resource vector: core Cost plus a separate count for every optional primitive\n" ++
  "Core embedding theorem: " ++
    (audit.embeddingTheorem.map toString).getD "not supplied" ++ "\n" ++
  "Warnings: " ++ stringList audit.warnings

/-- Audit data tied directly to one closed structured layout term. -/
structure LayoutAudit (alpha : Type) where
  layout : Layout alpha
  fixedFootprint : Option Footprint := none
  constantTimeAccessors : List String := []
  scanningOperations : List String := []
  notes : List String := []

def footprintText : Option Footprint → String
  | none => "no/unknown"
  | some footprint =>
      toString footprint.realCells ++ " real, " ++ toString footprint.natCells ++ " natural"

/-- Render all bank, footprint, and accessibility choices. -/
def LayoutAudit.summary (report : LayoutAudit alpha) : String :=
  "Machine model: two-bank structured exact-real/natural RAM\n" ++
  "Resolved closed syntax: " ++ report.layout.syntaxName ++ "\n" ++
  "Value-dependent footprint: layout.footprint(value), in separate real/natural cells\n" ++
  "Fixed footprint: " ++ footprintText report.fixedFootprint ++ "\n" ++
  "Initialization: canonical represented streams; every other cell/register is zero\n" ++
  "Proof fields: erased by subtype layout\n" ++
  "Compact arrays: RealArray and NatArray have contiguous native-bank payloads\n" ++
  "General arrays: structural streams; variable-footprint indexing requires offsets\n" ++
  "Matrix/tensor order: row-major/lexicographic, final index fastest\n" ++
  "Constant-time accessors: " ++ stringList report.constantTimeAccessors ++ "\n" ++
  "Scanning operations: " ++ stringList report.scanningOperations ++ "\n" ++
  "Notes: " ++ stringList report.notes

/-- Resolve a canonical layout once; callers may refine capability metadata. -/
def canonicalLayoutAudit (alpha : Type) [CanonicalLayout alpha] : LayoutAudit alpha where
  layout := layoutOf alpha
  scanningOperations := ["locating a variable-footprint packed element without an offset table"]

/-- Exact input-dependent deterministic publication. -/
structure FixedByPublication (problem : MachineProblem)
    (bound : problem.Input → Cost) where
  certificate : MachineProblem.FixedAlgorithmCertificateBy problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- General frame-safe callable-procedure publication. -/
structure ProcedurePublication (contract : ProcedureContract)
    (bound : ProcedureBound contract) where
  certificate : ProcedureCertificate contract bound
  certificateName : Lean.Name
  contractName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Stronger restoring-procedure publication. -/
structure RestoringProcedurePublication (contract : ProcedureContract)
    (bound : ProcedureBound contract) where
  certificate : RestoringProcedureCertificate contract bound
  certificateName : Lean.Name
  contractName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Unresolved contract-relative publication; intentionally not unconditional. -/
structure RelativePublication (signature : DependencySignature)
    (problem : MachineProblem) (bound : problem.Input → Cost) where
  certificate : RelativeAlgorithmCertificate signature problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Unresolved bounded-time Monte Carlo client with deterministic typed dependencies. -/
structure BoundedTimeMonteCarloRelativePublication (signature : DependencySignature)
    (problem : BitRandomizedMachineProblem) (bound : Nat → RandomBit.Cost)
    (failure : problem.Input → Probability) where
  certificate : BoundedTimeMonteCarloRelativeCertificate signature problem bound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Fully resolved bounded-time Monte Carlo publication from the same-source linker. -/
structure BoundedTimeMonteCarloLinkedPublication (signature : DependencySignature)
    (problem : BitRandomizedMachineProblem)
    (relativeBound linkedBound : Nat → RandomBit.Cost)
    (failure : problem.Input → Probability) where
  client : BoundedTimeMonteCarloRelativeCertificate signature problem relativeBound failure
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration
  assumptions : RandomLinker.LinkingAssumptions client implementations configuration linkedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  relativeBoundName : Lean.Name
  linkedBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Unresolved exact-uniform-real client with deterministic dependencies. -/
structure UniformRealRelativePublication (signature : DependencySignature)
    (problem : UniformRealRandomizedMachineProblem) (bound : Nat → UniformReal.Cost)
    (failure : problem.Input → Probability) where
  certificate : UniformRealBoundedTimeMonteCarloRelativeCertificate signature problem
    bound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Fully linked exact-uniform-real publication with unchanged sample cursor/count. -/
structure UniformRealLinkedPublication (signature : DependencySignature)
    (problem : UniformRealRandomizedMachineProblem)
    (relativeBound linkedBound : Nat → UniformReal.Cost)
    (failure : problem.Input → Probability) where
  client : UniformRealBoundedTimeMonteCarloRelativeCertificate signature problem
    relativeBound failure
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration
  assumptions : UniformRealLinker.LinkingAssumptions client implementations configuration
    linkedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  relativeBoundName : Lean.Name
  linkedBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

noncomputable def UniformRealLinkedPublication.certificate
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → UniformReal.Cost}
    {failure : problem.Input → Probability}
    (publication : UniformRealLinkedPublication signature problem relativeBound linkedBound
      failure) :
    UniformRealRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
      problem linkedBound failure :=
  UniformRealLinker.certificate publication.client publication.implementations
    publication.configuration linkedBound publication.assumptions

/-- The auditable concrete certificate is produced by the verified operational simulation. -/
noncomputable def BoundedTimeMonteCarloLinkedPublication.certificate
    {signature : DependencySignature} {problem : BitRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → RandomBit.Cost}
    {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloLinkedPublication signature problem relativeBound
      linkedBound failure) :
    BitRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
      problem linkedBound failure :=
  RandomLinker.boundedTimeMonteCarloCertificate publication.client publication.implementations
    publication.configuration linkedBound publication.assumptions

/-- Fully resolved shared-body linked publication. -/
structure LinkedPublication (signature : DependencySignature)
    (problem : MachineProblem) (relativeBound linkedBound : problem.Input → Cost) where
  client : RelativeAlgorithmCertificate signature problem relativeBound
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration
  refinement : Linker.Refinement client implementations configuration linkedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

def FixedByPublication.summary (publication : FixedByPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: exact input-dependent fixed structured-real machine algorithm\n" ++
  "Machine: " ++ coreProfile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Input layout: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Instruction count: " ++ toString program.length ++ "\n" ++
  "Description size: " ++ toString program.descriptionSize ++ " bits\n" ++
  "Bound: " ++ toString publication.boundName ++ " (function of the structured input)\n" ++
  "Cost/output source: one HaltingTrace\n" ++
  "Extensions/randomness/oracles: none\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

def ProcedurePublication.summary (publication : ProcedurePublication contract bound) : String :=
  let certificate := publication.certificate
  "Claim kind: general frame-safe structured-real procedure\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Contract: " ++ toString publication.contractName ++ "\n" ++
  "Input/output layouts: " ++ contract.inputLayout.syntaxName ++ " / " ++
    contract.outputLayout.syntaxName ++ "\n" ++
  "ABI realizability: carried by callingRealizes\n" ++
  "Actual-output frame: yes\nOwned scratch may change: yes\n" ++
  "Entry/instruction count: " ++ toString certificate.module.entry ++ " / " ++
    toString certificate.module.code.length ++ "\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def RestoringProcedurePublication.summary
    (publication : RestoringProcedurePublication contract bound) : String :=
  let certificate := publication.certificate
  "Claim kind: restoring structured-real procedure\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Contract: " ++ toString publication.contractName ++ "\n" ++
  "ABI realizability: carried by callingRealizes\n" ++
  "Actual-output frame: yes\n" ++
  "Final effect: only the canonical output write remains\n" ++
  "Instruction count: " ++ toString certificate.module.code.length ++ "\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def RelativePublication.summary (publication : RelativePublication signature problem bound) :
    String :=
  "RELATIVE ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL STRUCTURED REAL-RAM ALGORITHM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Unresolved typed operations: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Calls: first-order nodes with exact structured input/output/cost records\n" ++
  "External oracles: none; these dependencies are dischargeable procedures\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/-- Relative randomized certificates remain visibly non-publication claims. -/
def BoundedTimeMonteCarloRelativePublication.summary
    {signature : DependencySignature} {problem : BitRandomizedMachineProblem}
    {bound : Nat → RandomBit.Cost} {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloRelativePublication signature problem bound failure) :
    String :=
  "RELATIVE RANDOMIZED ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL STRUCTURED REAL-RAM ALGORITHM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Machine profile: " ++ RandomBit.profile.name ++ "\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Random-source length observable: no\n" ++
  "Random cursor across dependency calls: preserved and unobservable\n" ++
  "Unresolved deterministic operations: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Concrete discharge: automatic shared-body same-source linker\n" ++
  "Relative bound: " ++ toString publication.boundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/-- Concrete randomized audit, including linked syntax and hidden-source invariants. -/
noncomputable def BoundedTimeMonteCarloLinkedPublication.summary
    {signature : DependencySignature} {problem : BitRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → RandomBit.Cost}
    {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloLinkedPublication signature problem relativeBound
      linkedBound failure) : String :=
  let certificate := publication.certificate
  "Claim kind: concrete linked bounded-time Monte Carlo structured real/Nat RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Linked status: fully resolved, unconditional\n" ++
  "Machine profile: " ++ RandomBit.profile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Input/output layouts: " ++ problem.inputLayout.syntaxName ++ " / " ++
    problem.outputLayout.syntaxName ++ "\n" ++
  "Random-source length observable: no\n" ++
  "Random cursor across deterministic calls: exactly preserved\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " resolved\n" ++
  "Body sharing: one relocated deterministic body per operation\n" ++
  "Call overhead: exact sum derived from emitted setup/dispatcher/cleanup syntax\n" ++
  "Program instruction count: " ++ toString certificate.program.length ++ "\n" ++
  "Program description size: " ++ toString certificate.program.descriptionSize ++ " bits\n" ++
  "Relative/linked bounds: " ++ toString publication.relativeBoundName ++ " / " ++
    toString publication.linkedBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Cost/output/draw source: one concrete randomized HaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

def UniformRealRelativePublication.summary
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {bound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (publication : UniformRealRelativePublication signature problem bound failure) : String :=
  "RELATIVE EXACT-UNIFORM-REAL BOUNDED-TIME MONTE CARLO CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL STRUCTURED REAL-RAM ALGORITHM\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Machine profile: " ++ UniformReal.profile.name ++ "\n" ++
  "Source: hidden lengthless iid exact uniform [0,1] values\n" ++
  "Unresolved deterministic operations: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Same source/cursor contract: preserved across every abstract call\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

noncomputable def UniformRealLinkedPublication.summary
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → UniformReal.Cost}
    {failure : problem.Input → Probability}
    (publication : UniformRealLinkedPublication signature problem relativeBound linkedBound
      failure) : String :=
  let certificate := publication.certificate
  "Claim kind: fully linked exact-uniform-real bounded-time Monte Carlo algorithm\n" ++
  "Linked status: concrete, unconditional\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Machine profile: " ++ UniformReal.profile.name ++ "\n" ++
  "Same hidden source and cursor preserved: yes\n" ++
  "Deterministic calls consume samples: no\n" ++
  "Every callee instruction charged: yes\n" ++
  "Body sharing: one relocated body per operation\n" ++
  "Link overhead: derived from emitted syntax\n" ++
  "Program instruction/description size: " ++ toString certificate.program.length ++ " / " ++
    toString certificate.program.descriptionSize ++ " bits\n" ++
  "Relative/linked bounds: " ++ toString publication.relativeBoundName ++ " / " ++
    toString publication.linkedBoundName ++ "\n" ++
  "Measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

noncomputable def LinkedPublication.summary
    (publication : LinkedPublication signature problem relativeBound linkedBound) : String :=
  let certificate := Linker.RelativeAlgorithmCertificate.link publication.client
    publication.implementations publication.configuration linkedBound publication.refinement
  "Claim kind: fully linked structured exact-real/natural RAM algorithm\n" ++
  "Linked status: concrete, unconditional\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " resolved\n" ++
  "Body sharing: one relocated body per operation\n" ++
  "Program instruction count: " ++ toString certificate.program.length ++ "\n" ++
  "Program description size: " ++ toString certificate.program.descriptionSize ++ " bits\n" ++
  "Call/output/cost source: concrete core HaltingTrace\n" ++
  "External oracles: none\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

end Algolean.Algorithms.StructuredRealRAM.Audit

namespace Algolean.Algorithms.Audit

instance structuredRealRAMFixedByAuditable : AuditablePublication
    (StructuredRealRAM.Audit.FixedByPublication problem bound) :=
  ⟨StructuredRealRAM.Audit.FixedByPublication.summary⟩

instance structuredRealRAMProcedureAuditable : AuditablePublication
    (StructuredRealRAM.Audit.ProcedurePublication contract bound) :=
  ⟨StructuredRealRAM.Audit.ProcedurePublication.summary⟩

instance structuredRealRAMRestoringProcedureAuditable : AuditablePublication
    (StructuredRealRAM.Audit.RestoringProcedurePublication contract bound) :=
  ⟨StructuredRealRAM.Audit.RestoringProcedurePublication.summary⟩

noncomputable instance structuredRealRAMRelativeAuditable : AuditablePublication
    (StructuredRealRAM.Audit.RelativePublication signature problem bound) :=
  ⟨StructuredRealRAM.Audit.RelativePublication.summary⟩

noncomputable instance structuredRealRAMBoundedTimeMonteCarloRelativeAuditable
    {signature : StructuredRealRAM.DependencySignature}
    {problem : BitRandomizedMachineProblem}
    {bound : Nat → StructuredRealRAM.RandomBit.Cost}
    {failure : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.Audit.BoundedTimeMonteCarloRelativePublication signature problem bound
      failure) :=
  ⟨StructuredRealRAM.Audit.BoundedTimeMonteCarloRelativePublication.summary⟩

noncomputable instance structuredRealRAMBoundedTimeMonteCarloLinkedAuditable
    {signature : StructuredRealRAM.DependencySignature}
    {problem : BitRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → StructuredRealRAM.RandomBit.Cost}
    {failure : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.Audit.BoundedTimeMonteCarloLinkedPublication signature problem
      relativeBound linkedBound failure) :=
  ⟨StructuredRealRAM.Audit.BoundedTimeMonteCarloLinkedPublication.summary⟩

noncomputable instance structuredRealRAMUniformRealRelativeAuditable
    {signature : StructuredRealRAM.DependencySignature}
    {problem : UniformRealRandomizedMachineProblem}
    {bound : Nat → StructuredRealRAM.UniformReal.Cost}
    {failure : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.Audit.UniformRealRelativePublication signature problem bound failure) :=
  ⟨StructuredRealRAM.Audit.UniformRealRelativePublication.summary⟩

noncomputable instance structuredRealRAMUniformRealLinkedAuditable
    {signature : StructuredRealRAM.DependencySignature}
    {problem : UniformRealRandomizedMachineProblem}
    {relativeBound linkedBound : Nat → StructuredRealRAM.UniformReal.Cost}
    {failure : problem.Input → Probability} : AuditablePublication
    (StructuredRealRAM.Audit.UniformRealLinkedPublication signature problem relativeBound
      linkedBound failure) :=
  ⟨StructuredRealRAM.Audit.UniformRealLinkedPublication.summary⟩

noncomputable instance structuredRealRAMLinkedAuditable : AuditablePublication
    (StructuredRealRAM.Audit.LinkedPublication signature problem relativeBound linkedBound) :=
  ⟨StructuredRealRAM.Audit.LinkedPublication.summary⟩

end Algolean.Algorithms.Audit

/-- Print the resolved closed structured exact-real/natural layout for a type. -/
@[nolint topNamespace]
syntax (name := structuredRealRAMLayoutAuditCmd)
  "#layout_audit" "StructuredRealRAM" term:max : command

macro_rules
  | `(#layout_audit StructuredRealRAM $ty:term) =>
      `(#eval Algolean.Algorithms.StructuredRealRAM.Audit.LayoutAudit.summary
          (Algolean.Algorithms.StructuredRealRAM.Audit.canonicalLayoutAudit $ty))

/-- Print a typed closed machine-profile disclosure. -/
@[nolint topNamespace]
syntax (name := machineProfileAuditCmd) "#machine_profile_audit" term : command

macro_rules
  | `(#machine_profile_audit $profile:term) =>
      `(#eval Algolean.Algorithms.StructuredRealRAM.Audit.ProfileAudit.summary $profile)

/-- Print the strength and semantics of one closed exact-real arithmetic profile. -/
@[nolint topNamespace]
syntax (name := arithmeticProfileAuditCmd) "#arithmetic_profile_audit" term : command

macro_rules
  | `(#arithmetic_profile_audit $profile:term) =>
      `(#eval Algolean.Algorithms.StructuredRealRAM.Audit.ArithmeticProfileAudit.summary
          ({ profile := $profile } :
            Algolean.Algorithms.StructuredRealRAM.Audit.ArithmeticProfileAudit))
