/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Audit.Algorithm
public import Algolean.Complexity.WordRAMUniform
public import Algolean.Complexity.WordRAMRelative
public import Algolean.Complexity.WordRAMLinking
public import Algolean.Complexity.WordRAMRandomized
public import Algolean.Complexity.WordRAMRandomizedRelative
public import Algolean.Complexity.WordRAMUniformProcedure
public import Algolean.Complexity.WordRAMUniformLinking
public import Algolean.Models.WordRAM.TypedRegion
public import Algolean.Models.WordRAM.Profile

/-!
# Typed Word-RAM layout and algorithm audit artifacts
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.Audit

/-- Printable audit information tied directly to one closed layout term. -/
structure LayoutAudit (w : ℕ) (alpha : Type) where
  /-- Actual syntax being audited. -/
  layout : WordLayout w alpha
  /-- Optional independently certified fixed stride. -/
  fixedWords : Option ℕ := none
  /-- Structural accessors known to be constant time. -/
  constantTimeAccessors : List String := []
  /-- Operations which require scanning or an explicit index. -/
  scanningOperations : List String := []
  /-- Physical-format notes. -/
  notes : List String := []

def stringList (values : List String) : String :=
  if values.isEmpty then "none" else String.intercalate ", " values

/-- Render every security-relevant layout choice. -/
def LayoutAudit.summary (report : LayoutAudit w alpha) : String :=
  "Machine model: Word RAM\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Resolved closed syntax: " ++ report.layout.syntaxName ++ "\n" ++
  "Header/field format: visible in syntax above\n" ++
  "Value-dependent footprint: layout.encode(value).length words\n" ++
  "Fixed footprint: " ++ (report.fixedWords.map toString).getD "no/unknown" ++ "\n" ++
  "Address-space obligation: FitsAt; no represented address wrap\n" ++
  "Proof fields: erased by subtype constructor\n" ++
  "Array format: length-prefixed sequential payload\n" ++
  "Finite-function order: 0,...,n-1\n" ++
  "Matrix/tensor order: row-major/lexicographic, final index fastest\n" ++
  "Multiword limb order: little endian; normalized zero has no limbs\n" ++
  "Constant-time accessors: " ++ stringList report.constantTimeAccessors ++ "\n" ++
  "Scanning operations: " ++ stringList report.scanningOperations ++ "\n" ++
  "Notes: " ++ stringList report.notes

/-- Resolve a class-selected layout once and build its basic typed audit record. -/
def canonicalLayoutAudit (w : ℕ) (alpha : Type) [CanonicalLayout w alpha] :
    LayoutAudit w alpha where
  layout := layoutOf w alpha
  fixedWords := (layoutOf w alpha).fixedFootprint?
  constantTimeAccessors :=
    if (layoutOf w alpha).fixedFootprint?.isSome then
      ["typed fixed-stride field/element address"] else []
  scanningOperations :=
    if (layoutOf w alpha).fixedFootprint?.isSome then [] else
      ["locating variable-footprint packed elements"]

/-- Typed publication artifact for one structured fixed-width certificate. -/
structure FixedWidthPublication (problem : StructuredProblem w)
    (bound : problem.Input → ℕ) where
  certificate : FixedWidthAlgorithmCertificateBy problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Typed publication artifact for one width-uniform template certificate. -/
structure UniformPublication (family : UniformStructuredProblem)
    (bound : UniformBound family) where
  certificate : UniformAlgorithmCertificate family bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Typed publication artifact for the hidden-source randomized profile. -/
structure RandomizedPublication (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : problem.RandomizedAlgorithmCertificate stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Typed audit artifact for an unresolved randomized client with deterministic dependencies. -/
structure RandomRelativePublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : RandomRelativeAlgorithmCertificate signature problem stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Typed publication artifact for an unresolved contract-relative algorithm. -/
structure RelativePublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (bound : problem.Input → ℕ) where
  certificate : RelativeAlgorithmCertificate signature problem bound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Typed publication for a fully linkable relative client and its refinement theorem. -/
structure LinkablePublication (signature : DependencySignature w)
    (problem : StructuredProblem w)
    (relativeBound linkedBound : problem.Input → ℕ) where
  certificate : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Typed publication for one fully resolved concrete shared-body link. -/
structure LinkedPublication (signature : DependencySignature w)
    (problem : StructuredProblem w)
    (relativeBound linkedBound : problem.Input → Nat) where
  client : RelativeAlgorithmCertificate signature problem relativeBound
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration w
  link : client.ConcreteLink implementations configuration
    (relativeBound := relativeBound) (linkedBound := linkedBound)
  instructionCount : Nat
  instructionCount_eq : instructionCount = link.certificate.program.length
  descriptionSize : Nat
  descriptionSize_eq : descriptionSize = WordRAM.descriptionSize link.certificate.program
  dependencyCount : Nat
  dependencyCount_eq : dependencyCount = Fintype.card signature.Op
  certificateName : Lean.Name
  problemName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Typed publication for reusable callable procedure code. -/
structure ProcedurePublication (contract : ProcedureContract w)
    (bound : ProcedureBound contract) where
  certificate : ProcedureCertificate contract bound
  instructionCount : Nat
  instructionCount_eq : instructionCount = certificate.module.code.length
  descriptionSize : Nat
  descriptionSize_eq : descriptionSize = WordRAM.descriptionSize certificate.module.code
  certificateName : Lean.Name
  contractName : Lean.Name
  boundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Audit derived from the concrete fixed-width certificate, not a name-only manifest. -/
def FixedWidthPublication.summary {w : ℕ} {problem : StructuredProblem w}
    {bound : problem.Input → ℕ}
    (publication : FixedWidthPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: structured fixed-width Word-RAM algorithm\n" ++
  "Linked status: concrete, unconditional\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Input layout: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Input fit theorem: stored in StructuredProblem.inputFits\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++ toString (WordRAM.descriptionSize program) ++ " bits\n" ++
  "Cost/output source: same HaltingTrace\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Randomness: none\nOracles: none\nProcedure dependencies: none\n" ++
  (standardProfile w).summary ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Audit derived from the actual sealed uniform template. -/
def UniformPublication.summary (publication : UniformPublication family bound) : String :=
  let template := publication.certificate.program.template
  "Claim kind: width-uniform structured Word-RAM algorithm\n" ++
  "Uniformity: one sealed finite template before all widths and inputs\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem family: " ++ toString publication.problemName ++ "\n" ++
  "Template instruction count: " ++ toString template.length ++ "\n" ++
  "Template description size: " ++ toString template.descriptionSize ++ " bits\n" ++
  "Instantiation: fixed structural BitVec specialization\n" ++
  "Width admissibility: explicit family.WidthAdmissible\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Cost/output source: same width-specialized HaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Randomized audits disclose the hidden lengthless source and both same-trace resources. -/
def RandomizedPublication.summary {w : Nat} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : RandomizedPublication problem stepBound drawBound failure) : String :=
  let program := publication.certificate.program
  "Claim kind: randomized fixed-width Word-RAM algorithm\n" ++
  "Randomness: hidden lengthless iid fair-bit source\n" ++
  "Random-source length observable: no\n" ++
  "Random instruction: sealed randBit; one draw and one step per sample\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Input layout: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++ toString program.descriptionSize ++ " bits\n" ++
  "Step bound: " ++ toString publication.stepBoundName ++ "\n" ++
  "Random-draw bound: " ++ toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Termination semantics: success event; every-source Las Vegas is separately named\n" ++
  "Cost/output/draw source: same randomized HaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Random-relative reports cannot be confused with a concrete randomized certificate. -/
def RandomRelativePublication.summary {w : Nat} {signature : DependencySignature w}
    {problem : StructuredProblem w} {stepBound drawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : RandomRelativePublication signature problem stepBound drawBound failure) :
    String :=
  "RELATIVE RANDOMIZED ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL WORD-RAM ALGORITHM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Randomness: hidden lengthless iid fair-bit source\n" ++
  "Random-source cursor across calls: preserved and unobservable\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " unresolved\n" ++
  "Concrete discharge requirement: ordinary closed RandomBit.Program plus " ++
    "same-source refinement\n" ++
  "Step bound: " ++ toString publication.stepBoundName ++ "\n" ++
  "Draw bound: " ++ toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/-- Relative audits are deliberately prominent and cannot masquerade as linked certificates. -/
def RelativePublication.summary {w : ℕ} {signature : DependencySignature w}
    {problem : StructuredProblem w} {bound : problem.Input → ℕ}
    (publication : RelativePublication signature problem bound) : String :=
  "RELATIVE ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL WORD-RAM ALGORITHM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Unresolved operations: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Call syntax: first-order typed call nodes\n" ++
  "Call semantics: every admissible contract responder\n" ++
  "Dependency costs: exact input-dependent sum plus one dispatch step per call\n" ++
  "Call records: typed structured input/output/correctness/cost records\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/--
Linkable audit reports the concrete linker and dependency DAG without claiming an environment.
-/
def LinkablePublication.summary {w : ℕ} {signature : DependencySignature w}
    {problem : StructuredProblem w} {relativeBound linkedBound : problem.Input → ℕ}
    (publication : LinkablePublication signature problem relativeBound linkedBound) : String :=
  "Claim kind: verified linkable Word-RAM client\n" ++
  "Linker: concrete shared-body core Word-RAM linker\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Dependency DAG: finite canonical operation order\n" ++
  "Body sharing: one relocated body per operation\n" ++
  "Return mechanism: reserved address register, shared dispatcher, explicit cleanup\n" ++
  "Callee execution: ordinary instructions in the linked core trace\n" ++
  "Linked validity/correctness: proved uniformly for every implementation environment\n" ++
  "Linked bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/-- Concrete linked audits expose the actual linked syntax and the complete resolved signature. -/
def LinkedPublication.summary {w : Nat} {signature : DependencySignature w}
    {problem : StructuredProblem w} {relativeBound linkedBound : problem.Input → Nat}
    (publication : LinkedPublication signature problem relativeBound linkedBound) : String :=
  "Claim kind: concrete linked fixed-width Word-RAM algorithm\n" ++
  "Linked status: fully resolved, unconditional\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Input layout: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Dependency operations: " ++ toString publication.dependencyCount ++ "\n" ++
  "Dependency DAG: " ++ toString publication.dependencyCount ++
    " resolved operation nodes\n" ++
  "Unresolved dependencies: none\n" ++
  "Body sharing: one relocated implementation body per operation\n" ++
  "Calling convention: aliasing input/output regions; setup, dispatch, return, and callee " ++
    "instructions charged in one trace\n" ++
  "Program instruction count: " ++ toString publication.instructionCount ++ "\n" ++
  "Program description size: " ++ toString publication.descriptionSize ++ " bits\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Randomness: none\nOracles: none\n" ++
  (standardProfile w).summary ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Procedure audits expose finite callable code, ownership, and its canonical effect theorem. -/
def ProcedurePublication.summary {w : Nat} {contract : ProcedureContract w}
    {bound : ProcedureBound contract}
    (publication : ProcedurePublication contract bound) : String :=
  let certificate := publication.certificate
  "Claim kind: callable fixed-width Word-RAM procedure\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Contract: " ++ toString publication.contractName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Input layout: " ++ contract.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ contract.outputLayout.syntaxName ++ "\n" ++
  "Entry point: " ++ toString certificate.module.entry ++ "\n" ++
  "Instruction count: " ++ toString publication.instructionCount ++ "\n" ++
  "Description size: " ++ toString publication.descriptionSize ++ " bits\n" ++
  "Call overhead: " ++ toString certificate.calling.callOverhead ++ "\n" ++
  "Frame safety: certified outside input/output/scratch/register ownership\n" ++
  "Final effect: canonical structural output write\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

end Algolean.Algorithms.WordRAM.Audit

namespace Algolean.Algorithms.Audit

instance {problem : WordRAM.StructuredProblem w} {bound : problem.Input → ℕ} :
    AuditablePublication (WordRAM.Audit.FixedWidthPublication problem bound) :=
  ⟨WordRAM.Audit.FixedWidthPublication.summary⟩

instance {family : WordRAM.UniformStructuredProblem} {bound : WordRAM.UniformBound family} :
    AuditablePublication (WordRAM.Audit.UniformPublication family bound) :=
  ⟨WordRAM.Audit.UniformPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.RandomizedPublication problem stepBound drawBound failure) :=
  ⟨WordRAM.Audit.RandomizedPublication.summary⟩

instance {signature : WordRAM.DependencySignature w} {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.RandomRelativePublication signature problem stepBound drawBound failure) :=
  ⟨WordRAM.Audit.RandomRelativePublication.summary⟩

noncomputable instance {signature : WordRAM.DependencySignature w}
    {problem : WordRAM.StructuredProblem w}
    {bound : problem.Input → ℕ} :
    AuditablePublication (WordRAM.Audit.RelativePublication signature problem bound) :=
  ⟨WordRAM.Audit.RelativePublication.summary⟩

instance {signature : WordRAM.DependencySignature w} {problem : WordRAM.StructuredProblem w}
    {relativeBound linkedBound : problem.Input → ℕ} :
    AuditablePublication
      (WordRAM.Audit.LinkablePublication signature problem relativeBound linkedBound) :=
  ⟨WordRAM.Audit.LinkablePublication.summary⟩

noncomputable instance {signature : WordRAM.DependencySignature w}
    {problem : WordRAM.StructuredProblem w}
    {relativeBound linkedBound : problem.Input → ℕ} :
    AuditablePublication
      (WordRAM.Audit.LinkedPublication signature problem relativeBound linkedBound) :=
  ⟨WordRAM.Audit.LinkedPublication.summary⟩

instance {contract : WordRAM.ProcedureContract w} {bound : WordRAM.ProcedureBound contract} :
    AuditablePublication (WordRAM.Audit.ProcedurePublication contract bound) :=
  ⟨WordRAM.Audit.ProcedurePublication.summary⟩

end Algolean.Algorithms.Audit

/-- Print the class-selected closed Word-RAM layout for a type. -/
syntax (name := wordRAMLayoutAuditCmd) "#layout_audit" "WordRAM" term:max term:max : command

macro_rules
  | `(#layout_audit WordRAM $width:term $ty:term) =>
      `(#eval Algolean.Algorithms.WordRAM.Audit.LayoutAudit.summary
          (Algolean.Algorithms.WordRAM.Audit.canonicalLayoutAudit $width $ty))
