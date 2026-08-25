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
public import Algolean.Compiler.WordRAMRandomLinkerCorrectness
public import Algolean.Complexity.WordRAMUniformProcedure
public import Algolean.Complexity.WordRAMUniformLinking
public import Algolean.Models.WordRAM.TypedRegion
public import Algolean.Models.WordRAM.Profile
public import Algolean.Complexity.WordRAMDerivedOperations

/-!
# Typed Word-RAM layout and algorithm audit artifacts
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.Audit

open MeasureTheory

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

/-- Named physical graph format; no abstract graph enumeration is selected here. -/
inductive PhysicalGraphFormat where
  | directedEdgeList | undirectedDartList | csr | adjacencyMatrix
deriving DecidableEq, Repr

/-- Audit disclosure for an already materialized physical graph representation. -/
structure PhysicalGraphAudit (w : Nat) where
  format : PhysicalGraphFormat
  payloadLayout : String
  vertexCountLocation : String
  edgeCountLocation : String
  reverseMap : Bool
  neighborAccess : String
  footprint : String

def PhysicalGraphAudit.summary (audit : PhysicalGraphAudit w) : String :=
  "Machine model: fixed-width Word RAM\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Physical graph format: " ++ reprStr audit.format ++ "\n" ++
  "Payload layout: " ++ audit.payloadLayout ++ "\n" ++
  "Vertex-count location: " ++ audit.vertexCountLocation ++ "\n" ++
  "Edge/dart-count location: " ++ audit.edgeCountLocation ++ "\n" ++
  "Reverse map present: " ++ toString audit.reverseMap ++ "\n" ++
  "Neighbor access: " ++ audit.neighborAccess ++ "\n" ++
  "Footprint: " ++ audit.footprint ++ "\n" ++
  "Semantic predicates: EveryStoredEdgeSatisfies (one-sided) and RepresentsExactly (two-sided)\n" ++
  "Conversion from another representation: charged certified algorithm; never a layout codec"

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

/-- Audit artifact for a finite certified rich-operation library and its core lowering. -/
structure DerivedOperationLibraryPublication (library : PreprocessedWordOperationLibrary w) where
  libraryName : Lean.Name
  initializationTheorem : Lean.Name
  loweringTheorem : Lean.Name
  warnings : List String := []

/-- Width-uniform rich-operation publication backed by formal asymptotic inequalities. -/
structure UniformDerivedOperationLibraryPublication
    (family : UniformStructuredProblem)
    (library : UniformPreprocessedWordOperationLibrary) where
  robustness : DerivedOperationRobustness family library
  libraryName : Lean.Name
  widthLowerTheorem : Lean.Name
  widthUpperTheorem : Lean.Name
  preprocessingTheorem : Lean.Name
  spaceTheorem : Lean.Name
  operationCostTheorem : Lean.Name
  uniformityTheorem : Lean.Name
  warnings : List String := []

/-- Typed publication artifact for high-probability bounded success. -/
structure HighProbabilityBoundedSuccessPublication (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : problem.HighProbabilityBoundedSuccessCertificate stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Every-source-time two-sided-error publication; timeout is not part of its error event. -/
structure BoundedTimeMonteCarloPublication (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : problem.BoundedTimeMonteCarloCertificate stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

/-- Every-source-time RP-oriented one-sided-error publication. -/
structure OneSidedBoundedTimeMonteCarloPublication (problem : StructuredProblem w)
    (specification : StructuredProblem.OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : problem.OneSidedBoundedTimeMonteCarloCertificate specification
    stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  specificationName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

/-- Every-source-time coRP-oriented one-sided-error publication. -/
structure CoOneSidedBoundedTimeMonteCarloPublication (problem : StructuredProblem w)
    (specification : StructuredProblem.OneSidedDecisionSpec problem)
    (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : problem.CoOneSidedBoundedTimeMonteCarloCertificate specification
    stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  specificationName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  measurabilityTheorem : Lean.Name
  warnings : List String := []

/-- Zero-error almost-sure-termination publication without an expected-time claim. -/
structure AlmostSureLasVegasPublication (problem : StructuredProblem w) where
  certificate : problem.AlmostSureLasVegasCertificate
  certificateName : Lean.Name
  problemName : Lean.Name
  terminationMeasurabilityTheorem : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Zero-error finite-expected-time publication. -/
structure LasVegasExpectedTimePublication (problem : StructuredProblem w)
    (expectedStepBound : problem.Input → ENNReal) where
  certificate : problem.LasVegasExpectedTimeCertificate expectedStepBound
  certificateName : Lean.Name
  problemName : Lean.Name
  expectedStepBoundName : Lean.Name
  terminationMeasurabilityTheorem : Lean.Name
  runtimeMeasurabilityTheorem : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Zero-error almost-sure publication with a high-probability time/draw envelope. -/
structure LasVegasHighProbabilityTimePublication (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat)
    (timeout : problem.Input → Probability) where
  certificate : problem.LasVegasHighProbabilityTimeCertificate stepBound drawBound timeout
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  timeoutName : Lean.Name
  terminationMeasurabilityTheorem : Lean.Name
  withinMeasurabilityTheorem : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Expected measurable approximation-loss publication. -/
structure ExpectedApproximationPublication (problem : StructuredProblem w)
    (loss : problem.Input → problem.Output → ENNReal)
    (expectedLossBound : problem.Input → ENNReal) where
  certificate : problem.ExpectedApproximationCertificate loss expectedLossBound
  certificateName : Lean.Name
  problemName : Lean.Name
  lossName : Lean.Name
  expectedLossBoundName : Lean.Name
  measurabilityTheorem : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Exact output-distribution publication. -/
structure SamplerPublication (problem : StructuredProblem w)
    [MeasurableSpace problem.Output] (target : problem.Input → Measure problem.Output) where
  certificate : problem.SamplerCertificate target
  certificateName : Lean.Name
  problemName : Lean.Name
  targetName : Lean.Name
  measurabilityTheorem : Lean.Name
  distributionTheorem : Lean.Name
  warnings : List String := []

/-- Strong zero-error every-source-time publication. -/
structure EverySourceLasVegasPublication (problem : StructuredProblem w)
    (stepBound drawBound : problem.Input → Nat) where
  certificate : problem.EverySourceLasVegasCertificate stepBound drawBound
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Unresolved high-probability bounded-success client with deterministic dependencies. -/
structure HighProbabilityBoundedSuccessRelativePublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : HighProbabilityBoundedSuccessRelativeCertificate signature problem
    stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Unresolved every-source-time Monte Carlo client. -/
structure BoundedTimeMonteCarloRelativePublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  certificate : BoundedTimeMonteCarloRelativeCertificate signature problem
    stepBound drawBound failure
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name

/-- Fully linked high-probability bounded-success publication. -/
structure HighProbabilityBoundedSuccessLinkedPublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound overheadBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
    stepBound drawBound failure
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration w
  assumptions : RandomLinker.LinkingAssumptions client implementations configuration overheadBound
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  overheadBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

/-- Fully resolved linker publication preserving every-source termination. -/
structure BoundedTimeMonteCarloLinkedPublication (signature : DependencySignature w)
    (problem : StructuredProblem w) (stepBound drawBound overheadBound : problem.Input → Nat)
    (failure : problem.Input → Probability) where
  client : BoundedTimeMonteCarloRelativeCertificate signature problem
    stepBound drawBound failure
  implementations : ImplementationEnvironment signature
  configuration : Linker.Configuration w
  assumptions : RandomLinker.BoundedTimeLinkingAssumptions client implementations
    configuration overheadBound
  certificateName : Lean.Name
  problemName : Lean.Name
  stepBoundName : Lean.Name
  drawBoundName : Lean.Name
  overheadBoundName : Lean.Name
  failureName : Lean.Name
  correctnessTheorem : Lean.Name
  warnings : List String := []

noncomputable def BoundedTimeMonteCarloLinkedPublication.certificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloLinkedPublication signature problem stepBound drawBound
      overheadBound failure) :
    problem.BoundedTimeMonteCarloCertificate
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound failure :=
  RandomLinker.boundedTimeCertificate publication.client publication.implementations
    publication.configuration overheadBound publication.assumptions

/-- The actual unconditional certificate is computed by the verified linker. -/
noncomputable def HighProbabilityBoundedSuccessLinkedPublication.certificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : HighProbabilityBoundedSuccessLinkedPublication signature problem stepBound
      drawBound overheadBound failure) :
    problem.HighProbabilityBoundedSuccessCertificate
      (RandomLinker.linkedStepBound stepBound overheadBound) drawBound failure :=
  RandomLinker.certificate publication.client publication.implementations
    publication.configuration overheadBound publication.assumptions

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

/-- Typed publication for a callable procedure satisfying the restoring convention. -/
structure RestoringProcedurePublication (contract : ProcedureContract w)
    (bound : ProcedureBound contract) where
  certificate : RestoringProcedureCertificate contract bound
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

noncomputable def DerivedOperationLibraryPublication.summary
    {w : Nat} {library : PreprocessedWordOperationLibrary w}
    (publication : DerivedOperationLibraryPublication library) : String :=
  "Claim kind: certified derived Word-RAM operation library\n" ++
  "Library: " ++ toString publication.libraryName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Primitive core operations: sealed Word-RAM Profile instruction syntax\n" ++
  "Derived operations: " ++ reprStr library.derivedOperations ++ "\n" ++
  "Arbitrary host word callback: absent\n" ++
  "Initialization operation: one distinguished restoring procedure\n" ++
  "Initialization execution count: exactly one, proved from the dynamic call trace\n" ++
  "Preprocessing table base/words: " ++ toString library.tableRegion.base.toNat ++ " / " ++
    toString library.tableWords ++ "\n" ++
  "Table after initialization: read-only for every non-initializer procedure trace\n" ++
  "Width relation (descriptive metadata only): " ++ library.assumptions.widthRelation ++ "\n" ++
  "Maximum register/address: " ++ toString library.assumptions.maximumRegisterValue ++ " / " ++
    toString library.assumptions.maximumAddress ++ "\n" ++
  "Declared core space/preprocessing words: " ++ toString library.assumptions.spaceWords ++
    " / " ++ toString library.assumptions.polynomialIntegerWords ++ "\n" ++
  "Lowering: shared bodies; every initializer/operation instruction remains in the core trace\n" ++
  "Initialization theorem: " ++ toString publication.initializationTheorem ++ "\n" ++
  "Lowering theorem: " ++ toString publication.loweringTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

/-- Audit the proof-carrying asymptotic robustness layer separately from descriptive metadata. -/
def UniformDerivedOperationLibraryPublication.summary
    (publication : UniformDerivedOperationLibraryPublication family library) : String :=
  let robustness := publication.robustness
  "Claim kind: width-uniform certified derived Word-RAM operation library\n" ++
  "Library: " ++ toString publication.libraryName ++ "\n" ++
  "Uniformity: one finite operation signature and one sealed template per operation\n" ++
  "Width lower inequality: proved by " ++ toString publication.widthLowerTheorem ++ "\n" ++
  "Width upper logarithmic inequality: proved by " ++ toString publication.widthUpperTheorem ++
    " (constant " ++ toString robustness.widthUpperConstant ++ ")\n" ++
  "Preprocessing cost: proved linear by " ++ toString publication.preprocessingTheorem ++
    " (constant/offset " ++ toString robustness.preprocessingLinearConstant ++ "/" ++
    toString robustness.preprocessingLinearOffset ++ ")\n" ++
  "Table space: proved linear by " ++ toString publication.spaceTheorem ++
    " (constant/offset " ++ toString robustness.preprocessingSpaceConstant ++ "/" ++
    toString robustness.preprocessingSpaceOffset ++ ")\n" ++
  "Address-space fit: proof field addressSpaceFit\n" ++
  "Constant per-operation cost: " ++ toString publication.operationCostTheorem ++ "\n" ++
  "Instantiated code equals sealed template: " ++ toString publication.uniformityTheorem ++ "\n" ++
  "Arbitrary width-indexed program family: absent\n" ++
  "Warnings: " ++ stringList publication.warnings

/-- Randomized audits disclose the hidden lengthless source and both same-trace resources. -/
def HighProbabilityBoundedSuccessPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : HighProbabilityBoundedSuccessPublication problem stepBound drawBound failure) :
    String :=
  let program := publication.certificate.program
  "Claim kind: high-probability bounded-success fixed-width Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.highProbabilityBoundedSuccess.summary ++ "\n" ++
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
  "Measurability theorem: carried by the typed certificate\n" ++
  "Cost/output/draw source: same randomized HaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

def BoundedTimeMonteCarloPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloPublication problem stepBound drawBound failure) : String :=
  let program := publication.certificate.program
  "Claim kind: bounded-time Monte Carlo fixed-width Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Source: hidden iid fair bits\nSource visible length: none\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Program instruction/description size: " ++ toString program.length ++ " / " ++
    toString program.descriptionSize ++ " bits\n" ++
  "Step/draw bounds: " ++ toString publication.stepBoundName ++ " / " ++
    toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def hiddenFairBitHeader (w : Nat) (program : RandomBit.Program w) : String :=
  "Random source profile: hidden lengthless iid fair bits\n" ++
  "Source visible length: none\n" ++
  "Sample operation: sealed randBit; one draw is charged in the same trace\n" ++
  "Program instruction/description size: " ++ toString program.length ++ " / " ++
    toString program.descriptionSize ++ " bits\n"

def OneSidedBoundedTimeMonteCarloPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {specification : StructuredProblem.OneSidedDecisionSpec problem}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : OneSidedBoundedTimeMonteCarloPublication problem specification
      stepBound drawBound failure) : String :=
  "Claim kind: one-sided bounded-time Monte Carlo Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.oneSidedBoundedTimeMonteCarlo.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Decision specification: " ++ toString publication.specificationName ++ "\n" ++
  "Step/draw bounds: " ++ toString publication.stepBoundName ++ " / " ++
    toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def CoOneSidedBoundedTimeMonteCarloPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {specification : StructuredProblem.OneSidedDecisionSpec problem}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : CoOneSidedBoundedTimeMonteCarloPublication problem specification
      stepBound drawBound failure) : String :=
  "Claim kind: co-one-sided bounded-time Monte Carlo Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.coOneSidedBoundedTimeMonteCarlo.summary ++
    "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Decision specification: " ++ toString publication.specificationName ++ "\n" ++
  "Step/draw bounds: " ++ toString publication.stepBoundName ++ " / " ++
    toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def AlmostSureLasVegasPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    (publication : AlmostSureLasVegasPublication problem) : String :=
  "Claim kind: almost-sure Las Vegas Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.almostSureLasVegas.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Termination measurability theorem: " ++
    toString publication.terminationMeasurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def LasVegasExpectedTimePublication.summary
    {w : Nat} {problem : StructuredProblem w} {expectedStepBound : problem.Input → ENNReal}
    (publication : LasVegasExpectedTimePublication problem expectedStepBound) : String :=
  "Claim kind: finite-expected-time Las Vegas Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.expectedTimeLasVegas.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Expected-step bound: " ++ toString publication.expectedStepBoundName ++ "\n" ++
  "Termination/runtime measurability theorems: " ++
    toString publication.terminationMeasurabilityTheorem ++ " / " ++
    toString publication.runtimeMeasurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def LasVegasHighProbabilityTimePublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {timeout : problem.Input → Probability}
    (publication : LasVegasHighProbabilityTimePublication problem stepBound drawBound timeout) :
    String :=
  "Claim kind: high-probability-time Las Vegas Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.highProbabilityTimeLasVegas.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Step/draw bounds: " ++ toString publication.stepBoundName ++ " / " ++
    toString publication.drawBoundName ++ "\n" ++
  "Timeout probability: " ++ toString publication.timeoutName ++ " (typed ≤ 1)\n" ++
  "Termination/within-bound measurability theorems: " ++
    toString publication.terminationMeasurabilityTheorem ++ " / " ++
    toString publication.withinMeasurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def ExpectedApproximationPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {loss : problem.Input → problem.Output → ENNReal}
    {expectedLossBound : problem.Input → ENNReal}
    (publication : ExpectedApproximationPublication problem loss expectedLossBound) : String :=
  "Claim kind: expected-approximation Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.expectedApproximation.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Loss/bound declarations: " ++ toString publication.lossName ++ " / " ++
    toString publication.expectedLossBoundName ++ "\n" ++
  "Measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def SamplerPublication.summary
    {w : Nat} {problem : StructuredProblem w} [MeasurableSpace problem.Output]
    {target : problem.Input → Measure problem.Output}
    (publication : SamplerPublication problem target) : String :=
  "Claim kind: exact distributional Word-RAM sampler\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.exactSampler.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Target distribution: " ++ toString publication.targetName ++ "\n" ++
  "Output measurability theorem: " ++ toString publication.measurabilityTheorem ++ "\n" ++
  "Distribution theorem: " ++ toString publication.distributionTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

def EverySourceLasVegasPublication.summary
    {w : Nat} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat}
    (publication : EverySourceLasVegasPublication problem stepBound drawBound) : String :=
  "Claim kind: every-source bounded Las Vegas Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.everySourceLasVegas.summary ++ "\n" ++
  hiddenFairBitHeader w publication.certificate.program ++
  "Step/draw bounds: " ++ toString publication.stepBoundName ++ " / " ++
    toString publication.drawBoundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings

/-- Random-relative reports cannot be confused with a concrete randomized certificate. -/
def HighProbabilityBoundedSuccessRelativePublication.summary
    {w : Nat} {signature : DependencySignature w}
    {problem : StructuredProblem w} {stepBound drawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : HighProbabilityBoundedSuccessRelativePublication signature problem stepBound
      drawBound failure) : String :=
  "RELATIVE RANDOMIZED ALGORITHM CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL WORD-RAM ALGORITHM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Randomness: hidden lengthless iid fair-bit source\n" ++
  "Guarantee: high-probability bounded success; timeout/divergence count as failure\n" ++
  "Random-source cursor across calls: preserved and unobservable\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " unresolved\n" ++
  "Concrete discharge: automatic shared-body same-source linker after certified implementations\n" ++
  "Step bound: " ++ toString publication.stepBoundName ++ "\n" ++
  "Draw bound: " ++ toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

def BoundedTimeMonteCarloRelativePublication.summary
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloRelativePublication signature problem stepBound drawBound
      failure) : String :=
  "RELATIVE BOUNDED-TIME MONTE CARLO CERTIFICATE\n" ++
  "THIS IS NOT YET AN UNCONDITIONAL WORD-RAM ALGORITHM\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Source: hidden iid fair bits; visible length: none\n" ++
  "Dependencies unresolved: " ++ toString (Fintype.card signature.Op) ++ "\n" ++
  "Every-source termination is part of the relative certificate\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem

/-- Linked randomized audits expose the generated finite syntax and derived call overhead. -/
noncomputable def HighProbabilityBoundedSuccessLinkedPublication.summary
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : HighProbabilityBoundedSuccessLinkedPublication signature problem stepBound
      drawBound overheadBound failure) : String :=
  let certificate := publication.certificate
  "Claim kind: concrete linked high-probability bounded-success Word-RAM algorithm\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.highProbabilityBoundedSuccess.summary ++ "\n" ++
  "Linked status: fully resolved, unconditional\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Randomness: hidden lengthless iid fair-bit source\n" ++
  "Random-source length observable: no\n" ++
  "Random cursor across deterministic calls: exactly preserved\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " resolved\n" ++
  "Body sharing: one relocated deterministic body per operation\n" ++
  "Call overhead: derived from emitted setup/dispatcher/cleanup syntax\n" ++
  "Program instruction count: " ++ toString certificate.program.length ++ "\n" ++
  "Program description size: " ++ toString certificate.program.descriptionSize ++ " bits\n" ++
  "Step bound: " ++ toString publication.stepBoundName ++ " plus " ++
    toString publication.overheadBoundName ++ "\n" ++
  "Random-draw bound: " ++ toString publication.drawBoundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (typed ≤ 1)\n" ++
  "Cost/output/draw source: one concrete randomized HaltingTrace\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

noncomputable def BoundedTimeMonteCarloLinkedPublication.summary
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloLinkedPublication signature problem stepBound drawBound
      overheadBound failure) : String :=
  let certificate := publication.certificate
  "Claim kind: fully linked bounded-time Monte Carlo Word-RAM algorithm\n" ++
  "Linked status: fully resolved, unconditional\n" ++
  Algolean.Algorithms.Audit.RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Source: hidden iid fair bits; same source/cursor preserved across calls\n" ++
  "Dependency operations: " ++ toString (Fintype.card signature.Op) ++ " resolved\n" ++
  "Full callee execution: yes; one shared body per operation\n" ++
  "Link overhead: derived from emitted setup/dispatcher/cleanup syntax\n" ++
  "Program instruction/description size: " ++ toString certificate.program.length ++ " / " ++
    toString certificate.program.descriptionSize ++ " bits\n" ++
  "Step bound: " ++ toString publication.stepBoundName ++ " plus " ++
    toString publication.overheadBoundName ++ "\n" ++
  "Draw bound unchanged: " ++ toString publication.drawBoundName ++ "\n" ++
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
  "Procedure bound: complete callee-body cost\n" ++
  "Linker overhead: derived from emitted setup/dispatcher/cleanup syntax\n" ++
  "Frame safety: certified outside the actual input/output and owned scratch/registers\n" ++
  "Owned scratch after return: permitted to change\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Restoring-procedure audits disclose the stronger exact canonical effect. -/
def RestoringProcedurePublication.summary {w : Nat} {contract : ProcedureContract w}
    {bound : ProcedureBound contract}
    (publication : RestoringProcedurePublication contract bound) : String :=
  let certificate := publication.certificate
  "Claim kind: restoring callable fixed-width Word-RAM procedure\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Contract: " ++ toString publication.contractName ++ "\n" ++
  "Word width: " ++ toString w ++ "\n" ++
  "Input layout: " ++ contract.inputLayout.syntaxName ++ "\n" ++
  "Output layout: " ++ contract.outputLayout.syntaxName ++ "\n" ++
  "Entry point: " ++ toString certificate.module.entry ++ "\n" ++
  "Instruction count: " ++ toString certificate.module.code.length ++ "\n" ++
  "Description size: " ++ toString (WordRAM.descriptionSize certificate.module.code) ++
    " bits\n" ++
  "ABI realizability: carried by callingRealizes\n" ++
  "Actual-output frame: carried by the base procedure certificate\n" ++
  "Final effect: only the canonical output write remains\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

end Algolean.Algorithms.WordRAM.Audit

namespace Algolean.Algorithms.Audit

open MeasureTheory

instance {problem : WordRAM.StructuredProblem w} {bound : problem.Input → ℕ} :
    AuditablePublication (WordRAM.Audit.FixedWidthPublication problem bound) :=
  ⟨WordRAM.Audit.FixedWidthPublication.summary⟩

instance {family : WordRAM.UniformStructuredProblem} {bound : WordRAM.UniformBound family} :
    AuditablePublication (WordRAM.Audit.UniformPublication family bound) :=
  ⟨WordRAM.Audit.UniformPublication.summary⟩

noncomputable instance {library : WordRAM.PreprocessedWordOperationLibrary w} :
    AuditablePublication (WordRAM.Audit.DerivedOperationLibraryPublication library) :=
  ⟨WordRAM.Audit.DerivedOperationLibraryPublication.summary⟩

instance {family : WordRAM.UniformStructuredProblem}
    {library : WordRAM.UniformPreprocessedWordOperationLibrary} : AuditablePublication
    (WordRAM.Audit.UniformDerivedOperationLibraryPublication family library) :=
  ⟨WordRAM.Audit.UniformDerivedOperationLibraryPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.HighProbabilityBoundedSuccessPublication problem stepBound drawBound
        failure) :=
  ⟨WordRAM.Audit.HighProbabilityBoundedSuccessPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.BoundedTimeMonteCarloPublication problem stepBound drawBound failure) :=
  ⟨WordRAM.Audit.BoundedTimeMonteCarloPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {specification : WordRAM.StructuredProblem.OneSidedDecisionSpec problem}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.OneSidedBoundedTimeMonteCarloPublication problem specification
        stepBound drawBound failure) :=
  ⟨WordRAM.Audit.OneSidedBoundedTimeMonteCarloPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {specification : WordRAM.StructuredProblem.OneSidedDecisionSpec problem}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.CoOneSidedBoundedTimeMonteCarloPublication problem specification
        stepBound drawBound failure) :=
  ⟨WordRAM.Audit.CoOneSidedBoundedTimeMonteCarloPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w} :
    AuditablePublication (WordRAM.Audit.AlmostSureLasVegasPublication problem) :=
  ⟨WordRAM.Audit.AlmostSureLasVegasPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {expectedStepBound : problem.Input → ENNReal} :
    AuditablePublication
      (WordRAM.Audit.LasVegasExpectedTimePublication problem expectedStepBound) :=
  ⟨WordRAM.Audit.LasVegasExpectedTimePublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {timeout : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.LasVegasHighProbabilityTimePublication problem stepBound drawBound timeout) :=
  ⟨WordRAM.Audit.LasVegasHighProbabilityTimePublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {loss : problem.Input → problem.Output → ENNReal}
    {expectedLossBound : problem.Input → ENNReal} :
    AuditablePublication
      (WordRAM.Audit.ExpectedApproximationPublication problem loss expectedLossBound) :=
  ⟨WordRAM.Audit.ExpectedApproximationPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w} [MeasurableSpace problem.Output]
    {target : problem.Input → Measure problem.Output} :
    AuditablePublication (WordRAM.Audit.SamplerPublication problem target) :=
  ⟨WordRAM.Audit.SamplerPublication.summary⟩

instance {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} :
    AuditablePublication
      (WordRAM.Audit.EverySourceLasVegasPublication problem stepBound drawBound) :=
  ⟨WordRAM.Audit.EverySourceLasVegasPublication.summary⟩

instance {signature : WordRAM.DependencySignature w} {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.HighProbabilityBoundedSuccessRelativePublication signature problem
        stepBound drawBound failure) :=
  ⟨WordRAM.Audit.HighProbabilityBoundedSuccessRelativePublication.summary⟩

instance {signature : WordRAM.DependencySignature w} {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound : problem.Input → Nat} {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.BoundedTimeMonteCarloRelativePublication signature problem stepBound drawBound
        failure) :=
  ⟨WordRAM.Audit.BoundedTimeMonteCarloRelativePublication.summary⟩

noncomputable instance {signature : WordRAM.DependencySignature w}
    {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.HighProbabilityBoundedSuccessLinkedPublication signature problem stepBound
        drawBound overheadBound failure) :=
  ⟨WordRAM.Audit.HighProbabilityBoundedSuccessLinkedPublication.summary⟩

noncomputable instance {signature : WordRAM.DependencySignature w}
    {problem : WordRAM.StructuredProblem w}
    {stepBound drawBound overheadBound : problem.Input → Nat}
    {failure : problem.Input → WordRAM.Probability} :
    AuditablePublication
      (WordRAM.Audit.BoundedTimeMonteCarloLinkedPublication signature problem stepBound drawBound
        overheadBound failure) :=
  ⟨WordRAM.Audit.BoundedTimeMonteCarloLinkedPublication.summary⟩

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

instance {contract : WordRAM.ProcedureContract w} {bound : WordRAM.ProcedureBound contract} :
    AuditablePublication (WordRAM.Audit.RestoringProcedurePublication contract bound) :=
  ⟨WordRAM.Audit.RestoringProcedurePublication.summary⟩

end Algolean.Algorithms.Audit

/-- Print the class-selected closed Word-RAM layout for a type. -/
@[nolint topNamespace]
syntax (name := wordRAMLayoutAuditCmd) "#layout_audit" "WordRAM" term:max term:max : command

macro_rules
  | `(#layout_audit WordRAM $width:term $ty:term) =>
      `(#eval Algolean.Algorithms.WordRAM.Audit.LayoutAudit.summary
          (Algolean.Algorithms.WordRAM.Audit.canonicalLayoutAudit $width $ty))
