/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem
public import Algolean.Complexity.OracleMachineProblem
public import Algolean.Complexity.RAMProblem
public import Algolean.Complexity.RandomizedMachineProblem

/-!
# Algorithm audit manifests

Audit manifests are navigational metadata, not proof rules.  Correctness remains in the concrete
kernel-checked theorem named by `correctnessTheorem`.  The manifest makes claim kind, machine,
layout, uniformity, code-size, oracle, and randomness choices visible in one printable value.
-/

@[expose] public section

namespace Algolean.Algorithms.Audit

/-- Claim strengths that must not be conflated in theorem names or reports. -/
inductive ClaimKind where
  | queryAlgorithm
  | fixedMachineAlgorithm
  | oracleMachineAlgorithm
  | weightedMacroAlgorithm
  | nonuniformFamily
  | uniformlyGeneratedFamily
  | compiledAlgorithm
  | monteCarloAlgorithm
  | highProbabilityBoundedSuccessAlgorithm
  | boundedTimeMonteCarloAlgorithm
  | oneSidedMonteCarloAlgorithm
  | coOneSidedMonteCarloAlgorithm
  | expectedTimeLasVegasAlgorithm
  | highProbabilityTimeLasVegasAlgorithm
  | almostSureLasVegasAlgorithm
  | expectedApproximationAlgorithm
  | samplerAlgorithm
  | totalTapeLasVegasAlgorithm
  | everySourceLasVegasAlgorithm
deriving DecidableEq, Repr

/-- Stable semantic taxonomy printed by randomized publication artifacts. -/
inductive RandomGuaranteeKind where
  | highProbabilityBoundedSuccess
  | boundedTimeMonteCarlo
  | oneSidedBoundedTimeMonteCarlo
  | coOneSidedBoundedTimeMonteCarlo
  | everySourceLasVegas
  | expectedTimeLasVegas
  | highProbabilityTimeLasVegas
  | zeroErrorHighProbabilityBoundedTermination
  | almostSureLasVegas
  | expectedApproximation
  | exactSampler
  | approximateSampler
deriving DecidableEq, Repr

/-- Complete model-independent disclosure of one randomized guarantee category. -/
structure RandomGuaranteeAudit where
  kind : RandomGuaranteeKind
  runtimeGuarantee : String
  correctnessGuarantee : String
  timeoutIsFailure : Bool
  divergenceIsFailure : Bool
  drawBound : String
  outputClaim : String

namespace RandomGuaranteeAudit

def highProbabilityBoundedSuccess : RandomGuaranteeAudit where
  kind := .highProbabilityBoundedSuccess
  runtimeGuarantee := "bounded only on the measured success event"
  correctnessGuarantee := "two-sided bounded failure"
  timeoutIsFailure := true
  divergenceIsFailure := true
  drawBound := "worst-case only on the success event"
  outputClaim := "relational"

def boundedTimeMonteCarlo : RandomGuaranteeAudit where
  kind := .boundedTimeMonteCarlo
  runtimeGuarantee := "every source terminates within the stated bound"
  correctnessGuarantee := "two-sided bounded error"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "worst-case every source"
  outputClaim := "relational"

def oneSidedBoundedTimeMonteCarlo : RandomGuaranteeAudit where
  kind := .oneSidedBoundedTimeMonteCarlo
  runtimeGuarantee := "every source terminates within the stated bound"
  correctnessGuarantee := "one-sided decision error"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "worst-case every source"
  outputClaim := "decision acceptance event"

def coOneSidedBoundedTimeMonteCarlo : RandomGuaranteeAudit where
  kind := .coOneSidedBoundedTimeMonteCarlo
  runtimeGuarantee := "every source terminates within the stated bound"
  correctnessGuarantee := "coRP-oriented one-sided decision error"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "worst-case every source"
  outputClaim := "decision rejection event"

def everySourceLasVegas : RandomGuaranteeAudit where
  kind := .everySourceLasVegas
  runtimeGuarantee := "every source terminates within the stated bound"
  correctnessGuarantee := "zero error on every source"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "worst-case every source"
  outputClaim := "relational"

def expectedTimeLasVegas : RandomGuaranteeAudit where
  kind := .expectedTimeLasVegas
  runtimeGuarantee := "almost-sure termination with finite expected runtime"
  correctnessGuarantee := "zero error on every halting run"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "none unless stated separately"
  outputClaim := "relational"

def highProbabilityTimeLasVegas : RandomGuaranteeAudit where
  kind := .highProbabilityTimeLasVegas
  runtimeGuarantee := "the stated time/draw bound holds with high probability"
  correctnessGuarantee := "zero error on every halting run"
  timeoutIsFailure := true
  divergenceIsFailure := true
  drawBound := "high probability"
  outputClaim := "relational"

/-- Zero-error on halting runs, but with no almost-sure termination claim. -/
def zeroErrorHighProbabilityBoundedTermination : RandomGuaranteeAudit where
  kind := .zeroErrorHighProbabilityBoundedTermination
  runtimeGuarantee :=
    "bounded termination with high probability; positive-probability divergence is permitted"
  correctnessGuarantee := "zero error on every halting run"
  timeoutIsFailure := true
  divergenceIsFailure := true
  drawBound := "high probability"
  outputClaim := "relational"

def almostSureLasVegas : RandomGuaranteeAudit where
  kind := .almostSureLasVegas
  runtimeGuarantee := "almost-sure termination; no expectation bound implied"
  correctnessGuarantee := "zero error on every halting run"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "none"
  outputClaim := "relational"

def expectedApproximation : RandomGuaranteeAudit where
  kind := .expectedApproximation
  runtimeGuarantee := "every source terminates (as witnessed by the output realization)"
  correctnessGuarantee := "expected measurable loss bound"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "none unless stated separately"
  outputClaim := "expected quality"

def exactSampler : RandomGuaranteeAudit where
  kind := .exactSampler
  runtimeGuarantee := "every source terminates (as witnessed by the sampled output)"
  correctnessGuarantee := "exact pushforward distribution"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "none unless stated separately"
  outputClaim := "distributional"

def approximateSampler : RandomGuaranteeAudit where
  kind := .approximateSampler
  runtimeGuarantee := "every source terminates (as witnessed by the sampled output)"
  correctnessGuarantee := "explicit distance to a target measure is at most an explicit error"
  timeoutIsFailure := false
  divergenceIsFailure := false
  drawBound := "none unless stated separately"
  outputClaim := "approximate distributional"

def summary (audit : RandomGuaranteeAudit) : String :=
  "Guarantee category: " ++ reprStr audit.kind ++ "\n" ++
  "Runtime guarantee: " ++ audit.runtimeGuarantee ++ "\n" ++
  "Correctness guarantee: " ++ audit.correctnessGuarantee ++ "\n" ++
  "Failure event includes timeout: " ++ toString audit.timeoutIsFailure ++ "\n" ++
  "Failure event includes divergence: " ++ toString audit.divergenceIsFailure ++ "\n" ++
  "Draw bound: " ++ audit.drawBound ++ "\n" ++
  "Output claim: " ++ audit.outputClaim

end RandomGuaranteeAudit

/-- Whether reported execution costs count target steps or named weighted transitions. -/
inductive CostSource where
  | sameTrace
  | queryModel
  | weightedMacro (profile : Lean.Name)
  | refinedBy (theoremName : Lean.Name)
deriving DecidableEq, Repr

/-- Human- and machine-readable metadata attached to a published algorithm theorem. -/
structure AlgorithmAudit where
  /-- Strength/category of the public claim. -/
  claimKind : ClaimKind
  /-- Fixed machine-profile declaration. -/
  machineName : Lean.Name
  /-- Concrete program or family declaration. -/
  programName : Lean.Name
  /-- Structured problem declaration. -/
  problemName : Lean.Name
  /-- Canonical input-layout declaration, when applicable. -/
  inputLayout : Option Lean.Name := none
  /-- Canonical output-layout declaration, when applicable. -/
  outputLayout : Option Lean.Name := none
  /-- Theorem relating footprint to a conventional size parameter. -/
  sizeTheorem : Option Lean.Name := none
  /-- Emitted-code-size theorem for families or compilation. -/
  codeSizeTheorem : Option Lean.Name := none
  /-- Full serialized-description-size theorem for program-family claims. -/
  descriptionSizeTheorem : Option Lean.Name := none
  /-- Compiler correctness/refinement theorem. -/
  compilerTheorem : Option Lean.Name := none
  /-- Closed oracle interfaces used by the profile. -/
  oracleInterfaces : List Lean.Name := []
  /-- Random-tape or sampling model declaration. -/
  randomnessModel : Option Lean.Name := none
  /-- Sealed generator-machine model, when an absolute generated-family claim is made. -/
  generatorModel : Option Lean.Name := none
  /-- Concrete fixed generator program. -/
  generatorProgram : Option Lean.Name := none
  /-- Same-trace generation-cost theorem. -/
  generationTheorem : Option Lean.Name := none
  /-- Oracle non-vacuity theorem or explicit assumption. -/
  oracleNonvacuity : Option Lean.Name := none
  /-- Concrete correctness/termination/cost theorem. -/
  correctnessTheorem : Lean.Name
  /-- Source of the reported resource bound. -/
  costSource : CostSource
  /-- Named primitive extensions in the profile. -/
  extensions : List Lean.Name := []
  /-- Important arithmetic, memory, size, literal, and halt conventions. -/
  machineConventions : List String := []
  /-- Prominent semantic caveats printed with the manifest. -/
  warnings : List String := []

/--
Typed publication artifact for the strongest deterministic claim.  Unlike `AlgorithmAudit`, this
contains the actual certificate, so its program, layouts, and sizes cannot name unrelated values.
Declaration names remain navigation metadata for the human-readable mathematical specification.
-/
structure FixedAlgorithmPublication (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- Actual kernel-checked program/correctness/cost certificate. -/
  certificate : MachineProblem.FixedAlgorithmCertificate problem bound
  /-- Name of this publication value. -/
  certificateName : Lean.Name
  /-- Name of the mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Name of the resource-bound declaration. -/
  boundName : Lean.Name
  /-- Name of a theorem exposing or constructing the certificate. -/
  correctnessTheorem : Lean.Name
  /-- Optional footprint-to-conventional-size theorem. -/
  sizeTheorem : Option Lean.Name := none
  /-- Explicit caveats beyond the fixed profile conventions. -/
  warnings : List String := []

/-- Typed publication artifact for the ordinary unbounded-integer RAM. -/
structure IntegerRAMPublication (problem : IntegerRAM.Problem) (bound : ℕ → ℕ) where
  /-- Actual kernel-checked integer-RAM certificate. -/
  certificate : IntegerRAM.FixedAlgorithmCertificate problem bound
  /-- Name of this publication value. -/
  certificateName : Lean.Name
  /-- Name of the mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Name of the resource bound. -/
  boundName : Lean.Name
  /-- Name of the theorem exposing the certificate. -/
  correctnessTheorem : Lean.Name
  /-- Explicit semantic caveats. -/
  warnings : List String := []

/-- Typed publication artifact for one explicitly fixed-width word RAM. -/
structure WordRAMPublication (problem : WordRAM.Problem width) (bound : ℕ → ℕ) where
  /-- Actual kernel-checked fixed-width word-RAM certificate. -/
  certificate : WordRAM.FixedAlgorithmCertificate problem bound
  /-- Name of this publication value. -/
  certificateName : Lean.Name
  /-- Name of the mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Name of the resource bound. -/
  boundName : Lean.Name
  /-- Name of the theorem exposing the certificate. -/
  correctnessTheorem : Lean.Name
  /-- Explicit semantic caveats. -/
  warnings : List String := []

/-- Typed publication artifact for a compiled first-order CFG algorithm. -/
structure CompiledAlgorithmPublication (problem : MachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- Actual compiled-algorithm certificate. -/
  certificate : MachineProblem.CompiledAlgorithmCertificate problem bound
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Resource-bound declaration. -/
  boundName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Typed publication artifact for an absolute same-trace uniformly generated family. -/
structure UniformlyGeneratedFamilyPublication
    (problem : MachineProblem)
    (generationBound : ℕ → StructuredRealRAM.Cost)
    (instructionBound descriptionBound : ℕ → ℕ)
    (timeBound : ℕ → StructuredRealRAM.Cost) where
  /-- Actual sealed-generator certificate. -/
  certificate : MachineProblem.UniformlyGeneratedFamilyCertificate problem generationBound
    instructionBound descriptionBound timeBound
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Generator resource-bound declaration. -/
  generationBoundName : Lean.Name
  /-- Target instruction-count bound. -/
  instructionBoundName : Lean.Name
  /-- Target full-description-size bound. -/
  descriptionBoundName : Lean.Name
  /-- Generated target execution bound. -/
  timeBoundName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Typed publication artifact for hidden-bit every-source bounded-time Monte Carlo. -/
structure BoundedTimeMonteCarloAlgorithmPublication
    (problem : BitRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.RandomBit.Cost)
    (failure : problem.Input → Probability) where
  /-- Actual hidden-source every-source bounded-time certificate. -/
  certificate : BitRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
    problem bound failure
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Resource-bound declaration. -/
  boundName : Lean.Name
  /-- Failure-probability declaration. -/
  failureName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Typed publication artifact for exact-uniform-real every-source bounded-time Monte Carlo. -/
structure UniformRealBoundedTimeMonteCarloAlgorithmPublication
    (problem : UniformRealRandomizedMachineProblem)
    (bound : ℕ → StructuredRealRAM.UniformReal.Cost)
    (failure : problem.Input → Probability) where
  /-- Actual exact-uniform-real every-source bounded-time certificate. -/
  certificate :
    UniformRealRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
      problem bound failure
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Resource-bound declaration. -/
  boundName : Lean.Name
  /-- Failure-probability declaration. -/
  failureName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Compatibility name; prefer the guarantee-specific publication name. -/
abbrev MonteCarloAlgorithmPublication := BoundedTimeMonteCarloAlgorithmPublication

/-- Compatibility name; prefer the guarantee-specific publication name. -/
abbrev UniformRealMonteCarloAlgorithmPublication :=
  UniformRealBoundedTimeMonteCarloAlgorithmPublication

/-- Typed publication artifact for every-source-correct Las Vegas step complexity. -/
structure EverySourceLasVegasAlgorithmPublication
    (problem : BitRandomizedMachineProblem) (bound : ℕ → ENNReal) where
  /-- Actual every-source Las Vegas certificate. -/
  certificate :
    BitRandomizedMachineProblem.EverySourceLasVegasStepAlgorithmCertificate problem bound
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Expected-step-bound declaration. -/
  boundName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Typed publication artifact for a non-vacuous every-responder oracle-machine claim. -/
structure OracleAlgorithmPublication (problem : OracleMachineProblem)
    (bound : ℕ → StructuredRealRAM.Cost) where
  /-- Actual non-vacuous robust oracle certificate. -/
  certificate : OracleMachineProblem.OracleAlgorithmCertificate problem bound
  /-- Declaration name of this publication. -/
  certificateName : Lean.Name
  /-- Mathematical problem declaration. -/
  problemName : Lean.Name
  /-- Fixed typed oracle-interface declaration. -/
  interfaceName : Lean.Name
  /-- Interface non-vacuity theorem. -/
  nonvacuityTheorem : Lean.Name
  /-- Same-trace resource-bound declaration. -/
  boundName : Lean.Name
  /-- Certificate construction or exposure theorem. -/
  correctnessTheorem : Lean.Name
  /-- Explicit caveats. -/
  warnings : List String := []

/-- Standard audit metadata for the sealed structured exact-real profile. -/
def structuredRealRAMMachineName : Lean.Name :=
  `Algolean.Algorithms.StructuredRealRAM.coreProfile

/-- Standard audit metadata for the sealed ordinary integer-RAM profile. -/
def integerRAMMachineName : Lean.Name :=
  `Algolean.Algorithms.IntegerRAM.costedSemantics

/-- Standard audit metadata for the sealed fixed-width word-RAM profile. -/
def wordRAMMachineName : Lean.Name :=
  `Algolean.Algorithms.WordRAM.costedSemantics

/-- Query reports always disclose that pure Lean work is outside the charged query cost. -/
def queryWarning : String :=
  "Pure Lean computation and data manipulation between emitted queries are uncharged."

/-- Nonuniform reports always disclose that the witness is a family rather than one program. -/
def nonuniformWarning : String :=
  "The witness is a size-indexed program family, not one fixed machine program."

/-- Stable short label for a claim kind. -/
def ClaimKind.label : ClaimKind → String
  | .queryAlgorithm => "query algorithm"
  | .fixedMachineAlgorithm => "fixed machine algorithm"
  | .oracleMachineAlgorithm => "oracle machine algorithm"
  | .weightedMacroAlgorithm => "weighted macro algorithm"
  | .nonuniformFamily => "nonuniform family"
  | .uniformlyGeneratedFamily => "uniformly generated family"
  | .compiledAlgorithm => "compiled algorithm"
  | .monteCarloAlgorithm => "Monte Carlo algorithm"
  | .highProbabilityBoundedSuccessAlgorithm => "high-probability bounded-success algorithm"
  | .boundedTimeMonteCarloAlgorithm => "bounded-time Monte Carlo algorithm"
  | .oneSidedMonteCarloAlgorithm => "one-sided bounded-time Monte Carlo algorithm"
  | .coOneSidedMonteCarloAlgorithm => "co-one-sided bounded-time Monte Carlo algorithm"
  | .expectedTimeLasVegasAlgorithm => "expected-time Las Vegas algorithm"
  | .highProbabilityTimeLasVegasAlgorithm => "high-probability-time Las Vegas algorithm"
  | .almostSureLasVegasAlgorithm => "almost-sure Las Vegas algorithm"
  | .expectedApproximationAlgorithm => "expected-approximation algorithm"
  | .samplerAlgorithm => "sampler algorithm"
  | .totalTapeLasVegasAlgorithm => "total-tape Las Vegas algorithm"
  | .everySourceLasVegasAlgorithm => "every-source Las Vegas algorithm"

/-- Stable short label for the origin of a reported cost. -/
def CostSource.label : CostSource → String
  | .sameTrace => "same halting trace"
  | .queryModel => "query model"
  | .weightedMacro profile => "weighted macro profile " ++ toString profile
  | .refinedBy theoremName => "refined by " ++ toString theoremName

/-- Print an optional declaration name without silently dropping the field. -/
def optionalName : Option Lean.Name → String
  | none => "none"
  | some name => toString name

/-- Print a declaration-name list without silently dropping the field. -/
def nameList (names : List Lean.Name) : String :=
  if names.isEmpty then "none" else String.intercalate ", " (names.map toString)

/-- Print a string list without silently dropping an empty field. -/
def stringList (values : List String) : String :=
  if values.isEmpty then "none" else String.intercalate "; " values

/-- Full printable audit summary; theorem proof fields remain the source of truth. -/
def AlgorithmAudit.summary (audit : AlgorithmAudit) : String :=
  "Claim kind: " ++ audit.claimKind.label ++ "\n" ++
  "Machine: " ++ toString audit.machineName ++ "\n" ++
  "Program: " ++ toString audit.programName ++ "\n" ++
  "Problem: " ++ toString audit.problemName ++ "\n" ++
  "Input layout: " ++ optionalName audit.inputLayout ++ "\n" ++
  "Output layout: " ++ optionalName audit.outputLayout ++ "\n" ++
  "Input-size theorem: " ++ optionalName audit.sizeTheorem ++ "\n" ++
  "Instruction/code-size theorem: " ++ optionalName audit.codeSizeTheorem ++ "\n" ++
  "Description-size theorem: " ++ optionalName audit.descriptionSizeTheorem ++ "\n" ++
  "Compiler theorem: " ++ optionalName audit.compilerTheorem ++ "\n" ++
  "Oracle interfaces: " ++ nameList audit.oracleInterfaces ++ "\n" ++
  "Oracle non-vacuity: " ++ optionalName audit.oracleNonvacuity ++ "\n" ++
  "Randomness model: " ++ optionalName audit.randomnessModel ++ "\n" ++
  "Generator model: " ++ optionalName audit.generatorModel ++ "\n" ++
  "Generator program: " ++ optionalName audit.generatorProgram ++ "\n" ++
  "Generation theorem: " ++ optionalName audit.generationTheorem ++ "\n" ++
  "Extensions: " ++ nameList audit.extensions ++ "\n" ++
  "Machine conventions: " ++ stringList audit.machineConventions ++ "\n" ++
  "Cost source: " ++ audit.costSource.label ++ "\n" ++
  "Correctness theorem: " ++ toString audit.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList audit.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString audit.correctnessTheorem ++ "`"

/-- Complete report derived from an actual typed fixed-program certificate. -/
def FixedAlgorithmPublication.summary
    {problem : MachineProblem} {bound : ℕ → StructuredRealRAM.Cost}
    (publication : FixedAlgorithmPublication problem bound) : String :=
  let program := publication.certificate.program
  let region := problem.outputRegion
  "Claim kind: fixed machine algorithm\n" ++
  "Machine: " ++ StructuredRealRAM.coreProfile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++
    toString (StructuredRealRAM.Program.descriptionSize program) ++ " bits\n" ++
  "Input layout syntax: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout syntax: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Output region: real " ++ toString region.realBase ++ ", nat " ++
    toString region.natBase ++ "\n" ++
  "Input size: closed-layout represented cell count\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Cost coordinates: steps, real reads/writes/arithmetic/comparisons, " ++
    "Nat reads/writes/arithmetic/comparisons\n" ++
  "Cost source: same halting trace as output\n" ++
  "Randomness: none\nOracles: none\nExtensions: none\n" ++
  "Division by zero: totalized\nNatural subtraction: truncating\n" ++
  "Natural arithmetic: unbounded unit cost\nReal comparison: exact\n" ++
  "Real literals: rational only\nUnused memory/registers: zero\nHalt counted: yes\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Input-size theorem: " ++ optionalName publication.sizeTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual ordinary integer-RAM certificate. -/
def IntegerRAMPublication.summary {problem : IntegerRAM.Problem} {bound : ℕ → ℕ}
    (publication : IntegerRAMPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: fixed machine algorithm\n" ++
  "Machine: ordinary integer RAM\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++ toString (IntegerRAM.descriptionSize program) ++ " bits\n" ++
  "Data cells: unbounded signed integers\nAddresses: unbounded naturals\n" ++
  "Arithmetic and random access: unit cost\nNatural address subtraction: truncating\n" ++
  "Input: length header plus native cells; otherwise zero\nHalt counted: yes\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Cost source: same halting trace as output\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual fixed-width word-RAM certificate. -/
def WordRAMPublication.summary {width : ℕ} {problem : WordRAM.Problem width} {bound : ℕ → ℕ}
    (publication : WordRAMPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: fixed machine algorithm\n" ++
  "Machine: fixed-width word RAM\n" ++
  "Word width: " ++ toString width ++ " bits\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++ toString (WordRAM.descriptionSize program) ++ " bits\n" ++
  "Data and addresses: unsigned modular words\nArithmetic and random access: unit cost\n" ++
  "Input: length header plus native words with address-space-fit proof\nHalt counted: yes\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Cost source: same halting trace as output\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual compiled CFG certificate. -/
def CompiledAlgorithmPublication.summary
    {problem : MachineProblem} {bound : ℕ → StructuredRealRAM.Cost}
    (publication : CompiledAlgorithmPublication problem bound) : String :=
  let source := publication.certificate.source
  let target := StructuredRealRAM.CFG.compile source
  "Claim kind: compiled fixed machine algorithm\n" ++
  "Machine: " ++ StructuredRealRAM.coreProfile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Source: closed first-order labeled CFG\n" ++
  "Target instruction count: " ++ toString target.length ++ "\n" ++
  "Target description size: " ++
    toString (StructuredRealRAM.Program.descriptionSize target) ++ " bits\n" ++
  "Compilation: shared labels, numeric jumps, and backward edges\n" ++
  "Cost source: same target halting trace as output\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual sealed-generator family certificate. -/
def UniformlyGeneratedFamilyPublication.summary
    {problem : MachineProblem}
    {generationBound : ℕ → StructuredRealRAM.Cost}
    {instructionBound descriptionBound : ℕ → ℕ}
    {timeBound : ℕ → StructuredRealRAM.Cost}
    (publication : UniformlyGeneratedFamilyPublication problem generationBound instructionBound
      descriptionBound timeBound) : String :=
  let generator := publication.certificate.generator
  "Claim kind: uniformly generated family\n" ++
  "Generator machine: sealed structured exact-real RAM with unit-cost unbounded Nat bank\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Generator instruction count: " ++ toString generator.length ++ "\n" ++
  "Generator description size: " ++
    toString (StructuredRealRAM.Program.descriptionSize generator) ++ " bits\n" ++
  "Generator output: canonical binary target-program serialization in charged memory\n" ++
  "Generation bound: " ++ toString publication.generationBoundName ++ "\n" ++
  "Target instruction-count bound: " ++ toString publication.instructionBoundName ++ "\n" ++
  "Target description-size bound: " ++ toString publication.descriptionBoundName ++ "\n" ++
  "Target execution bound: " ++ toString publication.timeBoundName ++ "\n" ++
  "Generation cost source: same generator trace as materialized output\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual hidden-source Monte Carlo certificate. -/
def BoundedTimeMonteCarloAlgorithmPublication.summary
    {problem : BitRandomizedMachineProblem}
    {bound : ℕ → StructuredRealRAM.RandomBit.Cost}
    {failure : problem.Input → Probability}
    (publication : BoundedTimeMonteCarloAlgorithmPublication problem bound failure) : String :=
  let program := publication.certificate.program
  RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Machine: " ++ StructuredRealRAM.RandomBit.profile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++
    toString (StructuredRealRAM.RandomBit.Program.descriptionSize program) ++ " bits\n" ++
  "Input layout syntax: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout syntax: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Random source: hidden, lengthless iid fair-bit product source\n" ++
  "Random source cursor observable by program: no\n" ++
  "Random draw: one closed randBit instruction, charged in the output trace\n" ++
  "Success event measurability: carried by the typed certificate\n" ++
  "Termination/resource quantification: every source realization\n" ++
  "Bound (includes random draws): " ++ toString publication.boundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (certified at most one)\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Audit report that prominently distinguishes exact continuous samples from random bits. -/
def UniformRealBoundedTimeMonteCarloAlgorithmPublication.summary
    {problem : UniformRealRandomizedMachineProblem}
    {bound : ℕ → StructuredRealRAM.UniformReal.Cost}
    {failure : problem.Input → Probability}
    (publication : UniformRealBoundedTimeMonteCarloAlgorithmPublication problem bound failure) :
    String :=
  let program := publication.certificate.program
  "Source profile: hidden iid exact uniform reals\n" ++
  RandomGuaranteeAudit.boundedTimeMonteCarlo.summary ++ "\n" ++
  "Machine: " ++ StructuredRealRAM.UniformReal.profile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++
    toString (StructuredRealRAM.UniformReal.Program.descriptionSize program) ++ " bits\n" ++
  "Random source: hidden, lengthless product of exact uniform [0,1] samples\n" ++
  "Randomness strength: exact continuous primitive; stronger than random-bit RAM\n" ++
  "Random draw: one closed sampleUniform instruction charged in the output trace\n" ++
  "Success event measurability: carried by the typed certificate\n" ++
  "Bound (includes random draws): " ++ toString publication.boundName ++ "\n" ++
  "Failure probability: " ++ toString publication.failureName ++ " (certified at most one)\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report for the deliberately every-source Las Vegas predicate. -/
def EverySourceLasVegasAlgorithmPublication.summary
    {problem : BitRandomizedMachineProblem} {bound : ℕ → ENNReal}
    (publication : EverySourceLasVegasAlgorithmPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: every-source Las Vegas step algorithm\n" ++
  "Machine: " ++ StructuredRealRAM.RandomBit.profile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++
    toString (StructuredRealRAM.RandomBit.Program.descriptionSize program) ++ " bits\n" ++
  "Random source: hidden, lengthless iid fair-bit product source\n" ++
  "Termination/correctness: every source realization (stronger than almost sure)\n" ++
  "Expected resource: fixed fetched-instruction projection\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Complete report derived from an actual robust oracle certificate. -/
def OracleAlgorithmPublication.summary
    {problem : OracleMachineProblem} {bound : ℕ → StructuredRealRAM.Cost}
    (publication : OracleAlgorithmPublication problem bound) : String :=
  let program := publication.certificate.program
  "Claim kind: robust oracle machine algorithm\n" ++
  "Machine: " ++ StructuredRealRAM.OracleMachine.profile.name ++ "\n" ++
  "Certificate: " ++ toString publication.certificateName ++ "\n" ++
  "Problem: " ++ toString publication.problemName ++ "\n" ++
  "Oracle interface: " ++ toString publication.interfaceName ++ "\n" ++
  "Oracle quantification: every admissible responder; one responder fixed per run\n" ++
  "Oracle non-vacuity: proved by " ++ toString publication.nonvacuityTheorem ++ "\n" ++
  "Program instruction count: " ++ toString program.length ++ "\n" ++
  "Program description size: " ++
    toString (StructuredRealRAM.OracleMachine.Program.descriptionSize program) ++ " bits\n" ++
  "Input layout syntax: " ++ problem.inputLayout.syntaxName ++ "\n" ++
  "Output layout syntax: " ++ problem.outputLayout.syntaxName ++ "\n" ++
  "Query layout: " ++ problem.interface.queryLayout.syntaxName ++ "\n" ++
  "Answer layout: query-dependent closed Layout; selection is an external-contract assumption\n" ++
  "Query decoding: fixed closed-layout reader\n" ++
  "Responder semantics: one coherent answer function for the complete run\n" ++
  "Oracle computation cost: named interface assumption\n" ++
  "Transfer cost: derived from represented query read and represented answer write\n" ++
  "Cost: fetched call, represented query read, named oracle cost, represented answer write\n" ++
  "Cost/output source: one responder-indexed halting trace\n" ++
  "Bound: " ++ toString publication.boundName ++ "\n" ++
  "Correctness theorem: " ++ toString publication.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ stringList publication.warnings ++ "\n" ++
  "Axioms: run `#print axioms " ++ toString publication.correctnessTheorem ++ "`"

/-- Publication types accepted by the typed audit command. -/
class AuditablePublication (Publication : Type u) where
  /-- Render all auditable fields tied to the actual certificate. -/
  summary : Publication → String

instance {problem : MachineProblem} {bound : ℕ → StructuredRealRAM.Cost} :
    AuditablePublication (FixedAlgorithmPublication problem bound) :=
  ⟨FixedAlgorithmPublication.summary⟩

instance {problem : IntegerRAM.Problem} {bound : ℕ → ℕ} :
    AuditablePublication (IntegerRAMPublication problem bound) :=
  ⟨IntegerRAMPublication.summary⟩

instance {width : ℕ} {problem : WordRAM.Problem width} {bound : ℕ → ℕ} :
    AuditablePublication (WordRAMPublication problem bound) :=
  ⟨WordRAMPublication.summary⟩

instance {problem : MachineProblem} {bound : ℕ → StructuredRealRAM.Cost} :
    AuditablePublication (CompiledAlgorithmPublication problem bound) :=
  ⟨CompiledAlgorithmPublication.summary⟩

instance {problem : MachineProblem}
    {generationBound : ℕ → StructuredRealRAM.Cost}
    {instructionBound descriptionBound : ℕ → ℕ}
    {timeBound : ℕ → StructuredRealRAM.Cost} :
    AuditablePublication (UniformlyGeneratedFamilyPublication problem generationBound
      instructionBound descriptionBound timeBound) :=
  ⟨UniformlyGeneratedFamilyPublication.summary⟩

instance {problem : BitRandomizedMachineProblem}
    {bound : ℕ → StructuredRealRAM.RandomBit.Cost}
    {failure : problem.Input → Probability} :
    AuditablePublication
      (BoundedTimeMonteCarloAlgorithmPublication problem bound failure) :=
  ⟨BoundedTimeMonteCarloAlgorithmPublication.summary⟩

instance {problem : UniformRealRandomizedMachineProblem}
    {bound : ℕ → StructuredRealRAM.UniformReal.Cost}
    {failure : problem.Input → Probability} :
    AuditablePublication
      (UniformRealBoundedTimeMonteCarloAlgorithmPublication problem bound failure) :=
  ⟨UniformRealBoundedTimeMonteCarloAlgorithmPublication.summary⟩

instance {problem : BitRandomizedMachineProblem} {bound : ℕ → ENNReal} :
    AuditablePublication (EverySourceLasVegasAlgorithmPublication problem bound) :=
  ⟨EverySourceLasVegasAlgorithmPublication.summary⟩

instance {problem : OracleMachineProblem} {bound : ℕ → StructuredRealRAM.Cost} :
    AuditablePublication (OracleAlgorithmPublication problem bound) :=
  ⟨OracleAlgorithmPublication.summary⟩

/-- Produce the report for any supported typed publication. -/
def auditSummary (publication : Publication) [AuditablePublication Publication] : String :=
  AuditablePublication.summary publication

/-- Print a raw navigational manifest.  This command does not imply metadata consistency. -/
syntax (name := algorithmManifestCmd) "#algorithm_manifest " term : command

macro_rules
  | `(#algorithm_manifest $audit) =>
      `(#eval Algolean.Algorithms.Audit.AlgorithmAudit.summary $audit)

/-- Print an audit report from a typed fixed-algorithm publication certificate. -/
syntax (name := algorithmAuditCmd) "#algorithm_audit " term : command

macro_rules
  | `(#algorithm_audit $publication) =>
      `(#eval Algolean.Algorithms.Audit.auditSummary $publication)

end Algolean.Algorithms.Audit
