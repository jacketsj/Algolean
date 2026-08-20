/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.MachineProblem
public import Algolean.Complexity.RAMProblem

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
  | totalTapeLasVegasAlgorithm
deriving DecidableEq, Repr

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
  | .totalTapeLasVegasAlgorithm => "total-tape Las Vegas algorithm"

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
