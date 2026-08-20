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
  /-- Compiler correctness/refinement theorem. -/
  compilerTheorem : Option Lean.Name := none
  /-- Closed oracle interfaces used by the profile. -/
  oracleInterfaces : List Lean.Name := []
  /-- Random-tape or sampling model declaration. -/
  randomnessModel : Option Lean.Name := none
  /-- Concrete correctness/termination/cost theorem. -/
  correctnessTheorem : Lean.Name
  /-- Source of the reported resource bound. -/
  costSource : CostSource
  /-- Named primitive extensions in the profile. -/
  extensions : List Lean.Name := []
  /-- Prominent semantic caveats printed with the manifest. -/
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

/-- Stable short label for the origin of a reported cost. -/
def CostSource.label : CostSource → String
  | .sameTrace => "same halting trace"
  | .queryModel => "query model"
  | .weightedMacro profile => "weighted macro profile " ++ toString profile
  | .refinedBy theoremName => "refined by " ++ toString theoremName

/-- Compact printable audit summary; theorem proof fields remain the source of truth. -/
def AlgorithmAudit.summary (audit : AlgorithmAudit) : String :=
  "Claim kind: " ++ audit.claimKind.label ++ "\n" ++
  "Machine: " ++ toString audit.machineName ++ "\n" ++
  "Program: " ++ toString audit.programName ++ "\n" ++
  "Problem: " ++ toString audit.problemName ++ "\n" ++
  "Cost source: " ++ audit.costSource.label ++ "\n" ++
  "Correctness theorem: " ++ toString audit.correctnessTheorem ++ "\n" ++
  "Warnings: " ++ String.intercalate "; " audit.warnings

/-- Print a compact audit manifest.  The argument is an `AlgorithmAudit` value. -/
syntax (name := algorithmAuditCmd) "#algorithm_audit " term : command

macro_rules
  | `(#algorithm_audit $audit) =>
      `(#eval Algolean.Algorithms.Audit.AlgorithmAudit.summary $audit)

end Algolean.Algorithms.Audit
