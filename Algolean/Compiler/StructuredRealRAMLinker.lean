/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.StructuredRealRAMRelative

/-!
# Shared-body linker for structured exact-real/natural procedures

Every implementation body is materialized once.  Calls write a return identifier and jump into
that body; a shared dispatcher restores the reserved register and resumes the caller.  No
procedure is represented by a one-step extension or oracle instruction.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.Linker

noncomputable section

/-- Linker-owned reserved natural register. -/
structure Configuration where
  returnRegister : Nat

/-- Canonical finite operation order. -/
def operations (signature : DependencySignature) : List signature.Op :=
  Finset.univ.toList

def codeBefore (environment : ImplementationEnvironment signature) :
    List signature.Op → signature.Op → Nat
  | [], _ => 0
  | current :: rest, op =>
      if current = op then 0
      else (environment.implementation current).module.code.length +
        codeBefore environment rest op

def implementationCodeSize (environment : ImplementationEnvironment signature) : Nat :=
  ((operations signature).map fun op ↦
    (environment.implementation op).module.code.length).sum

def operationBase (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (op : signature.Op) : Nat :=
  client.length + codeBefore environment (operations signature) op

def dispatcherBase (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) : Nat :=
  client.length + implementationCodeSize environment

/-- Relocate all successors; callee halt becomes an ordinary jump to the dispatcher. -/
def relocateInstruction (base dispatcher : Nat) : Instruction → Instruction
  | .rset source destination next => .rset source destination (base + next)
  | .radd left right destination next => .radd left right destination (base + next)
  | .rsub left right destination next => .rsub left right destination (base + next)
  | .rmul left right destination next => .rmul left right destination (base + next)
  | .rdiv left right destination next => .rdiv left right destination (base + next)
  | .rneg source destination next => .rneg source destination (base + next)
  | .nset source destination next => .nset source destination (base + next)
  | .nadd left right destination next => .nadd left right destination (base + next)
  | .nsub left right destination next => .nsub left right destination (base + next)
  | .nmul left right destination next => .nmul left right destination (base + next)
  | .nload address destination next => .nload address destination (base + next)
  | .nstore source address next => .nstore source address (base + next)
  | .rcompare left right less equal greater =>
      .rcompare left right (base + less) (base + equal) (base + greater)
  | .ncompare left right less equal greater =>
      .ncompare left right (base + less) (base + equal) (base + greater)
  | .jump target => .jump (base + target)
  | .halt _ => .jump dispatcher

/-- One operation's one shared relocated implementation body. -/
def implementationBody (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (op : signature.Op) : Program :=
  let base := operationBase client environment op
  let dispatcher := dispatcherBase client environment
  (environment.implementation op).module.code.map (relocateInstruction base dispatcher)

/-- Core client instructions retain their pc; calls jump to the unique shared body. -/
def clientInstruction (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) : OpenInstruction signature → Instruction
  | .core instruction => instruction
  | .call op _ _ _ =>
      .nset (.literal pc) configuration.returnRegister
        (operationBase client environment op + (environment.implementation op).module.entry)

def clientCode (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration) : Program :=
  client.zipIdx.map fun (instruction, pc) ↦
    clientInstruction client environment configuration pc instruction

/-- One comparison slot in the shared return dispatcher. -/
def dispatcherInstruction (configuration : Configuration) (position pc : Nat) : Instruction :=
  .ncompare (.reg configuration.returnRegister) (.literal pc)
    (position + 2) (position + 1) (position + 2)

/-- Restore the linker-owned register and resume the statically declared continuation. -/
def dispatcherCleanup (configuration : Configuration) (position : Nat) :
    OpenInstruction signature → Instruction
  | .core _ => .nset (.literal 0) configuration.returnRegister (position + 1)
  | .call _ _ _ next => .nset (.literal 0) configuration.returnRegister next

def dispatcherEntries (configuration : Configuration) (base pc : Nat) :
    OpenProgram signature → Program
  | [] => []
  | instruction :: rest =>
      let position := base + 2 * pc
      dispatcherInstruction configuration position pc ::
        dispatcherCleanup configuration (position + 1) instruction ::
        dispatcherEntries configuration base (pc + 1) rest

/-- Shared return dispatcher followed by a finite halt fallback. -/
def dispatcherCode (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration) : Program :=
  dispatcherEntries configuration (dispatcherBase client environment) 0 client ++
    [.halt (.literal 0)]

/-- One concrete finite linked core program with each implementation body occurring once. -/
def link (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration) : Program :=
  clientCode client environment configuration ++
    (operations signature).flatMap (implementationBody client environment) ++
    dispatcherCode client environment configuration

theorem clientCode_length (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration) :
    (clientCode client environment configuration).length = client.length := by
  simp [clientCode]

theorem dispatcherEntries_length (configuration : Configuration) (base pc : Nat)
    (client : OpenProgram signature) :
    (dispatcherEntries configuration base pc client).length = 2 * client.length := by
  induction client generalizing pc with
  | nil => rfl
  | cons instruction rest induction => simp [dispatcherEntries, induction, Nat.mul_add]

theorem implementationBody_length (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (op : signature.Op) :
    (implementationBody client environment op).length =
      (environment.implementation op).module.code.length := by
  simp [implementationBody]

/-- Exact linked instruction count; shared bodies appear once, independent of dynamic call count. -/
theorem link_length (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration) :
    (link client environment configuration).length =
      3 * client.length + implementationCodeSize environment + 1 := by
  simp [link, dispatcherCode, clientCode_length, dispatcherEntries_length, implementationCodeSize,
    implementationBody_length]
  omega

/--
Typed proof object connecting relative and linked executions.  Its fields are proof-only: the
linked code is definitionally `link client environment configuration`, never caller-selected.
-/
structure Refinement (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (linkedBound : problem.Input → Cost) : Prop where
  returnRegisterInitiallyZero : ∀ input,
    (problem.initialMemory input).natReg configuration.returnRegister = 0
  linkedValid :
    (Algolean.Algorithms.StructuredRealRAM.Linker.link
      client.module environment configuration).Valid
  solves : problem.SolvesWithinBy
    (Algolean.Algorithms.StructuredRealRAM.Linker.link
      client.module environment configuration) linkedBound

/-- Concrete linked certificate; client correctness is not repeated. -/
def RelativeAlgorithmCertificate.link
    (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (linkedBound : problem.Input → Cost)
    (refinement : Refinement client environment configuration linkedBound) :
    MachineProblem.FixedAlgorithmCertificateBy problem linkedBound where
  program := Algolean.Algorithms.StructuredRealRAM.Linker.link
    client.module environment configuration
  valid := refinement.linkedValid
  solves := refinement.solves

/-- Existential wrapper for one-line discharge after a concrete environment and refinement exist. -/
theorem RelativeAlgorithmCertificate.hasAlgorithm
    (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (linkedBound : problem.Input → Cost)
    (refinement : Refinement client environment configuration linkedBound) :
    problem.HasAlgorithmBy linkedBound :=
  ⟨RelativeAlgorithmCertificate.link client environment configuration linkedBound refinement⟩

/--
A relative client whose concrete-link refinement is proved once for every completed environment.
Integration supplies only implementations; it does not repeat the client's correctness proof.
-/
structure LinkableRelativeAlgorithmCertificate
    (signature : DependencySignature) (problem : MachineProblem)
    (relativeBound linkedBound : problem.Input → Cost) where
  relative : RelativeAlgorithmCertificate signature problem relativeBound
  configuration : Configuration
  refinement : ∀ environment : ImplementationEnvironment signature,
    Refinement relative environment configuration linkedBound

namespace LinkableRelativeAlgorithmCertificate

/-- Produce the concrete finite shared-body program from a completed environment. -/
def link (client : LinkableRelativeAlgorithmCertificate signature problem
    relativeBound linkedBound) (environment : ImplementationEnvironment signature) :
    MachineProblem.FixedAlgorithmCertificateBy problem linkedBound :=
  Algolean.Algorithms.StructuredRealRAM.Linker.RelativeAlgorithmCertificate.link
    client.relative environment client.configuration linkedBound (client.refinement environment)

/-- One-line existential discharge after independently completed dependencies are imported. -/
theorem hasAlgorithm (client : LinkableRelativeAlgorithmCertificate signature problem
    relativeBound linkedBound) (implementations : HasImplementations signature) :
    problem.HasAlgorithmBy linkedBound := by
  rcases implementations with ⟨environment⟩
  exact ⟨client.link environment⟩

/-- Exact linked instruction count, with every implementation body stored exactly once. -/
theorem link_instructionCount (client : LinkableRelativeAlgorithmCertificate signature problem
    relativeBound linkedBound) (environment : ImplementationEnvironment signature) :
    (client.link environment).program.length =
      3 * client.relative.module.length + implementationCodeSize environment + 1 :=
  by
    change (Algolean.Algorithms.StructuredRealRAM.Linker.link
      client.relative.module environment client.configuration).length = _
    exact link_length client.relative.module environment client.configuration

/-- Complete finite dependency graph in its canonical operation order. -/
@[nolint unusedArguments]
def dependencyDAG (_client : LinkableRelativeAlgorithmCertificate signature problem
    relativeBound linkedBound) : List signature.Op :=
  operations signature

end LinkableRelativeAlgorithmCertificate

end

end Algolean.Algorithms.StructuredRealRAM.Linker
