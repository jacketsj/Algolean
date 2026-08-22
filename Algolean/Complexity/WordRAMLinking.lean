/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.WordRAMLinkerCorrectness

/-!
# Verified relative-to-concrete Word-RAM linking certificates

This layer separates contract-relative correctness from target-linker refinement.  A linkable
certificate proves once, uniformly for every implementation environment, that the concrete fixed
`Linker.link` output is valid and solves the client problem.  Integration then needs only the
completed implementation environment; no client correctness proof is repeated.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- A relative certificate plus a proof that the concrete shared-body linker refines it. -/
structure LinkableRelativeAlgorithmCertificate
    (signature : DependencySignature w) (problem : StructuredProblem w)
    (relativeBound linkedBound : problem.Input → ℕ) where
  /-- Contract-relative client theorem. -/
  relative : RelativeAlgorithmCertificate signature problem relativeBound
  /-- Reserved return-dispatch resources. -/
  linkerConfiguration : Linker.Configuration w
  /-- Static ABI and reserved-register compatibility, checked independently of runtime data. -/
  compatible : ∀ implementations : ImplementationEnvironment signature,
    Linker.Compatibility relative.program implementations linkerConfiguration
  /-- Exact call-trace aggregation proving the advertised linked bound. -/
  overheadBound : ∀ (implementations : ImplementationEnvironment signature)
      (input : problem.Input) (validInput : problem.pre input)
      (final : Memory w) (result : BitVec w) (cost : Nat)
      (calls : List (DependencyCallRecord signature)),
    OpenHaltingTrace signature implementations.responder relative.program
      ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
    cost ≤ relativeBound input →
    cost + Linker.totalConcreteCallOverhead implementations calls ≤ linkedBound input

namespace LinkableRelativeAlgorithmCertificate

/--
Resolve every abstract call into one concrete finite core Word-RAM program.  Each operation body is
present exactly once in the returned program; calls inside loops execute it repeatedly at runtime.
-/
def link
    (client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound)
    (implementations : ImplementationEnvironment signature) :
    FixedWidthAlgorithmCertificateBy problem linkedBound where
  program := Linker.link client.relative.program implementations client.linkerConfiguration
  valid := Linker.link_valid _ _ _ client.relative.valid
  solves input validInput := by
    rcases client.relative.solvesAgainstContracts implementations.responder input validInput with
      ⟨final, result, cost, calls, output, openTrace, represented, correct, relativeCost⟩
    have registerZero :
        (problem.initialMemory input validInput).address
          client.linkerConfiguration.jumpRegister = 0 := rfl
    rcases Linker.refine_trace client.relative.program implementations
        client.linkerConfiguration (client.compatible implementations) openTrace registerZero with
      ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
    let run : problem.SuccessfulRun
        (Linker.link client.relative.program implementations client.linkerConfiguration)
        input validInput := {
      final := final
      result := result
      cost := linkedCost
      steps := linkedSteps
      trace := linkedTrace }
    refine ⟨run, output, represented, correct, ?_⟩
    exact linkedCostBound.trans
      (client.overheadBound implementations input validInput final result cost calls
        openTrace relativeCost)

/-- Existential discharge from a completed dependency environment. -/
theorem hasAlgorithm
    (client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound)
    (implementations : Nonempty (ImplementationEnvironment signature)) :
    problem.HasAlgorithmBy linkedBound := by
  rcases implementations with ⟨environment⟩
  exact ⟨client.link environment⟩

/-- Exact instruction-count theorem for the concrete linked certificate. -/
theorem link_instructionCount
    (client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound)
    (implementations : ImplementationEnvironment signature) :
    (client.link implementations).program.length =
      client.relative.program.length + Linker.implementationCodeSize implementations +
        2 * client.relative.program.length + 1 :=
  Linker.link_length _ _ _

/-- Typed complete dependency graph exposed for audits. -/
def dependencyDAG
    (_client : LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound) :
    List signature.Op := Linker.operations signature

end LinkableRelativeAlgorithmCertificate

namespace RelativeAlgorithmCertificate

/--
All proof data needed to resolve one relative client against one completed environment.  The
concrete certificate is derived from this typed record, so audits retain dependency provenance.
-/
structure ConcreteLink
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeBound linkedBound : problem.Input → Nat}
    (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (implementations : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) where
  compatible : Linker.Compatibility client.program implementations configuration
  overheadBound : ∀ (input : problem.Input) (validInput : problem.pre input)
      (final : Memory w) (result : BitVec w) (cost : Nat)
      (calls : List (DependencyCallRecord signature)),
    OpenHaltingTrace signature implementations.responder client.program
        ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
    cost ≤ relativeBound input →
    cost + Linker.totalConcreteCallOverhead implementations calls ≤ linkedBound input

/--
Link one concrete completed environment.  Functional correctness is derived from the relative
certificate by the generic trace-refinement theorem; callers supply only static compatibility,
target validity, and the theorem-side aggregation of the exact recorded call overhead.
-/
def linkConcrete
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeBound linkedBound : problem.Input → Nat}
    (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (implementations : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (compatible : Linker.Compatibility client.program implementations configuration)
    (overheadBound : ∀ (input : problem.Input) (validInput : problem.pre input)
      (final : Memory w) (result : BitVec w) (cost : Nat)
      (calls : List (DependencyCallRecord signature)),
      OpenHaltingTrace signature implementations.responder client.program
        ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
      cost ≤ relativeBound input →
      cost + Linker.totalConcreteCallOverhead implementations calls ≤ linkedBound input) :
    FixedWidthAlgorithmCertificateBy problem linkedBound where
  program := Linker.link client.program implementations configuration
  valid := Linker.link_valid _ _ _ client.valid
  solves input validInput := by
    rcases client.solvesAgainstContracts implementations.responder input validInput with
      ⟨final, result, cost, calls, output, openTrace, represented, correct, relativeCost⟩
    have registerZero :
        (problem.initialMemory input validInput).address configuration.jumpRegister = 0 := rfl
    rcases Linker.refine_trace client.program implementations configuration compatible
        openTrace registerZero with
      ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
    refine ⟨{
      final := final
      result := result
      cost := linkedCost
      steps := linkedSteps
      trace := linkedTrace }, output, represented, correct, ?_⟩
    exact linkedCostBound.trans
      (overheadBound input validInput final result cost calls openTrace relativeCost)

namespace ConcreteLink

/-- Derive the inspectable concrete certificate from one complete typed link record. -/
def certificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeBound linkedBound : problem.Input → Nat}
    {client : RelativeAlgorithmCertificate signature problem relativeBound}
    {implementations : ImplementationEnvironment signature}
    {configuration : Linker.Configuration w}
    (link : ConcreteLink client implementations configuration
      (relativeBound := relativeBound) (linkedBound := linkedBound)) :
    FixedWidthAlgorithmCertificateBy problem linkedBound :=
  client.linkConcrete implementations configuration link.compatible link.overheadBound

/-- Proposition-level discharge without discarding the concrete link record used by audits. -/
theorem hasAlgorithm
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeBound linkedBound : problem.Input → Nat}
    {client : RelativeAlgorithmCertificate signature problem relativeBound}
    {implementations : ImplementationEnvironment signature}
    {configuration : Linker.Configuration w}
    (link : ConcreteLink client implementations configuration
      (relativeBound := relativeBound) (linkedBound := linkedBound)) :
    problem.HasAlgorithmBy linkedBound :=
  ⟨link.certificate⟩

end ConcreteLink

end RelativeAlgorithmCertificate

end

end Algolean.Algorithms.WordRAM
