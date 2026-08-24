/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.WordRAMLinkerCorrectness
public import Algolean.Complexity.WordRAMRandomizedRelative

/-!
# Shared-body linker for randomized Word-RAM clients

The client prefix retains each sealed random instruction.  Abstract calls use the deterministic
linker's ordinary setup instruction, and the remainder of the verified deterministic linked
artifact (shared callee bodies plus dispatcher) is embedded instruction-for-instruction through
the random profile's `.core` constructor.  The source and cursor are therefore neither reset nor
made visible during a deterministic call.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.RandomLinker

noncomputable section

/-- A semantics-free placement instruction with the same successor as a random draw. -/
def placementInstruction {w : Nat} {signature : DependencySignature w} :
    RandomOpenInstruction signature → OpenInstruction signature
  | .machine (.core instruction) => .core instruction
  | .machine (.randBit _ next) =>
      .core (.set (.immediate 0) (.immediate 0) next)
  | .call op input output next => .call op input output next

/-- Deterministic placement skeleton; it is used only for labels and shared-body layout. -/
def placement {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) : OpenProgram signature :=
  client.map placementInstruction

theorem placement_length {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) :
    (placement client).length = client.length := by simp [placement]

/-- Placement preserves all numeric successors and hence source validity. -/
theorem placement_valid {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (valid : client.Valid) :
    (placement client).Valid := by
  intro pc instruction fetch target successor
  simp only [placement, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨source, sourceFetch, rfl⟩
  simpa [placement] using valid pc source sourceFetch target (by
    cases source with
    | machine machine => cases machine <;> simpa [placementInstruction,
        OpenInstruction.successors, RandomOpenInstruction.successors,
        RandomBit.Instruction.successors, RAM.Instruction.successors] using successor
    | call => simpa [placementInstruction, OpenInstruction.successors,
        RandomOpenInstruction.successors] using successor)

/-- Compile only the randomized client prefix; every dependency body remains shared. -/
def clientInstruction {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (pc : Nat) : RandomOpenInstruction signature → RandomBit.Instruction w
  | .machine instruction => instruction
  | .call op input output next =>
      .core (Linker.clientInstruction (placement client) environment configuration pc
        (.call op input output next))

def clientCode {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    RandomBit.Program w :=
  client.zipIdx.map fun (instruction, pc) =>
    clientInstruction client environment configuration pc instruction

theorem clientCode_length {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    (clientCode client environment configuration).length = client.length := by
  simp [clientCode]

/-- The deterministic linked artifact used solely to place bodies and dispatcher entries. -/
def deterministicArtifact {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    Program w :=
  Linker.link (placement client) environment configuration

/-- One finite sealed randomized program with all deterministic dependencies materialized. -/
def link {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    RandomBit.Program w :=
  clientCode client environment configuration ++
    ((deterministicArtifact client environment configuration).drop client.length).map .core

theorem deterministic_length_le {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    client.length ≤ (deterministicArtifact client environment configuration).length := by
  rw [deterministicArtifact, Linker.link_length, placement_length]
  omega

/-- Linking changes no program-counter positions and appends the same shared-body suffix. -/
theorem link_length {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w) :
    (link client environment configuration).length =
      (deterministicArtifact client environment configuration).length := by
  simp only [link, List.length_append, clientCode_length, List.length_map,
    List.length_drop]
  have := deterministic_length_le client environment configuration
  omega

/-- Fetching a client position returns its original random instruction or concrete call setup. -/
theorem link_fetch_client {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (pc : Nat) (instruction : RandomOpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[pc]? =
      some (clientInstruction client environment configuration pc instruction) := by
  have pcInRange := List.getElem?_eq_some_iff.mp fetch |>.1
  rw [link, List.getElem?_append_left]
  · simp [clientCode, fetch]
  · simpa [clientCode] using pcInRange

/-- Every position after the client prefix is the `.core` image of the deterministic linker. -/
theorem link_fetch_tail {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (pc : Nat) (afterClient : client.length ≤ pc)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w))
    (fetch : (deterministicArtifact client environment configuration)[pc]? = some instruction) :
    (link client environment configuration)[pc]? = some (.core instruction) := by
  rw [link, List.getElem?_append_right]
  · rw [clientCode_length]
    simp only [List.getElem?_map, List.getElem?_drop]
    have indexEq : client.length + (pc - client.length) = pc := by omega
    rw [indexEq, fetch]
    rfl
  · rw [clientCode_length]
    exact afterClient

/-- Source validity and certified deterministic implementations imply concrete target validity. -/
theorem link_valid {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (valid : client.Valid) : (link client environment configuration).Valid := by
  let deterministic := deterministicArtifact client environment configuration
  have deterministicValid : deterministic.Valid :=
    Linker.link_valid (placement client) environment configuration (placement_valid client valid)
  intro pc instruction fetch target successor
  by_cases inClient : pc < client.length
  · have sourceFetch : client[pc]? = some client[pc] := List.getElem?_eq_getElem inClient
    have linkedFetch := link_fetch_client client environment configuration pc client[pc] sourceFetch
    rw [linkedFetch] at fetch
    injection fetch with instructionEq
    subst instruction
    cases source : client[pc] with
    | machine machine =>
        have placementFetch : (placement client)[pc]? =
            some (placementInstruction client[pc]) := by
          simp [placement, sourceFetch]
        have deterministicFetch := Linker.link_fetch_client (placement client) environment
          configuration pc _ placementFetch
        have sourceSuccessor : target ∈
            (Linker.clientInstruction (placement client) environment configuration pc
              (placementInstruction client[pc])).successors := by
          cases machine <;> simpa [source, clientInstruction, placementInstruction,
            Linker.clientInstruction,
            RandomBit.Instruction.successors, RAM.Instruction.successors] using successor
        have below := deterministicValid pc _ deterministicFetch target sourceSuccessor
        simpa [deterministic, link_length] using below
    | call op input output next =>
        have placementFetch : (placement client)[pc]? =
            some (.call op input output next) := by
          simp [placement, sourceFetch, source, placementInstruction]
        have deterministicFetch := Linker.link_fetch_client (placement client) environment
          configuration pc _ placementFetch
        have below := deterministicValid pc _ deterministicFetch target (by
          simpa [source, clientInstruction, Linker.clientInstruction,
            RandomBit.Instruction.successors] using successor)
        simpa [deterministic, link_length] using below
  · have afterClient : client.length ≤ pc := Nat.le_of_not_gt inClient
    rw [link, List.getElem?_append_right (by simpa [clientCode] using afterClient)] at fetch
    rw [clientCode_length] at fetch
    simp only [List.getElem?_map, List.getElem?_drop] at fetch
    have indexEq : client.length + (pc - client.length) = pc := by omega
    rw [indexEq] at fetch
    rcases Option.map_eq_some_iff.mp fetch with ⟨core, coreFetch, rfl⟩
    have below := deterministicValid pc core coreFetch target (by
      simpa [RandomBit.Instruction.successors] using successor)
    simpa [deterministic, link_length] using below

/-- Each implementation body is present once at the deterministic linker's canonical base. -/
theorem bodyMaterialized {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (op : signature.Op) (pc : Nat)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w))
    (fetch : (environment.implementation op).module.code[pc]? = some instruction) :
    (link client environment configuration)[
      Linker.operationBase (placement client) environment op + pc]? =
      some (.core (Linker.relocateInstruction
        (Linker.operationBase (placement client) environment op)
        (Linker.dispatcherBase (placement client) environment) instruction)) := by
  apply link_fetch_tail
  · simp only [Linker.operationBase, placement_length]
    omega
  · exact Linker.link_fetch_implementation (placement client) environment configuration op pc
      instruction fetch

end

end Algolean.Algorithms.WordRAM.RandomLinker
