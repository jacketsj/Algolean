/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.StructuredRealRAMLinkerCorrectness
public import Algolean.Complexity.StructuredRealRAMUniformRealRelative

/-! # Shared-body linker for randomized structured exact-real/natural clients -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.UniformRealLinker

noncomputable section

def placementInstruction : UniformOpenInstruction signature → OpenInstruction signature
  | .machine (.core instruction) => .core instruction
  | .machine (.sampleUniform _ next) => .core (.jump next)
  | .call op input output next => .call op input output next

def placement (client : UniformOpenProgram signature) : OpenProgram signature :=
  client.map placementInstruction

@[simp] theorem placement_length (client : UniformOpenProgram signature) :
    (placement client).length = client.length := by simp [placement]

theorem placement_valid (client : UniformOpenProgram signature) (valid : client.Valid) :
    (placement client).Valid := by
  intro pc instruction fetch target successor
  simp only [placement, List.getElem?_map] at fetch
  rcases Option.map_eq_some_iff.mp fetch with ⟨source, sourceFetch, rfl⟩
  have below := valid pc source sourceFetch target (by
    cases source with
    | machine machine => cases machine <;>
        simpa [placementInstruction, OpenInstruction.successors,
          UniformOpenInstruction.successors, UniformReal.Instruction.successors,
          Instruction.successors] using successor
    | call => simpa [placementInstruction, OpenInstruction.successors,
        UniformOpenInstruction.successors] using successor)
  simpa [placement] using below

def clientInstruction (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (pc : Nat) : UniformOpenInstruction signature → UniformReal.Instruction
  | .machine instruction => instruction
  | .call op input output next => .core
      (Linker.clientInstruction (placement client) environment configuration pc
        (.call op input output next))

def clientCode (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    UniformReal.Program :=
  client.zipIdx.map fun (instruction, pc) ↦
    clientInstruction client environment configuration pc instruction

@[simp] theorem clientCode_length (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    (clientCode client environment configuration).length = client.length := by
  simp [clientCode]

def deterministicArtifact (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    Program := Linker.link (placement client) environment configuration

/-- One concrete finite random program; deterministic dependency bodies occur exactly once. -/
def link (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    UniformReal.Program :=
  clientCode client environment configuration ++
    ((deterministicArtifact client environment configuration).drop client.length).map .core

theorem deterministic_length_le (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    client.length ≤ (deterministicArtifact client environment configuration).length := by
  rw [deterministicArtifact, Linker.link_length, placement_length]
  omega

theorem link_length (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration) :
    (link client environment configuration).length =
      (deterministicArtifact client environment configuration).length := by
  simp only [link, List.length_append, clientCode_length, List.length_map, List.length_drop]
  have := deterministic_length_le client environment configuration
  omega

theorem link_fetch_client (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (pc : Nat) (instruction : UniformOpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[pc]? =
      some (clientInstruction client environment configuration pc instruction) := by
  have inRange := List.getElem?_eq_some_iff.mp fetch |>.1
  rw [link, List.getElem?_append_left]
  · simp [clientCode, fetch]
  · simpa [clientCode] using inRange

theorem link_fetch_tail (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (pc : Nat) (afterClient : client.length ≤ pc) (instruction : Instruction)
    (fetch : (deterministicArtifact client environment configuration)[pc]? = some instruction) :
    (link client environment configuration)[pc]? = some (.core instruction) := by
  rw [link, List.getElem?_append_right]
  · rw [clientCode_length]
    simp only [List.getElem?_map, List.getElem?_drop]
    have equal : client.length + (pc - client.length) = pc := by omega
    rw [equal, fetch]
    rfl
  · rw [clientCode_length]
    exact afterClient

theorem link_valid (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
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
            some (placementInstruction client[pc]) := by simp [placement, sourceFetch]
        have deterministicFetch := Linker.link_fetch_client (placement client) environment
          configuration pc _ placementFetch
        have sourceSuccessor : target ∈
            (Linker.clientInstruction (placement client) environment configuration pc
              (placementInstruction client[pc])).successors := by
          cases machine <;> simpa [source, clientInstruction, placementInstruction,
            Linker.clientInstruction, UniformReal.Instruction.successors,
            Instruction.successors] using successor
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
            UniformReal.Instruction.successors] using successor)
        simpa [deterministic, link_length] using below
  · have afterClient := Nat.le_of_not_gt inClient
    rw [link, List.getElem?_append_right (by simpa [clientCode] using afterClient)] at fetch
    rw [clientCode_length] at fetch
    simp only [List.getElem?_map, List.getElem?_drop] at fetch
    have equal : client.length + (pc - client.length) = pc := by omega
    rw [equal] at fetch
    rcases Option.map_eq_some_iff.mp fetch with ⟨core, coreFetch, rfl⟩
    have below := deterministicValid pc core coreFetch target (by
      simpa [UniformReal.Instruction.successors] using successor)
    simpa [deterministic, link_length] using below

theorem bodyMaterialized (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (op : signature.Op) (pc : Nat) (instruction : Instruction)
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

end Algolean.Algorithms.StructuredRealRAM.UniformRealLinker
