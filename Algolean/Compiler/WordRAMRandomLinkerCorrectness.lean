/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.WordRAMRandomLinker

/-!
# Same-source correctness of the randomized Word-RAM linker

Every deterministic callee instruction is a `.core` transition in the linked random trace.  The
hidden source and cursor pass through setup, callee, dispatcher, and cleanup unchanged.  Only the
client's original `randBit` nodes can advance the cursor.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.RandomLinker

noncomputable section

open MeasureTheory

private theorem cost_add_assoc (left middle right : RandomBit.Cost) :
    (left + middle) + right = left + (middle + right) := by
  rcases left with ⟨leftSteps, leftDraws⟩
  rcases middle with ⟨middleSteps, middleDraws⟩
  rcases right with ⟨rightSteps, rightDraws⟩
  apply RandomBit.Cost.ext
  · change (leftSteps + middleSteps) + rightSteps =
      leftSteps + (middleSteps + rightSteps)
    omega
  · change (leftDraws + middleDraws) + rightDraws =
      leftDraws + (middleDraws + rightDraws)
    omega

/-- A deterministic segment inside a randomized execution. -/
inductive RunningTrace (program : RandomBit.Program w) (source : RandomBit.Source) :
    RandomBit.Configuration w → RandomBit.Configuration w → RandomBit.Cost → Nat → Prop where
  | one {initial final cost}
      (observes : RandomBit.step program source initial = ⟨.running final, cost⟩) :
      RunningTrace program source initial final cost 1
  | next {initial middle final headCost tailCost tailSteps}
      (observes : RandomBit.step program source initial = ⟨.running middle, headCost⟩)
      (tail : RunningTrace program source middle final tailCost tailSteps) :
      RunningTrace program source initial final (headCost + tailCost) (tailSteps + 1)

theorem RunningTrace.trans
    (first : RunningTrace program source initial middle firstCost firstSteps)
    (second : RunningTrace program source middle final secondCost secondSteps) :
    RunningTrace program source initial final
      (firstCost + secondCost) (firstSteps + secondSteps) := by
  induction first with
  | one observes =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RunningTrace.next observes second
  | next observes tail induction =>
      have combined := RunningTrace.next observes (induction second)
      convert combined using 1
      · exact cost_add_assoc _ _ _
      · omega

theorem RunningTrace.thenHalting
    (runningPrefix : RunningTrace program source initial middle prefixCost prefixSteps)
    (suffix : RandomBit.RawHaltingTrace program source middle final result draws suffixCost) :
    RandomBit.RawHaltingTrace program source initial final result draws
      (prefixCost + suffixCost) := by
  induction runningPrefix with
  | one observes => exact RandomBit.RawHaltingTrace.next observes suffix
  | next observes tail induction =>
      have combined := RandomBit.RawHaltingTrace.next observes (induction suffix)
      rw [cost_add_assoc]
      exact combined

/-- Lift a deterministic running transition at a position known to contain `.core`. -/
theorem core_running
    (deterministicProgram : Program w) (randomProgram : RandomBit.Program w)
    (source : RandomBit.Source) (cursor pc next : Nat) (before after : Memory w)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w))
    (deterministicFetch : deterministicProgram[pc]? = some instruction)
    (randomFetch : randomProgram[pc]? = some (.core instruction))
    (deterministicStep : WordRAM.stepCosted deterministicProgram ⟨pc, before⟩ =
      ⟨.running ⟨next, after⟩, 1⟩) :
    RandomBit.step randomProgram source ⟨pc, before, cursor⟩ =
      ⟨.running ⟨next, after, cursor⟩, RandomBit.Cost.core⟩ := by
  simp only [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
    deterministicFetch, RAM.CostedSemantics.unit] at deterministicStep
  simp only [RandomBit.step, randomFetch, RandomBit.execute, RandomBit.Cost.core]
  cases execution : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction before <;>
    simp [execution] at deterministicStep ⊢
  cases deterministicStep
  exact ⟨rfl, rfl⟩

/-- Lift a deterministic halting transition at a position known to contain `.core`. -/
theorem core_halted
    (deterministicProgram : Program w) (randomProgram : RandomBit.Program w)
    (source : RandomBit.Source) (cursor pc : Nat) (before after : Memory w)
    (result : BitVec w)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w))
    (deterministicFetch : deterministicProgram[pc]? = some instruction)
    (randomFetch : randomProgram[pc]? = some (.core instruction))
    (deterministicStep : WordRAM.stepCosted deterministicProgram ⟨pc, before⟩ =
      ⟨.halted after result, 1⟩) :
    RandomBit.step randomProgram source ⟨pc, before, cursor⟩ =
      ⟨.halted after result cursor, RandomBit.Cost.core⟩ := by
  simp only [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
    deterministicFetch, RAM.CostedSemantics.unit] at deterministicStep
  simp only [RandomBit.step, randomFetch, RandomBit.execute, RandomBit.Cost.core]
  cases execution : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction before <;>
    simp [execution] at deterministicStep ⊢
  exact deterministicStep

/-- Relocate and execute every certified callee instruction without consuming randomness. -/
theorem relocate_trace {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (op : signature.Op)
    {localInitial : WordRAM.Configuration w} {final : Memory w} {result : BitVec w}
    {cost steps : Nat}
    (trace : RAM.HaltingTrace
      (WordRAM.stepCosted (environment.implementation op).module.code)
      localInitial final result cost steps) :
    RunningTrace (link client environment configuration) source
      ⟨Linker.operationBase (placement client) environment op + localInitial.pc,
        localInitial.memory, cursor⟩
      ⟨Linker.dispatcherBase (placement client) environment, final, cursor⟩
      ⟨cost, 0⟩ steps := by
  induction trace with
  | halt observes =>
      rename_i calleeConfiguration calleeFinal calleeResult calleeCost
      simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
        RAM.CostedSemantics.step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have deterministicFetch := Linker.link_fetch_implementation (placement client)
          environment configuration op _ instruction fetch
        have randomFetch := bodyMaterialized client environment configuration op _ instruction fetch
        have costEq : calleeCost = 1 := by
          simpa [RAM.CostedSemantics.unit] using
            (congrArg RAM.StepObservation.cost observes).symm
        subst calleeCost
        apply RunningTrace.one
        apply core_running
          (deterministicProgram := deterministicArtifact client environment configuration)
          (randomProgram := link client environment configuration)
          (source := source) (cursor := cursor)
          (instruction := Linker.relocateInstruction
            (Linker.operationBase (placement client) environment op)
            (Linker.dispatcherBase (placement client) environment) instruction)
          (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
          (deterministicStep := by
            have originalExecution :
                RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction
                    calleeConfiguration.memory = .halted calleeFinal calleeResult := by
              simpa [RAM.CostedSemantics.unit] using
                congrArg RAM.StepObservation.outcome observes
            have relocated := Linker.relocate_execute_halted
              (Linker.operationBase (placement client) environment op)
              (Linker.dispatcherBase (placement client) environment)
              instruction calleeConfiguration.memory calleeFinal calleeResult originalExecution
            change WordRAM.stepCosted
              (Linker.link (placement client) environment configuration) _ = _
            simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
              RAM.CostedSemantics.step, deterministicFetch, RAM.CostedSemantics.unit]
            exact congrArg (fun outcome ↦ RAM.StepObservation.mk outcome (1 : Nat)) relocated)
  | next observes tail induction =>
      rename_i calleeConfiguration calleeNext calleeFinal calleeResult headCost tailCost tailSteps
      simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
        RAM.CostedSemantics.step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have deterministicFetch := Linker.link_fetch_implementation (placement client)
          environment configuration op _ instruction fetch
        have randomFetch := bodyMaterialized client environment configuration op _ instruction fetch
        have originalExecution :
            RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction
                calleeConfiguration.memory = .running calleeNext := by
          simpa [RAM.CostedSemantics.unit] using
            congrArg RAM.StepObservation.outcome observes
        have relocated := Linker.relocate_execute_running
          (Linker.operationBase (placement client) environment op)
          (Linker.dispatcherBase (placement client) environment)
          instruction calleeConfiguration.memory calleeNext originalExecution
        have head : WordRAM.stepCosted (deterministicArtifact client environment configuration)
            ⟨Linker.operationBase (placement client) environment op + calleeConfiguration.pc,
              calleeConfiguration.memory⟩ =
            ⟨.running ⟨Linker.operationBase (placement client) environment op + calleeNext.pc,
              calleeNext.memory⟩, 1⟩ := by
          change WordRAM.stepCosted
            (Linker.link (placement client) environment configuration) _ = _
          simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
            RAM.CostedSemantics.step, deterministicFetch, RAM.CostedSemantics.unit]
          rw [relocated]
        have randomHead := core_running
          (deterministicProgram := deterministicArtifact client environment configuration)
          (randomProgram := link client environment configuration)
          (source := source) (cursor := cursor)
          (instruction := Linker.relocateInstruction
            (Linker.operationBase (placement client) environment op)
            (Linker.dispatcherBase (placement client) environment) instruction)
          (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
          (deterministicStep := head)
        have combined := RunningTrace.next randomHead induction
        have headCostEq : headCost = 1 := by
          simpa [RAM.CostedSemantics.unit] using
            (congrArg RAM.StepObservation.cost observes).symm
        subst headCost
        exact combined

/-- Randomized counterpart of deterministic call setup. -/
theorem call_setup {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration w)
    (source : RandomBit.Source) (cursor pc : Nat) (op : signature.Op)
    (input output : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[pc]? = some (.call op input output next)) :
    RandomBit.step (link client environment configuration) source ⟨pc, memory, cursor⟩ =
      ⟨.running ⟨Linker.operationBase (placement client) environment op +
          (environment.implementation op).module.entry,
        memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc), cursor⟩,
        RandomBit.Cost.core⟩ := by
  have randomFetch := link_fetch_client client environment configuration pc _ fetch
  simp [RandomBit.step, randomFetch, clientInstruction, Linker.clientInstruction,
    RandomBit.execute, RAM.execute, RAM.AddressOperand.eval, RandomBit.Cost.core]

private theorem dispatcher_after_client {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (pc : Nat) :
    client.length ≤ Linker.dispatcherBase (placement client) environment + pc := by
  simp only [Linker.dispatcherBase, placement_length]
  omega

/-- One matching dispatcher comparison is an ordinary cursor-preserving core step. -/
theorem dispatcher_equal {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (returnPc : Nat) (op : signature.Op) (input output : Region w) (next : Nat)
    (memory : Memory w)
    (fetch : client[returnPc]? = some (.call op input output next))
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RandomBit.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc,
        memory, cursor⟩ =
      ⟨.running
        ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
          memory, cursor⟩, RandomBit.Cost.core⟩ := by
  have placementFetch : (placement client)[returnPc]? =
      some (.call op input output next) := by
    simp [placement, fetch, placementInstruction]
  let instruction := Linker.dispatcherInstruction configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc)
    returnPc (.call op input output next)
  have deterministicFetch :
      (deterministicArtifact client environment configuration)[
        Linker.dispatcherBase (placement client) environment + 2 * returnPc]? =
        some instruction :=
    Linker.link_fetch_dispatcher (placement client) environment configuration returnPc _
      placementFetch
  have randomFetch := link_fetch_tail client environment configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc)
    (dispatcher_after_client client environment (2 * returnPc))
    instruction deterministicFetch
  have deterministicStep := Linker.dispatcher_step_equal (placement client) environment
    configuration returnPc op input output next memory placementFetch returnId
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := deterministicStep)

/-- Dispatcher cleanup restores the linker-owned return register without consuming randomness. -/
theorem dispatcher_cleanup {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (returnPc : Nat) (op : signature.Op) (input output : Region w) (next : Nat)
    (memory : Memory w)
    (fetch : client[returnPc]? = some (.call op input output next)) :
    RandomBit.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
        memory, cursor⟩ =
      ⟨.running ⟨next, memory.writeAddress configuration.jumpRegister 0, cursor⟩,
        RandomBit.Cost.core⟩ := by
  have placementFetch : (placement client)[returnPc]? =
      some (.call op input output next) := by
    simp [placement, fetch, placementInstruction]
  let instruction := Linker.dispatcherCleanup configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1)
    (.call op input output next)
  have deterministicFetch :
      (deterministicArtifact client environment configuration)[
        Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1]? =
        some instruction :=
    Linker.link_fetch_dispatcherCleanup (placement client) environment configuration returnPc _
      placementFetch
  have randomFetch := link_fetch_tail client environment configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1)
    (dispatcher_after_client client environment (2 * returnPc + 1))
    instruction deterministicFetch
  have deterministicStep := Linker.dispatcher_cleanup_step (placement client) environment
    configuration returnPc op input output next memory placementFetch
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := deterministicStep)

/-- A nonmatching dispatcher comparison advances by one entry and preserves the cursor. -/
theorem dispatcher_before {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (returnPc index : Nat) (memory : Memory w)
    (returnInRange : returnPc < client.length) (before : index < returnPc)
    (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RandomBit.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * index, memory, cursor⟩ =
      ⟨.running
        ⟨Linker.dispatcherBase (placement client) environment + 2 * (index + 1),
          memory, cursor⟩, RandomBit.Cost.core⟩ := by
  have indexRange : index < client.length := before.trans returnInRange
  have sourceFetch : client[index]? = some client[index] := List.getElem?_eq_getElem indexRange
  have placementFetch : (placement client)[index]? =
      some (placementInstruction client[index]) := by simp [placement, sourceFetch]
  let instruction := Linker.dispatcherInstruction configuration
    (Linker.dispatcherBase (placement client) environment + 2 * index)
    index (placementInstruction client[index])
  have deterministicFetch :
      (deterministicArtifact client environment configuration)[
        Linker.dispatcherBase (placement client) environment + 2 * index]? =
        some instruction :=
    Linker.link_fetch_dispatcher (placement client) environment configuration index _
      placementFetch
  have randomFetch := link_fetch_tail client environment configuration _
    (dispatcher_after_client client environment _) instruction deterministicFetch
  have deterministicStep := Linker.dispatcher_step_before (placement client) environment
    configuration returnPc index memory (by simpa [placement_length] using returnInRange)
    before (by simpa [placement_length] using clientFits) returnId
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := deterministicStep)

/-- The full linear dispatcher is present in the same randomized trace. -/
theorem dispatcher_returns_from {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (returnPc index : Nat) (op : signature.Op) (input output : Region w) (next : Nat)
    (memory : Memory w) (fetch : client[returnPc]? = some (.call op input output next))
    (indexBefore : index ≤ returnPc) (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RunningTrace (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * index, memory, cursor⟩
      ⟨next, memory.writeAddress configuration.jumpRegister 0, cursor⟩
      ⟨returnPc - index + 2, 0⟩ (returnPc - index + 2) := by
  by_cases equal : index = returnPc
  · subst index
    have first := dispatcher_equal client environment configuration source cursor returnPc op
      input output next memory fetch returnId
    have second := dispatcher_cleanup client environment configuration source cursor returnPc op
      input output next memory fetch
    have combined := RunningTrace.next first (RunningTrace.one second)
    convert combined using 1
    · apply RandomBit.Cost.ext
      · change returnPc - returnPc + 2 = 1 + 1
        omega
      · rfl
    · omega
  · have before : index < returnPc := lt_of_le_of_ne indexBefore equal
    have first := dispatcher_before client environment configuration source cursor returnPc index
      memory (List.getElem?_eq_some_iff.mp fetch |>.1) before clientFits returnId
    have recursive := dispatcher_returns_from client environment configuration source cursor
      returnPc (index + 1) op input output next memory fetch before clientFits returnId
    have combined := RunningTrace.next first recursive
    convert combined using 1
    · apply RandomBit.Cost.ext
      · change returnPc - index + 2 = 1 + (returnPc - (index + 1) + 2)
        omega
      · rfl
    · omega
termination_by returnPc - index

theorem dispatcher_returns {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (source : RandomBit.Source) (cursor : Nat)
    (returnPc : Nat) (op : signature.Op) (input output : Region w) (next : Nat)
    (memory : Memory w) (fetch : client[returnPc]? = some (.call op input output next))
    (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RunningTrace (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment, memory, cursor⟩
      ⟨next, memory.writeAddress configuration.jumpRegister 0, cursor⟩
      ⟨returnPc + 2, 0⟩ (returnPc + 2) := by
  simpa using dispatcher_returns_from client environment configuration source cursor returnPc 0
    op input output next memory fetch (Nat.zero_le _) clientFits returnId

/-- One abstract call expands to setup, every callee step, and syntax-derived dispatch overhead. -/
theorem refine_call {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : RandomBit.Source) (cursor pc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat)
    (input : (signature.contract op).Input) (validInput : (signature.contract op).pre input)
    (memory : Memory w)
    (inputRep : (signature.contract op).inputLayout.RepAt inputRegion input memory)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (registerZero : memory.address configuration.jumpRegister = 0) :
    ∃ linkedCost linkedSteps,
      RunningTrace (link client environment configuration) source
        ⟨pc, memory, cursor⟩
        ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory, cursor⟩
        linkedCost linkedSteps ∧
      linkedCost.steps ≤ signature.bound op input + 1 +
        Linker.concreteCallOverhead environment {
          callSite := pc
          op := op
          input := input
          output := environment.responder.answer op input
          outputCorrect := environment.responder.correct op input validInput
          chargedCost := signature.bound op input + 1
          chargedCost_eq := rfl } ∧
      linkedCost.randomDraws = 0 := by
  let implementation := environment.implementation op
  have placementFetch : (placement client)[pc]? =
      some (.call op inputRegion outputRegion next) := by
    simp [placement, fetch, placementInstruction]
  have inputRegionEq := compatible.inputRegion_eq pc op inputRegion outputRegion next
    placementFetch
  have outputRegionEq := compatible.outputRegion_eq pc op inputRegion outputRegion next
    placementFetch
  have setupRep : (signature.contract op).inputLayout.RepAt
      implementation.calling.inputRegion input
      (memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc)) := by
    rw [← inputRegionEq]
    exact Linker.inputRep_writeAddress _ _ _ _ _ _ inputRep
  rcases implementation.restoringCorrect input validInput
      (memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc)) setupRep with
    ⟨run, outputRep, costBound, canonicalEffect⟩
  have setup := RunningTrace.one (call_setup client environment configuration source cursor pc op
    inputRegion outputRegion next memory fetch)
  have relocated := relocate_trace client environment configuration source cursor op run.trace
  have returnId : run.final.address configuration.jumpRegister = BitVec.ofNat w pc := by
    rw [canonicalEffect, Linker.writeAt_address]
    simp [RAM.Memory.writeAddress]
  have returned := dispatcher_returns client environment configuration source cursor pc op
    inputRegion outputRegion next run.final fetch
      (by simpa [placement_length] using compatible.clientFits) returnId
  have allSteps := setup.trans (relocated.trans returned)
  have finalMemory :
      run.final.writeAddress configuration.jumpRegister 0 =
        (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory := by
    rw [canonicalEffect, outputRegionEq]
    exact Linker.writeAt_setup_cleanup _ _ _ _ _ _ registerZero
  rw [finalMemory] at allSteps
  refine ⟨_, _, allSteps, ?_, ?_⟩
  · simp only [Linker.concreteCallOverhead]
    change 1 + (run.cost + (pc + 2)) ≤ signature.bound op input + 1 + (pc + 2)
    omega
  · rfl

/-- A client random instruction that runs preserves the linker-owned address register. -/
theorem randomInstruction_preserves_register {w : Nat}
    {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : RandomBit.Source) (initial next : RandomBit.Configuration w)
    (instruction : RandomBit.Instruction w)
    (fetch : client[initial.pc]? = some (.machine instruction))
    (observed : RandomBit.execute source instruction initial =
      ⟨.running next, cost⟩) :
    next.memory.address configuration.jumpRegister =
      initial.memory.address configuration.jumpRegister := by
  cases instruction with
  | core coreInstruction =>
      have placementFetch : (placement client)[initial.pc]? =
          some (.core coreInstruction) := by
        simp [placement, fetch, placementInstruction]
      have safe := compatible.clientAvoidsReturnRegister _ _ placementFetch
      simp only [RandomBit.execute] at observed
      split at observed <;> cases observed
      rename_i nextConfiguration execution
      exact Linker.instructionAvoids_preserves_register _ _ safe _ _ execution
  | randBit destination successor =>
      simp only [RandomBit.execute] at observed
      cases observed
      rfl

/-- Flatten a complete relative random trace into one same-source linked trace. -/
theorem refine_trace {w : Nat} {signature : DependencySignature w}
    (client : RandomOpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : RandomBit.Source)
    {initial : RandomBit.Configuration w} {final : Memory w} {result : BitVec w}
    {draws : Nat} {cost : RandomBit.Cost}
    {calls : List (DependencyCallRecord signature)}
    (trace : RandomOpenHaltingTrace signature environment.responder client source
      initial final result draws cost calls)
    (registerZero : initial.memory.address configuration.jumpRegister = 0) :
    ∃ linkedCost,
      RandomBit.RawHaltingTrace (link client environment configuration) source
        initial final result draws linkedCost ∧
      linkedCost.steps ≤ cost.steps + Linker.totalConcreteCallOverhead environment calls ∧
      linkedCost.randomDraws = cost.randomDraws := by
  induction trace with
  | halt openStep =>
      cases openStep with
      | machine fetch observed =>
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨_, .halt ?_, ?_, rfl⟩
          · simp only [RandomBit.step, linkedFetch, clientInstruction]
            exact observed
          · simp [Linker.totalConcreteCallOverhead]
  | next openStep tail induction =>
      rename_i current nextConfiguration final result draws headCost tailCost headCall calls
      cases openStep with
      | machine fetch observed =>
          have preserved := randomInstruction_preserves_register client environment configuration
            compatible source _ _ _ fetch observed
          have nextZero := preserved.trans registerZero
          rcases induction nextZero with ⟨tailLinkedCost, linkedTail, tailBound, drawsEq⟩
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨headCost + tailLinkedCost, .next ?_ linkedTail, ?_, ?_⟩
          · simp only [RandomBit.step, linkedFetch, clientInstruction]
            exact observed
          · simp only [Option.toList_none, List.nil_append]
            change headCost.steps + tailLinkedCost.steps ≤
              headCost.steps + tailCost.steps +
                Linker.totalConcreteCallOverhead environment calls
            omega
          · change _ + tailLinkedCost.randomDraws = _ + _
            rw [drawsEq]
      | call fetch inputRep validInput =>
          rcases refine_call client environment configuration compatible source _ _ _ _ _ _ _
              validInput _ inputRep fetch registerZero with
            ⟨callCost, callSteps, linkedCall, callBound, noDraws⟩
          rcases induction (by simpa only [Linker.writeAt_address] using registerZero) with
            ⟨tailLinkedCost, linkedTail, tailBound, drawsEq⟩
          refine ⟨callCost + tailLinkedCost, linkedCall.thenHalting linkedTail, ?_, ?_⟩
          · simp only [Linker.totalConcreteCallOverhead] at tailBound
            simp only [Option.toList_some, List.singleton_append,
              Linker.totalConcreteCallOverhead, List.map_cons, List.sum_cons]
            change callCost.steps + tailLinkedCost.steps ≤
              (signature.bound _ _ + 1 + tailCost.steps) +
                (Linker.concreteCallOverhead environment _ +
                  (calls.map (Linker.concreteCallOverhead environment)).sum)
            omega
          · change callCost.randomDraws + tailLinkedCost.randomDraws = _
            rw [noDraws, drawsEq]
            rfl

/-- Syntax-derived extra step bound for a linked randomized client. -/
def linkedStepBound (relativeBound overheadBound : alpha → Nat) : alpha → Nat :=
  fun input ↦ relativeBound input + overheadBound input

/-- Static and theorem-side obligations for the automatic same-source randomized linker. -/
structure LinkingAssumptions {w : Nat} {signature : DependencySignature w}
    {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (overheadBound : problem.Input → Nat) : Prop where
  compatible : Linker.Compatibility (placement client.program) environment configuration
  /-- The input-dependent theorem bound covers the exact dynamic call-site dispatcher costs. -/
  overhead_le : ∀ source input, ∀ validInput : problem.pre input,
    ∀ final result draws cost calls,
      RandomOpenHaltingTrace signature environment.responder client.program source
        (RandomBit.Configuration.initial (problem.initialMemory input validInput))
        final result draws cost calls →
      Linker.totalConcreteCallOverhead environment calls ≤ overheadBound input
  /-- Measurability remains an explicit probability-theory obligation, not machine semantics. -/
  measurableSuccess : ∀ input validInput,
    MeasurableSet (problem.RandomSuccessEvent
      (link client.program environment configuration)
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound input validInput)

/-- Every relative success is a concrete linked success from only operational linker facts. -/
theorem successEvent_mono_of
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (compatible : Linker.Compatibility (placement client.program) environment configuration)
    (overhead_le : ∀ source input, ∀ validInput : problem.pre input,
      ∀ final result draws cost calls,
        RandomOpenHaltingTrace signature environment.responder client.program source
          (RandomBit.Configuration.initial (problem.initialMemory input validInput))
          final result draws cost calls →
        Linker.totalConcreteCallOverhead environment calls ≤ overheadBound input)
    (input : problem.Input) (validInput : problem.pre input) :
    RandomRelativeSuccessEvent signature environment.responder problem client.program
        relativeStepBound relativeDrawBound input validInput ⊆
      problem.RandomSuccessEvent (link client.program environment configuration)
        (linkedStepBound relativeStepBound overheadBound) relativeDrawBound input validInput := by
  intro source success
  rcases success with ⟨final, result, draws, cost, calls, output, trace,
    outputRep, correct, stepBound, drawBound⟩
  have registerZero :
      (problem.initialMemory input validInput).address configuration.jumpRegister = 0 := rfl
  rcases refine_trace client.program environment configuration compatible source
      trace registerZero with ⟨linkedCost, linkedTrace, linkedCostBound, drawCostEq⟩
  have overhead := overhead_le source input validInput final result draws cost calls trace
  let run : problem.RandomSuccessfulRun
      (link client.program environment configuration) source input validInput := {
    final := final
    result := result
    draws := draws
    cost := linkedCost
    trace := {
      operational := linkedTrace
      cursorAccounting := linkedTrace.cursorAccounting } }
  refine ⟨run, output, outputRep, correct, ?_, drawBound⟩
  change linkedCost.steps ≤ relativeStepBound input + overheadBound input
  omega

/-- Every relative success under the implementation responder is a concrete linked success. -/
theorem successEvent_mono
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : LinkingAssumptions client environment configuration overheadBound)
    (input : problem.Input) (validInput : problem.pre input) :
    RandomRelativeSuccessEvent signature environment.responder problem client.program
        relativeStepBound relativeDrawBound input validInput ⊆
      problem.RandomSuccessEvent (link client.program environment configuration)
        (linkedStepBound relativeStepBound overheadBound) relativeDrawBound input validInput :=
  successEvent_mono_of client environment configuration overheadBound assumptions.compatible
    assumptions.overhead_le input validInput

/-- Automatic publication: no user-supplied operational refinement is accepted. -/
def certificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : LinkingAssumptions client environment configuration overheadBound) :
    problem.HighProbabilityBoundedSuccessCertificate
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound failure where
  program := link client.program environment configuration
  valid := link_valid client.program environment configuration client.valid
  measurableSuccess := assumptions.measurableSuccess
  successProbability input validInput :=
    (client.successProbability environment.responder input validInput).trans
      (measure_mono (successEvent_mono client environment configuration overheadBound assumptions
        input validInput))

/-- Existential one-line discharge through the automatic same-source linker. -/
theorem hasAlgorithm
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : HighProbabilityBoundedSuccessRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : LinkingAssumptions client environment configuration overheadBound) :
    problem.HasHighProbabilityBoundedSuccessAlgorithm
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound failure :=
  ⟨certificate client environment configuration overheadBound assumptions⟩

/-! ## Every-source-time Monte Carlo linking -/

/-- Linker obligations for the guarantee that separates runtime from correctness probability. -/
structure BoundedTimeLinkingAssumptions
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : BoundedTimeMonteCarloRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (overheadBound : problem.Input → Nat) : Prop where
  compatible : Linker.Compatibility (placement client.program) environment configuration
  overhead_le : ∀ source input, ∀ validInput : problem.pre input,
    ∀ final result draws cost calls,
      RandomOpenHaltingTrace signature environment.responder client.program source
        (RandomBit.Configuration.initial (problem.initialMemory input validInput))
        final result draws cost calls →
      Linker.totalConcreteCallOverhead environment calls ≤ overheadBound input
  correctMeasurable : ∀ input validInput,
    MeasurableSet (problem.RandomCorrectEvent
      (link client.program environment configuration) input validInput)

/-- Every relative bounded run becomes a concrete bounded run on the identical hidden source. -/
theorem boundedTime_terminatesWithin
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : BoundedTimeMonteCarloRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : BoundedTimeLinkingAssumptions client environment configuration overheadBound)
    (source : RandomBit.Source) (input : problem.Input) (validInput : problem.pre input) :
    source ∈ problem.RandomTerminationWithinEvent
      (link client.program environment configuration)
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound input validInput := by
  rcases client.terminatesWithin environment.responder source input validInput with
    ⟨final, result, draws, cost, calls, output, trace, outputRep, stepBound, drawBound⟩
  rcases refine_trace client.program environment configuration assumptions.compatible source
      trace rfl with ⟨linkedCost, linkedTrace, linkedCostBound, linkedDraws⟩
  let run : problem.RandomSuccessfulRun
      (link client.program environment configuration) source input validInput := {
    final := final
    result := result
    draws := draws
    cost := linkedCost
    trace := {
      operational := linkedTrace
      cursorAccounting := linkedTrace.cursorAccounting } }
  refine ⟨run, output, outputRep, ?_, drawBound⟩
  have overhead := assumptions.overhead_le source input validInput final result draws cost calls trace
  change linkedCost.steps ≤ relativeStepBound input + overheadBound input
  omega

/-- Relative correctness transfers pointwise without merging timeout into the error event. -/
theorem boundedTime_correctEvent_mono
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : BoundedTimeMonteCarloRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w)
    (compatible : Linker.Compatibility (placement client.program) environment configuration)
    (input : problem.Input) (validInput : problem.pre input) :
    RandomRelativeCorrectEvent signature environment.responder problem client.program
        input validInput ⊆
      problem.RandomCorrectEvent (link client.program environment configuration)
        input validInput := by
  intro source success
  rcases success with ⟨final, result, draws, cost, calls, output, trace, outputRep, correct⟩
  rcases refine_trace client.program environment configuration compatible source
      trace rfl with ⟨linkedCost, linkedTrace, linkedCostBound, linkedDraws⟩
  let run : problem.RandomSuccessfulRun
      (link client.program environment configuration) source input validInput := {
    final := final
    result := result
    draws := draws
    cost := linkedCost
    trace := {
      operational := linkedTrace
      cursorAccounting := linkedTrace.cursorAccounting } }
  exact ⟨run, output, outputRep, correct⟩

/-- Automatic every-source-time Monte Carlo certificate with unchanged random-draw bound. -/
def boundedTimeCertificate
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : BoundedTimeMonteCarloRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : BoundedTimeLinkingAssumptions client environment configuration overheadBound) :
    problem.BoundedTimeMonteCarloCertificate
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound failure where
  program := link client.program environment configuration
  valid := link_valid client.program environment configuration client.valid
  terminatesWithin := boundedTime_terminatesWithin client environment configuration
    overheadBound assumptions
  correctMeasurable := assumptions.correctMeasurable
  correctProbability input validInput :=
    (client.correctProbability environment.responder input validInput).trans
      (measure_mono
        (boundedTime_correctEvent_mono client environment configuration assumptions.compatible
          input validInput))

/-- One-line existential discharge preserving every-source-time Monte Carlo semantics. -/
theorem hasBoundedTimeMonteCarloAlgorithm
    {w : Nat} {signature : DependencySignature w} {problem : StructuredProblem w}
    {relativeStepBound relativeDrawBound : problem.Input → Nat}
    {failure : problem.Input → Probability}
    (client : BoundedTimeMonteCarloRelativeCertificate signature problem
      relativeStepBound relativeDrawBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration w) (overheadBound : problem.Input → Nat)
    (assumptions : BoundedTimeLinkingAssumptions client environment configuration overheadBound) :
    problem.HasBoundedTimeMonteCarloAlgorithm
      (linkedStepBound relativeStepBound overheadBound) relativeDrawBound failure :=
  ⟨boundedTimeCertificate client environment configuration overheadBound assumptions⟩

end

end Algolean.Algorithms.WordRAM.RandomLinker
