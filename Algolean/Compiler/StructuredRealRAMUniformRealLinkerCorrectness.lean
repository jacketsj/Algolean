/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.StructuredRealRAMUniformRealLinker

/-! # Same-source correctness of randomized structured-real linking -/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.UniformRealLinker

open MeasureTheory

noncomputable section

private theorem randomCost_add_assoc (left middle right : UniformReal.Cost) :
    (left + middle) + right = left + (middle + right) := by
  apply RandomBit.Cost.ext
  · funext coordinate
    change (left.machine coordinate + middle.machine coordinate) + right.machine coordinate =
      left.machine coordinate + (middle.machine coordinate + right.machine coordinate)
    omega
  · change (left.randomDraws + middle.randomDraws) + right.randomDraws =
      left.randomDraws + (middle.randomDraws + right.randomDraws)
    omega

private theorem randomCost_add_mono
    {left left' right right' : UniformReal.Cost}
    (leftBound : left ≤ left') (rightBound : right ≤ right') :
    left + right ≤ left' + right' := by
  constructor
  · intro coordinate
    exact Nat.add_le_add (leftBound.1 coordinate) (rightBound.1 coordinate)
  · exact Nat.add_le_add leftBound.2 rightBound.2

private theorem ofCore_mono {left right : Cost} (bound : left ≤ right) :
    RandomBit.Cost.ofCore left ≤ RandomBit.Cost.ofCore right :=
  ⟨bound, le_rfl⟩

private theorem ofCore_add (left right : Cost) :
    RandomBit.Cost.ofCore (left + right) =
      RandomBit.Cost.ofCore left + RandomBit.Cost.ofCore right := by
  apply RandomBit.Cost.ext <;> rfl

private theorem randomCost_add_coreZero (cost : UniformReal.Cost) :
    cost + RandomBit.Cost.ofCore 0 = cost := by
  apply RandomBit.Cost.ext
  · funext coordinate
    change cost.machine coordinate + 0 = cost.machine coordinate
    omega
  · change cost.randomDraws + 0 = cost.randomDraws
    omega

inductive RunningTrace (program : UniformReal.Program) (source : UniformReal.Source) :
    UniformReal.Configuration → UniformReal.Configuration → UniformReal.Cost → Nat → Prop where
  | one {initial final cost}
      (step : UniformReal.step program source initial = ⟨.running final, cost⟩) :
      RunningTrace program source initial final cost 1
  | next {initial middle final headCost tailCost tailSteps}
      (step : UniformReal.step program source initial = ⟨.running middle, headCost⟩)
      (tail : RunningTrace program source middle final tailCost tailSteps) :
      RunningTrace program source initial final (headCost + tailCost) (tailSteps + 1)

theorem RunningTrace.trans
    (first : RunningTrace program source initial middle firstCost firstSteps)
    (second : RunningTrace program source middle final secondCost secondSteps) :
    RunningTrace program source initial final (firstCost + secondCost)
      (firstSteps + secondSteps) := by
  induction first with
  | one step =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using RunningTrace.next step second
  | next step tail induction =>
      have combined := RunningTrace.next step (induction second)
      rw [← randomCost_add_assoc] at combined
      convert combined using 1 <;> omega

theorem RunningTrace.thenHalting
    (runningPrefix : RunningTrace program source initial middle prefixCost prefixSteps)
    (suffix : UniformReal.HaltingTrace program source middle final result suffixCost suffixSteps draws) :
    UniformReal.HaltingTrace program source initial final result
      (prefixCost + suffixCost) (suffixSteps + prefixSteps) draws := by
  induction runningPrefix with
  | one step =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using
        UniformReal.HaltingTrace.next step suffix
  | next step tail induction =>
      have combined := UniformReal.HaltingTrace.next step (induction suffix)
      rw [← randomCost_add_assoc] at combined
      convert combined using 1 <;> omega

/-- Lift a fetched deterministic running step at the same program counter. -/
theorem core_running (deterministicProgram : Program) (randomProgram : UniformReal.Program)
    (source : UniformReal.Source) (cursor : Nat) (initial next : Configuration)
    (instruction : Instruction)
    (deterministicFetch : deterministicProgram[initial.pc]? = some instruction)
    (randomFetch : randomProgram[initial.pc]? = some (.core instruction))
    (deterministicStep : step deterministicProgram initial = ⟨.running next, cost⟩) :
    UniformReal.step randomProgram source ⟨initial.pc, initial.memory, cursor⟩ =
      ⟨.running ⟨next.pc, next.memory, cursor⟩, RandomBit.Cost.ofCore cost⟩ := by
  simp only [StructuredRealRAM.step, deterministicFetch] at deterministicStep
  simp only [UniformReal.step, randomFetch, UniformReal.execute]
  rw [deterministicStep]
  rfl

/-- Lift a fetched deterministic halt at the same program counter. -/
theorem core_halted (deterministicProgram : Program) (randomProgram : UniformReal.Program)
    (source : UniformReal.Source) (cursor : Nat) (initial : Configuration)
    (final : Memory) (result : Real) (instruction : Instruction)
    (deterministicFetch : deterministicProgram[initial.pc]? = some instruction)
    (randomFetch : randomProgram[initial.pc]? = some (.core instruction))
    (deterministicStep : step deterministicProgram initial = ⟨.halted final result, cost⟩) :
    UniformReal.step randomProgram source ⟨initial.pc, initial.memory, cursor⟩ =
      ⟨.halted final result cursor, RandomBit.Cost.ofCore cost⟩ := by
  simp only [StructuredRealRAM.step, deterministicFetch] at deterministicStep
  simp only [UniformReal.step, randomFetch, UniformReal.execute]
  rw [deterministicStep]
  rfl

/-- Every relocated callee transition executes as a cursor-preserving core transition. -/
theorem relocate_trace (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor : Nat) (op : signature.Op)
    (trace : HaltingTrace (environment.implementation op).module.code
      localInitial final result cost steps) :
    ∃ linkedCost,
      RunningTrace (link client environment configuration) source
        ⟨Linker.operationBase (placement client) environment op + localInitial.pc,
          localInitial.memory, cursor⟩
        ⟨Linker.dispatcherBase (placement client) environment, final, cursor⟩
        (RandomBit.Cost.ofCore linkedCost) steps ∧ linkedCost ≤ cost := by
  induction trace with
  | halt observed =>
      rename_i calleeConfiguration calleeFinal calleeResult calleeCost
      simp only [StructuredRealRAM.step] at observed
      split at observed
      · cases observed
      · rename_i instruction fetch
        have deterministicFetch := Linker.link_fetch_implementation (placement client)
          environment configuration op _ instruction fetch
        have randomFetch := bodyMaterialized client environment configuration op _ instruction fetch
        have original : execute instruction calleeConfiguration.memory =
            ⟨.halted calleeFinal calleeResult, calleeCost⟩ := by simpa using observed
        rcases Linker.relocate_execute_halted
            (Linker.operationBase (placement client) environment op)
            (Linker.dispatcherBase (placement client) environment) instruction
            calleeConfiguration.memory calleeFinal calleeResult calleeCost original with
          ⟨linkedCost, relocated, costBound⟩
        refine ⟨linkedCost, RunningTrace.one ?_, costBound⟩
        exact core_running
          (deterministicProgram := deterministicArtifact client environment configuration)
          (randomProgram := link client environment configuration) (source := source)
          (cursor := cursor)
          (initial := ⟨Linker.operationBase (placement client) environment op +
            calleeConfiguration.pc, calleeConfiguration.memory⟩)
          (next := ⟨Linker.dispatcherBase (placement client) environment, calleeFinal⟩)
          (instruction := Linker.relocateInstruction
            (Linker.operationBase (placement client) environment op)
            (Linker.dispatcherBase (placement client) environment) instruction)
          (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
          (deterministicStep := by
            change StructuredRealRAM.step
              (Linker.link (placement client) environment configuration) _ = _
            simp only [StructuredRealRAM.step, deterministicFetch]
            exact relocated)
  | next observed tail induction =>
      rename_i calleeConfiguration calleeNext calleeFinal calleeResult headCost tailCost tailSteps
      simp only [StructuredRealRAM.step] at observed
      split at observed
      · cases observed
      · rename_i instruction fetch
        have deterministicFetch := Linker.link_fetch_implementation (placement client)
          environment configuration op _ instruction fetch
        have randomFetch := bodyMaterialized client environment configuration op _ instruction fetch
        have original : execute instruction calleeConfiguration.memory =
            ⟨.running calleeNext, headCost⟩ := by simpa using observed
        have relocated := Linker.relocate_execute_running
          (Linker.operationBase (placement client) environment op)
          (Linker.dispatcherBase (placement client) environment) instruction
          calleeConfiguration.memory calleeNext headCost original
        rcases induction with ⟨linkedTailCost, linkedTail, tailBound⟩
        have randomHead := core_running
            (deterministicProgram := deterministicArtifact client environment configuration)
            (randomProgram := link client environment configuration) (source := source)
            (cursor := cursor)
            (initial := ⟨Linker.operationBase (placement client) environment op +
              calleeConfiguration.pc, calleeConfiguration.memory⟩)
            (next := ⟨Linker.operationBase (placement client) environment op + calleeNext.pc,
              calleeNext.memory⟩)
            (instruction := Linker.relocateInstruction
              (Linker.operationBase (placement client) environment op)
              (Linker.dispatcherBase (placement client) environment) instruction)
            (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
            (deterministicStep := by
              change StructuredRealRAM.step
                (Linker.link (placement client) environment configuration) _ = _
              simp only [StructuredRealRAM.step, deterministicFetch]
              exact relocated)
        have combined := RunningTrace.next randomHead linkedTail
        have costEq : RandomBit.Cost.ofCore headCost +
            RandomBit.Cost.ofCore linkedTailCost =
            RandomBit.Cost.ofCore (headCost + linkedTailCost) := by
          apply RandomBit.Cost.ext <;> rfl
        rw [costEq] at combined
        refine ⟨headCost + linkedTailCost, combined, ?_⟩
        · intro coordinate
          exact Nat.add_le_add_left (tailBound coordinate) (headCost coordinate)

private theorem dispatcher_after_client (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (pc : Nat) :
    client.length ≤ Linker.dispatcherBase (placement client) environment + pc := by
  simp only [Linker.dispatcherBase, placement_length]
  omega

theorem dispatcher_equal (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor returnPc : Nat) (op : signature.Op)
    (input output : Region) (next : Nat) (memory : Memory)
    (fetch : client[returnPc]? = some (.call op input output next))
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    UniformReal.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc, memory, cursor⟩ =
      ⟨.running ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
        memory, cursor⟩,
        RandomBit.Cost.ofCore ((Instruction.ncompare
          (.reg configuration.returnRegister) (.literal returnPc) 0 0 0).cost)⟩ := by
  have placementFetch : (placement client)[returnPc]? =
      some (.call op input output next) := by simp [placement, fetch, placementInstruction]
  let instruction := Linker.dispatcherInstruction configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc) returnPc
  have deterministicFetch := Linker.link_fetch_dispatcher (placement client) environment
    configuration returnPc _ placementFetch
  have randomFetch := link_fetch_tail client environment configuration _
    (dispatcher_after_client client environment _) instruction deterministicFetch
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (initial := ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc, memory⟩)
    (next := ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
      memory⟩)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := Linker.dispatcher_step_equal (placement client) environment
      configuration returnPc op input output next memory placementFetch returnId)

theorem dispatcher_cleanup (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor returnPc : Nat) (op : signature.Op)
    (input output : Region) (next : Nat) (memory : Memory)
    (fetch : client[returnPc]? = some (.call op input output next)) :
    UniformReal.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
        memory, cursor⟩ =
      ⟨.running ⟨next, memory.writeReg configuration.returnRegister 0, cursor⟩,
        RandomBit.Cost.ofCore
          ((Instruction.nset (.literal 0) configuration.returnRegister next).cost)⟩ := by
  have placementFetch : (placement client)[returnPc]? =
      some (.call op input output next) := by simp [placement, fetch, placementInstruction]
  let instruction := Linker.dispatcherCleanup configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1)
    (.call op input output next)
  have deterministicFetch := Linker.link_fetch_dispatcherCleanup (placement client) environment
    configuration returnPc _ placementFetch
  have randomFetch := link_fetch_tail client environment configuration
    (Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1)
    (dispatcher_after_client client environment (2 * returnPc + 1))
    instruction deterministicFetch
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (initial := ⟨Linker.dispatcherBase (placement client) environment + 2 * returnPc + 1,
      memory⟩)
    (next := ⟨next, memory.writeReg configuration.returnRegister 0⟩)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := Linker.dispatcher_cleanup_step (placement client) environment
      configuration returnPc op input output next memory placementFetch)

theorem dispatcher_before (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor returnPc index : Nat) (memory : Memory)
    (returnInRange : returnPc < client.length) (before : index < returnPc)
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    UniformReal.step (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * index, memory, cursor⟩ =
      ⟨.running
        ⟨Linker.dispatcherBase (placement client) environment + 2 * (index + 1),
          memory, cursor⟩,
        RandomBit.Cost.ofCore ((Instruction.ncompare
          (.reg configuration.returnRegister) (.literal index) 0 0 0).cost)⟩ := by
  have indexRange := before.trans returnInRange
  have sourceFetch : client[index]? = some client[index] := List.getElem?_eq_getElem indexRange
  have placementFetch : (placement client)[index]? =
      some (placementInstruction client[index]) := by simp [placement, sourceFetch]
  let instruction := Linker.dispatcherInstruction configuration
    (Linker.dispatcherBase (placement client) environment + 2 * index) index
  have deterministicFetch := Linker.link_fetch_dispatcher (placement client) environment
    configuration index _ placementFetch
  have randomFetch := link_fetch_tail client environment configuration _
    (dispatcher_after_client client environment _) instruction deterministicFetch
  exact core_running
    (deterministicProgram := deterministicArtifact client environment configuration)
    (randomProgram := link client environment configuration) (source := source)
    (cursor := cursor) (instruction := instruction)
    (initial := ⟨Linker.dispatcherBase (placement client) environment + 2 * index, memory⟩)
    (next := ⟨Linker.dispatcherBase (placement client) environment + 2 * (index + 1),
      memory⟩)
    (deterministicFetch := deterministicFetch) (randomFetch := randomFetch)
    (deterministicStep := Linker.dispatcher_step_before (placement client) environment
      configuration returnPc index memory (by simpa using returnInRange) before returnId)

theorem dispatcher_returns_from (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor returnPc index : Nat) (op : signature.Op)
    (input output : Region) (next : Nat) (memory : Memory)
    (fetch : client[returnPc]? = some (.call op input output next))
    (indexBefore : index ≤ returnPc)
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    RunningTrace (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment + 2 * index, memory, cursor⟩
      ⟨next, memory.writeReg configuration.returnRegister 0, cursor⟩
      (RandomBit.Cost.ofCore (Linker.dispatcherCostFrom returnPc index))
      (returnPc - index + 2) := by
  by_cases equal : index = returnPc
  · subst index
    have first := dispatcher_equal client environment configuration source cursor returnPc op
      input output next memory fetch returnId
    have second := dispatcher_cleanup client environment configuration source cursor returnPc op
      input output next memory fetch
    have combined := RunningTrace.next first (RunningTrace.one second)
    convert combined using 1
    · apply RandomBit.Cost.ext
      · funext coordinate
        change Linker.dispatcherCostFrom returnPc returnPc coordinate =
          (Instruction.ncompare (.reg configuration.returnRegister) (.literal returnPc)
            0 0 0).cost coordinate +
            (Instruction.nset (.literal 0) configuration.returnRegister next).cost coordinate
        simp [Linker.dispatcherCostFrom, Instruction.cost, NatOperand.reads]
      · rfl
    · omega
  · have before := lt_of_le_of_ne indexBefore equal
    have first := dispatcher_before client environment configuration source cursor returnPc index
      memory (List.getElem?_eq_some_iff.mp fetch |>.1) before returnId
    have recursive := dispatcher_returns_from client environment configuration source cursor
      returnPc (index + 1) op input output next memory fetch before returnId
    have combined := RunningTrace.next first recursive
    convert combined using 1
    · apply RandomBit.Cost.ext
      · funext coordinate
        change Linker.dispatcherCostFrom returnPc index coordinate =
          (Instruction.ncompare (.reg configuration.returnRegister) (.literal index)
            0 0 0).cost coordinate +
            Linker.dispatcherCostFrom returnPc (index + 1) coordinate
        simp [Linker.dispatcherCostFrom, Instruction.cost, NatOperand.reads]
        have subtract : returnPc - (index + 1) + 1 = returnPc - index := by omega
        rw [subtract]
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · rfl
    · omega
termination_by returnPc - index

theorem dispatcher_returns (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor returnPc : Nat) (op : signature.Op)
    (input output : Region) (next : Nat) (memory : Memory)
    (fetch : client[returnPc]? = some (.call op input output next))
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    RunningTrace (link client environment configuration) source
      ⟨Linker.dispatcherBase (placement client) environment, memory, cursor⟩
      ⟨next, memory.writeReg configuration.returnRegister 0, cursor⟩
      (RandomBit.Cost.ofCore (Linker.dispatcherCostFrom returnPc 0)) (returnPc + 2) := by
  simpa using dispatcher_returns_from client environment configuration source cursor returnPc 0
    op input output next memory fetch (Nat.zero_le _) returnId

theorem call_setup (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (source : UniformReal.Source) (cursor pc : Nat) (op : signature.Op)
    (input output : Region) (next : Nat) (memory : Memory)
    (fetch : client[pc]? = some (.call op input output next)) :
    UniformReal.step (link client environment configuration) source ⟨pc, memory, cursor⟩ =
      ⟨.running ⟨Linker.operationBase (placement client) environment op +
        (environment.implementation op).module.entry,
        memory.writeReg configuration.returnRegister pc, cursor⟩,
        RandomBit.Cost.ofCore
          ((Instruction.nset (.literal pc) configuration.returnRegister 0).cost)⟩ := by
  have randomFetch := link_fetch_client client environment configuration pc _ fetch
  simp [UniformReal.step, randomFetch, clientInstruction, Linker.clientInstruction,
    UniformReal.execute, UniformReal.liftCoreOutcome, RandomBit.Cost.ofCore,
    StructuredRealRAM.execute, NatOperand.eval, Instruction.cost]

/-- One abstract call expands to setup, every deterministic callee step, and dispatch. -/
theorem refine_call (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : UniformReal.Source) (cursor pc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region) (next : Nat)
    (input : (signature.contract op).Input) (validInput : (signature.contract op).pre input)
    (memory : Memory)
    (inputRep : (signature.contract op).inputLayout.RepAt inputRegion input memory)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (registerZero : memory.natReg configuration.returnRegister = 0) :
    ∃ linkedCoreCost linkedSteps,
      RunningTrace (link client environment configuration) source
        ⟨pc, memory, cursor⟩
        ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory, cursor⟩
        (RandomBit.Cost.ofCore linkedCoreCost) linkedSteps ∧
      linkedCoreCost ≤ signature.bound op input +
        Linker.concreteCallOverhead environment {
          callSite := pc
          op := op
          input := input
          output := environment.responder.answer op input
          outputCorrect := environment.responder.correct op input validInput
          chargedCost := signature.bound op input
          chargedCost_eq := rfl } := by
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
      (memory.writeReg configuration.returnRegister pc) := by
    rw [← inputRegionEq]
    exact Linker.inputRep_writeReg _ _ _ _ _ _ inputRep
  rcases implementation.restoringCorrect input validInput
      (memory.writeReg configuration.returnRegister pc) setupRep with
    ⟨run, outputRep, runBound, canonicalEffect⟩
  have setup := RunningTrace.one (call_setup client environment configuration source cursor pc op
    inputRegion outputRegion next memory fetch)
  rcases relocate_trace client environment configuration source cursor op run.trace with
    ⟨relocatedCost, relocated, relocatedBound⟩
  have returnId : run.final.natReg configuration.returnRegister = pc := by
    rw [canonicalEffect, Linker.writeAt_natReg]
    simp [Memory.writeReg]
  have returned := dispatcher_returns client environment configuration source cursor pc op
    inputRegion outputRegion next run.final fetch returnId
  have allSteps := setup.trans (relocated.trans returned)
  have finalMemory :
      run.final.writeReg configuration.returnRegister 0 =
        (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory := by
    rw [canonicalEffect, outputRegionEq]
    exact Linker.writeAt_setup_cleanup _ _ _ _ _ _ registerZero
  rw [finalMemory] at allSteps
  let linkedCoreCost :=
    (Instruction.nset (.literal pc) configuration.returnRegister 0).cost +
      (relocatedCost + Linker.dispatcherCostFrom pc 0)
  have normalized : RunningTrace (link client environment configuration) source
      ⟨pc, memory, cursor⟩
      ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
        (environment.responder.answer op input) memory, cursor⟩
      (RandomBit.Cost.ofCore linkedCoreCost) (1 + (run.steps + (pc + 2))) := by
    convert allSteps using 1
    apply RandomBit.Cost.ext <;> rfl
  refine ⟨linkedCoreCost, _, normalized, ?_⟩
  intro coordinate
  have relocatedCoordinate := relocatedBound coordinate
  have runCoordinate := runBound coordinate
  change
    (Instruction.nset (.literal pc) configuration.returnRegister 0).cost coordinate +
        (relocatedCost coordinate + Linker.dispatcherCostFrom pc 0 coordinate) ≤
      (signature.bound op input + Linker.concreteCallOverhead environment {
        callSite := pc
        op := op
        input := input
        output := environment.responder.answer op input
        outputCorrect := environment.responder.correct op input validInput
        chargedCost := signature.bound op input
        chargedCost_eq := rfl }) coordinate
  simp only [Linker.concreteCallOverhead, Pi.add_apply]
  simp only [Instruction.cost, NatOperand.reads, Cost.ofFields] at relocatedCoordinate runCoordinate ⊢
  simp only [Linker.dispatcherCostFrom, Nat.sub_zero]
  have linkedRun := relocatedCoordinate.trans runCoordinate
  calc
    _ ≤ ![1, 0, 0, 0, 0, 0, 0, 0, 0] coordinate +
        (signature.bound op input coordinate +
          ((pc + 1) * ![1, 0, 0, 0, 0, 0, 0, 0, 1] coordinate +
            ![1, 0, 0, 0, 0, 0, 0, 0, 0] coordinate)) :=
      Nat.add_le_add_left
        (Nat.add_le_add_right linkedRun
          ((pc + 1) * ![1, 0, 0, 0, 0, 0, 0, 0, 1] coordinate +
            ![1, 0, 0, 0, 0, 0, 0, 0, 0] coordinate)) _
    _ = _ := by ac_rfl

/-- A running random-client instruction preserves the linker-owned natural register. -/
theorem randomInstruction_preserves_register
    (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : UniformReal.Source) (initial next : UniformReal.Configuration)
    (instruction : UniformReal.Instruction)
    (fetch : client[initial.pc]? = some (.machine instruction))
    (observed : UniformReal.execute source instruction initial = ⟨.running next, cost⟩) :
    next.memory.natReg configuration.returnRegister =
      initial.memory.natReg configuration.returnRegister := by
  cases instruction with
  | core coreInstruction =>
      have placementFetch : (placement client)[initial.pc]? =
          some (.core coreInstruction) := by
        simp [placement, fetch, placementInstruction]
      have safe := compatible.clientAvoidsReturnRegister _ _ placementFetch
      simp only [UniformReal.execute, UniformReal.liftCoreOutcome] at observed
      generalize execution : StructuredRealRAM.execute coreInstruction initial.memory =
        coreObservation at observed
      cases coreObservation with
      | mk outcome coreCost =>
          cases outcome <;> cases observed
          exact Linker.instructionAvoids_preserves_register _ _ safe _ _ _ execution
  | sampleUniform destination successor =>
      simp only [UniformReal.execute] at observed
      cases observed
      rfl

/-- Flatten a complete relative random trace into one concrete same-source linked trace. -/
theorem refine_trace (client : UniformOpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Linker.Configuration)
    (compatible : Linker.Compatibility (placement client) environment configuration)
    (source : UniformReal.Source)
    {initial : UniformReal.Configuration} {final : Memory} {result : Real}
    {cost : UniformReal.Cost} {steps draws : Nat}
    {calls : List (DependencyCallRecord signature)}
    (trace : UniformOpenHaltingTrace signature environment.responder client source
      initial final result cost steps draws calls)
    (registerZero : initial.memory.natReg configuration.returnRegister = 0) :
    ∃ linkedCost linkedSteps,
      UniformReal.HaltingTrace (link client environment configuration) source
        initial final result linkedCost linkedSteps draws ∧
      linkedCost ≤ cost +
        RandomBit.Cost.ofCore (Linker.totalConcreteCallOverhead environment calls) := by
  induction trace with
  | halt openStep =>
      cases openStep with
      | machine fetch observed =>
          rename_i haltMemory haltResult haltCost haltDraws instruction
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨haltCost, 1, .halt ?_, ?_⟩
          · simp only [UniformReal.step, linkedFetch, clientInstruction]
            exact observed
          · rw [show Linker.totalConcreteCallOverhead environment [] = 0 by
                  rfl, randomCost_add_coreZero]
  | machine openStep tail induction =>
      rename_i current nextConfiguration final result headCost tailCost tailSteps draws calls
      cases openStep with
      | machine fetch observed =>
          have preserved := randomInstruction_preserves_register client environment configuration
            compatible source _ _ _ fetch observed
          have nextZero := preserved.trans registerZero
          rcases induction nextZero with
            ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨headCost + tailLinkedCost, tailLinkedSteps + 1, .next ?_ linkedTail, ?_⟩
          · simp only [UniformReal.step, linkedFetch, clientInstruction]
            exact observed
          · calc
              headCost + tailLinkedCost ≤
                  headCost + (tailCost + RandomBit.Cost.ofCore
                    (Linker.totalConcreteCallOverhead environment calls)) :=
                randomCost_add_mono le_rfl tailBound
              _ = (headCost + tailCost) + RandomBit.Cost.ofCore
                    (Linker.totalConcreteCallOverhead environment calls) :=
                (randomCost_add_assoc _ _ _).symm
  | call openStep tail induction =>
      rename_i current nextConfiguration final result headCost tailCost tailSteps draws call calls
      cases openStep with
      | call fetch inputRep validInput =>
          rename_i operation inputRegion outputRegion callNext input
          rcases refine_call client environment configuration compatible source _ _ _ _ _ _ _
              validInput _ inputRep fetch registerZero with
            ⟨callCoreCost, callSteps, linkedCall, callBound⟩
          have nextZero :
              ((signature.contract operation).outputLayout.writeAt outputRegion
                (environment.responder.answer operation input)
                current.memory).natReg configuration.returnRegister = 0 := by
            simpa only [Linker.writeAt_natReg] using registerZero
          rcases induction nextZero with
            ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          refine ⟨RandomBit.Cost.ofCore callCoreCost + tailLinkedCost,
            tailLinkedSteps + callSteps, linkedCall.thenHalting linkedTail, ?_⟩
          let callRecord : DependencyCallRecord signature := {
            callSite := current.pc
            op := operation
            input := input
            output := environment.responder.answer operation input
            outputCorrect := environment.responder.correct operation input validInput
            chargedCost := signature.bound operation input
            chargedCost_eq := rfl }
          have callRandomBound : RandomBit.Cost.ofCore callCoreCost ≤
              RandomBit.Cost.ofCore
                (signature.bound operation input +
                  Linker.concreteCallOverhead environment callRecord) := by
            apply ofCore_mono
            simpa [callRecord] using callBound
          calc
            RandomBit.Cost.ofCore callCoreCost + tailLinkedCost ≤
                RandomBit.Cost.ofCore
                    (signature.bound operation input +
                      Linker.concreteCallOverhead environment callRecord) +
                  (tailCost + RandomBit.Cost.ofCore
                    (Linker.totalConcreteCallOverhead environment calls)) :=
              randomCost_add_mono callRandomBound tailBound
            _ = (RandomBit.Cost.ofCore (signature.bound operation input) + tailCost) +
                RandomBit.Cost.ofCore
                  (Linker.totalConcreteCallOverhead environment (callRecord :: calls)) := by
              rw [ofCore_add]
              simp only [Linker.totalConcreteCallOverhead, List.map_cons, List.sum_cons]
              rw [ofCore_add]
              apply RandomBit.Cost.ext
              · funext coordinate
                change
                  (signature.bound operation input coordinate +
                      Linker.concreteCallOverhead environment callRecord coordinate) +
                    (tailCost.machine coordinate +
                      (calls.map (Linker.concreteCallOverhead environment)).sum coordinate) =
                  (signature.bound operation input coordinate + tailCost.machine coordinate) +
                    (Linker.concreteCallOverhead environment callRecord coordinate +
                      (calls.map (Linker.concreteCallOverhead environment)).sum coordinate)
                ac_rfl
              · change (0 + 0) + (tailCost.randomDraws + 0) =
                  (0 + tailCost.randomDraws) + (0 + 0)
                omega
            _ = _ := by simp [callRecord]

/-- Exact trace-side condition for choosing a public linked resource bound. -/
def BoundCovers
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (linkedBound : Nat → UniformReal.Cost) : Prop :=
  ∀ (source : UniformReal.Source) (input : problem.Input)
      (final : Memory) (result : Real) (cost : UniformReal.Cost)
      (steps draws : Nat) (calls : List (DependencyCallRecord signature)),
    problem.pre input →
    UniformOpenHaltingTrace signature environment.responder client.program source
      (RandomBit.Configuration.initial (problem.initialMemory input))
      final result cost steps draws calls →
    cost ≤ relativeBound (problem.inputSize input) →
    cost + RandomBit.Cost.ofCore (Linker.totalConcreteCallOverhead environment calls) ≤
      linkedBound (problem.inputSize input)

/-- Static, cost, and measurability obligations for automatic same-source publication. -/
structure LinkingAssumptions
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration)
    (linkedBound : Nat → UniformReal.Cost) : Prop where
  compatible : Linker.Compatibility (placement client.program) environment configuration
  returnRegisterInitiallyZero : ∀ input,
    (problem.initialMemory input).natReg configuration.returnRegister = 0
  boundCovers : BoundCovers client environment linkedBound
  /-- This is a probability-theory obligation, not an operational refinement callback. -/
  measurableSuccess : ∀ input, problem.pre input →
    MeasurableSet (problem.SuccessEvent
      (link client.program environment configuration) input
      (linkedBound (problem.inputSize input)))

/-- Relative termination under the implementation responder implies concrete linked termination. -/
theorem terminates
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration) (linkedBound : Nat → UniformReal.Cost)
    (assumptions : LinkingAssumptions client environment configuration linkedBound)
    (input : problem.Input) (validInput : problem.pre input) (source : UniformReal.Source) :
    problem.TerminatesWithin (link client.program environment configuration) input source
      (linkedBound (problem.inputSize input)) := by
  rcases client.terminates environment.responder input validInput source with
    ⟨output, final, result, cost, steps, draws, calls, trace, outputRep, relativeCost⟩
  rcases refine_trace client.program environment configuration assumptions.compatible source trace
      (assumptions.returnRegisterInitiallyZero input) with
    ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
  let run : problem.SuccessfulRun
      (link client.program environment configuration) input source := {
    final := final
    result := result
    cost := linkedCost
    steps := linkedSteps
    randomDraws := draws
    trace := linkedTrace }
  refine ⟨output, run, outputRep, ?_⟩
  exact linkedCostBound.trans
    (assumptions.boundCovers source input final result cost steps draws calls validInput
      trace relativeCost)

/-- Operational event transfer, independent of any measurability certificate. -/
theorem successEvent_mono_of
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration) (linkedBound : Nat → UniformReal.Cost)
    (compatible : Linker.Compatibility (placement client.program) environment configuration)
    (returnRegisterInitiallyZero : ∀ input,
      (problem.initialMemory input).natReg configuration.returnRegister = 0)
    (boundCovers : BoundCovers client environment linkedBound)
    (input : problem.Input) (validInput : problem.pre input) :
    UniformRelativeSuccessEvent signature environment.responder problem client.program
        relativeBound input ⊆
      problem.SuccessEvent (link client.program environment configuration) input
        (linkedBound (problem.inputSize input)) := by
  intro source success
  rcases success with
    ⟨output, final, result, cost, steps, draws, calls, trace, outputRep, correct,
      relativeCost⟩
  rcases refine_trace client.program environment configuration compatible source trace
      (returnRegisterInitiallyZero input) with
    ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
  let run : problem.SuccessfulRun
      (link client.program environment configuration) input source := {
    final := final
    result := result
    cost := linkedCost
    steps := linkedSteps
    randomDraws := draws
    trace := linkedTrace }
  refine ⟨output, run, outputRep, correct, ?_⟩
  exact linkedCostBound.trans
    (boundCovers source input final result cost steps draws calls validInput
      trace relativeCost)

/-- Every relative successful source remains successful after automatic concrete linking. -/
theorem successEvent_mono
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration) (linkedBound : Nat → UniformReal.Cost)
    (assumptions : LinkingAssumptions client environment configuration linkedBound)
    (input : problem.Input) (validInput : problem.pre input) :
    UniformRelativeSuccessEvent signature environment.responder problem client.program
        relativeBound input ⊆
      problem.SuccessEvent (link client.program environment configuration) input
        (linkedBound (problem.inputSize input)) :=
  successEvent_mono_of client environment configuration linkedBound assumptions.compatible
    assumptions.returnRegisterInitiallyZero assumptions.boundCovers input validInput

/-- Automatic publication with no user-supplied operational simulation. -/
def certificate
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration) (linkedBound : Nat → UniformReal.Cost)
    (assumptions : LinkingAssumptions client environment configuration linkedBound) :
    UniformRealRandomizedMachineProblem.BoundedTimeMonteCarloAlgorithmCertificate
      problem linkedBound failure where
  program := link client.program environment configuration
  valid := link_valid client.program environment configuration client.valid
  measurableSuccess := assumptions.measurableSuccess
  solves input validInput := by
    constructor
    · exact terminates client environment configuration linkedBound assumptions input validInput
    · change UniformReal.sourceLaw
          (problem.SuccessEvent (link client.program environment configuration) input
            (linkedBound (problem.inputSize input))) ≥ 1 - (failure input : ENNReal)
      exact (client.successProbability environment.responder input validInput).trans
        (measure_mono (successEvent_mono client environment configuration linkedBound assumptions
          input validInput))

/-- One-line existential discharge through the automatic same-source linker. -/
theorem hasBoundedTimeMonteCarloAlgorithm
    {signature : DependencySignature} {problem : UniformRealRandomizedMachineProblem}
    {relativeBound : Nat → UniformReal.Cost} {failure : problem.Input → Probability}
    (client : UniformRelativeAlgorithmCertificate signature problem relativeBound failure)
    (environment : ImplementationEnvironment signature)
    (configuration : Linker.Configuration) (linkedBound : Nat → UniformReal.Cost)
    (assumptions : LinkingAssumptions client environment configuration linkedBound) :
    problem.HasBoundedTimeMonteCarloAlgorithm linkedBound failure :=
  ⟨certificate client environment configuration linkedBound assumptions⟩

/-- Compatibility name for the explicitly bounded-time discharge theorem. -/
abbrev hasAlgorithm := @hasBoundedTimeMonteCarloAlgorithm

end

end Algolean.Algorithms.StructuredRealRAM.UniformRealLinker
