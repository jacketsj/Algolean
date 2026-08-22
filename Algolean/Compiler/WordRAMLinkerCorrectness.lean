/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.WordRAMLinker

/-!
# Operational correctness of the shared-body Word-RAM linker

The lemmas here transform callee instructions and traces one fetched instruction at a time.  A
linked call never executes a host callback and never collapses the callee to one charged step.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.Linker

def addressOperandAvoids (reserved : Nat) : RAM.AddressOperand (BitVec w) → Prop
  | .immediate _ => True
  | .reg register => register ≠ reserved

def operandAvoids (reserved : Nat) : RAM.Operand (BitVec w) (BitVec w) → Prop
  | .immediate _ => True
  | .load address => addressOperandAvoids reserved address

/-- Static noninterference check for the linker-owned return register. -/
def instructionAvoids (reserved : Nat) :
    RAM.Instruction (BitVec w) (BitVec w) Empty → Prop
  | .set source destination _ | .neg source destination _ =>
      operandAvoids reserved source ∧ addressOperandAvoids reserved destination
  | .add left right destination _ | .sub left right destination _
  | .mul left right destination _ | .div left right destination _ =>
      operandAvoids reserved left ∧ operandAvoids reserved right ∧
        addressOperandAvoids reserved destination
  | .setAddress source destination _ =>
      addressOperandAvoids reserved source ∧ destination ≠ reserved
  | .addAddress left right destination _ | .subAddress left right destination _ =>
      addressOperandAvoids reserved left ∧ addressOperandAvoids reserved right ∧
        destination ≠ reserved
  | .compare left right _ _ _ =>
      operandAvoids reserved left ∧ operandAvoids reserved right
  | .compareAddress left right _ _ _ =>
      addressOperandAvoids reserved left ∧ addressOperandAvoids reserved right
  | .extra impossible _ => nomatch impossible
  | .halt result => operandAvoids reserved result

/-- Static and ABI obligations needed by the generic linker proof. -/
structure Compatibility {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) : Prop where
  clientFits : client.length ≤ 2 ^ w
  clientAvoidsReturnRegister : ∀ (pc : Nat)
      (instruction : RAM.Instruction (BitVec w) (BitVec w) Empty),
    client[pc]? = some (OpenInstruction.core instruction) →
      instructionAvoids configuration.jumpRegister instruction
  inputRegion_eq : ∀ (pc : Nat) (op : signature.Op)
      (inputRegion outputRegion : Region w) (next : Nat),
    client[pc]? = some (OpenInstruction.call op inputRegion outputRegion next) →
      inputRegion = (environment.implementation op).calling.inputRegion
  outputRegion_eq : ∀ (pc : Nat) (op : signature.Op)
      (inputRegion outputRegion : Region w) (next : Nat),
    client[pc]? = some (OpenInstruction.call op inputRegion outputRegion next) →
      outputRegion = (environment.implementation op).calling.outputRegion

/-- Exact implementation-specific overhead attached to one dynamic relative call. -/
def concreteCallOverhead (environment : ImplementationEnvironment signature)
    (call : DependencyCallRecord signature) : Nat :=
  (environment.implementation call.op).calling.callOverhead + call.callSite + 2

def totalConcreteCallOverhead (environment : ImplementationEnvironment signature)
    (calls : List (DependencyCallRecord signature)) : Nat :=
  (calls.map (concreteCallOverhead environment)).sum

@[simp] theorem writeAt_address (layout : WordLayout w alpha) (region : Region w)
    (value : alpha) (memory : Memory w) (register : Nat) :
    (layout.writeAt region value memory).address register = memory.address register := rfl

theorem writeAt_setup_cleanup (layout : WordLayout w alpha) (region : Region w)
    (value : alpha) (memory : Memory w) (register : Nat) (identifier : BitVec w)
    (initialZero : memory.address register = 0) :
    (layout.writeAt region value (memory.writeAddress register identifier)).writeAddress
        register 0 = layout.writeAt region value memory := by
  simp [WordLayout.writeAt, RAM.Memory.writeAddress, initialZero]

theorem inputRep_writeAddress (layout : WordLayout w alpha) (region : Region w)
    (value : alpha) (memory : Memory w) (register : Nat) (word : BitVec w)
    (represented : layout.RepAt region value memory) :
    layout.RepAt region value (memory.writeAddress register word) := by
  exact ⟨represented.1, fun index inRange ↦ represented.2 index inRange⟩

/-- A safe client core step preserves the linker-owned address register. -/
theorem instructionAvoids_preserves_register (instruction :
    RAM.Instruction (BitVec w) (BitVec w) Empty) (reserved : Nat)
    (safe : instructionAvoids reserved instruction) (memory : Memory w)
    (next : WordRAM.Configuration w)
    (executes : RAM.execute (WordRAM.ops w) RAM.noExtra instruction memory = .running next) :
    next.memory.address reserved = memory.address reserved := by
  cases instruction with
  | set | add | sub | mul | div | neg | compare | compareAddress =>
      simp only [RAM.execute] at executes
      injection executes with equal
      subst next
      rfl
  | setAddress source destination pc =>
      rcases safe with ⟨_, destinationSafe⟩
      simp only [RAM.execute] at executes
      injection executes with equal
      subst next
      simpa only [RAM.Memory.writeAddress] using
        (Function.update_of_ne destinationSafe.symm
          (RAM.AddressOperand.eval memory source) memory.address)
  | addAddress left right destination pc =>
      rcases safe with ⟨_, _, destinationSafe⟩
      simp only [RAM.execute] at executes
      injection executes with equal
      subst next
      simpa only [RAM.Memory.writeAddress] using
        (Function.update_of_ne destinationSafe.symm
          ((WordRAM.ops w).addressAdd
            (RAM.AddressOperand.eval memory left)
            (RAM.AddressOperand.eval memory right)) memory.address)
  | subAddress left right destination pc =>
      rcases safe with ⟨_, _, destinationSafe⟩
      simp only [RAM.execute] at executes
      injection executes with equal
      subst next
      simpa only [RAM.Memory.writeAddress] using
        (Function.update_of_ne destinationSafe.symm
          ((WordRAM.ops w).addressSub
            (RAM.AddressOperand.eval memory left)
            (RAM.AddressOperand.eval memory right)) memory.address)
  | extra impossible pc => exact Empty.elim impossible
  | halt result => cases executes

/-- A finite sequence of running transitions, used for call and return segments. -/
inductive RunningTrace
    (step : WordRAM.Configuration w →
      RAM.StepObservation (BitVec w) (BitVec w) Nat) :
    WordRAM.Configuration w → WordRAM.Configuration w → Nat → Nat → Prop where
  | one {initial final cost}
      (observes : step initial = ⟨.running final, cost⟩) :
      RunningTrace step initial final cost 1
  | next {initial middle final headCost tailCost tailSteps}
      (observes : step initial = ⟨.running middle, headCost⟩)
      (tail : RunningTrace step middle final tailCost tailSteps) :
      RunningTrace step initial final (headCost + tailCost) (tailSteps + 1)

/-- Prefix a halting trace by a finite running segment. -/
theorem RunningTrace.thenHalting
    (runningPrefix : RunningTrace step initial middle prefixCost prefixSteps)
    (suffix : RAM.HaltingTrace step middle final result suffixCost suffixSteps) :
    RAM.HaltingTrace step initial final result
      (prefixCost + suffixCost) (suffixSteps + prefixSteps) := by
  induction runningPrefix with
  | one observes =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RAM.HaltingTrace.next observes suffix
  | next observes tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RAM.HaltingTrace.next observes (ih suffix)

/-- Concatenate two finite running segments without hiding either segment's cost. -/
theorem RunningTrace.trans
    (first : RunningTrace step initial middle firstCost firstSteps)
    (second : RunningTrace step middle final secondCost secondSteps) :
    RunningTrace step initial final
      (firstCost + secondCost) (firstSteps + secondSteps) := by
  induction first with
  | one observes =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RunningTrace.next observes second
  | next observes tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RunningTrace.next observes (ih second)

theorem relocate_execute_running (base dispatcher : Nat)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) Empty)
    (memory : Memory w) (next : WordRAM.Configuration w)
    (executes : RAM.execute (WordRAM.ops w) RAM.noExtra instruction memory = .running next) :
    RAM.execute (WordRAM.ops w) RAM.noExtra
      (relocateInstruction base dispatcher instruction) memory =
      .running ⟨base + next.pc, next.memory⟩ := by
  cases instruction <;>
    simp only [RAM.execute, relocateInstruction, RAM.Operand.eval,
      RAM.AddressOperand.eval] at executes ⊢ <;>
    try { cases executes; rfl }
  case compare =>
    cases executes
    generalize (WordRAM.ops w).compare _ _ = ordering
    cases ordering <;> rfl
  case compareAddress =>
    cases executes
    generalize (WordRAM.ops w).addressCompare _ _ = ordering
    cases ordering <;> rfl
  case halt => cases executes
  case extra impossible next => exact Empty.elim impossible

theorem relocate_execute_halted (base dispatcher : Nat)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) Empty)
    (memory final : Memory w) (result : BitVec w)
    (executes : RAM.execute (WordRAM.ops w) RAM.noExtra instruction memory =
      .halted final result) :
    RAM.execute (WordRAM.ops w) RAM.noExtra
      (relocateInstruction base dispatcher instruction) memory =
      .running ⟨dispatcher, final⟩ := by
  cases instruction <;>
    simp only [RAM.execute, relocateInstruction, RAM.Operand.eval,
      RAM.AddressOperand.eval] at executes ⊢ <;>
    try { cases executes }
  case halt => cases executes; rfl

/--
Relocate a complete certified callee trace into its one shared body.  The final halt becomes one
ordinary return transition to the dispatcher, so linked cost and step count equal the callee's
full original cost and step count.
-/
theorem relocate_trace {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (op : signature.Op)
    {localInitial : WordRAM.Configuration w} {final : Memory w} {result : BitVec w}
    {cost steps : Nat}
    (trace : RAM.HaltingTrace
      (WordRAM.stepCosted (environment.implementation op).module.code)
      localInitial final result cost steps) :
    RunningTrace (WordRAM.stepCosted (link client environment configuration))
      ⟨operationBase client environment op + localInitial.pc, localInitial.memory⟩
      ⟨dispatcherBase client environment, final⟩
      cost steps := by
  induction trace with
  | halt observes =>
      rename_i calleeConfig calleeFinal calleeResult calleeCost
      simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
        RAM.CostedSemantics.step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have linkedFetch := link_fetch_implementation client environment configuration op _ _ fetch
        apply RunningTrace.one
        simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
          RAM.CostedSemantics.step, linkedFetch, RAM.CostedSemantics.unit]
        have originalExecution :
            RAM.execute (WordRAM.ops w) RAM.noExtra instruction calleeConfig.memory =
              .halted calleeFinal calleeResult := by
          simpa [RAM.CostedSemantics.unit] using
            congrArg RAM.StepObservation.outcome observes
        have originalCost : (1 : Nat) = calleeCost := by
          simpa [RAM.CostedSemantics.unit] using
            congrArg RAM.StepObservation.cost observes
        have relocated := relocate_execute_halted
          (operationBase client environment op) (dispatcherBase client environment)
          instruction calleeConfig.memory calleeFinal calleeResult
          originalExecution
        rw [relocated]
        cases originalCost
        rfl
  | next observes tail ih =>
      rename_i calleeConfig calleeNext calleeFinal calleeResult calleeHeadCost
        calleeTailCost calleeSteps
      simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
        RAM.CostedSemantics.step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have linkedFetch := link_fetch_implementation client environment configuration op _ _ fetch
        apply RunningTrace.next
        · simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
            RAM.CostedSemantics.step, linkedFetch, RAM.CostedSemantics.unit]
          have originalExecution :
              RAM.execute (WordRAM.ops w) RAM.noExtra instruction calleeConfig.memory =
                .running calleeNext := by
            simpa [RAM.CostedSemantics.unit] using
              congrArg RAM.StepObservation.outcome observes
          have originalCost : (1 : Nat) = calleeHeadCost := by
            simpa [RAM.CostedSemantics.unit] using
              congrArg RAM.StepObservation.cost observes
          have relocated := relocate_execute_running
            (operationBase client environment op) (dispatcherBase client environment)
            instruction calleeConfig.memory calleeNext
            originalExecution
          rw [relocated]
          cases originalCost
          rfl
        · exact ih

private theorem ofNat_injective_below {w left right : Nat}
    (leftBelow : left < 2 ^ w) (rightBelow : right < 2 ^ w)
    (different : left ≠ right) :
    BitVec.ofNat w left ≠ BitVec.ofNat w right := by
  intro equal
  have := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBelow,
    Nat.mod_eq_of_lt rightBelow] at this
  exact different this

/-- Matching a return id performs one ordinary comparison and resumes the client continuation. -/
theorem dispatcher_step_equal {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w pc) :
    WordRAM.stepCosted (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * pc, memory⟩ =
      ⟨.running ⟨dispatcherBase client environment + 2 * pc + 1, memory⟩, 1⟩ := by
  have linkedFetch := link_fetch_dispatcher client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
    linkedFetch, dispatcherInstruction, RAM.CostedSemantics.unit, RAM.execute,
    RAM.AddressOperand.eval, returnId, WordRAM.ops, RAM.branch]

/-- The matching cleanup slot restores the reserved register and resumes the client. -/
theorem dispatcher_cleanup_step {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next)) :
    WordRAM.stepCosted (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * pc + 1, memory⟩ =
      ⟨.running ⟨next, memory.writeAddress configuration.jumpRegister 0⟩, 1⟩ := by
  have linkedFetch := link_fetch_dispatcherCleanup client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
    linkedFetch, dispatcherCleanup, RAM.CostedSemantics.unit, RAM.execute,
    RAM.AddressOperand.eval]

/-- A smaller dispatcher slot takes one charged comparison step toward the matching id. -/
theorem dispatcher_step_before {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (returnPc index : Nat) (memory : Memory w)
    (returnInRange : returnPc < client.length) (before : index < returnPc)
    (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    WordRAM.stepCosted (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * index, memory⟩ =
      ⟨.running ⟨dispatcherBase client environment + 2 * (index + 1), memory⟩, 1⟩ := by
  have indexInRange : index < client.length := before.trans returnInRange
  have fetch : client[index]? = some client[index] := List.getElem?_eq_getElem indexInRange
  have linkedFetch := link_fetch_dispatcher client environment configuration index
    client[index] fetch
  have returnBelow : returnPc < 2 ^ w := returnInRange.trans_le clientFits
  have indexBelow : index < 2 ^ w := indexInRange.trans_le clientFits
  have wordsDifferent : BitVec.ofNat w returnPc ≠ BitVec.ofNat w index :=
    ofNat_injective_below returnBelow indexBelow (Nat.ne_of_gt before)
  have returnToNat : (BitVec.ofNat w returnPc).toNat = returnPc := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt returnBelow]
  have indexToNat : (BitVec.ofNat w index).toNat = index := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBelow]
  have returnNotBelowIndex : ¬ returnPc < index := Nat.not_lt_of_ge (Nat.le_of_lt before)
  cases instructionAtIndex : client[index] with
  | core instruction =>
      simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
        linkedFetch, dispatcherInstruction, RAM.CostedSemantics.unit, RAM.execute,
        RAM.AddressOperand.eval, returnId, WordRAM.ops,
        returnToNat, indexToNat, returnNotBelowIndex, wordsDifferent,
        instructionAtIndex, RAM.branch, Nat.add_assoc, Nat.mul_add]
  | call operation input output next =>
      simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
        linkedFetch, dispatcherInstruction, RAM.CostedSemantics.unit, RAM.execute,
        RAM.AddressOperand.eval, returnId, WordRAM.ops,
        returnToNat, indexToNat, returnNotBelowIndex, wordsDifferent,
        instructionAtIndex, RAM.branch, Nat.add_assoc, Nat.mul_add]

/-- Dispatcher comparisons are all present in the same linked execution trace. -/
theorem dispatcher_returns_from {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (returnPc index : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[returnPc]? = some (.call op inputRegion outputRegion next))
    (indexBefore : index ≤ returnPc) (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RunningTrace (WordRAM.stepCosted (link client environment configuration))
      ⟨dispatcherBase client environment + 2 * index, memory⟩
      ⟨next, memory.writeAddress configuration.jumpRegister 0⟩
      (returnPc - index + 2) (returnPc - index + 2) := by
  by_cases equal : index = returnPc
  · subst index
    have equalStep := dispatcher_step_equal client environment configuration returnPc op
      inputRegion outputRegion next memory fetch returnId
    have cleanupStep := dispatcher_cleanup_step client environment configuration returnPc op
      inputRegion outputRegion next memory fetch
    simpa using RunningTrace.next equalStep (RunningTrace.one cleanupStep)
  · have before : index < returnPc := lt_of_le_of_ne indexBefore equal
    have nextBefore : index + 1 ≤ returnPc := before
    have first := dispatcher_step_before client environment configuration returnPc index memory
      (List.getElem?_eq_some_iff.mp fetch |>.1) before clientFits returnId
    have recursive := dispatcher_returns_from client environment configuration returnPc
      (index + 1) op inputRegion outputRegion next memory fetch nextBefore clientFits returnId
    have combined := RunningTrace.next first recursive
    convert combined using 1 <;> omega
termination_by returnPc - index

/-- Start-to-return specialization used by the whole-program linker simulation. -/
theorem dispatcher_returns {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (returnPc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[returnPc]? = some (.call op inputRegion outputRegion next))
    (clientFits : client.length ≤ 2 ^ w)
    (returnId : memory.address configuration.jumpRegister = BitVec.ofNat w returnPc) :
    RunningTrace (WordRAM.stepCosted (link client environment configuration))
      ⟨dispatcherBase client environment, memory⟩
      ⟨next, memory.writeAddress configuration.jumpRegister 0⟩
      (returnPc + 2) (returnPc + 2) := by
  simpa using dispatcher_returns_from client environment configuration returnPc 0 op
    inputRegion outputRegion next memory fetch (Nat.zero_le _) clientFits returnId

/-- A relative call site expands to one ordinary setup instruction. -/
theorem call_setup_step {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (op : signature.Op)
    (inputRegion outputRegion : Region w) (next : Nat) (memory : Memory w)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next)) :
    WordRAM.stepCosted (link client environment configuration) ⟨pc, memory⟩ =
      ⟨.running ⟨operationBase client environment op +
          (environment.implementation op).module.entry,
        memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc)⟩, 1⟩ := by
  have linkedFetch := link_fetch_client client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [WordRAM.stepCosted, WordRAM.costedSemantics, RAM.CostedSemantics.step,
    linkedFetch, clientInstruction, RAM.CostedSemantics.unit, RAM.execute,
    RAM.AddressOperand.eval]

/--
One contract-relative call is refined by setup, the complete certified callee trace, the shared
dispatcher, and cleanup.  The resulting memory is exactly the abstract structural overwrite.
-/
theorem refine_call {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (compatible : Compatibility client environment configuration)
    (pc : Nat) (op : signature.Op) (inputRegion outputRegion : Region w) (next : Nat)
    (input : (signature.contract op).Input) (validInput : (signature.contract op).pre input)
    (memory : Memory w)
    (inputRep : (signature.contract op).inputLayout.RepAt inputRegion input memory)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (registerZero : memory.address configuration.jumpRegister = 0) :
    ∃ linkedCost linkedSteps,
      RunningTrace (WordRAM.stepCosted (link client environment configuration))
        ⟨pc, memory⟩
        ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory⟩
        linkedCost linkedSteps ∧
      linkedCost ≤ signature.bound op input + 1 +
        concreteCallOverhead environment {
          callSite := pc
          op := op
          input := input
          output := environment.responder.answer op input
          outputCorrect := environment.responder.correct op input validInput
          chargedCost := signature.bound op input + 1
          chargedCost_eq := rfl } := by
  let implementation := environment.implementation op
  have inputRegionEq := compatible.inputRegion_eq pc op inputRegion outputRegion next fetch
  have outputRegionEq := compatible.outputRegion_eq pc op inputRegion outputRegion next fetch
  have setupRep : (signature.contract op).inputLayout.RepAt
      implementation.calling.inputRegion input
      (memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc)) := by
    rw [← inputRegionEq]
    exact inputRep_writeAddress _ _ _ _ _ _ inputRep
  rcases implementation.correct input validInput
      (memory.writeAddress configuration.jumpRegister (BitVec.ofNat w pc)) setupRep with
    ⟨run, outputRep, costBound, frame, canonicalEffect⟩
  have setup := RunningTrace.one (call_setup_step client environment configuration pc op
    inputRegion outputRegion next memory fetch)
  have relocated := relocate_trace client environment configuration op run.trace
  have returnId : run.final.address configuration.jumpRegister = BitVec.ofNat w pc := by
    rw [canonicalEffect, writeAt_address]
    simp [RAM.Memory.writeAddress]
  have returned := dispatcher_returns client environment configuration pc op inputRegion
    outputRegion next run.final fetch compatible.clientFits returnId
  have allSteps := setup.trans (relocated.trans returned)
  have finalMemory :
      run.final.writeAddress configuration.jumpRegister 0 =
        (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory := by
    rw [canonicalEffect, outputRegionEq]
    exact writeAt_setup_cleanup _ _ _ _ _ _ registerZero
  rw [finalMemory] at allSteps
  refine ⟨_, _, allSteps, ?_⟩
  simp only [concreteCallOverhead]
  change run.cost ≤ signature.bound op input +
    (environment.implementation op).calling.callOverhead at costBound
  omega

/--
Flatten a complete relative execution into one ordinary linked-machine trace.  Each dependency
call contributes the full certified callee trace plus explicit setup/dispatch overhead.
-/
theorem refine_trace {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (compatible : Compatibility client environment configuration)
    {initial : WordRAM.Configuration w} {final : Memory w} {result : BitVec w}
    {cost : Nat} {calls : List (DependencyCallRecord signature)}
    (trace : OpenHaltingTrace signature environment.responder client
      initial final result cost calls)
    (registerZero : initial.memory.address configuration.jumpRegister = 0) :
    ∃ linkedCost linkedSteps,
      RAM.HaltingTrace (WordRAM.stepCosted (link client environment configuration))
        initial final result linkedCost linkedSteps ∧
      linkedCost ≤ cost + totalConcreteCallOverhead environment calls := by
  induction trace with
  | halt openStep =>
      cases openStep with
      | core fetch execute =>
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨1, 1, RAM.HaltingTrace.halt ?_, ?_⟩
          · simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
              RAM.CostedSemantics.step, linkedFetch, clientInstruction,
              RAM.CostedSemantics.unit]
            rw [execute]
          · simp [totalConcreteCallOverhead]
  | next openStep tail ih =>
      cases openStep with
      | core fetch execute =>
          have safe := compatible.clientAvoidsReturnRegister _ _ fetch
          have preserved := instructionAvoids_preserves_register _ _ safe _ _ execute
          have nextZero : _ := preserved.trans registerZero
          rcases ih nextZero with ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨1 + tailLinkedCost, tailLinkedSteps + 1,
            RAM.HaltingTrace.next ?_ linkedTail, ?_⟩
          · simp only [WordRAM.stepCosted, WordRAM.costedSemantics,
              RAM.CostedSemantics.step, linkedFetch, clientInstruction,
              RAM.CostedSemantics.unit]
            rw [execute]
          · simpa only [Option.toList_none, List.nil_append, Nat.add_assoc] using
              Nat.add_le_add_left tailBound 1
      | call fetch inputRep validInput =>
          rcases refine_call client environment configuration compatible _ _ _ _ _ _ validInput
              _ inputRep fetch registerZero with
            ⟨callCost, callSteps, linkedCall, callBound⟩
          rcases ih (by simpa only [writeAt_address] using registerZero) with
            ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          refine ⟨callCost + tailLinkedCost, tailLinkedSteps + callSteps,
            linkedCall.thenHalting linkedTail, ?_⟩
          simp only [totalConcreteCallOverhead] at tailBound
          simp only [Option.toList_some, List.singleton_append,
            totalConcreteCallOverhead, List.map_cons, List.sum_cons]
          omega

end Algolean.Algorithms.WordRAM.Linker
