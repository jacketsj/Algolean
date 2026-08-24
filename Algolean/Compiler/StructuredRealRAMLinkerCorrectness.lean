/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Compiler.StructuredRealRAMLinker

/-!
# Operational correctness of the structured exact-real/natural RAM linker

The simulation in this module expands every relative call into setup, every transition of the
certified callee, shared-dispatch traversal, and cleanup.  It therefore turns a relative proof
and a completed implementation environment into an unconditional certificate without asking an
integration module to repeat the caller's correctness proof.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.Linker

noncomputable section

/-- A core instruction avoids modifying the linker-owned natural register. -/
def instructionAvoids (reserved : Nat) : Instruction → Prop
  | .nset _ destination _ | .nadd _ _ destination _ | .nsub _ _ destination _
  | .nmul _ _ destination _ | .nload _ destination _ => destination ≠ reserved
  | _ => True

/-- Static ABI and register obligations needed by the generic linker simulation. -/
structure Compatibility {signature : DependencySignature}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration) : Prop where
  clientAvoidsReturnRegister : ∀ (pc : Nat) (instruction : Instruction),
    client[pc]? = some (OpenInstruction.core instruction) →
      instructionAvoids configuration.returnRegister instruction
  inputRegion_eq : ∀ (pc : Nat) (op : signature.Op)
      (inputRegion outputRegion : Region) (next : Nat),
    client[pc]? = some (OpenInstruction.call op inputRegion outputRegion next) →
      inputRegion = (environment.implementation op).calling.inputRegion
  outputRegion_eq : ∀ (pc : Nat) (op : signature.Op)
      (inputRegion outputRegion : Region) (next : Nat),
    client[pc]? = some (OpenInstruction.call op inputRegion outputRegion next) →
      outputRegion = (environment.implementation op).calling.outputRegion

/-- Exact implementation-specific overhead added to one dynamic call. -/
@[nolint unusedArguments]
def concreteCallOverhead (_environment : ImplementationEnvironment signature)
    (call : DependencyCallRecord signature) : Cost :=
  (Instruction.nset (.literal call.callSite) 0 0).cost +
    (fun coordinate =>
      (call.callSite + 1) * (Instruction.ncompare (.literal 0) (.literal 0) 0 0 0).cost coordinate +
        (Instruction.nset (.literal 0) 0 0).cost coordinate)

/-- Sum of all concrete call overheads in a relative trace. -/
def totalConcreteCallOverhead (environment : ImplementationEnvironment signature)
    (calls : List (DependencyCallRecord signature)) : Cost :=
  (calls.map (concreteCallOverhead environment)).sum

@[simp] theorem writeAt_natReg (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) (register : Nat) :
    (layout.writeAt region value memory).natReg register = memory.natReg register := rfl

theorem writeAt_setup_cleanup (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) (register identifier : Nat)
    (initialZero : memory.natReg register = 0) :
    (layout.writeAt region value (memory.writeReg register identifier)).writeReg register 0 =
      layout.writeAt region value memory := by
  simp [Layout.writeAt, Memory.writeReg, initialZero]

theorem inputRep_writeReg (layout : Layout alpha) (region : Region)
    (value : alpha) (memory : Memory) (register word : Nat)
    (represented : layout.RepAt region value memory) :
    layout.RepAt region value (memory.writeReg register word) := by
  exact ⟨represented.1, represented.2.1, represented.2.2.1, represented.2.2.2⟩

/-- A compatible client core step preserves the linker-owned register. -/
theorem instructionAvoids_preserves_register (instruction : Instruction) (reserved : Nat)
    (safe : instructionAvoids reserved instruction) (memory : Memory)
    (next : Algolean.Algorithms.StructuredRealRAM.Configuration)
    (cost : Cost) (executes : execute instruction memory = ⟨.running next, cost⟩) :
    next.memory.natReg reserved = memory.natReg reserved := by
  cases instruction <;> simp only [execute] at executes <;> cases executes <;>
    simp_all [instructionAvoids, Memory.writeReal, Memory.writeNat, Memory.writeReg] <;>
    rw [Function.update_of_ne (Ne.symm safe)]

/-- A finite sequence of running transitions. -/
inductive RunningTrace (program : Program) :
    Algolean.Algorithms.StructuredRealRAM.Configuration →
      Algolean.Algorithms.StructuredRealRAM.Configuration → Cost → Nat → Prop where
  | one {initial final cost}
      (observes : step program initial = ⟨.running final, cost⟩) :
      RunningTrace program initial final cost 1
  | next {initial middle final headCost tailCost tailSteps}
      (observes : step program initial = ⟨.running middle, headCost⟩)
      (tail : RunningTrace program middle final tailCost tailSteps) :
      RunningTrace program initial final (headCost + tailCost) (tailSteps + 1)

/-- Prefix a halting trace by a finite running segment. -/
theorem RunningTrace.thenHalting
    (runningPrefix : RunningTrace program initial middle prefixCost prefixSteps)
    (suffix : HaltingTrace program middle final result suffixCost suffixSteps) :
    HaltingTrace program initial final result (prefixCost + suffixCost)
      (suffixSteps + prefixSteps) := by
  induction runningPrefix with
  | one observes =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using HaltingTrace.next observes suffix
  | next observes tail induction =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using
        HaltingTrace.next observes (induction suffix)

/-- Concatenate two finite running segments. -/
theorem RunningTrace.trans
    (first : RunningTrace program initial middle firstCost firstSteps)
    (second : RunningTrace program middle final secondCost secondSteps) :
    RunningTrace program initial final (firstCost + secondCost)
      (firstSteps + secondSteps) := by
  induction first with
  | one observes =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using RunningTrace.next observes second
  | next observes tail induction =>
      simpa [add_assoc, Nat.add_comm, Nat.add_left_comm] using
        RunningTrace.next observes (induction second)

/-- Total code before an operation, exposed as concrete syntax for placement proofs. -/
def bodiesBefore (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) :
    List signature.Op → signature.Op → Program
  | [], _ => []
  | current :: rest, op =>
      if current = op then []
      else implementationBody client environment current ++ bodiesBefore client environment rest op

/-- Concrete code after an operation, used only for placement proofs. -/
def bodiesAfter (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) :
    List signature.Op → signature.Op → Program
  | [], _ => []
  | current :: rest, op =>
      if current = op then rest.flatMap (implementationBody client environment)
      else bodiesAfter client environment rest op

theorem bodiesBefore_length (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (items : List signature.Op)
    (op : signature.Op) :
    (bodiesBefore client environment items op).length = codeBefore environment items op := by
  induction items with
  | nil => rfl
  | cons current rest induction =>
      simp only [bodiesBefore, codeBefore]
      split
      · rfl
      · simp [implementationBody, induction]

theorem bodies_split (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (items : List signature.Op)
    (op : signature.Op) (member : op ∈ items) :
    items.flatMap (implementationBody client environment) =
      bodiesBefore client environment items op ++ implementationBody client environment op ++
        bodiesAfter client environment items op := by
  induction items with
  | nil => simp at member
  | cons current rest induction =>
      simp only [List.mem_cons] at member
      by_cases equal : current = op
      · subst current
        simp [bodiesBefore, bodiesAfter]
      · have tailMember : op ∈ rest := member.resolve_left (fun same => equal same.symm)
        simp only [List.flatMap_cons, bodiesBefore, bodiesAfter, if_neg equal]
        rw [induction tailMember]
        simp [List.append_assoc]

theorem mem_operations (op : signature.Op) : op ∈ operations signature := by
  simp [operations]

/-- The linker materializes each implementation body exactly once. -/
theorem sharedBody_count (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) :
    ((operations signature).flatMap (implementationBody client environment)).length =
      implementationCodeSize environment := by
  simp [implementationBody, implementationCodeSize]

/-- Fetching a linked client pc yields its compiled instruction. -/
theorem link_fetch_client (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[pc]? =
      some (clientInstruction client environment configuration pc instruction) := by
  have pcInRange : pc < client.length := List.getElem?_eq_some_iff.mp fetch |>.1
  unfold link
  rw [List.getElem?_append_left]
  · rw [List.getElem?_append_left]
    · simp [clientCode, fetch]
    · simpa [clientCode] using pcInRange
  · simp only [List.length_append]
    rw [clientCode_length]
    omega

/-- Fetching inside a shared implementation body returns the relocated local instruction. -/
theorem link_fetch_implementation (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (op : signature.Op) (pc : Nat) (instruction : Instruction)
    (fetch : (environment.implementation op).module.code[pc]? = some instruction) :
    (link client environment configuration)[operationBase client environment op + pc]? =
      some (relocateInstruction (operationBase client environment op)
        (dispatcherBase client environment) instruction) := by
  have pcInRange : pc < (environment.implementation op).module.code.length :=
    List.getElem?_eq_some_iff.mp fetch |>.1
  have split := bodies_split client environment (operations signature) op (mem_operations op)
  unfold link
  rw [split]
  rw [List.getElem?_append_left]
  · rw [List.getElem?_append_right]
    · rw [clientCode_length]
      simp only [operationBase]
      have subtractClient : client.length + codeBefore environment (operations signature) op + pc -
          client.length = codeBefore environment (operations signature) op + pc := by omega
      rw [subtractClient]
      rw [List.getElem?_append_left]
      · rw [List.getElem?_append_right]
        · rw [bodiesBefore_length, Nat.add_sub_cancel_left]
          simp [implementationBody, fetch, operationBase]
        · rw [bodiesBefore_length]
          exact Nat.le_add_right _ _
      · simp only [List.length_append]
        rw [bodiesBefore_length]
        have bodyLonger : pc < (implementationBody client environment op).length := by
          simpa [implementationBody] using pcInRange
        omega
    · rw [clientCode_length]
      simp only [operationBase]
      omega
  · simp only [List.length_append]
    rw [clientCode_length, bodiesBefore_length]
    simp only [operationBase]
    have bodyLonger : pc < (implementationBody client environment op).length := by
      simpa [implementationBody] using pcInRange
    omega

theorem dispatcherEntries_fetch (configuration : Configuration) (base start pc : Nat)
    (client : OpenProgram signature) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (dispatcherEntries configuration base start client)[2 * pc]? =
      some (dispatcherInstruction configuration (base + 2 * (start + pc)) (start + pc)) := by
  induction pc generalizing start client with
  | zero =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp at fetch
          subst head
          simp [dispatcherEntries]
  | succ pc induction =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at fetch
          simp only [dispatcherEntries, List.getElem?_cons_succ, Nat.mul_add, Nat.mul_one]
          simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using induction (start := start + 1) (client := tail) fetch

theorem dispatcherEntries_fetchCleanup (configuration : Configuration) (base start pc : Nat)
    (client : OpenProgram signature) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (dispatcherEntries configuration base start client)[2 * pc + 1]? =
      some (dispatcherCleanup configuration (base + 2 * (start + pc) + 1) instruction) := by
  induction pc generalizing start client with
  | zero =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp at fetch
          subst head
          simp [dispatcherEntries]
  | succ pc induction =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at fetch
          simp only [dispatcherEntries, List.getElem?_cons_succ, Nat.mul_add, Nat.mul_one]
          simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using induction (start := start + 1) (client := tail) fetch

/-- Fetch the comparison slot corresponding to one client pc. -/
theorem link_fetch_dispatcher (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[dispatcherBase client environment + 2 * pc]? =
      some (dispatcherInstruction configuration
        (dispatcherBase client environment + 2 * pc) pc) := by
  have pcInRange : pc < client.length := List.getElem?_eq_some_iff.mp fetch |>.1
  unfold link
  rw [List.getElem?_append_right]
  · have prefixLength :
        (clientCode client environment configuration ++
          (operations signature).flatMap (implementationBody client environment)).length =
          dispatcherBase client environment := by
        rw [List.length_append, clientCode_length, sharedBody_count]
        rfl
    rw [prefixLength, Nat.add_sub_cancel_left]
    unfold dispatcherCode
    rw [List.getElem?_append_left]
    · simpa using dispatcherEntries_fetch configuration
        (dispatcherBase client environment) 0 pc client instruction fetch
    · rw [dispatcherEntries_length]
      omega
  · rw [List.length_append, clientCode_length, sharedBody_count]
    simp only [dispatcherBase]
    exact Nat.le_add_right _ _

/-- Fetch the cleanup slot corresponding to one client pc. -/
theorem link_fetch_dispatcherCleanup (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[dispatcherBase client environment + 2 * pc + 1]? =
      some (dispatcherCleanup configuration
        (dispatcherBase client environment + 2 * pc + 1) instruction) := by
  have pcInRange : pc < client.length := List.getElem?_eq_some_iff.mp fetch |>.1
  unfold link
  rw [List.getElem?_append_right]
  · have prefixLength :
        (clientCode client environment configuration ++
          (operations signature).flatMap (implementationBody client environment)).length =
          dispatcherBase client environment := by
        rw [List.length_append, clientCode_length, sharedBody_count]
        rfl
    rw [prefixLength]
    have subtract : dispatcherBase client environment + 2 * pc + 1 -
        dispatcherBase client environment = 2 * pc + 1 := by omega
    rw [subtract]
    unfold dispatcherCode
    rw [List.getElem?_append_left]
    · simpa using dispatcherEntries_fetchCleanup configuration
        (dispatcherBase client environment) 0 pc client instruction fetch
    · rw [dispatcherEntries_length]
      omega
  · rw [List.length_append, clientCode_length, sharedBody_count]
    simp only [dispatcherBase]
    exact (Nat.le_add_right
      (client.length + implementationCodeSize environment) (2 * pc)).trans (Nat.le_succ _)

/-- A valid finite program bounds every successor of every occurring instruction. -/
theorem targets_lt_of_mem_valid (valid : Program.Valid program)
    (member : instruction ∈ program) (successor : target ∈ instruction.successors) :
    target < program.length := by
  obtain ⟨pc, pcBelow, rfl⟩ := List.getElem_of_mem member
  exact valid pc _ (by simp) target successor

/-- The end of an implementation body never passes the shared dispatcher. -/
theorem operation_end_le_dispatcher (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (op : signature.Op) :
    operationBase client environment op +
        (environment.implementation op).module.code.length ≤
      dispatcherBase client environment := by
  have split := bodies_split client environment (operations signature) op (mem_operations op)
  have lengths := congrArg List.length split
  have allLength := sharedBody_count client environment
  simp only [List.length_append] at lengths
  have prefixBodyLe :
      (bodiesBefore client environment (operations signature) op).length +
          (implementationBody client environment op).length ≤
        implementationCodeSize environment := by
    rw [← allLength, lengths]
    omega
  rw [bodiesBefore_length] at prefixBodyLe
  simp only [implementationBody, List.length_map] at prefixBodyLe
  simp only [operationBase, dispatcherBase]
  omega

/-- Every compiled client target lies in the linked program. -/
theorem clientCode_targets_lt (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (clientValid : client.Valid) (member : instruction ∈ clientCode client environment configuration)
    (successor : target ∈ instruction.successors) :
    target < (link client environment configuration).length := by
  simp only [clientCode, List.mem_map] at member
  rcases member with ⟨⟨source, pc⟩, sourceMember, rfl⟩
  have fetch : client[pc]? = some source := List.mem_zipIdx_iff_getElem?.mp sourceMember
  cases source with
  | core coreInstruction =>
      have targetBelow := clientValid pc (.core coreInstruction) fetch target successor
      rw [link_length]
      omega
  | call op inputRegion outputRegion next =>
      simp only [clientInstruction, Instruction.successors, List.mem_singleton] at successor
      subst target
      have entryBelow := (environment.implementation op).valid.2
      have bodyEnd := operation_end_le_dispatcher client environment op
      rw [link_length]
      simp only [dispatcherBase] at bodyEnd
      omega

/-- A relocated successor is local to the body or is the shared dispatcher. -/
theorem relocate_successor (base dispatcher : Nat) (original : Instruction)
    (successor : target ∈ (relocateInstruction base dispatcher original).successors) :
    target = dispatcher ∨
      ∃ localTarget, localTarget ∈ original.successors ∧ target = base + localTarget := by
  cases original <;> simp_all [relocateInstruction, Instruction.successors]

/-- Every relocated implementation target lies in the linked program. -/
theorem implementationBodies_targets_lt (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (member : instruction ∈
      (operations signature).flatMap (implementationBody client environment))
    (successor : target ∈ instruction.successors) :
    target < (link client environment configuration).length := by
  simp only [List.mem_flatMap] at member
  rcases member with ⟨op, _opMember, bodyMember⟩
  simp only [implementationBody, List.mem_map] at bodyMember
  rcases bodyMember with ⟨original, originalMember, rfl⟩
  have localTargets : ∀ localTarget ∈ original.successors,
      localTarget < (environment.implementation op).module.code.length :=
    fun localTarget localSuccessor =>
      targets_lt_of_mem_valid (environment.implementation op).valid.1 originalMember localSuccessor
  have bodyEnd := operation_end_le_dispatcher client environment op
  have dispatcherBelow :
      dispatcherBase client environment < (link client environment configuration).length := by
    rw [link_length]
    simp only [dispatcherBase]
    omega
  rcases relocate_successor _ _ original successor with targetDispatcher | targetLocal
  · subst target
    exact dispatcherBelow
  · rcases targetLocal with ⟨localTarget, localSuccessor, rfl⟩
    have localBelow := localTargets localTarget localSuccessor
    omega

/-- A dispatcher comparison advances to either of its two adjacent slots. -/
theorem dispatcherInstruction_successor (configuration : Configuration) (position pc : Nat)
    (successor : target ∈ (dispatcherInstruction configuration position pc).successors) :
    target = position + 1 ∨ target = position + 2 := by
  simp_all [dispatcherInstruction, Instruction.successors]
  aesop

/-- Every shared-dispatch instruction targets the dispatcher or a valid client continuation. -/
theorem dispatcherEntries_targets_lt (configuration : Configuration)
    (base start clientLength limit : Nat) (client : OpenProgram signature)
    (sourceTargets : ∀ source ∈ client, ∀ target ∈ source.successors,
      target < clientLength)
    (clientBelow : clientLength ≤ limit)
    (slotsBelow : base + 2 * (start + client.length) + 1 ≤ limit)
    (member : instruction ∈ dispatcherEntries configuration base start client)
    (successor : target ∈ instruction.successors) : target < limit := by
  induction client generalizing start instruction with
  | nil => simp [dispatcherEntries] at member
  | cons head tail induction =>
      simp only [List.length_cons] at slotsBelow
      simp only [dispatcherEntries, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · rcases dispatcherInstruction_successor configuration
            (base + 2 * start) start successor with rfl | rfl <;> omega
      · cases head with
        | core coreInstruction =>
            simp only [dispatcherCleanup, Instruction.successors,
              List.mem_singleton] at successor
            subst target
            omega
        | call op inputRegion outputRegion next =>
            simp only [dispatcherCleanup, Instruction.successors,
              List.mem_singleton] at successor
            subst target
            exact (sourceTargets (.call op inputRegion outputRegion next) (by simp) next
              (List.mem_singleton.mpr rfl)).trans_le clientBelow
      · exact induction (start := start + 1)
          (fun source sourceMember target targetMember =>
            sourceTargets source (List.mem_cons_of_mem head sourceMember) target targetMember)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using slotsBelow)
          member successor

/-- Every instruction in the dispatcher and its fallback halt targets the linked program. -/
theorem dispatcherCode_targets_lt (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (clientValid : client.Valid) (member : instruction ∈ dispatcherCode client environment configuration)
    (successor : target ∈ instruction.successors) :
    target < (link client environment configuration).length := by
  simp only [dispatcherCode, List.mem_append, List.mem_singleton] at member
  rcases member with entriesMember | rfl
  · apply dispatcherEntries_targets_lt configuration (dispatcherBase client environment) 0
      client.length (link client environment configuration).length client
    · intro source sourceMember target targetMember
      obtain ⟨pc, pcBelow, rfl⟩ := List.getElem_of_mem sourceMember
      exact clientValid pc _ (by simp) target targetMember
    · rw [link_length]
      omega
    · rw [link_length]
      simp [dispatcherBase]
      generalize implementationCodeSize environment = implementationSize
      omega
    · exact entriesMember
    · exact successor
  · simp [Instruction.successors] at successor

/-- The shared-body linker derives concrete validity from client and callee validity. -/
theorem link_valid (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (clientValid : client.Valid) : (link client environment configuration).Valid := by
  intro pc instruction fetch target successor
  have member : instruction ∈ link client environment configuration := List.mem_of_getElem? fetch
  simp only [link, List.mem_append] at member
  rcases member with (clientMember | bodyMember) | dispatcherMember
  · exact clientCode_targets_lt client environment configuration clientValid clientMember successor
  · exact implementationBodies_targets_lt client environment configuration bodyMember successor
  · exact dispatcherCode_targets_lt client environment configuration clientValid dispatcherMember successor

theorem relocate_execute_running (base dispatcher : Nat) (instruction : Instruction)
    (memory : Memory) (next : Algolean.Algorithms.StructuredRealRAM.Configuration)
    (cost : Cost) (executes : execute instruction memory = ⟨.running next, cost⟩) :
    execute (relocateInstruction base dispatcher instruction) memory =
      ⟨.running ⟨base + next.pc, next.memory⟩, cost⟩ := by
  cases instruction <;>
    simp only [execute, relocateInstruction] at executes ⊢ <;>
    try { cases executes; rfl }
  case rcompare left right less equal greater =>
    by_cases below : RealOperand.eval memory left < RealOperand.eval memory right
    · simp [execute, relocateInstruction, below] at executes ⊢
      rcases executes with ⟨configurationEqual, costEqual⟩
      cases configurationEqual
      cases costEqual
      simp [branch, Instruction.cost]
    · by_cases equalValues : RealOperand.eval memory left = RealOperand.eval memory right
      · simp [execute, relocateInstruction, below, equalValues] at executes ⊢
        rcases executes with ⟨configurationEqual, costEqual⟩
        cases configurationEqual
        cases costEqual
        simp [branch, Instruction.cost]
      · simp [execute, relocateInstruction, below, equalValues] at executes ⊢
        rcases executes with ⟨configurationEqual, costEqual⟩
        cases configurationEqual
        cases costEqual
        simp [branch, Instruction.cost]
  case ncompare left right less equal greater =>
    by_cases below : NatOperand.eval memory left < NatOperand.eval memory right
    · simp [execute, relocateInstruction, below] at executes ⊢
      rcases executes with ⟨configurationEqual, costEqual⟩
      cases configurationEqual
      cases costEqual
      simp [branch, Instruction.cost]
    · by_cases equalValues : NatOperand.eval memory left = NatOperand.eval memory right
      · simp [execute, relocateInstruction, below, equalValues] at executes ⊢
        rcases executes with ⟨configurationEqual, costEqual⟩
        cases configurationEqual
        cases costEqual
        simp [branch, Instruction.cost]
      · simp [execute, relocateInstruction, below, equalValues] at executes ⊢
        rcases executes with ⟨configurationEqual, costEqual⟩
        cases configurationEqual
        cases costEqual
        simp [branch, Instruction.cost]
  case halt => cases executes

theorem relocate_execute_halted (base dispatcher : Nat) (instruction : Instruction)
    (memory final : Memory) (result : Real) (cost : Cost)
    (executes : execute instruction memory = ⟨.halted final result, cost⟩) :
    ∃ linkedCost,
      execute (relocateInstruction base dispatcher instruction) memory =
        ⟨.running ⟨dispatcher, final⟩, linkedCost⟩ ∧ linkedCost ≤ cost := by
  cases instruction <;> simp only [execute, relocateInstruction] at executes ⊢ <;>
    try { cases executes }
  case halt operand =>
    cases executes
    refine ⟨Instruction.jump dispatcher |>.cost, rfl, ?_⟩
    intro coordinate
    fin_cases coordinate <;> simp [Instruction.cost, Cost.control, Cost.ofFields]

/-- Relocate every actual callee transition; the replaced halt is never more expensive. -/
theorem relocate_trace (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (op : signature.Op)
    (trace : HaltingTrace (environment.implementation op).module.code
      localInitial final result cost steps) :
    ∃ linkedCost,
      RunningTrace (link client environment configuration)
        ⟨operationBase client environment op + localInitial.pc, localInitial.memory⟩
        ⟨dispatcherBase client environment, final⟩ linkedCost steps ∧
      linkedCost ≤ cost := by
  induction trace with
  | halt observes =>
      rename_i calleeConfiguration calleeFinal calleeResult calleeCost
      simp only [step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have linkedFetch := link_fetch_implementation client environment configuration op _ _ fetch
        have originalExecution : execute instruction calleeConfiguration.memory =
            ⟨.halted calleeFinal calleeResult, calleeCost⟩ := by
          simpa using observes
        rcases relocate_execute_halted (operationBase client environment op)
            (dispatcherBase client environment) instruction calleeConfiguration.memory
            calleeFinal calleeResult calleeCost originalExecution with
          ⟨linkedCost, relocated, bound⟩
        refine ⟨linkedCost, RunningTrace.one ?_, bound⟩
        simp only [step, linkedFetch]
        exact relocated
  | next observes tail induction =>
      rename_i calleeConfiguration calleeNext calleeFinal calleeResult headCost tailCost tailSteps
      simp only [step] at observes
      split at observes
      · cases observes
      · rename_i instruction fetch
        have linkedFetch := link_fetch_implementation client environment configuration op _ _ fetch
        have originalExecution : execute instruction calleeConfiguration.memory =
            ⟨.running calleeNext, headCost⟩ := by
          simpa using observes
        have relocated := relocate_execute_running (operationBase client environment op)
          (dispatcherBase client environment) instruction calleeConfiguration.memory
          calleeNext headCost originalExecution
        rcases induction with ⟨linkedTailCost, linkedTail, tailBound⟩
        refine ⟨headCost + linkedTailCost, RunningTrace.next ?_ linkedTail, ?_⟩
        · simp only [step, linkedFetch]
          exact relocated
        · intro coordinate
          exact Nat.add_le_add_left (tailBound coordinate) (headCost coordinate)

/-- Cost of dispatch comparisons from `index` through `returnPc`, plus cleanup. -/
def dispatcherCostFrom (returnPc index : Nat) : Cost := fun coordinate =>
  (returnPc - index + 1) *
      (Instruction.ncompare (.literal 0) (.literal 0) 0 0 0).cost coordinate +
    (Instruction.nset (.literal 0) 0 0).cost coordinate

/-- Matching a return identifier performs one charged comparison. -/
theorem dispatcher_step_equal (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)
    (memory : Memory) (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (returnId : memory.natReg configuration.returnRegister = pc) :
    step (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * pc, memory⟩ =
      ⟨.running ⟨dispatcherBase client environment + 2 * pc + 1, memory⟩,
        (Instruction.ncompare (.reg configuration.returnRegister) (.literal pc)
          0 0 0).cost⟩ := by
  have linkedFetch := link_fetch_dispatcher client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [step, linkedFetch, dispatcherInstruction, execute, NatOperand.eval, returnId, branch,
    Instruction.cost]

/-- The cleanup slot restores the reserved register and resumes the client. -/
theorem dispatcher_cleanup_step (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)
    (memory : Memory) (fetch : client[pc]? = some (.call op inputRegion outputRegion next)) :
    step (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * pc + 1, memory⟩ =
      ⟨.running ⟨next, memory.writeReg configuration.returnRegister 0⟩,
        (Instruction.nset (.literal 0) configuration.returnRegister next).cost⟩ := by
  have linkedFetch := link_fetch_dispatcherCleanup client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [step, linkedFetch, dispatcherCleanup, execute, NatOperand.eval]

/-- A dispatcher slot before the return identifier advances to the next slot. -/
theorem dispatcher_step_before (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (returnPc index : Nat) (memory : Memory) (returnInRange : returnPc < client.length)
    (before : index < returnPc)
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    step (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * index, memory⟩ =
      ⟨.running ⟨dispatcherBase client environment + 2 * (index + 1), memory⟩,
        (Instruction.ncompare (.reg configuration.returnRegister) (.literal index)
          0 0 0).cost⟩ := by
  have indexInRange : index < client.length := before.trans returnInRange
  have fetch : client[index]? = some client[index] := List.getElem?_eq_getElem indexInRange
  have linkedFetch := link_fetch_dispatcher client environment configuration index client[index] fetch
  simp [step, linkedFetch, dispatcherInstruction, execute, NatOperand.eval, returnId,
    Nat.ne_of_gt before, Nat.not_lt_of_ge (Nat.le_of_lt before), branch, Instruction.cost,
    Nat.mul_add, Nat.add_assoc]

/-- All shared-dispatch comparisons and cleanup occur in the same linked trace. -/
theorem dispatcher_returns_from (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (returnPc index : Nat) (op : signature.Op) (inputRegion outputRegion : Region)
    (next : Nat) (memory : Memory)
    (fetch : client[returnPc]? = some (.call op inputRegion outputRegion next))
    (indexBefore : index ≤ returnPc)
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    RunningTrace (link client environment configuration)
      ⟨dispatcherBase client environment + 2 * index, memory⟩
      ⟨next, memory.writeReg configuration.returnRegister 0⟩
      (dispatcherCostFrom returnPc index) (returnPc - index + 2) := by
  by_cases equal : index = returnPc
  · subst index
    have equalStep := dispatcher_step_equal client environment configuration returnPc op
      inputRegion outputRegion next memory fetch returnId
    have cleanupStep := dispatcher_cleanup_step client environment configuration returnPc op
      inputRegion outputRegion next memory fetch
    have combined := RunningTrace.next equalStep (RunningTrace.one cleanupStep)
    convert combined using 1
    · funext coordinate
      simp [dispatcherCostFrom, Instruction.cost, NatOperand.reads]
    · omega
  · have before : index < returnPc := lt_of_le_of_ne indexBefore equal
    have nextBefore : index + 1 ≤ returnPc := before
    have first := dispatcher_step_before client environment configuration returnPc index memory
      (List.getElem?_eq_some_iff.mp fetch |>.1) before returnId
    have recursive := dispatcher_returns_from client environment configuration returnPc
      (index + 1) op inputRegion outputRegion next memory fetch nextBefore returnId
    have combined := RunningTrace.next first recursive
    convert combined using 1
    · funext coordinate
      change
        dispatcherCostFrom returnPc index coordinate =
          (Instruction.ncompare (.reg configuration.returnRegister) (.literal index)
            0 0 0).cost coordinate + dispatcherCostFrom returnPc (index + 1) coordinate
      simp [dispatcherCostFrom, Instruction.cost, NatOperand.reads]
      have subSuccessor : returnPc - (index + 1) + 1 = returnPc - index := by omega
      rw [subSuccessor]
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · omega
termination_by returnPc - index

/-- Dispatcher specialization starting at its first slot. -/
theorem dispatcher_returns (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (returnPc : Nat) (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)
    (memory : Memory) (fetch : client[returnPc]? = some (.call op inputRegion outputRegion next))
    (returnId : memory.natReg configuration.returnRegister = returnPc) :
    RunningTrace (link client environment configuration)
      ⟨dispatcherBase client environment, memory⟩
      ⟨next, memory.writeReg configuration.returnRegister 0⟩
      (dispatcherCostFrom returnPc 0) (returnPc + 2) := by
  simpa using dispatcher_returns_from client environment configuration returnPc 0 op
    inputRegion outputRegion next memory fetch (Nat.zero_le _) returnId

/-- A relative call site expands to one ordinary setup instruction. -/
theorem call_setup_step (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (pc : Nat) (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)
    (memory : Memory) (fetch : client[pc]? = some (.call op inputRegion outputRegion next)) :
    step (link client environment configuration) ⟨pc, memory⟩ =
      ⟨.running ⟨operationBase client environment op +
          (environment.implementation op).module.entry,
        memory.writeReg configuration.returnRegister pc⟩,
        (Instruction.nset (.literal pc) configuration.returnRegister 0).cost⟩ := by
  have linkedFetch := link_fetch_client client environment configuration pc
    (.call op inputRegion outputRegion next) fetch
  simp [step, linkedFetch, clientInstruction, execute, NatOperand.eval, Instruction.cost]

/-- Expand one abstract call into setup, every callee step, dispatch, and cleanup. -/
theorem refine_call (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (compatible : Compatibility client environment configuration)
    (pc : Nat) (op : signature.Op) (inputRegion outputRegion : Region) (next : Nat)
    (input : (signature.contract op).Input) (validInput : (signature.contract op).pre input)
    (memory : Memory)
    (inputRep : (signature.contract op).inputLayout.RepAt inputRegion input memory)
    (fetch : client[pc]? = some (.call op inputRegion outputRegion next))
    (registerZero : memory.natReg configuration.returnRegister = 0) :
    ∃ linkedCost linkedSteps,
      RunningTrace (link client environment configuration) ⟨pc, memory⟩
        ⟨next, (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory⟩ linkedCost linkedSteps ∧
      linkedCost ≤ signature.bound op input + concreteCallOverhead environment {
        callSite := pc
        op := op
        input := input
        output := environment.responder.answer op input
        outputCorrect := environment.responder.correct op input validInput
        chargedCost := signature.bound op input
        chargedCost_eq := rfl } := by
  let implementation := environment.implementation op
  have inputRegionEq := compatible.inputRegion_eq pc op inputRegion outputRegion next fetch
  have outputRegionEq := compatible.outputRegion_eq pc op inputRegion outputRegion next fetch
  have setupRep : (signature.contract op).inputLayout.RepAt
      implementation.calling.inputRegion input
      (memory.writeReg configuration.returnRegister pc) := by
    rw [← inputRegionEq]
    exact inputRep_writeReg _ _ _ _ _ _ inputRep
  rcases implementation.restoringCorrect input validInput
      (memory.writeReg configuration.returnRegister pc) setupRep with
    ⟨run, outputRep, runBound, canonicalEffect⟩
  have setup := RunningTrace.one (call_setup_step client environment configuration pc op
    inputRegion outputRegion next memory fetch)
  rcases relocate_trace client environment configuration op run.trace with
    ⟨relocatedCost, relocated, relocatedBound⟩
  have returnId : run.final.natReg configuration.returnRegister = pc := by
    rw [canonicalEffect, writeAt_natReg]
    simp [Memory.writeReg]
  have returned := dispatcher_returns client environment configuration pc op inputRegion
    outputRegion next run.final fetch returnId
  have allSteps := setup.trans (relocated.trans returned)
  have finalMemory :
      run.final.writeReg configuration.returnRegister 0 =
        (signature.contract op).outputLayout.writeAt outputRegion
          (environment.responder.answer op input) memory := by
    rw [canonicalEffect, outputRegionEq]
    exact writeAt_setup_cleanup _ _ _ _ _ _ registerZero
  rw [finalMemory] at allSteps
  refine ⟨_, _, allSteps, ?_⟩
  intro coordinate
  have relocatedCoordinate := relocatedBound coordinate
  have runCoordinate := runBound coordinate
  change
    (Instruction.nset (.literal pc) configuration.returnRegister 0).cost coordinate +
        (relocatedCost coordinate + dispatcherCostFrom pc 0 coordinate) ≤
      (signature.bound op input + concreteCallOverhead environment {
        callSite := pc
        op := op
        input := input
        output := environment.responder.answer op input
        outputCorrect := environment.responder.correct op input validInput
        chargedCost := signature.bound op input
        chargedCost_eq := rfl }) coordinate
  simp only [concreteCallOverhead, Pi.add_apply]
  simp only [Instruction.cost, NatOperand.reads, Cost.ofFields] at relocatedCoordinate runCoordinate ⊢
  simp only [dispatcherCostFrom, Nat.sub_zero]
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

/-- Flatten a complete relative execution into one ordinary linked halting trace. -/
theorem refine_trace (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (compatible : Compatibility client environment configuration)
    (trace : OpenHaltingTrace signature environment.responder client
      initial final result cost steps calls)
    (registerZero : initial.memory.natReg configuration.returnRegister = 0) :
    ∃ linkedCost linkedSteps,
      HaltingTrace (link client environment configuration) initial final result
        linkedCost linkedSteps ∧
      linkedCost ≤ cost + totalConcreteCallOverhead environment calls := by
  induction trace with
  | @halt traceConfiguration traceMemory traceResult traceCost openStep =>
      cases openStep with
      | core fetch executes =>
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨traceCost, 1, HaltingTrace.halt ?_, ?_⟩
          · simp only [step, linkedFetch, clientInstruction]
            exact executes
          · simp [totalConcreteCallOverhead]
  | @core traceConfiguration traceNext traceFinal traceResult headCost tailCost
      tailSteps tailCalls openStep tail induction =>
      cases openStep with
      | core fetch executes =>
          have safe := compatible.clientAvoidsReturnRegister _ _ fetch
          have preserved := instructionAvoids_preserves_register _ _ safe _ _ _ executes
          have nextZero := preserved.trans registerZero
          rcases induction nextZero with
            ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          have linkedFetch := link_fetch_client client environment configuration _ _ fetch
          refine ⟨headCost + tailLinkedCost, tailLinkedSteps + 1,
            HaltingTrace.next ?_ linkedTail, ?_⟩
          · simp only [step, linkedFetch, clientInstruction]
            exact executes
          · intro coordinate
            simpa only [Pi.add_apply, Nat.add_assoc] using
              Nat.add_le_add_left (tailBound coordinate) (headCost coordinate)
  | @call traceConfiguration traceNext traceFinal traceResult headCost tailCost
      tailSteps call tailCalls openStep tail induction =>
      cases openStep with
      | call fetch inputRep validInput =>
          rename_i operation inputRegion outputRegion callNext input
          rcases refine_call client environment configuration compatible _ _ _ _ _ _ validInput
              _ inputRep fetch registerZero with
            ⟨callCost, callSteps, linkedCall, callBound⟩
          rcases induction (by simpa only [writeAt_natReg] using registerZero) with
            ⟨tailLinkedCost, tailLinkedSteps, linkedTail, tailBound⟩
          refine ⟨callCost + tailLinkedCost, tailLinkedSteps + callSteps,
            linkedCall.thenHalting linkedTail, ?_⟩
          intro coordinate
          simp only [totalConcreteCallOverhead, List.map_cons, List.sum_cons,
            Pi.add_apply]
          have callCoordinate := callBound coordinate
          have tailCoordinate := tailBound coordinate
          calc
            callCost coordinate + tailLinkedCost coordinate ≤
                (signature.bound operation input coordinate +
                  concreteCallOverhead environment {
                    callSite := traceConfiguration.pc
                    op := operation
                    input := input
                    output := environment.responder.answer operation input
                    outputCorrect := environment.responder.correct operation input validInput
                    chargedCost := signature.bound operation input
                    chargedCost_eq := rfl } coordinate) +
                  (tailCost coordinate +
                    totalConcreteCallOverhead environment tailCalls coordinate) :=
              Nat.add_le_add callCoordinate tailCoordinate
            _ = _ := by ac_rfl

/--
Numeric side condition turning the exact relative/call bound of an actual client execution into a
chosen linked bound.  Tying the condition to a trace is important: a caller need only cover call
records which its fixed open program can really produce, rather than arbitrary caller-supplied
lists of calls.
-/
def BoundCovers (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ImplementationEnvironment signature)
    (linkedBound : problem.Input → Cost) : Prop :=
  ∀ (input : problem.Input) (final : Memory) (result : Real) (cost : Cost)
      (steps : Nat) (calls : List (DependencyCallRecord signature)),
    problem.pre input →
    OpenHaltingTrace signature environment.responder client.module
      ⟨0, problem.initialMemory input⟩ final result cost steps calls →
    cost ≤ relativeBound input →
    cost + totalConcreteCallOverhead environment calls ≤ linkedBound input

/-- Construct the concrete refinement entirely from the generic operational simulation. -/
theorem Refinement.ofCompatibility
    (client : RelativeAlgorithmCertificate signature problem relativeBound)
    (environment : ImplementationEnvironment signature) (configuration : Configuration)
    (linkedBound : problem.Input → Cost)
    (compatible : Compatibility client.module environment configuration)
    (returnRegisterInitiallyZero : ∀ input,
      (problem.initialMemory input).natReg configuration.returnRegister = 0)
    (boundCovers : BoundCovers client environment linkedBound) :
    Refinement client environment configuration linkedBound where
  returnRegisterInitiallyZero := returnRegisterInitiallyZero
  linkedValid := link_valid client.module environment configuration client.valid
  solves input validInput := by
    rcases client.solvesAgainstContracts environment.responder input validInput with
      ⟨output, final, result, cost, steps, calls, relativeTrace,
        outputRep, post, relativeCost⟩
    rcases refine_trace client.module environment configuration compatible relativeTrace
        (returnRegisterInitiallyZero input) with
      ⟨linkedCost, linkedSteps, linkedTrace, linkedCostBound⟩
    refine ⟨output, {
      final := final
      result := result
      cost := linkedCost
      steps := linkedSteps
      trace := linkedTrace }, outputRep, post, ?_⟩
    exact linkedCostBound.trans
      (boundCovers input final result cost steps calls validInput relativeTrace relativeCost)

/-- Build the publication-oriented linkable wrapper without an ad hoc correctness proof. -/
def LinkableRelativeAlgorithmCertificate.ofCompatibility
    (relative : RelativeAlgorithmCertificate signature problem relativeBound)
    (configuration : Configuration) (linkedBound : problem.Input → Cost)
    (compatible : ∀ environment : ImplementationEnvironment signature,
      Compatibility relative.module environment configuration)
    (returnRegisterInitiallyZero : ∀ input,
      (problem.initialMemory input).natReg configuration.returnRegister = 0)
    (boundCovers : ∀ environment : ImplementationEnvironment signature,
      BoundCovers relative environment linkedBound) :
    LinkableRelativeAlgorithmCertificate signature problem relativeBound linkedBound where
  relative := relative
  configuration := configuration
  refinement environment := Refinement.ofCompatibility relative environment configuration
    linkedBound (compatible environment) returnRegisterInitiallyZero (boundCovers environment)

end

end Algolean.Algorithms.StructuredRealRAM.Linker
