/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMRelative

/-!
# Concrete shared-body linker for relative Word-RAM modules

The linker emits one client instruction per open instruction, one relocated implementation body
per dependency operation, and one shared return dispatcher.  A call writes its call-site id to a
reserved word and jumps to the shared callee body.  Every callee halt is rewritten to jump to the
dispatcher, which returns to the statically declared client continuation.  Thus runtime loops
repeat callee execution without duplicating its code.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.Linker

noncomputable section

/-- Reserved resources and explicit linker overhead policy. -/
structure Configuration (w : ℕ) where
  returnCell : BitVec w
  jumpRegister : ℕ

/-- A statically known open call site. -/
structure CallSite (signature : DependencySignature w) where
  pc : ℕ
  op : signature.Op
  next : ℕ

/-- Extract call sites in source order. -/
def callSites (program : OpenProgram signature) : List (CallSite signature) :=
  program.zipIdx.filterMap fun (instruction, pc) =>
    match instruction with
    | .core _ => none
    | .call op _ _ next => some ⟨pc, op, next⟩

/-- Canonical inspectable operation order from the finite signature. -/
def operations (signature : DependencySignature w) : List signature.Op :=
  Finset.univ.toList

/-- Total implementation code preceding `op` in canonical operation order. -/
def codeBefore (environment : ImplementationEnvironment signature) :
    List signature.Op → signature.Op → ℕ
  | [], _ => 0
  | current :: rest, op =>
      if current = op then 0
      else (environment.implementation current).module.code.length +
        codeBefore environment rest op

/-- Start address of an operation's one shared implementation body. -/
def operationBase (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (op : signature.Op) : ℕ :=
  client.length + codeBefore environment (operations signature) op

/-- Total words occupied by all shared implementation bodies. -/
def implementationCodeSize (environment : ImplementationEnvironment signature) : ℕ :=
  ((operations signature).map fun op =>
    (environment.implementation op).module.code.length).sum

/-- First program counter of the shared return dispatcher. -/
def dispatcherBase (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) : ℕ :=
  client.length + implementationCodeSize environment

/-- Relocate one callee instruction; halts become jumps to the shared dispatcher. -/
def relocateInstruction {w : ℕ} (base dispatcher : ℕ) :
    RAM.Instruction (BitVec w) (BitVec w) Empty →
      RAM.Instruction (BitVec w) (BitVec w) Empty
  | .set source destination next => .set source destination (base + next)
  | .add left right destination next => .add left right destination (base + next)
  | .sub left right destination next => .sub left right destination (base + next)
  | .mul left right destination next => .mul left right destination (base + next)
  | .div left right destination next => .div left right destination (base + next)
  | .neg source destination next => .neg source destination (base + next)
  | .setAddress source destination next => .setAddress source destination (base + next)
  | .addAddress left right destination next =>
      .addAddress left right destination (base + next)
  | .subAddress left right destination next =>
      .subAddress left right destination (base + next)
  | .compare left right less equal greater =>
      .compare left right (base + less) (base + equal) (base + greater)
  | .compareAddress left right less equal greater =>
      .compareAddress left right (base + less) (base + equal) (base + greater)
  | .extra impossible _ => nomatch impossible
  | .halt _ => .compareAddress (.immediate 0) (.immediate 0)
      dispatcher dispatcher dispatcher

/-- Relocate one implementation body exactly once. -/
def implementationBody {w : ℕ} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (_configuration : Configuration w)
    (op : signature.Op) : Program w :=
  let base := operationBase client environment op
  let dispatcher := dispatcherBase client environment
  (environment.implementation op).module.code.map
    (relocateInstruction base dispatcher)

/-- Concrete implementation syntax preceding `op` in an operation list. -/
def bodiesBefore {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    List signature.Op → signature.Op → Program w
  | [], _ => []
  | current :: rest, op =>
      if current = op then []
      else implementationBody client environment configuration current ++
        bodiesBefore client environment configuration rest op

/-- Concrete implementation syntax following `op`; used only for placement proofs. -/
def bodiesAfter {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    List signature.Op → signature.Op → Program w
  | [], _ => []
  | current :: rest, op =>
      if current = op then rest.flatMap (implementationBody client environment configuration)
      else bodiesAfter client environment configuration rest op

theorem bodiesBefore_length {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w)
    (items : List signature.Op) (op : signature.Op) :
    (bodiesBefore client environment configuration items op).length =
      codeBefore environment items op := by
  induction items with
  | nil => rfl
  | cons current rest ih =>
      simp only [bodiesBefore, codeBefore]
      split
      · rfl
      · simp [implementationBody, ih]

/-- Every operation body occurs as one contiguous block at its computed prefix length. -/
theorem bodies_split {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w)
    (items : List signature.Op) (op : signature.Op) (member : op ∈ items) :
    items.flatMap (implementationBody client environment configuration) =
      bodiesBefore client environment configuration items op ++
        implementationBody client environment configuration op ++
        bodiesAfter client environment configuration items op := by
  induction items with
  | nil => simp at member
  | cons current rest ih =>
      simp only [List.mem_cons] at member
      by_cases equal : current = op
      · subst current
        simp [bodiesBefore, bodiesAfter]
      · have tailMember : op ∈ rest := member.resolve_left (fun same ↦ equal same.symm)
        simp only [List.flatMap_cons, bodiesBefore, bodiesAfter, if_neg equal]
        rw [ih tailMember]
        simp [List.append_assoc]

/-- Every finite signature operation appears in the canonical linker order. -/
theorem mem_operations {w : Nat} {signature : DependencySignature w}
    (op : signature.Op) : op ∈ operations signature := by
  simp [operations]

/-- Compile a client instruction.  Calls jump to shared bodies after recording their return id. -/
def clientInstruction {w : ℕ} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w)
    (pc : ℕ) : OpenInstruction signature → RAM.Instruction (BitVec w) (BitVec w) Empty
  | .core instruction => instruction
  | .call op _ _ _ =>
      .setAddress (.immediate (BitVec.ofNat w pc)) configuration.jumpRegister
        (operationBase client environment op + (environment.implementation op).module.entry)

/-- Compile the client while preserving its program-counter numbering. -/
def clientCode {w : ℕ} {signature : DependencySignature w} (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    Program w :=
  client.zipIdx.map fun (instruction, pc) =>
    clientInstruction client environment configuration pc instruction

/-- One dispatcher comparison; every client pc has one canonical return-id slot. -/
def dispatcherInstruction {w : ℕ} {signature : DependencySignature w}
    (configuration : Configuration w) (position : ℕ)
    (pc : Nat) (instruction : OpenInstruction signature) :
    RAM.Instruction (BitVec w) (BitVec w) Empty :=
  let equalTarget := match instruction with
    | .core _ => position + 1
    | .call _ _ _ _ => position + 1
  .compareAddress (.reg configuration.jumpRegister)
    (.immediate (BitVec.ofNat w pc)) (position + 2) equalTarget (position + 2)

/-- Restore the reserved return register before resuming the client. -/
def dispatcherCleanup {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (position : Nat)
    (instruction : OpenInstruction signature) :
    RAM.Instruction (BitVec w) (BitVec w) Empty :=
  let next := match instruction with
    | .core _ => position + 1
    | .call _ _ _ next => next
  .setAddress (.immediate 0) configuration.jumpRegister next

/-- Two dispatcher instructions per client pc, generated without duplicating any continuation. -/
def dispatcherEntries {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (base pc : Nat) :
    OpenProgram signature → Program w
  | [] => []
  | instruction :: rest =>
      let position := base + 2 * pc
      dispatcherInstruction configuration position pc instruction ::
        dispatcherCleanup configuration (position + 1) instruction ::
        dispatcherEntries configuration base (pc + 1) rest

theorem dispatcherEntries_length {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (base pc : Nat) (client : OpenProgram signature) :
    (dispatcherEntries configuration base pc client).length = 2 * client.length := by
  induction client generalizing pc with
  | nil => rfl
  | cons instruction rest ih => simp [dispatcherEntries, ih, Nat.mul_add]

theorem dispatcherEntries_fetch {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (base start pc : Nat)
    (client : OpenProgram signature) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (dispatcherEntries configuration base start client)[2 * pc]? =
      some (dispatcherInstruction configuration (base + 2 * (start + pc))
        (start + pc) instruction) := by
  induction pc generalizing start client with
  | zero =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp at fetch
          subst head
          simp [dispatcherEntries]
  | succ pc ih =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at fetch
          simp only [dispatcherEntries, List.getElem?_cons_succ, Nat.mul_add, Nat.mul_one]
          simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (start := start + 1) (client := tail) fetch

theorem dispatcherEntries_fetchCleanup {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (base start pc : Nat)
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
  | succ pc ih =>
      cases client with
      | nil => simp at fetch
      | cons head tail =>
          simp only [List.getElem?_cons_succ] at fetch
          simp only [dispatcherEntries, List.getElem?_cons_succ, Nat.mul_add, Nat.mul_one]
          simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (start := start + 1) (client := tail) fetch

/-- Shared linear return dispatcher followed by a stuck-safe halt fallback. -/
def dispatcherCode {w : ℕ} {signature : DependencySignature w} (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    Program w :=
  let base := dispatcherBase client environment
  dispatcherEntries configuration base 0 client ++
    [.halt (.immediate 0)]

/-- Concrete linked core Word-RAM program with one body per dependency operation. -/
def link {w : ℕ} {signature : DependencySignature w} (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    Program w :=
  clientCode client environment configuration ++
    (operations signature).flatMap
      (implementationBody client environment configuration) ++
    dispatcherCode client environment configuration

theorem clientCode_length {w : ℕ} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    (clientCode client environment configuration).length = client.length := by
  simp [clientCode]

/-- The linker materializes each dependency implementation exactly once. -/
theorem sharedBody_count {w : ℕ} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    ((operations signature).flatMap
      (implementationBody client environment configuration)).length =
      implementationCodeSize environment := by
  simp [implementationBody, implementationCodeSize]

/-- Exact linked instruction count, including one dispatcher fallback halt. -/
theorem link_length {w : ℕ} {signature : DependencySignature w}
    (client : OpenProgram signature)
    (environment : ImplementationEnvironment signature) (configuration : Configuration w) :
    (link client environment configuration).length =
      client.length + implementationCodeSize environment + 2 * client.length + 1 := by
  unfold link
  rw [List.length_append, List.length_append]
  rw [clientCode_length, sharedBody_count]
  unfold dispatcherCode
  simp only [List.length_append, dispatcherEntries_length, List.length_singleton]
  omega

/-- Full finite binary size of the concrete linked syntax, including every literal and target. -/
def linkedDescriptionSize {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) : Nat :=
  WordRAM.descriptionSize (link client environment configuration)

/-- The published linker description bound is the exact serialization size of its output. -/
theorem link_descriptionSize {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) :
    WordRAM.descriptionSize (link client environment configuration) =
      linkedDescriptionSize client environment configuration := rfl

/-- A valid finite program bounds the successors of every instruction occurring in it. -/
theorem targets_lt_of_mem_valid
    {Literal Address Extra : Type} {program : RAM.Program Literal Address Extra}
    (valid : program.Valid) {instruction : RAM.Instruction Literal Address Extra}
    (member : instruction ∈ program) {target : Nat}
    (successor : target ∈ instruction.successors) :
    target < program.length := by
  obtain ⟨pc, pcBelow, rfl⟩ := List.getElem_of_mem member
  exact valid pc _ (by simp) target successor

/-- The end of each shared implementation body precedes the return dispatcher. -/
theorem operation_end_le_dispatcher {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (op : signature.Op) :
    operationBase client environment op +
        (environment.implementation op).module.code.length ≤
      dispatcherBase client environment := by
  have split := bodies_split client environment configuration (operations signature) op
    (mem_operations op)
  have lengths := congrArg List.length split
  have allLength := sharedBody_count client environment configuration
  simp only [List.length_append] at lengths
  have prefixBodyLe :
      (bodiesBefore client environment configuration (operations signature) op).length +
          (implementationBody client environment configuration op).length ≤
        implementationCodeSize environment := by
    rw [← allLength, lengths]
    omega
  rw [bodiesBefore_length] at prefixBodyLe
  simp only [implementationBody, List.length_map] at prefixBodyLe
  simp only [operationBase, dispatcherBase]
  omega

/-- Every compiled client instruction targets the finite linked program. -/
theorem clientCode_targets_lt {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (clientValid : client.Valid)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) Empty}
    (member : instruction ∈ clientCode client environment configuration)
    {target : Nat} (successor : target ∈ instruction.successors) :
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
      simp only [clientInstruction, RAM.Instruction.successors, List.mem_singleton] at successor
      subst target
      have entryBelow := (environment.implementation op).valid.2
      have bodyEnd := operation_end_le_dispatcher client environment configuration op
      rw [link_length]
      simp only [dispatcherBase] at bodyEnd
      omega

/-- Every relocated callee instruction targets its own body or the shared dispatcher. -/
theorem relocate_successor {w : Nat} (base dispatcher : Nat)
    (original : RAM.Instruction (BitVec w) (BitVec w) Empty) {target : Nat}
    (successor : target ∈ (relocateInstruction base dispatcher original).successors) :
    target = dispatcher ∨
      ∃ localTarget, localTarget ∈ original.successors ∧ target = base + localTarget := by
  cases original <;>
    simp_all [relocateInstruction, RAM.Instruction.successors] <;> aesop

/-- Every relocated callee instruction targets its own body or the shared dispatcher. -/
theorem implementationBodies_targets_lt {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) Empty}
    (member : instruction ∈
      (operations signature).flatMap (implementationBody client environment configuration))
    {target : Nat} (successor : target ∈ instruction.successors) :
    target < (link client environment configuration).length := by
  simp only [List.mem_flatMap] at member
  rcases member with ⟨op, _opMember, bodyMember⟩
  simp only [implementationBody, List.mem_map] at bodyMember
  rcases bodyMember with ⟨original, originalMember, rfl⟩
  have localTargets : ∀ localTarget ∈ original.successors,
      localTarget < (environment.implementation op).module.code.length :=
    fun localTarget localSuccessor ↦
      targets_lt_of_mem_valid (environment.implementation op).valid.1 originalMember
        localSuccessor
  have bodyEnd := operation_end_le_dispatcher client environment configuration op
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

/-- Dispatcher entries target either another dispatcher slot or a valid original continuation. -/
theorem dispatcherInstruction_successor {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (position pc : Nat)
    (source : OpenInstruction signature) {target : Nat}
    (successor : target ∈ (dispatcherInstruction configuration position pc source).successors) :
    target = position + 1 ∨ target = position + 2 := by
  cases source <;>
    simp_all [dispatcherInstruction, RAM.Instruction.successors] <;> aesop

/-- Dispatcher entries target either another dispatcher slot or a valid original continuation. -/
theorem dispatcherEntries_targets_lt {w : Nat} {signature : DependencySignature w}
    (configuration : Configuration w) (base start clientLength limit : Nat)
    (client : OpenProgram signature)
    (sourceTargets : ∀ source ∈ client, ∀ target ∈ source.successors,
      target < clientLength)
    (clientBelow : clientLength ≤ limit)
    (slotsBelow : base + 2 * (start + client.length) + 1 ≤ limit)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) Empty}
    (member : instruction ∈ dispatcherEntries configuration base start client)
    {target : Nat} (successor : target ∈ instruction.successors) :
    target < limit := by
  induction client generalizing start instruction with
  | nil => simp [dispatcherEntries] at member
  | cons head tail ih =>
      simp only [List.length_cons] at slotsBelow
      simp only [dispatcherEntries, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · rcases dispatcherInstruction_successor configuration
            (base + 2 * start) start head successor with rfl | rfl <;> omega
      · cases head with
        | core coreInstruction =>
            simp only [dispatcherCleanup, RAM.Instruction.successors,
              List.mem_singleton] at successor
            subst target
            omega
        | call op inputRegion outputRegion next =>
            simp only [dispatcherCleanup, RAM.Instruction.successors,
              List.mem_singleton] at successor
            subst target
            exact (sourceTargets (.call op inputRegion outputRegion next) (by simp) next
              (List.mem_singleton.mpr rfl)).trans_le clientBelow
      · exact ih (start := start + 1)
          (fun source sourceMember target targetMember ↦
            sourceTargets source (List.mem_cons_of_mem head sourceMember) target targetMember)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using slotsBelow)
          member successor

/-- Every instruction in the shared dispatcher targets the complete linked program. -/
theorem dispatcherCode_targets_lt {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (clientValid : client.Valid)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) Empty}
    (member : instruction ∈ dispatcherCode client environment configuration)
    {target : Nat} (successor : target ∈ instruction.successors) :
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
    · exact entriesMember
    · exact successor
  · simp [RAM.Instruction.successors] at successor

/-- The shared-body linker derives target-program validity from source and callee validity. -/
theorem link_valid {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (clientValid : client.Valid) :
    (link client environment configuration).Valid := by
  intro pc instruction fetch target successor
  have member : instruction ∈ link client environment configuration :=
    List.mem_of_getElem? fetch
  simp only [link, List.mem_append] at member
  rcases member with (clientMember | bodyMember) | dispatcherMember
  · exact clientCode_targets_lt client environment configuration clientValid clientMember successor
  · exact implementationBodies_targets_lt client environment configuration bodyMember successor
  · exact dispatcherCode_targets_lt client environment configuration clientValid
      dispatcherMember successor

/-- Fetching inside a shared body returns exactly the relocated local instruction. -/
theorem link_fetch_implementation {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (op : signature.Op) (pc : Nat)
    (instruction : RAM.Instruction (BitVec w) (BitVec w) Empty)
    (fetch : (environment.implementation op).module.code[pc]? = some instruction) :
    (link client environment configuration)[operationBase client environment op + pc]? =
      some (relocateInstruction (operationBase client environment op)
        (dispatcherBase client environment) instruction) := by
  have pcInRange : pc < (environment.implementation op).module.code.length :=
    List.getElem?_eq_some_iff.mp fetch |>.1
  have split := bodies_split client environment configuration (operations signature) op
    (mem_operations op)
  unfold link
  rw [split]
  rw [List.getElem?_append_left]
  · rw [List.getElem?_append_right]
    · rw [clientCode_length]
      simp only [operationBase]
      have subtractClient :
          client.length + codeBefore environment (operations signature) op + pc - client.length =
            codeBefore environment (operations signature) op + pc := by omega
      rw [subtractClient]
      rw [List.getElem?_append_left]
      · rw [List.getElem?_append_right]
        · rw [bodiesBefore_length, Nat.add_sub_cancel_left]
          simp [implementationBody, fetch, operationBase]
        · rw [bodiesBefore_length]
          exact Nat.le_add_right _ _
      · simp only [List.length_append]
        rw [bodiesBefore_length]
        have bodyLonger :
            pc < (implementationBody client environment configuration op).length := by
          simpa [implementationBody] using pcInRange
        omega
    · rw [clientCode_length]
      simp only [operationBase]
      omega
  · simp only [List.length_append]
    rw [clientCode_length, bodiesBefore_length]
    simp only [operationBase]
    have bodyLonger : pc < (implementationBody client environment configuration op).length := by
      simpa [implementationBody] using pcInRange
    omega

/-- Client program counters are preserved verbatim by linking. -/
theorem link_fetch_client {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (instruction : OpenInstruction signature)
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

/-- The dispatcher has one comparison slot for each original client program counter. -/
theorem link_fetch_dispatcher {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[dispatcherBase client environment + 2 * pc]? =
      some (dispatcherInstruction configuration (dispatcherBase client environment + 2 * pc)
        pc instruction) := by
  have pcInRange : pc < client.length := List.getElem?_eq_some_iff.mp fetch |>.1
  unfold link
  rw [List.getElem?_append_right]
  · have prefixLength :
        (clientCode client environment configuration ++
          (operations signature).flatMap
            (implementationBody client environment configuration)).length =
          dispatcherBase client environment := by
        rw [List.length_append, clientCode_length, sharedBody_count]
        rfl
    have subtractPrefix :
        dispatcherBase client environment + 2 * pc - dispatcherBase client environment =
          2 * pc := by omega
    rw [prefixLength, subtractPrefix]
    unfold dispatcherCode
    rw [List.getElem?_append_left]
    · simpa using dispatcherEntries_fetch configuration
        (dispatcherBase client environment) 0 pc client instruction fetch
    · rw [dispatcherEntries_length]
      omega
  · rw [List.length_append, clientCode_length, sharedBody_count]
    simp [dispatcherBase]

/-- The cleanup slot immediately follows its dispatcher comparison. -/
theorem link_fetch_dispatcherCleanup {w : Nat} {signature : DependencySignature w}
    (client : OpenProgram signature) (environment : ImplementationEnvironment signature)
    (configuration : Configuration w) (pc : Nat) (instruction : OpenInstruction signature)
    (fetch : client[pc]? = some instruction) :
    (link client environment configuration)[dispatcherBase client environment + 2 * pc + 1]? =
      some (dispatcherCleanup configuration
        (dispatcherBase client environment + 2 * pc + 1) instruction) := by
  have pcInRange : pc < client.length := List.getElem?_eq_some_iff.mp fetch |>.1
  unfold link
  rw [List.getElem?_append_right]
  · have prefixLength :
        (clientCode client environment configuration ++
          (operations signature).flatMap
            (implementationBody client environment configuration)).length =
          dispatcherBase client environment := by
        rw [List.length_append, clientCode_length, sharedBody_count]
        rfl
    rw [prefixLength]
    have subtractPrefix :
        dispatcherBase client environment + 2 * pc + 1 - dispatcherBase client environment =
          2 * pc + 1 := by omega
    rw [subtractPrefix]
    unfold dispatcherCode
    rw [List.getElem?_append_left]
    · simpa using dispatcherEntries_fetchCleanup configuration
        (dispatcherBase client environment) 0 pc client instruction fetch
    · rw [dispatcherEntries_length]
      omega
  · rw [List.length_append, clientCode_length, sharedBody_count]
    simp [dispatcherBase]
    omega

end

end Algolean.Algorithms.WordRAM.Linker
