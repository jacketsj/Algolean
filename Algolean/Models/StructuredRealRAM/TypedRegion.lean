/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Data

/-!
# Typed two-bank regions and operational accessors

Address arithmetic lowers to ordinary closed structured-machine instructions.  The public
theorems below concern actual `step` and `HaltingTrace` derivations, not only a host-side address
formula.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- A typed reference retains its concrete closed layout and two-bank base region. -/
structure Ref (alpha : Type) where
  layout : Layout alpha
  region : Region

/-- Construct a typed reference by resolving canonical syntax once. -/
def Ref.ofCanonical (alpha : Type) [CanonicalLayout alpha] (region : Region) : Ref alpha :=
  ⟨layoutOf alpha, region⟩

/-- Relational meaning of a typed reference. -/
noncomputable def Ref.Rep (reference : Ref alpha) (value : alpha) (memory : Memory) : Prop :=
  reference.layout.RepAt reference.region value memory

/-- Closed natural-address calculations used by typed accessors. -/
inductive NatAddressPlan where
  | constant (address : Nat)
  | fixedIndex (base headerCells stride indexRegister : Nat)
  | registerFixedIndex (baseRegister headerCells stride indexRegister : Nat)
  | rowMajor (base headerCells rowRegister columnRegister columnCountRegister stride : Nat)
deriving DecidableEq, Repr

namespace NatAddressPlan

/-- Mathematical address denoted by a plan in the current machine state. -/
def eval (plan : NatAddressPlan) (memory : Memory) : Nat :=
  match plan with
  | .constant address => address
  | .fixedIndex base header stride index =>
      base + header + memory.natReg index * stride
  | .registerFixedIndex base header stride index =>
      memory.natReg base + header + memory.natReg index * stride
  | .rowMajor base header row column columns stride =>
      memory.natReg base + header +
        (memory.natReg row * memory.natReg columns + memory.natReg column) * stride

/-- Exact number of emitted unit transitions. -/
def cost : NatAddressPlan → Nat
  | .constant _ => 1
  | .fixedIndex .. => 2
  | .registerFixedIndex .. => 3
  | .rowMajor .. => 5

/-- Lower one plan to finite first-order core syntax. -/
def compile (plan : NatAddressPlan) (destination start next : Nat) : Program :=
  match plan with
  | .constant address => [.nset (.literal address) destination next]
  | .fixedIndex base header stride index =>
      [.nmul (.reg index) (.literal stride) destination (start + 1),
        .nadd (.reg destination) (.literal (base + header)) destination next]
  | .registerFixedIndex base header stride index =>
      [.nmul (.reg index) (.literal stride) destination (start + 1),
        .nadd (.reg destination) (.reg base) destination (start + 2),
        .nadd (.reg destination) (.literal header) destination next]
  | .rowMajor base header row column columns stride =>
      [.nmul (.reg row) (.reg columns) destination (start + 1),
        .nadd (.reg destination) (.reg column) destination (start + 2),
        .nmul (.reg destination) (.literal stride) destination (start + 3),
        .nadd (.reg destination) (.reg base) destination (start + 4),
        .nadd (.reg destination) (.literal header) destination next]

theorem compile_length (plan : NatAddressPlan) (destination start next : Nat) :
    (plan.compile destination start next).length = plan.cost := by
  cases plan <;> rfl

/-- Address code never changes either memory bank. -/
def AddressOnly : Instruction → Prop
  | .nset .. | .nadd .. | .nsub .. | .nmul .. | .nload .. | .jump .. => True
  | _ => False

theorem compile_addressOnly (plan : NatAddressPlan) (destination start next : Nat) :
    ∀ instruction ∈ plan.compile destination start next, AddressOnly instruction := by
  cases plan <;> simp [compile, AddressOnly]

/-- One address-only transition preserves both random-access data banks. -/
theorem AddressOnly.execute_preservesBanks (instruction : Instruction)
    (addressOnly : AddressOnly instruction) (memory : Memory) (next : Configuration)
    (executes : execute instruction memory = ⟨.running next, instruction.cost⟩) :
    next.memory.realMem = memory.realMem ∧ next.memory.natMem = memory.natMem := by
  cases instruction <;> simp only [AddressOnly] at addressOnly
  all_goals simp only [execute] at executes
  all_goals cases executes
  all_goals exact ⟨rfl, rfl⟩

end NatAddressPlan

/-- Actual trace-level execution of the constant-time fixed-index address plan. -/
theorem fixedIndex_trace (memory : Memory) (base header stride index destination : Nat) :
    let program : Program :=
      (NatAddressPlan.fixedIndex base header stride index).compile destination 0 2 ++
        [.halt (.literal 0)]
    ∃ final cost,
      HaltingTrace program ⟨0, memory⟩ final 0 cost 3 ∧
      final.natReg destination = base + header + memory.natReg index * stride ∧
      final.realMem = memory.realMem ∧ final.natMem = memory.natMem ∧
      cost =
        (Instruction.nmul (.reg index) (.literal stride) destination 1).cost +
        ((Instruction.nadd (.reg destination) (.literal (base + header)) destination 2).cost +
          (Instruction.halt (.literal 0)).cost) := by
  dsimp [NatAddressPlan.compile]
  let firstMemory := memory.writeReg destination (memory.natReg index * stride)
  let finalMemory := firstMemory.writeReg destination
    (memory.natReg index * stride + (base + header))
  refine ⟨finalMemory,
    (Instruction.nmul (.reg index) (.literal stride) destination 1).cost +
      ((Instruction.nadd (.reg destination) (.literal (base + header)) destination 2).cost +
        (Instruction.halt (.literal 0)).cost), ?_, ?_, rfl, rfl, rfl⟩
  · have haltTrace : HaltingTrace
        [Instruction.nmul (.reg index) (.literal stride) destination 1,
          Instruction.nadd (.reg destination) (.literal (base + header)) destination 2,
          Instruction.halt (.literal 0)]
        ⟨2, finalMemory⟩ finalMemory 0 (Instruction.halt (.literal 0)).cost 1 :=
      .halt (by simp [step, execute, RealOperand.eval])
    have addTrace : HaltingTrace
        [Instruction.nmul (.reg index) (.literal stride) destination 1,
          Instruction.nadd (.reg destination) (.literal (base + header)) destination 2,
          Instruction.halt (.literal 0)]
        ⟨1, firstMemory⟩ finalMemory 0
          ((Instruction.nadd (.reg destination) (.literal (base + header)) destination 2).cost +
            (Instruction.halt (.literal 0)).cost) 2 :=
      .next (by simp [step, execute, NatOperand.eval, firstMemory, finalMemory]) haltTrace
    exact .next (by simp [step, execute, NatOperand.eval, firstMemory]) addTrace
  · simp [finalMemory, firstMemory, Memory.writeReg, Nat.add_assoc, Nat.add_comm]

/-- Compact exact-real array view: payload starts directly at the region's real base. -/
structure RealArrayRef where
  region : Region

/-- Address of one compact exact-real array element. -/
def RealArrayRef.elementAddress (reference : RealArrayRef) (index : Nat) : Nat :=
  reference.region.realBase + index

/-- A represented compact array exposes its indexed real cell. -/
theorem RealArrayRef.represented_get (reference : RealArrayRef) (values : Array Real)
    (memory : Memory) (represented : Layout.realArray.RepAt reference.region ⟨values⟩ memory)
    (index : Nat) (inRange : index < values.size) :
    memory.realMem (reference.elementAddress index) = values[index] := by
  have streams := represented.2.2.1
  have atIndex := congrArg (fun list ↦ list[index]?) streams
  simpa [Layout.encode, Layout.readReals, RealArrayRef.elementAddress, inRange] using atIndex

/-- Closed program for natural-table indirection followed by an exact-real table read. -/
def indirectRealLookupProgram (indexCell realBase indexAddressRegister indexRegister
    realAddressRegister : Nat) : Program :=
  [.nset (.literal indexCell) indexAddressRegister 1,
    .nload indexAddressRegister indexRegister 2,
    .nadd (.literal realBase) (.reg indexRegister) realAddressRegister 3,
    .halt (.load realAddressRegister)]

/--
Actual two-bank indirect lookup: a natural loaded from `natMem` becomes the address offset for a
real-memory read.  All four fetched transitions occur in the same charged trace.
-/
theorem indirectRealLookup_trace (memory : Memory) (indexCell realBase indexAddressRegister
    indexRegister realAddressRegister : Nat) :
    let index := memory.natMem indexCell
    ∃ final cost,
      HaltingTrace (indirectRealLookupProgram indexCell realBase indexAddressRegister
        indexRegister realAddressRegister) ⟨0, memory⟩ final
        (memory.realMem (realBase + index)) cost 4 ∧
      final.realMem = memory.realMem ∧ final.natMem = memory.natMem ∧
      final.natReg realAddressRegister = realBase + index := by
  dsimp
  let afterAddress := memory.writeReg indexAddressRegister indexCell
  let afterLoad := afterAddress.writeReg indexRegister (memory.natMem indexCell)
  let finalMemory := afterLoad.writeReg realAddressRegister
    (realBase + memory.natMem indexCell)
  let totalCost : Cost :=
    (Instruction.nset (.literal indexCell) indexAddressRegister 1).cost +
      ((Instruction.nload indexAddressRegister indexRegister 2).cost +
        ((Instruction.nadd (.literal realBase) (.reg indexRegister)
          realAddressRegister 3).cost +
          (Instruction.halt (.load realAddressRegister)).cost))
  refine ⟨finalMemory, totalCost, ?_, rfl, rfl, ?_⟩
  · have haltTrace : HaltingTrace
        (indirectRealLookupProgram indexCell realBase indexAddressRegister indexRegister
          realAddressRegister) ⟨3, finalMemory⟩ finalMemory
        (memory.realMem (realBase + memory.natMem indexCell))
        (Instruction.halt (.load realAddressRegister)).cost 1 :=
      .halt (by simp [step, execute, indirectRealLookupProgram, RealOperand.eval,
        finalMemory, afterLoad, afterAddress, Memory.writeReg])
    have addTrace : HaltingTrace
        (indirectRealLookupProgram indexCell realBase indexAddressRegister indexRegister
          realAddressRegister) ⟨2, afterLoad⟩ finalMemory
        (memory.realMem (realBase + memory.natMem indexCell))
        ((Instruction.nadd (.literal realBase) (.reg indexRegister)
          realAddressRegister 3).cost + (Instruction.halt (.load realAddressRegister)).cost) 2 :=
      .next (by simp [step, execute, indirectRealLookupProgram, NatOperand.eval,
        finalMemory, afterLoad, afterAddress, Memory.writeReg, Nat.add_comm]) haltTrace
    have loadTrace : HaltingTrace
        (indirectRealLookupProgram indexCell realBase indexAddressRegister indexRegister
          realAddressRegister) ⟨1, afterAddress⟩ finalMemory
        (memory.realMem (realBase + memory.natMem indexCell))
        ((Instruction.nload indexAddressRegister indexRegister 2).cost +
          ((Instruction.nadd (.literal realBase) (.reg indexRegister)
            realAddressRegister 3).cost +
            (Instruction.halt (.load realAddressRegister)).cost)) 3 :=
      .next (by simp [step, execute, indirectRealLookupProgram, afterLoad, afterAddress,
        Memory.writeReg]) addTrace
    exact .next (by simp [step, execute, indirectRealLookupProgram, NatOperand.eval,
      afterAddress]) loadTrace
  · simp [finalMemory, afterLoad, afterAddress, Memory.writeReg]

/-- Runtime row-major element address computed from represented dimension registers. -/
def MatrixRef.elementPlan
    (baseRegister rowRegister columnRegister columnCountRegister stride : Nat) : NatAddressPlan :=
  .rowMajor baseRegister 0 rowRegister columnRegister columnCountRegister stride

end Algolean.Algorithms.StructuredRealRAM
