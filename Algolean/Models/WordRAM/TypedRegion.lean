/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.WordRAM.Data.Physical

/-!
# Typed Word-RAM regions and first-order address plans

References retain the concrete closed layout selected at problem construction.  Fixed-stride
indexing requires a `FixedFootprint` witness.  Runtime address calculations are reified as closed
plans and lower to ordinary RAM instructions; they do not execute Lean callbacks on machine data.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- A typed region stores closed layout syntax and a machine base address. -/
structure TypedRegion (w : Nat) (alpha : Type) where
  layout : WordLayout w alpha
  region : Region w

/-- A typed reference into ordinary Word-RAM memory. -/
abbrev Ref (w : Nat) (alpha : Type) := TypedRegion w alpha

/-- Closed paths through structural layouts; no `alpha → beta` projection is accepted. -/
inductive Path (w : Nat) : WordLayout w alpha → WordLayout w beta → Type 1 where
  | prodFst (left : WordLayout w alpha) (right : WordLayout w beta) :
      Path w (.prod left right) left
  | prodSnd (left : WordLayout w alpha) (right : WordLayout w beta)
      (leftWords : Nat) : Path w (.prod left right) right
  | subtypeValue (predicate : alpha → Prop) (base : WordLayout w alpha) :
      Path w (.subtype predicate base) base
  | taggedValue (tag : DataTag) (base : WordLayout w alpha) :
      Path w (.tagged tag base) base
  | then (first : Path w source middle) (second : Path w middle target) :
      Path w source target

namespace Ref

def ofCanonical (w : Nat) (alpha : Type) [CanonicalLayout w alpha]
    (base : BitVec w) : Ref w alpha :=
  ⟨layoutOf w alpha, ⟨base⟩⟩

def Rep (reference : Ref w alpha) (value : alpha) (memory : Memory w) : Prop :=
  reference.layout.RepAt reference.region value memory

end Ref

/- Typed product projections.  The right projection requires a fixed left footprint. -/
namespace ProdRef

@[nolint unusedArguments]
def fst (left : WordLayout w alpha) (_right : WordLayout w beta)
    (reference : Ref w (alpha × beta)) : Ref w alpha :=
  ⟨left, reference.region⟩

@[nolint unusedArguments]
def snd (_left : WordLayout w alpha) (right : WordLayout w beta)
    (leftWords : Nat) (reference : Ref w (alpha × beta)) : Ref w beta :=
  ⟨right, ⟨BitVec.ofNat w (reference.region.base.toNat + leftWords)⟩⟩

end ProdRef

/-- A typed length-prefixed array view. -/
structure ArrayRef (w : Nat) (alpha : Type) where
  elementLayout : WordLayout w alpha
  base : BitVec w

namespace ArrayRef

/-- The first represented word is the canonical array length header. -/
def lengthAddress (reference : ArrayRef w alpha) : BitVec w := reference.base

/-- Fixed-stride element address.  Variable-footprint arrays deliberately have no such operation. -/
def elementAddress (reference : ArrayRef w alpha) (stride index : Nat) : BitVec w :=
  BitVec.ofNat w (reference.base.toNat + 1 + index * stride)

def get (reference : ArrayRef w alpha) (stride index : Nat) : Ref w alpha :=
  ⟨reference.elementLayout, ⟨reference.elementAddress stride index⟩⟩

/-- Canonical constant-time indexing is available only from a fixed-footprint witness. -/
@[nolint unusedArguments]
def getFixed [fixed : FixedFootprint w alpha]
    (reference : ArrayRef w alpha) (_layoutMatches : reference.elementLayout = fixed.layout)
    (index : Nat) : Ref w alpha :=
  ⟨fixed.layout, ⟨reference.elementAddress fixed.words index⟩⟩

end ArrayRef

/-- A typed row-major runtime matrix view. -/
structure MatrixRef (w : Nat) (alpha : Type) where
  elementLayout : WordLayout w alpha
  base : BitVec w

namespace MatrixRef

/-- Header convention: rows, columns, array length, then row-major payload. -/
def dataBase (reference : MatrixRef w alpha) : Nat := reference.base.toNat + 3

@[nolint unusedArguments]
def elementAddress (reference : MatrixRef w alpha) (stride _rows cols row column : Nat) :
    BitVec w :=
  BitVec.ofNat w (reference.dataBase + (row * cols + column) * stride)

def get (reference : MatrixRef w alpha) (stride rows cols row column : Nat) : Ref w alpha :=
  ⟨reference.elementLayout, ⟨reference.elementAddress stride rows cols row column⟩⟩

end MatrixRef

/-- Closed address calculations supported by the typed builder. -/
inductive AddressPlan (w : Nat) where
  | constant (address : BitVec w)
  | addConstant (base : BitVec w) (offset : Nat)
  | fixedIndex (base : BitVec w) (headerWords stride : Nat) (indexRegister : Nat)
  | registerFixedIndex (baseRegister headerWords stride indexRegister : Nat)
deriving DecidableEq, Repr

namespace AddressPlan

/-- Unbounded address calculation used to state the absence of modular wraparound. -/
def evalNat (plan : AddressPlan w) (memory : Memory w) : Nat :=
  match plan with
  | .constant address => address.toNat
  | .addConstant base offset => base.toNat + offset
  | .fixedIndex base headerWords stride indexRegister =>
      base.toNat + headerWords + (memory.address indexRegister).toNat * stride
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      (memory.address baseRegister).toNat + headerWords +
        (memory.address indexRegister).toNat * stride

/-- The calculated address is genuinely representable, rather than silently reduced modulo width. -/
def NoWrap (plan : AddressPlan w) (memory : Memory w) : Prop :=
  plan.evalNat memory < 2 ^ w

/-- Syntactic fragment which changes address registers but never the data bank. -/
def AddressOnly : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w) → Prop
  | .setAddress _ _ _ | .addAddress _ _ _ _ | .subAddress _ _ _ _ => True
  | .extra (.valueToAddress _ _) _ | .extra (.mulAddress _ _ _) _ => True
  | _ => False

/-- Mathematical modulo-`2^w` interpretation of a closed plan. -/
def eval (plan : AddressPlan w) (memory : Memory w) : BitVec w :=
  match plan with
  | .constant address => address
  | .addConstant base offset => BitVec.ofNat w (base.toNat + offset)
  | .fixedIndex base headerWords stride indexRegister =>
      BitVec.ofNat w
        (base.toNat + headerWords + (memory.address indexRegister).toNat * stride)
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      BitVec.ofNat w
        ((memory.address baseRegister).toNat + headerWords +
          (memory.address indexRegister).toNat * stride)

/-- Under the explicit fit obligation, the machine word denotes the unbounded address exactly. -/
theorem eval_toNat_eq (plan : AddressPlan w) (memory : Memory w)
    (noWrap : plan.NoWrap memory) :
    (plan.eval memory).toNat = plan.evalNat memory := by
  cases plan with
  | constant => rfl
  | addConstant | fixedIndex | registerFixedIndex =>
      simp only [NoWrap, evalNat] at noWrap
      simp only [eval, evalNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt noWrap

/-- Number of ordinary instructions emitted by the plan. -/
def cost : AddressPlan w → Nat
  | .constant _ => 1
  | .addConstant _ _ => 1
  | .fixedIndex _ _ _ _ => 2
  | .registerFixedIndex _ _ _ _ => 3

def repeatedAdds (indexRegister destination start : Nat) : Nat → Program w
  | 0 => []
  | count + 1 =>
      .addAddress (.reg destination) (.reg indexRegister) destination (start + 1) ::
        repeatedAdds indexRegister destination (start + 1) count

/-- Lower a plan to finite first-order core Word-RAM syntax. -/
def compile (plan : AddressPlan w) (destination start next : Nat) : Program w :=
  match plan with
  | .constant address => [.setAddress (.immediate address) destination next]
  | .addConstant base offset =>
      [.setAddress (.immediate (BitVec.ofNat w (base.toNat + offset))) destination next]
  | .fixedIndex base headerWords stride indexRegister =>
      [.extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
          destination) (start + 1),
        .addAddress (.reg destination)
          (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination next]
  | .registerFixedIndex baseRegister headerWords stride indexRegister =>
      [.extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
          destination) (start + 1),
        .addAddress (.reg destination) (.reg baseRegister) destination (start + 2),
        .addAddress (.reg destination) (.immediate (BitVec.ofNat w headerWords))
          destination next]

theorem repeatedAdds_length (indexRegister destination start count : Nat) :
    (repeatedAdds (w := w) indexRegister destination start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [repeatedAdds, ih]

/-- Exact emitted instruction count; this is also the unit-cost address-computation charge. -/
theorem compile_length (plan : AddressPlan w) (destination start next : Nat) :
    (plan.compile destination start next).length = plan.cost := by
  cases plan <;> simp [compile, cost]

/-- Every emitted address-plan instruction belongs to the address-only fragment. -/
theorem repeatedAdds_addressOnly (indexRegister destination start count : Nat) :
    ∀ instruction ∈ repeatedAdds (w := w) indexRegister destination start count,
      AddressOnly instruction := by
  induction count generalizing start with
  | zero => simp [repeatedAdds]
  | succ count ih =>
      intro instruction member
      simp only [repeatedAdds, List.mem_cons] at member
      rcases member with rfl | member
      · trivial
      · exact ih (start + 1) instruction member

/-- Every emitted accessor instruction preserves the complete data-memory bank. -/
theorem compile_addressOnly (plan : AddressPlan w) (destination start next : Nat) :
    ∀ instruction ∈ plan.compile destination start next, AddressOnly instruction := by
  cases plan <;> simp [compile, AddressOnly]

/-- Every emitted instruction is fixed first-order syntax and preserves the complete data bank. -/
theorem compile_firstOrder (plan : AddressPlan w) (destination start next : Nat) :
    ∀ instruction ∈ plan.compile destination start next, AddressOnly instruction :=
  plan.compile_addressOnly destination start next

/-- Executing one address-only instruction cannot alter any data cell. -/
theorem AddressOnly.execute_preservesData
    {instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w)}
    (addressOnly : AddressOnly instruction) (memory : Memory w)
    (next : Configuration w)
    (executes : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction memory = .running next) :
    next.memory.data = memory.data := by
  cases instruction with
  | set | add | sub | mul | div | neg | compare | compareAddress | halt =>
      simp [AddressOnly] at addressOnly
  | setAddress | addAddress | subAddress =>
      simp only [RAM.execute] at executes
      cases executes
      rfl
  | extra extra successor =>
      cases extra with
      | valueToAddress source destination =>
          simp only [RAM.execute] at executes
          cases executes
          rfl
      | addressToValue source destination => simp [AddressOnly] at addressOnly
      | mulAddress left right destination =>
          simp only [RAM.execute] at executes
          cases executes
          rfl

/-- Evaluation of a fixed-index plan exposes the exact modulo-word address formula. -/
theorem eval_fixedIndex (base : BitVec w) (headerWords stride indexRegister : Nat)
    (memory : Memory w) :
    (AddressPlan.fixedIndex base headerWords stride indexRegister).eval memory =
      BitVec.ofNat w
        (base.toNat + headerWords + (memory.address indexRegister).toNat * stride) := rfl

/--
Actual same-trace execution of a fixed-stride address accessor.  Both address operations and the
halt are charged, the data bank is preserved, and the destination contains the plan result.
-/
theorem fixedIndex_trace (memory : Memory w) (base : BitVec w)
    (headerWords stride indexRegister destination : Nat) :
    let plan := AddressPlan.fixedIndex base headerWords stride indexRegister
    let program := plan.compile destination 0 2 ++ [.halt (.immediate 0)]
    ∃ final,
      RAM.HaltingTrace (stepCosted program) ⟨0, memory⟩ final 0 3 3 ∧
      final.address destination =
        memory.address indexRegister * BitVec.ofNat w stride +
          BitVec.ofNat w (base.toNat + headerWords) ∧
      final.data = memory.data := by
  dsimp [AddressPlan.compile, AddressPlan.eval]
  let scaled := memory.writeAddress destination
    (memory.address indexRegister * BitVec.ofNat w stride)
  let finalMemory := scaled.writeAddress destination
    (memory.address indexRegister * BitVec.ofNat w stride +
      BitVec.ofNat w (base.toNat + headerWords))
  refine ⟨finalMemory, ?_, ?_, rfl⟩
  · have haltTrace : RAM.HaltingTrace
        (stepCosted [
          .extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
            destination) 1,
          .addAddress (.reg destination)
            (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination 2,
          .halt (.immediate 0)])
        ⟨2, finalMemory⟩ finalMemory 0 1 1 :=
      .halt (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, RAM.execute, RAM.Operand.eval, WordRAM.ops])
    have addTrace : RAM.HaltingTrace
        (stepCosted [
          .extra (.mulAddress (.reg indexRegister) (.immediate (BitVec.ofNat w stride))
            destination) 1,
          .addAddress (.reg destination)
            (.immediate (BitVec.ofNat w (base.toNat + headerWords))) destination 2,
          .halt (.immediate 0)])
        ⟨1, scaled⟩ finalMemory 0 2 2 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, RAM.execute, WordRAM.ops, RAM.AddressOperand.eval,
        scaled, finalMemory, RAM.Memory.writeAddress]) haltTrace
    exact .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
      RAM.CostedSemantics.unit, RAM.execute, WordRAM.evalExtra, RAM.AddressOperand.eval,
      scaled, RAM.Memory.writeAddress]) addTrace
  · simp [finalMemory, scaled, RAM.Memory.writeAddress]

end AddressPlan

/-- A closed accessor bundles its plan, destination register, and exact unit cost. -/
structure CertifiedAccessor (w : Nat) where
  plan : AddressPlan w
  destinationRegister : Nat
  start : Nat
  next : Nat

namespace CertifiedAccessor

def code (accessor : CertifiedAccessor w) : Program w :=
  accessor.plan.compile accessor.destinationRegister accessor.start accessor.next

theorem cost (accessor : CertifiedAccessor w) :
    accessor.code.length = accessor.plan.cost := accessor.plan.compile_length _ _ _

theorem firstOrder (accessor : CertifiedAccessor w) :
    ∀ instruction ∈ accessor.code, AddressPlan.AddressOnly instruction :=
  accessor.plan.compile_firstOrder _ _ _

/-- `_cost`: the exact charge is the number of ordinary emitted instructions. -/
theorem _cost (accessor : CertifiedAccessor w) :
    accessor.code.length = accessor.plan.cost := accessor.cost

/-- `_correct`: the accessor code is exactly the lowering of its closed semantic plan. -/
theorem _correct (accessor : CertifiedAccessor w) :
    accessor.code = accessor.plan.compile accessor.destinationRegister accessor.start
      accessor.next := rfl

/-- `_preservesFrame`: every emitted step preserves all caller-owned data cells. -/
theorem _preservesFrame (accessor : CertifiedAccessor w)
    {instruction : RAM.Instruction (BitVec w) (BitVec w) (ExtraInstruction w)}
    (member : instruction ∈ accessor.code) (memory : Memory w) (next : Configuration w)
    (executes : RAM.execute (WordRAM.ops w) WordRAM.evalExtra instruction memory = .running next) :
    next.memory.data = memory.data :=
  (accessor.plan.compile_addressOnly _ _ _ instruction member).execute_preservesData
    memory next executes

end CertifiedAccessor

/-- Minimal closed program exercising data-dependent random access twice. -/
def indirectLookupProgram (indexAddress pointerBase valueBase : BitVec w)
    (indexRegister pointerAddressRegister pointerRegister valueAddressRegister : Nat) :
    Program w :=
  [.extra (.valueToAddress (.load (.immediate indexAddress)) indexRegister) 1,
    .addAddress (.immediate pointerBase) (.reg indexRegister) pointerAddressRegister 2,
    .extra (.valueToAddress (.load (.reg pointerAddressRegister)) pointerRegister) 3,
    .addAddress (.immediate valueBase) (.reg pointerRegister) valueAddressRegister 4,
    .halt (.load (.reg valueAddressRegister))]

/--
Actual same-trace indirect lookup: the word loaded from the pointer table becomes the address of
the value-table read.  The five fetched instructions are all charged.
-/
theorem indirectLookup_trace (memory : Memory w) (indexAddress pointerBase valueBase : BitVec w)
    (indexRegister pointerAddressRegister pointerRegister valueAddressRegister : Nat) :
    let index := memory.data indexAddress
    let pointerAddress := pointerBase + index
    let pointer := memory.data pointerAddress
    let valueAddress := valueBase + pointer
    ∃ final,
      RAM.HaltingTrace (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
        indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨0, memory⟩ final (memory.data valueAddress) 5 5 ∧
      final.data = memory.data ∧
      final.address valueAddressRegister = valueAddress := by
  dsimp
  let afterIndex := memory.writeAddress indexRegister (memory.data indexAddress)
  let afterPointerAddress := afterIndex.writeAddress pointerAddressRegister
    (pointerBase + memory.data indexAddress)
  let afterPointer := afterPointerAddress.writeAddress pointerRegister
    (memory.data (pointerBase + memory.data indexAddress))
  let finalMemory := afterPointer.writeAddress valueAddressRegister
    (valueBase + memory.data (pointerBase + memory.data indexAddress))
  refine ⟨finalMemory, ?_, rfl, ?_⟩
  · have haltTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨4, finalMemory⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 1 1 :=
      .halt (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, RAM.Operand.eval,
        RAM.AddressOperand.eval, WordRAM.ops,
        finalMemory, afterPointer, afterPointerAddress, afterIndex, RAM.Memory.writeAddress])
    have valueAddressTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨3, afterPointer⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 2 2 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.ops,
        RAM.AddressOperand.eval, afterPointer, finalMemory,
        afterPointerAddress, afterIndex, RAM.Memory.writeAddress]) haltTrace
    have pointerTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨2, afterPointerAddress⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 3 3 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.evalExtra,
        WordRAM.ops, RAM.Operand.eval, RAM.AddressOperand.eval, afterPointer,
        afterPointerAddress, afterIndex, RAM.Memory.writeAddress]) valueAddressTrace
    have pointerAddressTrace : RAM.HaltingTrace
        (stepCosted (indirectLookupProgram indexAddress pointerBase valueBase
          indexRegister pointerAddressRegister pointerRegister valueAddressRegister))
        ⟨1, afterIndex⟩ finalMemory
        (memory.data (valueBase + memory.data (pointerBase + memory.data indexAddress))) 4 4 :=
      .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
        RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.ops,
        RAM.AddressOperand.eval, afterPointerAddress, afterIndex,
        RAM.Memory.writeAddress]) pointerTrace
    exact .next (by simp [stepCosted, costedSemantics, RAM.CostedSemantics.step,
      RAM.CostedSemantics.unit, indirectLookupProgram, RAM.execute, WordRAM.evalExtra,
      WordRAM.ops, RAM.Operand.eval, RAM.AddressOperand.eval, afterIndex,
      RAM.Memory.writeAddress]) pointerAddressTrace
  · simp [finalMemory, afterPointer, afterPointerAddress, afterIndex, RAM.Memory.writeAddress]

/-- Runtime CSR view with explicitly maintained address registers for dynamic subregions. -/
structure CSRGraphRef (w : Nat) (edgeData : Type) where
  dataLayout : WordLayout w edgeData
  graphBaseRegister : Nat
  offsetsBaseRegister : Nat
  destinationsBaseRegister : Nat
  payloadBaseRegister : Nat

namespace CSRGraphRef

def vertexCountPlan (reference : CSRGraphRef w edgeData) : AddressPlan w :=
  .registerFixedIndex reference.graphBaseRegister 0 0 reference.graphBaseRegister

def edgeCountPlan (reference : CSRGraphRef w edgeData) : AddressPlan w :=
  .registerFixedIndex reference.graphBaseRegister 1 0 reference.graphBaseRegister

def neighborStartPlan (reference : CSRGraphRef w edgeData) (vertexRegister : Nat) :
    AddressPlan w :=
  .registerFixedIndex reference.offsetsBaseRegister 1 1 vertexRegister

def neighborEndPlan (reference : CSRGraphRef w edgeData) (vertexPlusOneRegister : Nat) :
    AddressPlan w :=
  .registerFixedIndex reference.offsetsBaseRegister 1 1 vertexPlusOneRegister

def destinationPlan (reference : CSRGraphRef w edgeData) (edgeRegister : Nat) : AddressPlan w :=
  .registerFixedIndex reference.destinationsBaseRegister 1 1 edgeRegister

def dataPlan (reference : CSRGraphRef w edgeData) (stride edgeRegister : Nat) : AddressPlan w :=
  .registerFixedIndex reference.payloadBaseRegister 1 stride edgeRegister

end CSRGraphRef

end Algolean.Algorithms.WordRAM
