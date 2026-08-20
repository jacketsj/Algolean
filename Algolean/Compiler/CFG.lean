/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Core

/-!
# First-order control-flow graphs for the structured real RAM

Branches target shared labels.  They do not contain host-language continuations, so following a
branch cannot materialize the remainder of the program once per arm.  Runtime loops are backward
label references.  The assembler lowers labels to numeric program counters and has an exact
code-size theorem.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM.CFG

/-- A compile-time handle for a real data cell address register. -/
structure RReg where
  /-- Underlying natural address-register number. -/
  index : ℕ
deriving DecidableEq

/-- A compile-time handle for a natural value/address register. -/
structure NReg where
  /-- Underlying natural register number. -/
  index : ℕ
deriving DecidableEq

/-- A first-order basic-block label. -/
structure Label where
  /-- Stable source-level label identifier. -/
  index : ℕ
deriving DecidableEq

/-- Non-branching source operations.  Runtime values remain machine operands and registers. -/
inductive Operation where
  | rset (source : RealOperand) (destination : RReg)
  | radd (left right : RealOperand) (destination : RReg)
  | rsub (left right : RealOperand) (destination : RReg)
  | rmul (left right : RealOperand) (destination : RReg)
  | rdiv (left right : RealOperand) (destination : RReg)
  | rneg (source : RealOperand) (destination : RReg)
  | nset (source : NatOperand) (destination : NReg)
  | nadd (left right : NatOperand) (destination : NReg)
  | nsub (left right : NatOperand) (destination : NReg)
  | nload (address destination : NReg)
  | nstore (source : NatOperand) (address : NReg)
deriving DecidableEq

/-- Every block ends in exactly one first-order terminator. -/
inductive Terminator where
  | jump (target : Label)
  | rbranch (left right : RealOperand) (less equal greater : Label)
  | nbranch (left right : NatOperand) (less equal greater : Label)
  | halt (result : RealOperand)
deriving DecidableEq

/-- A labeled straight-line body and one terminator. -/
structure BasicBlock where
  /-- Label declared by this block. -/
  label : Label
  /-- Straight-line operation body. -/
  body : List Operation
  /-- Single control-flow terminator. -/
  terminator : Terminator
deriving DecidableEq

/-- A finite CFG.  `WellFormed` is the auditable static side condition. -/
structure Program where
  /-- Entry block label. -/
  entry : Label
  /-- Finite materialized basic blocks. -/
  blocks : List BasicBlock
deriving DecidableEq

namespace BasicBlock

/-- Every source operation and the terminator lower to one target instruction. -/
def codeSize (block : BasicBlock) : ℕ := block.body.length + 1

end BasicBlock

namespace Terminator

/-- Labels referenced by a terminator. -/
def targets : Terminator → List Label
  | .jump target => [target]
  | .rbranch _ _ less equal greater | .nbranch _ _ less equal greater =>
      [less, equal, greater]
  | .halt _ => []

end Terminator

namespace Program

/-- Materialized target-code size, computed without generating target syntax. -/
def codeSize (program : Program) : ℕ :=
  (program.blocks.map BasicBlock.codeSize).sum

/-- Labels declared by the program. -/
def labels (program : Program) : List Label := program.blocks.map BasicBlock.label

/--
Static CFG validity: labels are unique, the first block is the entry block, and every target is
closed over the finite block list.
-/
def WellFormed (program : Program) : Prop :=
  program.labels.Nodup ∧
    program.blocks.head?.map BasicBlock.label = some program.entry ∧
    ∀ block ∈ program.blocks, ∀ target ∈ block.terminator.targets,
      target ∈ program.labels

end Program

/-- Program counter of a label, relative to `base`; zero is returned only for an absent label. -/
def labelPCFrom : ℕ → List BasicBlock → Label → ℕ
  | _, [], _ => 0
  | base, block :: blocks, label =>
      if block.label = label then base
      else labelPCFrom (base + block.codeSize) blocks label

/-- Program counter of a label in the final assembled list. -/
def labelPC (blocks : List BasicBlock) (label : Label) : ℕ :=
  labelPCFrom 0 blocks label

/-- Lower one straight-line source operation with its fallthrough successor. -/
def compileOperation (operation : Operation) (next : ℕ) : Instruction :=
  match operation with
  | .rset source destination => .rset source destination.index next
  | .radd left right destination => .radd left right destination.index next
  | .rsub left right destination => .rsub left right destination.index next
  | .rmul left right destination => .rmul left right destination.index next
  | .rdiv left right destination => .rdiv left right destination.index next
  | .rneg source destination => .rneg source destination.index next
  | .nset source destination => .nset source destination.index next
  | .nadd left right destination => .nadd left right destination.index next
  | .nsub left right destination => .nsub left right destination.index next
  | .nload address destination => .nload address.index destination.index next
  | .nstore source address => .nstore source address.index next

/-- Lower a straight-line body starting at `pc`. -/
def compileBody : ℕ → List Operation → List Instruction
  | _, [] => []
  | pc, operation :: operations =>
      compileOperation operation (pc + 1) :: compileBody (pc + 1) operations

/-- Lower one terminator using the final label table. -/
def compileTerminator (allBlocks : List BasicBlock) : Terminator → Instruction
  | .jump target => .jump (labelPC allBlocks target)
  | .rbranch left right less equal greater =>
      .rcompare left right (labelPC allBlocks less) (labelPC allBlocks equal)
        (labelPC allBlocks greater)
  | .nbranch left right less equal greater =>
      .ncompare left right (labelPC allBlocks less) (labelPC allBlocks equal)
        (labelPC allBlocks greater)
  | .halt result => .halt result

/-- Assemble blocks in source order, retaining one copy of every shared continuation block. -/
def compileBlocks (allBlocks : List BasicBlock) : ℕ → List BasicBlock → List Instruction
  | _, [] => []
  | pc, block :: blocks =>
      compileBody pc block.body ++
        compileTerminator allBlocks block.terminator ::
          compileBlocks allBlocks (pc + block.codeSize) blocks

/-- Assemble a finite CFG to one fixed numeric-jump program. -/
def compile (program : Program) : StructuredRealRAM.Program :=
  compileBlocks program.blocks 0 program.blocks

@[simp]
theorem compileBody_length (pc : ℕ) (body : List Operation) :
    (compileBody pc body).length = body.length := by
  induction body generalizing pc with
  | nil => rfl
  | cons operation body induction => simp [compileBody, induction]

theorem compileBlocks_length (allBlocks blocks : List BasicBlock) (pc : ℕ) :
    (compileBlocks allBlocks pc blocks).length =
      (blocks.map BasicBlock.codeSize).sum := by
  induction blocks generalizing pc with
  | nil => rfl
  | cons block blocks induction =>
      simp [compileBlocks, BasicBlock.codeSize, induction]
      omega

/-- Exact code-size theorem required of the CFG assembler. -/
theorem compile_length (program : Program) :
    (compile program).length = program.codeSize := by
  exact compileBlocks_length program.blocks program.blocks 0

/-- A branch block contributes its body once plus one terminator, independent of arm count. -/
theorem branch_block_codeSize (label : Label) (body : List Operation)
    (left right : NatOperand) (less equal greater : Label) :
    (BasicBlock.mk label body (.nbranch left right less equal greater)).codeSize =
      body.length + 1 := rfl

/--
Build a two-way conditional with one shared continuation block.  Natural conditions equal to zero
take `otherwise`; positive conditions take `then`.  The continuation syntax occurs exactly once.
-/
def ifThenElseBlocks (branchLabel thenLabel elseLabel joinLabel : Label)
    (condition : NatOperand) (thenBody elseBody joinBody : List Operation)
    (joinTerminator : Terminator) : List BasicBlock := [
  ⟨branchLabel, [], .nbranch condition (.literal 0) elseLabel elseLabel thenLabel⟩,
  ⟨thenLabel, thenBody, .jump joinLabel⟩,
  ⟨elseLabel, elseBody, .jump joinLabel⟩,
  ⟨joinLabel, joinBody, joinTerminator⟩
]

/-- The shared-join conditional materializes each body and continuation once. -/
theorem ifThenElseBlocks_codeSize (branchLabel thenLabel elseLabel joinLabel : Label)
    (condition : NatOperand) (thenBody elseBody joinBody : List Operation)
    (joinTerminator : Terminator) :
    ((Program.mk branchLabel
      (ifThenElseBlocks branchLabel thenLabel elseLabel joinLabel condition
        thenBody elseBody joinBody joinTerminator)).codeSize) =
      thenBody.length + elseBody.length + joinBody.length + 4 := by
  simp [Program.codeSize, ifThenElseBlocks, BasicBlock.codeSize]
  omega

/-- A runtime loop is represented by an ordinary backward label target, not host iteration. -/
def whileBlocks (header body exit : Label) (conditionLeft conditionRight : NatOperand)
    (bodyOperations : List Operation) : List BasicBlock := [
  ⟨header, [], .nbranch conditionLeft conditionRight exit body body⟩,
  ⟨body, bodyOperations, .jump header⟩
]

/--
Runtime `for` loop blocks.  The counter is compared with `limit` at the header, incremented in the
body, and followed by a backward jump.  `bodyOperations` is not host-language unrolling.
-/
def forRangeBlocks (header body exit : Label) (counter : NReg) (limit : NatOperand)
    (bodyOperations : List Operation) : List BasicBlock := [
  ⟨header, [], .nbranch (.reg counter.index) limit body exit exit⟩,
  ⟨body, bodyOperations ++ [.nadd (.reg counter.index) (.literal 1) counter], .jump header⟩
]

end Algolean.Algorithms.StructuredRealRAM.CFG
