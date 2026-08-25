/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMLinking
public import Algolean.Complexity.WordRAMUniformProcedure

/-!
# Certified derived Word-RAM operation libraries

This layer expresses the usual rich-to-core robustness workflow without adding an arbitrary
unit-cost operation to the machine.  Initialization and every derived operation are ordinary
typed procedures.  The existing shared-body linker executes their instructions in the final core
trace and materializes each body once.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

noncomputable section

/-- Closed names for conventional derived scalar word operations. -/
inductive DerivedOperationKind where
  | bitAnd | bitOr | bitXor | shiftLeft | shiftRight
  | countLeadingZeros | countTrailingZeros
  | integerPower | integerLog | fixedRoot
deriving DecidableEq, Repr

/-- Audit-visible assumptions under which a rich operation library simulates the core model. -/
structure DerivedOperationAssumptions (w : Nat) where
  /-- Descriptive only; asymptotic claims must use `DerivedOperationRobustness`. -/
  widthRelation : String
  maximumRegisterValue : Nat
  maximumAddress : Nat
  spaceWords : Nat
  polynomialIntegerWords : Nat
  maximumRegisterValue_fits : maximumRegisterValue < 2 ^ w
  maximumAddress_fits : maximumAddress < 2 ^ w
  space_fits : spaceWords ≤ 2 ^ w

/--
A completed library is a finite typed signature with one distinguished initialization operation.
All implementations are restoring core Word-RAM procedures; no operation evaluator is stored.
-/
structure PreprocessedWordOperationLibrary (w : Nat) where
  signature : DependencySignature w
  initializationOp : signature.Op
  /-- Fixed public initializer input; it cannot be selected from the client problem input. -/
  initializationInput : (signature.contract initializationOp).Input
  initializationInputValid :
    (signature.contract initializationOp).pre initializationInput
  operationKind : signature.Op → Option DerivedOperationKind
  initialization_not_derived : operationKind initializationOp = none
  implementations : ImplementationEnvironment signature
  assumptions : DerivedOperationAssumptions w
  tableRegion : Region w
  tableWords : Nat
  tableWords_le_space : tableWords ≤ assumptions.spaceWords
  /-- Initialization writes only through its certified ABI and later operations preserve it. -/
  tableReadOnlyAfterInit :
    ∀ (op : signature.Op), op ≠ initializationOp →
      ∀ (input : (signature.contract op).Input)
        (_validInput : (signature.contract op).pre input) (initial : Memory w),
        (signature.contract op).inputLayout.RepAt
          (implementations.implementation op).calling.inputRegion input initial →
        ∀ address,
          (tableRegion.base.toNat ≤ address.toNat ∧
            address.toNat < tableRegion.base.toNat + tableWords) →
          ((signature.contract op).outputLayout.writeAt
            (implementations.implementation op).calling.outputRegion
            ((implementations.implementation op).output input) initial).data address =
              initial.data address

namespace PreprocessedWordOperationLibrary

/-- Closed list of derived operations implemented by the library. -/
def derivedOperations (library : PreprocessedWordOperationLibrary w) :
    List DerivedOperationKind :=
  (Linker.operations library.signature).filterMap library.operationKind

/-- Initialization is itself one ordinary certified procedure with a visible exact bound. -/
def preprocessingBound (library : PreprocessedWordOperationLibrary w) :
    ProcedureBound (library.signature.contract library.initializationOp) :=
  library.signature.bound library.initializationOp

/-- The concrete initializer certificate used by the core linker. -/
def preprocessing (library : PreprocessedWordOperationLibrary w) :
    RestoringProcedureCertificate
      (library.signature.contract library.initializationOp) library.preprocessingBound :=
  library.implementations.implementation library.initializationOp

end PreprocessedWordOperationLibrary

/--
A rich-profile client whose dynamic relative trace performs initialization exactly once.  This is
stronger than merely containing one syntactic call site: it excludes placing that site in a loop.
-/
structure RichWordAlgorithmCertificate (library : PreprocessedWordOperationLibrary w)
    (problem : StructuredProblem w)
    (relativeBound linkedBound : problem.Input → Nat) where
  client : RelativeAlgorithmCertificate library.signature problem relativeBound
  linkerConfiguration : Linker.Configuration w
  /-- Concrete ABI compatibility and exact dynamic-overhead proof for this fixed library. -/
  link : client.ConcreteLink library.implementations linkerConfiguration
    (relativeBound := relativeBound) (linkedBound := linkedBound)
  preprocessingRunsOnce :
    ∀ responder input validInput final result cost calls,
      OpenHaltingTrace library.signature responder client.program
        ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
      dependencyCallCount library.initializationOp calls = 1
  /-- Every dynamic initializer call receives the library's fixed input, excluding input advice. -/
  preprocessingInputFixed :
    ∀ responder input validInput final result cost calls,
      OpenHaltingTrace library.signature responder client.program
        ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
      ∀ call ∈ calls, call.op = library.initializationOp →
        HEq call.input library.initializationInput
  /-- A rich certificate actually invokes at least one declared derived operation. -/
  usesDerivedOperation :
    ∃ op : library.signature.Op,
      library.operationKind op ≠ none ∧
      ∀ responder input validInput final result cost calls,
        OpenHaltingTrace library.signature responder client.program
          ⟨0, problem.initialMemory input validInput⟩ final result cost calls →
        0 < dependencyCallCount op calls

namespace RichWordAlgorithmCertificate

/--
Lower a rich client to the sealed core Word RAM.  Initialization and every derived operation body
are linked as ordinary finite code, and the client certificate's exact linked bound already
includes every dynamic call plus syntax-derived setup/return overhead.
-/
def lowerToCore
    (algorithm : RichWordAlgorithmCertificate library problem relativeBound linkedBound) :
    FixedWidthAlgorithmCertificateBy problem linkedBound :=
  algorithm.link.certificate

/-- Proposition-level rich-to-core discharge retaining the inspectable concrete certificate. -/
theorem hasCoreAlgorithm
    (algorithm : RichWordAlgorithmCertificate library problem relativeBound linkedBound) :
    problem.HasAlgorithmBy linkedBound :=
  ⟨algorithm.lowerToCore⟩

/-- The initializer's implementation body occurs exactly once in linked program syntax. -/
theorem preprocessingBody_materialized_once
    (algorithm : RichWordAlgorithmCertificate library problem relativeBound linkedBound) :
    (Linker.implementationBody algorithm.client.program library.implementations
      algorithm.linkerConfiguration library.initializationOp).length =
      (library.implementations.implementation library.initializationOp).module.code.length := by
  simp [Linker.implementationBody]

/-- The complete linked instruction-count equation includes all bodies and one dispatcher. -/
theorem lowerToCore_instructionCount
    (algorithm : RichWordAlgorithmCertificate library problem relativeBound linkedBound) :
    algorithm.lowerToCore.program.length =
      algorithm.client.program.length +
        Linker.implementationCodeSize library.implementations +
        2 * algorithm.client.program.length + 1 :=
  Linker.link_length _ _ _

end RichWordAlgorithmCertificate

/-! ## Width-uniform operation-set robustness -/

/-- One finite operation family with one sealed template per operation and width. -/
structure UniformPreprocessedWordOperationLibrary where
  signature : UniformDependencySignature
  initializationOp : signature.Op
  initializationInput : (width : AdmissibleWidth) →
    ((signature.procedure initializationOp).contract width).Input
  initializationInputValid : ∀ (width : AdmissibleWidth),
    ((signature.procedure initializationOp).contract width).pre
      (initializationInput width)
  operationKind : signature.Op → Option DerivedOperationKind
  initialization_not_derived : operationKind initializationOp = none
  implementations : UniformImplementationEnvironment signature
  tableWords : AdmissibleWidth → Nat

namespace UniformPreprocessedWordOperationLibrary

def preprocessingCost (library : UniformPreprocessedWordOperationLibrary)
    (width : AdmissibleWidth) : Nat :=
  (library.signature.procedure library.initializationOp).bound width
    (library.initializationInput width)

end UniformPreprocessedWordOperationLibrary

/--
Formal asymptotic robustness theorem.  Every relation formerly represented only by prose is an
inequality, and width-uniformity follows from the finite `UniformProgram` templates stored in the
library's certified implementation environment.
-/
structure DerivedOperationRobustness (family : UniformStructuredProblem)
    (library : UniformPreprocessedWordOperationLibrary) where
  inputSize : (width : AdmissibleWidth) → (family.problem width).Input → Nat
  requiredIndexBits : (width : AdmissibleWidth) →
    (family.problem width).Input → Nat
  widthUpperConstant : Nat
  preprocessingLinearConstant : Nat
  preprocessingLinearOffset : Nat
  preprocessingSpaceConstant : Nat
  preprocessingSpaceOffset : Nat
  widthLower : ∀ (width : AdmissibleWidth) input,
    family.WidthAdmissible width input →
      requiredIndexBits width input ≤ width.value
  widthUpper : ∀ (width : AdmissibleWidth) input,
    family.WidthAdmissible width input →
      width.value ≤ widthUpperConstant * Nat.log2 (inputSize width input + 2)
  preprocessingLinear : ∀ (width : AdmissibleWidth) input,
    family.WidthAdmissible width input →
      library.preprocessingCost width ≤
        preprocessingLinearConstant * inputSize width input + preprocessingLinearOffset
  preprocessingSpace : ∀ (width : AdmissibleWidth) input,
    family.WidthAdmissible width input →
      library.tableWords width ≤
        preprocessingSpaceConstant * inputSize width input + preprocessingSpaceOffset
  addressSpaceFit : ∀ (width : AdmissibleWidth),
    library.tableWords width ≤ 2 ^ width.value
  operationConstant : ∀ op, op ≠ library.initializationOp →
    ∃ constant : Nat, ∀ (width : AdmissibleWidth) input,
      ((library.signature.procedure op).contract width).pre input →
      (library.signature.procedure op).bound width input ≤ constant

namespace DerivedOperationRobustness

/-- Uniformity is theorem-visible: one fixed template exists for each finite operation. -/
def operationTemplate (_robustness : DerivedOperationRobustness family library)
    (op : library.signature.Op) : UniformProgram :=
  (library.implementations.implementation op).program

/-- No arbitrary width-indexed program choice appears in a robustness certificate. -/
theorem instantiatedCode_eq (robustness : DerivedOperationRobustness family library)
    (op : library.signature.Op) (width : AdmissibleWidth) :
    ((library.implementations.implementation op).certificateAt width).module.code =
      (robustness.operationTemplate op).instantiate width.value :=
  (library.implementations.implementation op).code_eq width

end DerivedOperationRobustness

end

end Algolean.Algorithms.WordRAM
