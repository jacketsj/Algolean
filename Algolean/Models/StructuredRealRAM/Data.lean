/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.CanonicalLayout

/-!
# Generic physical data for the structured exact-real/natural RAM

These types name physical formats.  They do not choose a representation for an abstract graph or
perform conversions.  Proof fields state shape and indexing invariants and are erased by the
closed subtype layout.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

/-- Compact exact-real payload: one natural length and contiguous real cells. -/
abbrev RealArray := Tagged .realArray (Array Real)

/-- Compact natural payload: one natural length and contiguous natural cells. -/
abbrev NatArray := Tagged .natArray (Array Nat)

instance (priority := 1100) : CanonicalLayout RealArray := ⟨.realArray⟩
instance (priority := 1100) : CanonicalLayout NatArray := ⟨.natArray⟩

/-- Named fixed-stride array; availability of constant-time access additionally requires proof. -/
abbrev FixedStrideArray (alpha : Type) := Tagged .fixedStrideArray (Array alpha)

/-- Indexed variable-footprint payload with exact two-bank boundaries. -/
def IndexedArray.Valid [Inhabited alpha] (element : Layout alpha)
    (payload : Array (Nat × Nat) × Array alpha) : Prop :=
  payload.1.size = payload.2.size + 1 ∧ payload.1[0]? = some (0, 0) ∧
    (∀ index, index < payload.2.size →
      payload.1[index + 1]? = some
        (payload.1[index]!.1 + (element.footprint payload.2[index]!).realCells,
          payload.1[index]!.2 + (element.footprint payload.2[index]!).natCells)) ∧
    payload.1[payload.2.size]? = some
      ((payload.2.toList.map fun value ↦ (element.footprint value).realCells).sum,
        (payload.2.toList.map fun value ↦ (element.footprint value).natCells).sum)

/-- Explicit offsets certify random access to variable-footprint elements. -/
abbrev IndexedArray [Inhabited alpha] (element : Layout alpha) :=
  Tagged .indexedArray {payload : Array (Nat × Nat) × Array alpha //
    IndexedArray.Valid element payload}

/-- Row-major runtime matrix shape invariant. -/
def DenseMatrix.Valid (payload : Nat × Nat × Array alpha) : Prop :=
  payload.2.2.size = payload.1 * payload.2.1

/-- Runtime-sized row-major dense matrix. -/
abbrev DenseMatrix (alpha : Type) :=
  Tagged .denseMatrix {payload : Nat × Nat × Array alpha // DenseMatrix.Valid payload}

/-- Runtime three-dimensional dense tensor shape invariant. -/
def DenseTensor3.Valid (payload : Nat × Nat × Nat × Array alpha) : Prop :=
  payload.2.2.2.size = payload.1 * payload.2.1 * payload.2.2.1

abbrev DenseTensor3 (alpha : Type) := Tagged .denseTensor3
  {payload : Nat × Nat × Nat × Array alpha // DenseTensor3.Valid payload}

/-- Runtime four-dimensional dense tensor shape invariant. -/
def DenseTensor4.Valid (payload : Nat × Nat × Nat × Nat × Array alpha) : Prop :=
  payload.2.2.2.2.size = payload.1 * payload.2.1 * payload.2.2.1 * payload.2.2.2.1

abbrev DenseTensor4 (alpha : Type) := Tagged .denseTensor4
  {payload : Nat × Nat × Nat × Nat × Array alpha // DenseTensor4.Valid payload}

abbrev VertexTable (alpha : Type) := Tagged .vertexTable (Array alpha)
abbrev EdgeTable (alpha : Type) := Tagged .edgeTable (Array alpha)
abbrev DartTable (alpha : Type) := Tagged .dartTable (Array alpha)

/-- Sorted sparse vector with explicit dimension. -/
def SparseVector.Valid (payload : Nat × Array Nat × Array alpha) : Prop :=
  payload.2.1.size = payload.2.2.size ∧
    (∀ index ∈ payload.2.1, index < payload.1) ∧
    payload.2.1.toList.Pairwise (· < ·)

abbrev SparseVector (alpha : Type) := Tagged .sparseVector
  {payload : Nat × Array Nat × Array alpha // SparseVector.Valid payload}

/-- Coordinate sparse matrix with row/column/value arrays of equal size. -/
def COOMatrix.Valid (payload : Nat × Nat × Array Nat × Array Nat × Array alpha) : Prop :=
  payload.2.2.1.size = payload.2.2.2.1.size ∧
    payload.2.2.2.1.size = payload.2.2.2.2.size

abbrev COOMatrix (alpha : Type) := Tagged .cooMatrix
  {payload : Nat × Nat × Array Nat × Array Nat × Array alpha // COOMatrix.Valid payload}

/-- Compressed sparse-row matrix with explicit canonical offset invariants. -/
def CSRMatrix.Valid (payload : Nat × Nat × Array Nat × Array Nat × Array alpha) : Prop :=
  payload.2.1 + 1 = payload.2.2.1.size ∧
    payload.2.2.2.1.size = payload.2.2.2.2.size ∧
    payload.2.2.1[0]? = some 0 ∧
    payload.2.2.1[payload.2.1]? = some payload.2.2.2.1.size ∧
    payload.2.2.1.toList.Pairwise (· ≤ ·) ∧
    ∀ column ∈ payload.2.2.2.1, column < payload.1

abbrev CSRMatrix (alpha : Type) := Tagged .csrMatrix
  {payload : Nat × Nat × Array Nat × Array Nat × Array alpha // CSRMatrix.Valid payload}

/-- Runtime-sized bit set stored as an explicit natural-limb array. -/
abbrev DynamicBitSet := Tagged .dynamicBitSet (Nat × Array Nat)

/-- Permutation represented by mutually inverse forward and inverse tables. -/
def FinPermutation.Valid (payload : Nat × Array Nat × Array Nat) : Prop :=
  payload.2.1.size = payload.1 ∧ payload.2.2.size = payload.1 ∧
    (∀ index, index < payload.1 → payload.2.1[index]! < payload.1) ∧
    (∀ index, index < payload.1 → payload.2.2[payload.2.1[index]!]! = index)

abbrev FinPermutation := Tagged .permutation
  {payload : Nat × Array Nat × Array Nat // FinPermutation.Valid payload}

abbrev LabelPartition := Tagged .labelPartition (Nat × Array Nat)
abbrev ParentPartition := Tagged .parentPartition (Nat × Array Nat)
abbrev ParentForest := Tagged .parentForest (Nat × Array Nat)

/-- Directed edge-list physical format. -/
def DirectedEdgeList.Valid (payload : Nat × Array Nat × Array Nat × Array edgeData) : Prop :=
  payload.2.1.size = payload.2.2.1.size ∧ payload.2.2.1.size = payload.2.2.2.size ∧
    (∀ endpoint ∈ payload.2.1, endpoint < payload.1) ∧
    ∀ endpoint ∈ payload.2.2.1, endpoint < payload.1

abbrev DirectedEdgeList (edgeData : Type) := Tagged .directedEdgeList
  {payload : Nat × Array Nat × Array Nat × Array edgeData // DirectedEdgeList.Valid payload}

/-- Undirected dart-list physical format with an involutive reverse map. -/
def UndirectedDartList.Valid
    (payload : Nat × Array Nat × Array Nat × Array Nat × Array dartData) : Prop :=
  payload.2.1.size = payload.2.2.1.size ∧
    payload.2.2.1.size = payload.2.2.2.1.size ∧
    payload.2.2.2.1.size = payload.2.2.2.2.size ∧
    (∀ endpoint ∈ payload.2.1, endpoint < payload.1) ∧
    (∀ endpoint ∈ payload.2.2.1, endpoint < payload.1) ∧
    ∀ dart, dart < payload.2.2.2.1.size →
      payload.2.2.2.1[payload.2.2.2.1[dart]!]! = dart

abbrev UndirectedDartList (dartData : Type) := Tagged .undirectedDartList
  {payload : Nat × Array Nat × Array Nat × Array Nat × Array dartData //
    UndirectedDartList.Valid payload}

/-- CSR graph physical format; conversion from an edge list is charged computation. -/
def CSRGraph.Valid (payload : Nat × Array Nat × Array Nat × Array edgeData) : Prop :=
  payload.2.1.size = payload.1 + 1 ∧ payload.2.2.1.size = payload.2.2.2.size ∧
    payload.2.1[0]? = some 0 ∧ payload.2.1[payload.1]? = some payload.2.2.1.size ∧
    payload.2.1.toList.Pairwise (· ≤ ·) ∧
    ∀ endpoint ∈ payload.2.2.1, endpoint < payload.1

abbrev CSRGraph (edgeData : Type) := Tagged .csrGraph
  {payload : Nat × Array Nat × Array Nat × Array edgeData // CSRGraph.Valid payload}

/-- Dense adjacency-matrix physical format. -/
def AdjacencyMatrixGraph.Valid (payload : Nat × DenseMatrix Bool × DenseMatrix edgeData) : Prop :=
  payload.2.1.value.1.1 = payload.1 ∧ payload.2.1.value.1.2.1 = payload.1 ∧
    payload.2.2.value.1.1 = payload.1 ∧ payload.2.2.value.1.2.1 = payload.1

abbrev AdjacencyMatrixGraph (edgeData : Type) := Tagged .adjacencyMatrixGraph
  {payload : Nat × DenseMatrix Bool × DenseMatrix edgeData //
    AdjacencyMatrixGraph.Valid payload}

end Algolean.Algorithms.StructuredRealRAM
