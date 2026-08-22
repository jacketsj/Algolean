/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Complexity.WordRAMStructured
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Generic physical Word-RAM data views

These definitions expose fieldwise views and mathematical representation relations for the
closed physical carriers in `Data.Types`.  They never convert an abstract object into a physical
format: constructing CSR offsets, sorting COO entries, or building an index remains an ordinary
charged algorithm.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

namespace DenseMatrix

/-- Row-major element index; the final (column) index varies fastest. -/
def rowMajorIndex (matrix : DenseMatrix w alpha) (row column : Nat) : Nat :=
  row * matrix.cols.toNat + column

theorem rowMajorIndex_lt (matrix : DenseMatrix w alpha)
    {row column : Nat} (rowInRange : row < matrix.rows.toNat)
    (columnInRange : column < matrix.cols.toNat) :
    matrix.rowMajorIndex row column < matrix.data.size := by
  have valid := matrix.value.2
  calc
    matrix.rowMajorIndex row column < row * matrix.cols.toNat + matrix.cols.toNat := by
      exact Nat.add_lt_add_left columnInRange _
    _ = (row + 1) * matrix.cols.toNat := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ matrix.rows.toNat * matrix.cols.toNat := by
      exact Nat.mul_le_mul_right _ (Nat.succ_le_iff.2 rowInRange)
    _ = matrix.data.size := by
      simpa [DenseMatrix.rows, DenseMatrix.cols, DenseMatrix.data,
        WordArray.size, WordArray.data] using valid.1.symm

end DenseMatrix

namespace DirectedEdgeList

def payload (graph : DirectedEdgeList w edgeData) := graph.value.1
def vertexCount (graph : DirectedEdgeList w edgeData) : BitVec w := graph.payload.1
def edgeCount (graph : DirectedEdgeList w edgeData) : BitVec w := graph.payload.2.1
def tail (graph : DirectedEdgeList w edgeData) : WordArray w (BitVec w) := graph.payload.2.2.1
def head (graph : DirectedEdgeList w edgeData) : WordArray w (BitVec w) := graph.payload.2.2.2.1
def data (graph : DirectedEdgeList w edgeData) : WordArray w edgeData := graph.payload.2.2.2.2

/-- Proof-layer semantics of an already materialized directed edge list. -/
def Represents (graph : DirectedEdgeList w edgeData)
    (edge : Nat → Nat → edgeData → Prop) : Prop :=
  ∀ index, index < graph.edgeCount.toNat →
    ∃ datum, graph.data.data[index]? = some datum ∧
      edge (graph.tail.data.getD index 0).toNat
        (graph.head.data.getD index 0).toNat datum

end DirectedEdgeList

namespace UndirectedDartList

def payload (graph : UndirectedDartList w dartData) := graph.value.1
def vertexCount (graph : UndirectedDartList w dartData) : BitVec w := graph.payload.1
def dartCount (graph : UndirectedDartList w dartData) : BitVec w := graph.payload.2.1
def tail (graph : UndirectedDartList w dartData) : WordArray w (BitVec w) := graph.payload.2.2.1
def head (graph : UndirectedDartList w dartData) : WordArray w (BitVec w) := graph.payload.2.2.2.1
def reverse (graph : UndirectedDartList w dartData) : WordArray w (BitVec w) :=
  graph.payload.2.2.2.2.1
def data (graph : UndirectedDartList w dartData) : WordArray w dartData :=
  graph.payload.2.2.2.2.2

/-- Relation to a mathlib simple graph; no enumeration or conversion is selected implicitly. -/
def Represents (graph : UndirectedDartList w dartData)
    (abstract : SimpleGraph (Fin graph.vertexCount.toNat)) : Prop :=
  ∀ left right,
    abstract.Adj left right ↔
      ∃ dart, dart < graph.dartCount.toNat ∧
        (graph.tail.data.getD dart 0).toNat = left ∧
        (graph.head.data.getD dart 0).toNat = right

end UndirectedDartList

namespace CSRGraph

def payload (graph : CSRGraph w edgeData) := graph.value.1
def vertexCount (graph : CSRGraph w edgeData) : BitVec w := graph.payload.1
def edgeCount (graph : CSRGraph w edgeData) : BitVec w := graph.payload.2.1
def offsets (graph : CSRGraph w edgeData) : WordArray w (BitVec w) := graph.payload.2.2.1
def destination (graph : CSRGraph w edgeData) : WordArray w (BitVec w) :=
  graph.payload.2.2.2.1
def data (graph : CSRGraph w edgeData) : WordArray w edgeData := graph.payload.2.2.2.2
def neighborStart (graph : CSRGraph w edgeData) (vertex : Nat) : Nat :=
  (graph.offsets.data.getD vertex 0).toNat
def neighborEnd (graph : CSRGraph w edgeData) (vertex : Nat) : Nat :=
  (graph.offsets.data.getD (vertex + 1) 0).toNat

/-- Proof-layer semantics of an already materialized CSR representation. -/
def Represents (graph : CSRGraph w edgeData)
    (edge : Nat → Nat → edgeData → Prop) : Prop :=
  ∀ vertex, vertex < graph.vertexCount.toNat →
    ∀ index, graph.neighborStart vertex ≤ index → index < graph.neighborEnd vertex →
      ∃ datum, graph.data.data[index]? = some datum ∧
        edge vertex (graph.destination.data.getD index 0).toNat datum

end CSRGraph

namespace AdjacencyMatrixGraph

def payload (graph : AdjacencyMatrixGraph w edgeData) := graph.value.1
def vertexCount (graph : AdjacencyMatrixGraph w edgeData) : BitVec w := graph.payload.1
def present (graph : AdjacencyMatrixGraph w edgeData) : DenseMatrix w Bool := graph.payload.2.1
def data (graph : AdjacencyMatrixGraph w edgeData) : DenseMatrix w edgeData := graph.payload.2.2

/-- Relation to a mathlib simple graph using the documented row-major presence matrix. -/
def Represents (graph : AdjacencyMatrixGraph w edgeData)
    (abstract : SimpleGraph (Fin graph.vertexCount.toNat)) : Prop :=
  ∀ left right,
    abstract.Adj left right ↔
      graph.present.data.data.getD
        (left.val * graph.vertexCount.toNat + right.val) false

end AdjacencyMatrixGraph

/-- Conversion is computation: it is described by an ordinary structured problem. -/
def RepresentationConversionProblem (w : Nat) (source target : Type)
    (sourceLayout : WordLayout w source) (targetLayout : WordLayout w target)
    (widthAtLeastTwo : 2 ≤ w) (outputRegion : Region w)
    (pre : source → Prop) (representsSame : source → target → Prop)
    (sourceFits : ∀ input, pre input → sourceLayout.FitsInput input) :
    StructuredProblem w where
  widthAtLeastTwo := widthAtLeastTwo
  Input := source
  Output := target
  inputLayout := sourceLayout
  outputLayout := targetLayout
  outputRegion := outputRegion
  pre := pre
  post := representsSame
  inputFits := sourceFits

end Algolean.Algorithms.WordRAM
