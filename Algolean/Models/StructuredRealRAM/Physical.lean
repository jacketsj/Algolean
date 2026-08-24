/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.StructuredRealRAM.Data
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Mathematical views of structured exact-real/natural physical data

The names distinguish one-sided validation of stored entries from exact representation of an
abstract relation.  No theorem here constructs, sorts, indexes, or converts a physical value.
-/

@[expose] public section

namespace Algolean.Algorithms.StructuredRealRAM

namespace DirectedEdgeList

def payload (graph : DirectedEdgeList edgeData) := graph.value.1
def vertexCount (graph : DirectedEdgeList edgeData) : Nat := graph.payload.1
def tail (graph : DirectedEdgeList edgeData) : Array Nat := graph.payload.2.1
def head (graph : DirectedEdgeList edgeData) : Array Nat := graph.payload.2.2.1
def data (graph : DirectedEdgeList edgeData) : Array edgeData := graph.payload.2.2.2

/-- Every materialized edge satisfies a downstream semantic edge predicate. -/
def EveryStoredEdgeSatisfies (graph : DirectedEdgeList edgeData)
    (edge : Nat → Nat → edgeData → Prop) : Prop :=
  ∀ index, index < graph.data.size →
    ∃ tail head datum,
      graph.tail[index]? = some tail ∧ graph.head[index]? = some head ∧
      graph.data[index]? = some datum ∧ edge tail head datum

end DirectedEdgeList

namespace UndirectedDartList

def payload (graph : UndirectedDartList dartData) := graph.value.1
def vertexCount (graph : UndirectedDartList dartData) : Nat := graph.payload.1
def tail (graph : UndirectedDartList dartData) : Array Nat := graph.payload.2.1
def head (graph : UndirectedDartList dartData) : Array Nat := graph.payload.2.2.1
def reverse (graph : UndirectedDartList dartData) : Array Nat := graph.payload.2.2.2.1
def data (graph : UndirectedDartList dartData) : Array dartData := graph.payload.2.2.2.2

/-- The dart endpoints represent exactly the adjacency relation of the abstract simple graph. -/
def RepresentsExactly (graph : UndirectedDartList dartData)
    (abstract : SimpleGraph (Fin graph.vertexCount)) : Prop :=
  ∀ left right,
    abstract.Adj left right ↔
      ∃ dart, dart < graph.data.size ∧
        graph.tail[dart]! = left ∧ graph.head[dart]! = right

end UndirectedDartList

namespace CSRGraph

def payload (graph : CSRGraph edgeData) := graph.value.1
def vertexCount (graph : CSRGraph edgeData) : Nat := graph.payload.1
def offsets (graph : CSRGraph edgeData) : Array Nat := graph.payload.2.1
def destination (graph : CSRGraph edgeData) : Array Nat := graph.payload.2.2.1
def data (graph : CSRGraph edgeData) : Array edgeData := graph.payload.2.2.2
def neighborStart (graph : CSRGraph edgeData) (vertex : Nat) : Nat :=
  graph.offsets[vertex]!
def neighborEnd (graph : CSRGraph edgeData) (vertex : Nat) : Nat :=
  graph.offsets[vertex + 1]!

/-- Every entry in every materialized CSR row satisfies the downstream edge predicate. -/
def EveryStoredEdgeSatisfies (graph : CSRGraph edgeData)
    (edge : Nat → Nat → edgeData → Prop) : Prop :=
  ∀ vertex, vertex < graph.vertexCount →
    ∀ index, graph.neighborStart vertex ≤ index → index < graph.neighborEnd vertex →
      ∃ destination datum,
        graph.destination[index]? = some destination ∧
        graph.data[index]? = some datum ∧ edge vertex destination datum

end CSRGraph

namespace AdjacencyMatrixGraph

def payload (graph : AdjacencyMatrixGraph edgeData) := graph.value.1
def vertexCount (graph : AdjacencyMatrixGraph edgeData) : Nat := graph.payload.1
def present (graph : AdjacencyMatrixGraph edgeData) : DenseMatrix Bool := graph.payload.2.1
def data (graph : AdjacencyMatrixGraph edgeData) : DenseMatrix edgeData := graph.payload.2.2

/-- The row-major presence matrix represents exactly the abstract adjacency relation. -/
def RepresentsExactly (graph : AdjacencyMatrixGraph edgeData)
    (abstract : SimpleGraph (Fin graph.vertexCount)) : Prop :=
  ∀ left right,
    abstract.Adj left right ↔
      graph.present.value.1.2.2[
        left.val * graph.vertexCount + right.val]!

end AdjacencyMatrixGraph

end Algolean.Algorithms.StructuredRealRAM
