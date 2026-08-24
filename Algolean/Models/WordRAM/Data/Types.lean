/-
Copyright (c) 2026 Algolean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algolean contributors
-/

module

public import Algolean.Models.RAM
public import Mathlib.Data.Matrix.Basic

/-!
# Generic physical data types for the fixed-width Word RAM

The types in this module describe finite physical data.  They contain no encoders, algorithms, or
mathematical problem semantics.  `Tagged` is a closed nominal wrapper used to distinguish physical
formats whose payloads happen to have the same Lean type.  Its Word-RAM layout is interpreted by a
dedicated structural layout constructor, not by an arbitrary equivalence.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Phantom tags for library-maintained physical Word-RAM formats. -/
inductive DataTag where
  | wordNat | signedWord | fixedPoint | multiwordNat | multiwordInt
  | wordArray | packedArray | indexedArray
  | denseMatrix | denseTensor3 | denseTensor4
  | vertexTable | edgeTable | dartTable
  | vertexByColumnTable | edgeByColumnTable | dartByColumnTable
  | sparseVector | cooMatrix | csrMatrix
  | dynamicBitSet | bitsetFinset | sortedFinset
  | sortedArrayMap | denseFinMap | openAddressMap
  | finPermutation | labelPartition | parentPartition | parentForest
  | directedEdgeList | undirectedDartList | csrGraph | adjacencyMatrixGraph
  | polyBoundedWordArray | multiwordRat
deriving DecidableEq, Repr

/-- A closed nominal wrapper with exactly one structural payload field. -/
inductive Tagged (tag : DataTag) (alpha : Type) where
  | mk (value : alpha)
deriving DecidableEq

namespace Tagged

/-- Extract the sole structural payload. -/
def value : Tagged tag alpha → alpha
  | .mk value => value

@[simp] theorem value_mk (value : alpha) : (Tagged.mk value : Tagged tag alpha).value = value := rfl

end Tagged

/-- Native unsigned word with mathematical interpretation through `BitVec.toNat`. -/
abbrev WordNat (w : ℕ) := Tagged .wordNat (BitVec w)

namespace WordNat

def ofBits (bits : BitVec w) : WordNat w := .mk bits
def bits (value : WordNat w) : BitVec w := value.value
def toNat (value : WordNat w) : ℕ := value.bits.toNat

end WordNat

/-- Native signed word using the explicit two's-complement `BitVec.toInt` convention. -/
abbrev SignedWord (w : ℕ) := Tagged .signedWord (BitVec w)

namespace SignedWord

def ofBits (bits : BitVec w) : SignedWord w := .mk bits
def bits (value : SignedWord w) : BitVec w := value.value
def toInt (value : SignedWord w) : ℤ := value.bits.toInt

end SignedWord

/-- One fixed-width dyadic value with `fracBits` fractional places. -/
inductive FixedPoint (w fracBits : ℕ) where
  | mk (bits : BitVec w)
deriving DecidableEq

namespace FixedPoint

def ofBits (bits : BitVec w) : FixedPoint w fracBits := .mk bits
def bits (value : FixedPoint w fracBits) : BitVec w :=
  match value with | .mk bits => bits
def toRat (value : FixedPoint w fracBits) : ℚ :=
  (value.bits.toNat : ℚ) / (2 ^ fracBits : ℕ)
noncomputable def toReal (value : FixedPoint w fracBits) : ℝ := value.toRat

end FixedPoint

/-- An addressable array whose length is strictly below the `w`-bit address-space size. -/
abbrev WordArray (w : ℕ) (alpha : Type) :=
  Tagged .wordArray {data : Array alpha // data.size < 2 ^ w}

namespace WordArray

def mk (data : Array alpha) (size_fits : data.size < 2 ^ w) : WordArray w alpha :=
  Tagged.mk ⟨data, size_fits⟩

def data (values : WordArray w alpha) : Array alpha := values.value.1
def size (values : WordArray w alpha) : ℕ := values.data.size
theorem size_fits (values : WordArray w alpha) : values.size < 2 ^ w := values.value.2

end WordArray

/-- Little-endian normalized nonnegative multiword magnitude.  Zero has no limbs. -/
def MultiwordNat.Normalized (limbs : WordArray w (BitVec w)) : Prop :=
  limbs.size = 0 ∨ limbs.data.back? ≠ some 0

abbrev MultiwordNat (w : ℕ) :=
  Tagged .multiwordNat {limbs : WordArray w (BitVec w) // MultiwordNat.Normalized limbs}

namespace MultiwordNat

def limbs (value : MultiwordNat w) : WordArray w (BitVec w) := value.value.1
def isZero (value : MultiwordNat w) : Prop := value.limbs.size = 0
def toNat (value : MultiwordNat w) : ℕ :=
  value.limbs.data.toList.zipIdx.foldl
    (fun total pair ↦ total + pair.1.toNat * (2 ^ w) ^ pair.2) 0

end MultiwordNat

/-- Sign-magnitude normalized multiword integer; zero is never negative. -/
def MultiwordInt.Normalized (value : Bool × MultiwordNat w) : Prop :=
  value.2.isZero → value.1 = false

abbrev MultiwordInt (w : ℕ) :=
  Tagged .multiwordInt {value : Bool × MultiwordNat w // MultiwordInt.Normalized value}

namespace MultiwordInt

def negative (value : MultiwordInt w) : Bool := value.value.1.1
def magnitude (value : MultiwordInt w) : MultiwordNat w := value.value.1.2
def toInt (value : MultiwordInt w) : ℤ :=
  if value.negative then -(value.magnitude.toNat : ℤ) else value.magnitude.toNat

end MultiwordInt

/-- Reduced finite rational represented by a signed numerator and positive multiword denominator. -/
def MultiwordRat.Normalized (value : MultiwordInt w × MultiwordNat w) : Prop :=
  ¬ value.2.isZero ∧ Nat.Coprime value.1.magnitude.toNat value.2.toNat

/-- Explicit finite Word-RAM representation of a rational number. -/
abbrev MultiwordRat (w : ℕ) :=
  Tagged .multiwordRat
    {value : MultiwordInt w × MultiwordNat w // MultiwordRat.Normalized value}

namespace MultiwordRat

def numerator (value : MultiwordRat w) : MultiwordInt w := value.value.1.1
def denominator (value : MultiwordRat w) : MultiwordNat w := value.value.1.2
def toRat (value : MultiwordRat w) : ℚ :=
  value.numerator.toInt / value.denominator.toNat

end MultiwordRat

/-- Sequential variable-footprint array without an offset index. -/
abbrev PackedArray (w : ℕ) (alpha : Type) := Tagged .packedArray (WordArray w alpha)

/--
Offset-indexed variable-footprint array validity.  Every boundary is tied to the represented
element footprint, rather than merely required to be monotone.
-/
def IndexedArray.Valid [Inhabited alpha] (elementWords : alpha → Nat)
    (payload : WordArray w (BitVec w) × WordArray w alpha) : Prop :=
  payload.1.size = payload.2.size + 1 ∧
    (payload.1.data.getD 0 0).toNat = 0 ∧
    (∀ i, i < payload.2.size →
      (payload.1.data.getD (i + 1) 0).toNat =
        (payload.1.data.getD i 0).toNat + elementWords (payload.2.data.getD i default)) ∧
    (payload.1.data.getD payload.2.size 0).toNat =
      (payload.2.data.toList.map elementWords).sum ∧
    (payload.1.data.getD payload.2.size 0).toNat < 2 ^ w

abbrev IndexedArray (w : ℕ) (alpha : Type) [Inhabited alpha]
    (elementWords : alpha → Nat) :=
  Tagged .indexedArray
    {payload : WordArray w (BitVec w) × WordArray w alpha //
      IndexedArray.Valid elementWords payload}

/-- Row-major runtime matrix payload predicate. -/
def DenseMatrix.Valid (payload : BitVec w × BitVec w × WordArray w alpha) : Prop :=
  payload.2.2.size = payload.1.toNat * payload.2.1.toNat ∧
    payload.1.toNat * payload.2.1.toNat < 2 ^ w

/-- Runtime-sized row-major dense matrix. -/
abbrev DenseMatrix (w : ℕ) (alpha : Type) :=
  Tagged .denseMatrix
    {payload : BitVec w × BitVec w × WordArray w alpha // DenseMatrix.Valid payload}

namespace DenseMatrix

def rows (matrix : DenseMatrix w alpha) : BitVec w := matrix.value.1.1
def cols (matrix : DenseMatrix w alpha) : BitVec w := matrix.value.1.2.1
def data (matrix : DenseMatrix w alpha) : WordArray w alpha := matrix.value.1.2.2

end DenseMatrix

def DenseTensor3.Valid
    (payload : BitVec w × BitVec w × BitVec w × WordArray w alpha) : Prop :=
  payload.2.2.2.size = payload.1.toNat * payload.2.1.toNat * payload.2.2.1.toNat ∧
    payload.1.toNat * payload.2.1.toNat * payload.2.2.1.toNat < 2 ^ w

abbrev DenseTensor3 (w : ℕ) (alpha : Type) :=
  Tagged .denseTensor3
    {payload : BitVec w × BitVec w × BitVec w × WordArray w alpha //
      DenseTensor3.Valid payload}

def DenseTensor4.Valid
    (payload : BitVec w × BitVec w × BitVec w × BitVec w × WordArray w alpha) : Prop :=
  payload.2.2.2.2.size =
      payload.1.toNat * payload.2.1.toNat * payload.2.2.1.toNat * payload.2.2.2.1.toNat ∧
    payload.1.toNat * payload.2.1.toNat * payload.2.2.1.toNat *
      payload.2.2.2.1.toNat < 2 ^ w

abbrev DenseTensor4 (w : ℕ) (alpha : Type) :=
  Tagged .denseTensor4
    {payload : BitVec w × BitVec w × BitVec w × BitVec w × WordArray w alpha //
      DenseTensor4.Valid payload}

abbrev VertexTable (w : ℕ) (alpha : Type) := Tagged .vertexTable (WordArray w alpha)
abbrev EdgeTable (w : ℕ) (alpha : Type) := Tagged .edgeTable (WordArray w alpha)
abbrev DartTable (w : ℕ) (alpha : Type) := Tagged .dartTable (WordArray w alpha)
abbrev VertexByColumnTable (w : ℕ) (alpha : Type) :=
  Tagged .vertexByColumnTable (DenseMatrix w alpha)
abbrev EdgeByColumnTable (w : ℕ) (alpha : Type) :=
  Tagged .edgeByColumnTable (DenseMatrix w alpha)
abbrev DartByColumnTable (w : ℕ) (alpha : Type) :=
  Tagged .dartByColumnTable (DenseMatrix w alpha)

def SparseVector.Valid
    (payload : BitVec w × WordArray w (BitVec w) × WordArray w alpha) : Prop :=
  payload.2.1.size = payload.2.2.size ∧
    (∀ index ∈ payload.2.1.data, index.toNat < payload.1.toNat) ∧
    ∀ i, i + 1 < payload.2.1.size →
      (payload.2.1.data.getD i 0).toNat < (payload.2.1.data.getD (i + 1) 0).toNat

abbrev SparseVector (w : ℕ) (alpha : Type) :=
  Tagged .sparseVector
    {payload : BitVec w × WordArray w (BitVec w) × WordArray w alpha //
      SparseVector.Valid payload}

def COOMatrix.Valid
    (payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w alpha) : Prop :=
  payload.2.2.1.size = payload.2.2.2.1.size ∧
    payload.2.2.1.size = payload.2.2.2.2.size ∧
    (∀ row ∈ payload.2.2.1.data, row.toNat < payload.1.toNat) ∧
    (∀ col ∈ payload.2.2.2.1.data, col.toNat < payload.2.1.toNat) ∧
    ∀ i, i + 1 < payload.2.2.1.size →
      let row := (payload.2.2.1.data.getD i 0).toNat
      let col := (payload.2.2.2.1.data.getD i 0).toNat
      let nextRow := (payload.2.2.1.data.getD (i + 1) 0).toNat
      let nextCol := (payload.2.2.2.1.data.getD (i + 1) 0).toNat
      row < nextRow ∨ (row = nextRow ∧ col < nextCol)

abbrev COOMatrix (w : ℕ) (alpha : Type) :=
  Tagged .cooMatrix
    {payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w alpha // COOMatrix.Valid payload}

def CSRMatrix.Valid
    (payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w alpha) : Prop :=
  payload.2.2.2.1.size = payload.2.2.2.2.size ∧
    payload.2.2.1.size = payload.1.toNat + 1 ∧
    (payload.2.2.1.data.getD 0 0).toNat = 0 ∧
    (payload.2.2.1.data.getD payload.1.toNat 0).toNat = payload.2.2.2.1.size ∧
    (∀ i, i + 1 < payload.2.2.1.size →
      (payload.2.2.1.data.getD i 0).toNat ≤
        (payload.2.2.1.data.getD (i + 1) 0).toNat) ∧
    ∀ col ∈ payload.2.2.2.1.data, col.toNat < payload.2.1.toNat

abbrev CSRMatrix (w : ℕ) (alpha : Type) :=
  Tagged .csrMatrix
    {payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w alpha // CSRMatrix.Valid payload}

def DynamicBitSet.Valid (payload : BitVec w × WordArray w (BitVec w)) : Prop :=
  payload.2.size = (payload.1.toNat + w - 1) / w

abbrev DynamicBitSet (w : ℕ) :=
  Tagged .dynamicBitSet
    {payload : BitVec w × WordArray w (BitVec w) // DynamicBitSet.Valid payload}

abbrev BitsetFinset (n : ℕ) := Tagged .bitsetFinset (Vector Bool n)

/-- Strictly increasing finite-index array invariant. -/
def SortedFinset.Valid (values : WordArray w (Fin n)) : Prop :=
  ∀ i left right,
    values.data[i]? = some left → values.data[i + 1]? = some right → left.val < right.val

/-- Sorted unique finite subset with an explicit array physical representation. -/
abbrev SortedFinset (w n : ℕ) :=
  Tagged .sortedFinset {values : WordArray w (Fin n) // SortedFinset.Valid values}

/-- Strict key order for the sorted-array map physical format. -/
def SortedArrayMap.Valid [LT key] (entries : WordArray w (key × value)) : Prop :=
  ∀ i left right,
    entries.data[i]? = some left → entries.data[i + 1]? = some right → left.1 < right.1

/-- Sorted-array finite map; the key ordering is explicit in the ambient `LT` instance. -/
abbrev SortedArrayMap (w : ℕ) (key value : Type) [LT key] :=
  Tagged .sortedArrayMap
    {entries : WordArray w (key × value) // SortedArrayMap.Valid entries}
abbrev DenseFinMap (n : ℕ) (value : Type) :=
  Tagged .denseFinMap (Fin n → Option value)
abbrev OpenAddressMap (w : ℕ) (key value : Type) :=
  Tagged .openAddressMap (WordArray w (Option (key × value)))

def FinPermutation.Valid
    (payload : BitVec w × WordArray w (BitVec w) × WordArray w (BitVec w)) : Prop :=
  payload.2.1.size = payload.1.toNat ∧ payload.2.2.size = payload.1.toNat ∧
    (∀ value ∈ payload.2.1.data, value.toNat < payload.1.toNat) ∧
    (∀ value ∈ payload.2.2.data, value.toNat < payload.1.toNat) ∧
    (∀ i, i < payload.1.toNat →
      (payload.2.2.data.getD (payload.2.1.data.getD i 0).toNat 0).toNat = i) ∧
    ∀ i, i < payload.1.toNat →
      (payload.2.1.data.getD (payload.2.2.data.getD i 0).toNat 0).toNat = i

abbrev FinPermutation (w : ℕ) :=
  Tagged .finPermutation
    {payload : BitVec w × WordArray w (BitVec w) × WordArray w (BitVec w) //
      FinPermutation.Valid payload}

def LabelPartition.Valid (labels : WordArray w (BitVec w)) : Prop :=
  ∀ label ∈ labels.data, label.toNat < labels.size

abbrev LabelPartition (w : ℕ) :=
  Tagged .labelPartition {labels : WordArray w (BitVec w) // LabelPartition.Valid labels}

def ParentPartition.Valid (parents : WordArray w (BitVec w)) : Prop :=
  (∀ parent ∈ parents.data, parent.toNat < parents.size) ∧
    ∀ vertex, vertex < parents.size →
      ∃ steps, steps ≤ parents.size ∧
        (Nat.iterate (fun current ↦ (parents.data.getD current 0).toNat) steps vertex) =
          (parents.data.getD
            (Nat.iterate (fun current ↦ (parents.data.getD current 0).toNat) steps vertex) 0).toNat

abbrev ParentPartition (w : ℕ) :=
  Tagged .parentPartition
    {parents : WordArray w (BitVec w) // ParentPartition.Valid parents}

def ParentForest.Valid (payload : BitVec w × WordArray w (BitVec w)) : Prop :=
  payload.2.size = payload.1.toNat ∧
    (∀ parent ∈ payload.2.data, parent.toNat < payload.1.toNat) ∧
    ∀ vertex, vertex < payload.1.toNat →
      ∃ steps, steps ≤ payload.1.toNat ∧
        (Nat.iterate
          (fun current ↦ (payload.2.data.getD current 0).toNat) steps vertex) =
          (payload.2.data.getD
            (Nat.iterate
              (fun current ↦ (payload.2.data.getD current 0).toNat) steps vertex) 0).toNat

abbrev ParentForest (w : ℕ) :=
  Tagged .parentForest
    {payload : BitVec w × WordArray w (BitVec w) // ParentForest.Valid payload}

def DirectedEdgeList.Valid
    (payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w edgeData) : Prop :=
  payload.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.2.size = payload.2.1.toNat ∧
    ∀ endpoint ∈ payload.2.2.1.data ++ payload.2.2.2.1.data,
      endpoint.toNat < payload.1.toNat

abbrev DirectedEdgeList (w : ℕ) (edgeData : Type) :=
  Tagged .directedEdgeList
    {payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w edgeData // DirectedEdgeList.Valid payload}

def UndirectedDartList.Valid
    (payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w (BitVec w) × WordArray w dartData) : Prop :=
  payload.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.2.2.size = payload.2.1.toNat ∧
    (∀ endpoint ∈ payload.2.2.1.data ++ payload.2.2.2.1.data,
      endpoint.toNat < payload.1.toNat) ∧
    (∀ reverse ∈ payload.2.2.2.2.1.data, reverse.toNat < payload.2.1.toNat) ∧
    ∀ dart, dart < payload.2.1.toNat →
      let reverse := (payload.2.2.2.2.1.data.getD dart 0).toNat
      (payload.2.2.2.2.1.data.getD reverse 0).toNat = dart ∧
      payload.2.2.1.data.getD reverse 0 = payload.2.2.2.1.data.getD dart 0 ∧
      payload.2.2.2.1.data.getD reverse 0 = payload.2.2.1.data.getD dart 0

abbrev UndirectedDartList (w : ℕ) (dartData : Type) :=
  Tagged .undirectedDartList
    {payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w (BitVec w) × WordArray w dartData //
      UndirectedDartList.Valid payload}

def CSRGraph.Valid
    (payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w edgeData) : Prop :=
  payload.2.2.1.size = payload.1.toNat + 1 ∧
    payload.2.2.2.1.size = payload.2.1.toNat ∧
    payload.2.2.2.2.size = payload.2.1.toNat ∧
    (payload.2.2.1.data.getD 0 0).toNat = 0 ∧
    (payload.2.2.1.data.getD payload.1.toNat 0).toNat = payload.2.1.toNat ∧
    (∀ i, i + 1 < payload.2.2.1.size →
      (payload.2.2.1.data.getD i 0).toNat ≤
        (payload.2.2.1.data.getD (i + 1) 0).toNat) ∧
    ∀ destination ∈ payload.2.2.2.1.data,
      destination.toNat < payload.1.toNat

abbrev CSRGraph (w : ℕ) (edgeData : Type) :=
  Tagged .csrGraph
    {payload : BitVec w × BitVec w × WordArray w (BitVec w) ×
      WordArray w (BitVec w) × WordArray w edgeData // CSRGraph.Valid payload}

def AdjacencyMatrixGraph.Valid
    (payload : BitVec w × DenseMatrix w Bool × DenseMatrix w edgeData) : Prop :=
  payload.2.1.rows = payload.1 ∧ payload.2.1.cols = payload.1 ∧
    payload.2.2.rows = payload.1 ∧ payload.2.2.cols = payload.1

abbrev AdjacencyMatrixGraph (w : ℕ) (edgeData : Type) :=
  Tagged .adjacencyMatrixGraph
    {payload : BitVec w × DenseMatrix w Bool × DenseMatrix w edgeData //
      AdjacencyMatrixGraph.Valid payload}

def PolyBoundedWordArray.Valid (k : ℕ)
    (payload : BitVec w × WordArray w (BitVec w)) : Prop :=
  (∀ value ∈ payload.2.data, value.toNat ≤ payload.1.toNat ^ k) ∧
    payload.1.toNat ^ k < 2 ^ w

abbrev PolyBoundedWordArray (w k : ℕ) :=
  Tagged .polyBoundedWordArray
    {payload : BitVec w × WordArray w (BitVec w) // PolyBoundedWordArray.Valid k payload}

end Algolean.Algorithms.WordRAM
