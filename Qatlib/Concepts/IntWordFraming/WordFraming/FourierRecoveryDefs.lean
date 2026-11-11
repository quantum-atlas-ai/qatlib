/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Init.Data.Vector.OfFn
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort

/-!
# Integer presentation reduction and Smith coordinates

This module defines rectangular integer matrix reduction with explicit left and right change of
basis data. `rectangularSmith` combines Euclidean row and column operations, while `SmithForm`
specifies nonnegative diagonal pivots with divisibility conditions.

`PresentationModule`, `smithEncode`, and `smithDecode` express the associated quotient and
cyclic coordinates. Such presentations provide algebraic data for finite Abelian group
decomposition, as studied in [CheungMosca2001].

## Main statements

* `rectangularSmith`: recursive reduction of an integer presentation matrix.
* `SmithForm`: the recursive Smith form predicate.
* `smithWordEq`: comparison of words through cyclic coordinates.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.IntWordFraming.WordFraming

open Matrix

/-- Tabulate a finite integer matrix as a vector of row vectors. -/
@[noinline] def matrixTable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Vector (Vector ℤ n) m := Vector.ofFn (fun r => Vector.ofFn (A r))

/-- Interpret a vector of integer row vectors as a finite matrix. -/
def tableMatrix {m n : ℕ} (rows : Vector (Vector ℤ n) m) : Matrix (Fin m) (Fin n) ℤ :=
  fun r c => rows[r.val][c.val]

/-- Materialize a finite integer matrix by tabulating its entries and reading the table back. -/
def materializeMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) ℤ := tableMatrix (matrixTable A)

/-- The two by two integer row transformation built from Bezout coefficients and the gcd of `a`
and `b`, with the identity used when the gcd is zero. -/
def euclidPair (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if Int.gcd a b = 0 then 1 else
    !![Int.gcdA a b, Int.gcdB a b;
       -(b / (Int.gcd a b : ℤ)), a / (Int.gcd a b : ℤ)]

/-- The inverse transformation associated with `euclidPair`, with the identity used when the gcd
is zero. -/
def euclidPairInverse (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if Int.gcd a b = 0 then 1 else
    !![a / (Int.gcd a b : ℤ), -Int.gcdB a b;
       b / (Int.gcd a b : ℤ), Int.gcdA a b]

/-- Replace rows `i` and `j` by the linear combinations specified by `C`, giving the `i` branch
precedence when the indices coincide. -/
def rowMix {m n : ℕ} (i j : Fin m) (C : Matrix (Fin 2) (Fin 2) ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℤ := fun r c =>
  if r = i then C 0 0 * A i c + C 0 1 * A j c
  else if r = j then C 1 0 * A i c + C 1 1 * A j c else A r c

/-- An integer matrix together with a left transformation matrix and a proposed inverse. -/
structure ColumnEliminationState (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  left : Matrix (Fin m) (Fin m) ℤ
  inverse : Matrix (Fin m) (Fin m) ℤ

/-- The state value equals `left * A`, and the stored left transformation and inverse are mutual
inverses. -/
def ColumnEliminationState.Encodes {m n : ℕ} (s : ColumnEliminationState m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = s.left * A ∧ s.left * s.inverse = 1 ∧ s.inverse * s.left = 1

/-- Apply a Euclidean row transformation to rows zero and `k.succ` using their entries in column
`p`, updating the transformation data. -/
def columnStep {m n : ℕ} (p : Fin n) (s : ColumnEliminationState (m+1) n)
    (k : Fin m) : ColumnEliminationState (m+1) n :=
  let a := s.value 0 p
  let b := s.value k.succ p
  { value := rowMix 0 k.succ (euclidPair a b) s.value
    left := rowMix 0 k.succ (euclidPair a b) s.left
    inverse := s.inverse * rowMix 0 k.succ (euclidPairInverse a b) 1 }

/-- Fold Euclidean row transformations over the rows below row zero in column `p`. -/
def columnReduce {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  (List.finRange m).foldl (columnStep p) ⟨A,1,1⟩

/-- An integer matrix together with a right transformation matrix and a proposed inverse. -/
structure RowEliminationState (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  right : Matrix (Fin n) (Fin n) ℤ
  inverse : Matrix (Fin n) (Fin n) ℤ

/-- The state value equals `A * right`, and the stored right transformation and inverse are
mutual inverses. -/
def RowEliminationState.Encodes {m n : ℕ} (s : RowEliminationState m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = A * s.right ∧ s.right * s.inverse = 1 ∧ s.inverse * s.right = 1

/-- Reduce row `p` by applying `columnReduce` to the transpose and transposing the resulting
data back. -/
def rowReduce {m n : ℕ} (p : Fin m) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := columnReduce p A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

/-- The identity matrix plus the matrix whose first column is `v` and whose other columns are
zero. -/
def firstRowShear {m : ℕ} (v : Fin (m+1) → ℤ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
  fun r c => (if r = c then 1 else 0) + if c = 0 then v r else 0

/-- The row subtraction coefficients `-A r p / A 0 p` for clearing column `p`, with coefficient
zero at row zero. -/
def columnClearCoefficients {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) : Fin (m+1) → ℤ :=
  fun r => if r = 0 then 0 else -(A r p / A 0 p)

/-- Apply the first-column shear determined by `columnClearCoefficients`, storing the shear and
its proposed inverse. -/
def columnClear {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  let v := columnClearCoefficients p A
  ⟨firstRowShear v * A, firstRowShear v, firstRowShear (-v)⟩

/-- Apply the column clearing construction to the transpose to obtain a right transformation for
row `p`. -/
def rowClear {m n : ℕ} (p : Fin m) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := columnClear p A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

/-- An integer matrix with left and right transformation matrices and their proposed inverses. -/
structure PresentationReduction (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  left : Matrix (Fin m) (Fin m) ℤ
  leftInverse : Matrix (Fin m) (Fin m) ℤ
  right : Matrix (Fin n) (Fin n) ℤ
  rightInverse : Matrix (Fin n) (Fin n) ℤ

/-- The value equals `left * A * right`, and both stored transformation pairs are mutual
inverses. -/
def PresentationReduction.Encodes {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = s.left * A * s.right ∧
    s.left * s.leftInverse = 1 ∧ s.leftInverse * s.left = 1 ∧
    s.right * s.rightInverse = 1 ∧ s.rightInverse * s.right = 1

/-- The reduction data with value `A` and identity transformations on both sides. -/
def PresentationReduction.identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    PresentationReduction m n := ⟨A,1,1,1,1⟩

/-- Extend a left elimination state to presentation reduction data using identity right
transformations. -/
def ColumnEliminationState.toReduction {m n : ℕ} (s : ColumnEliminationState m n) :
    PresentationReduction m n := ⟨s.value, s.left, s.inverse, 1, 1⟩

/-- Extend a right elimination state to presentation reduction data using identity left
transformations. -/
def RowEliminationState.toReduction {m n : ℕ} (s : RowEliminationState m n) :
    PresentationReduction m n := ⟨s.value, 1, 1, s.right, s.inverse⟩

/-- Compose the transformation data of `s` followed by `t`, retaining the value stored in `t`. -/
def PresentationReduction.then {m n : ℕ} (s t : PresentationReduction m n) :
    PresentationReduction m n :=
  ⟨t.value, t.left * s.left, s.leftInverse * t.leftInverse,
    s.right * t.right, t.rightInverse * s.rightInverse⟩

/-- Apply column clearing at column zero followed by row clearing at row zero, composing their
transformation data. -/
def clearPivot {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    PresentationReduction (m+1) (n+1) :=
  let c := columnClear 0 A
  let r := rowClear 0 c.value
  c.toReduction.then r.toReduction

/-- Add row `r` to row zero when `r` is nonzero, storing the corresponding transformation and
inverse. -/
def exposeRow {m n : ℕ} (r : Fin (m+1)) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  if r = 0 then ⟨A,1,1⟩ else
    ⟨rowMix 0 r !![1,1;0,1] A,
      rowMix 0 r !![1,1;0,1] 1, rowMix 0 r !![1,-1;0,1] 1⟩

/-- Find the first matrix entry, in row-major order, that is not divisible by the top-left
entry. -/
def badPivotEntry {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    Option (Fin (m+1) × Fin (n+1)) :=
  ((List.finRange (m+1)).product (List.finRange (n+1))).find?
    (fun rc => decide (¬ A 0 0 ∣ A rc.1 rc.2))

/-- Perform a fuel-bounded sequence of divisibility tests, Euclidean sweeps, and clearing
operations to isolate the top-left pivot. -/
def isolatePivotLoop {m n : ℕ} : ℕ → Matrix (Fin (m+1)) (Fin (n+1)) ℤ →
    PresentationReduction (m+1) (n+1)
  | 0, A => PresentationReduction.identity A
  | fuel+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    if ∀ r, A 0 0 ∣ A r 0 then
      if ∀ c, A 0 0 ∣ A 0 c then
        let s := clearPivot A
        match badPivotEntry s.value with
        | none => s
        | some rc =>
          let e := (exposeRow rc.1 s.value).toReduction
          let t := (rowReduce 0 e.value).toReduction
          s.then (e.then (t.then (isolatePivotLoop fuel t.value)))
      else
        let s := (rowReduce 0 A).toReduction
        s.then (isolatePivotLoop fuel s.value)
    else
      let s := (columnReduce 0 A).toReduction
      s.then (isolatePivotLoop fuel s.value)

/-- Run pivot isolation with fuel equal to the absolute value of the top-left entry plus one. -/
def isolatePivot {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    PresentationReduction (m+1) (n+1) :=
  isolatePivotLoop ((A 0 0).natAbs + 1) A

/-- The first row and column vanish away from the pivot, and the pivot divides every matrix
entry. -/
def PivotIsolated {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : Prop :=
  (∀ r : Fin m, A r.succ 0 = 0) ∧ (∀ c : Fin n, A 0 c.succ = 0) ∧
    ∀ r c, A 0 0 ∣ A r c

/-- Swap row zero with row `r`, recording the row permutation as both the transformation and its
inverse. -/
def swapRows {m n : ℕ} (r : Fin (m+1)) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  let e := Equiv.swap 0 r
  ⟨A.submatrix e id, (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix e id,
    (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix e id⟩

/-- Swap column zero with column `c`, recording the column permutation and its inverse. -/
def swapColumns {m n : ℕ} (c : Fin (n+1)) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := swapRows c A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

/-- Move the entry at `rc` to the top-left position using a row swap followed by a column swap. -/
def movePivot {m n : ℕ} (rc : Fin (m+1) × Fin (n+1))
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : PresentationReduction (m+1) (n+1) :=
  let s := swapRows rc.1 A
  s.toReduction.then (swapColumns rc.2 s.value).toReduction

/-- Find the first nonzero matrix entry in row-major order. -/
def nonzeroEntry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Option (Fin m × Fin n) :=
  ((List.finRange m).product (List.finRange n)).find?
    (fun rc => decide (A rc.1 rc.2 ≠ 0))

/-- Form a block diagonal matrix with scalar leading block `a` and residual block `B`. -/
def pivotBlock {m n : ℕ} (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m+1)) (Fin (n+1)) ℤ :=
  fun r c => Fin.cases (Fin.cases a (fun _ => 0) c)
    (fun i => Fin.cases 0 (B i) c) r

/-- Return minus one for a negative integer and one otherwise. -/
def pivotSign (a : ℤ) : ℤ := if a < 0 then -1 else 1

/-- Extend reduction data by a leading pivot, replacing that pivot by its absolute value and
recording its sign on the left. -/
def PresentationReduction.lift {m n : ℕ} (a : ℤ) (s : PresentationReduction m n) :
    PresentationReduction (m+1) (n+1) :=
  ⟨pivotBlock (a.natAbs : ℤ) s.value,
    pivotBlock (pivotSign a) s.left, pivotBlock (pivotSign a) s.leftInverse,
    pivotBlock 1 s.right, pivotBlock 1 s.rightInverse⟩

/-- Recursively reduce a rectangular integer matrix by selecting a nonzero pivot, isolating it,
and reducing the residual submatrix. -/
def rectangularSmith : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → PresentationReduction m n
  | 0, _, A => PresentationReduction.identity A
  | _+1, 0, A => PresentationReduction.identity A
  | _+1, _+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    match nonzeroEntry A with
    | none => PresentationReduction.identity A
    | some rc =>
      let s := movePivot rc A
      let t := isolatePivot s.value
      let residual := t.value.submatrix Fin.succ Fin.succ
      let u := (rectangularSmith residual).lift (t.value 0 0)
      s.then (t.then u)

/-- The recursive Smith form condition: each leading pivot is nonnegative, divides its block,
and has zero entries elsewhere in its row and column. -/
def SmithForm : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → Prop
  | 0, _, _ => True
  | _+1, 0, _ => True
  | m+1, n+1, A =>
    (∀ r : Fin m, A r.succ 0 = 0) ∧ (∀ c : Fin n, A 0 c.succ = 0) ∧ 0 ≤ A 0 0 ∧
      (∀ r c, A 0 0 ∣ A r c) ∧ SmithForm (A.submatrix Fin.succ Fin.succ)

/-- List the diagonal entries of a rectangular matrix up to its smaller dimension. -/
def diagonalList : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → List ℤ
  | 0, _, _ => []
  | _+1, 0, _ => []
  | _+1, _+1, A => A 0 0 :: diagonalList (A.submatrix Fin.succ Fin.succ)

/-- The absolute values of the diagonal entries produced by `rectangularSmith`. -/
def smithFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : List ℕ :=
  (diagonalList (rectangularSmith A).value).map Int.natAbs

/-- The diagonal entry in row `r` when the corresponding column exists, and zero otherwise. -/
def diagonalCoefficient {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) : ℤ :=
  if h : r.val < n then A r ⟨r.val,h⟩ else 0

/-- Divide each available coordinate of `v` by the corresponding diagonal entry of `A`,
returning zero for columns beyond the row dimension. -/
def diagonalRelationCoefficients {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) : Fin n → ℤ :=
  fun c => if h : c.val < m then v ⟨c.val,h⟩ / A ⟨c.val,h⟩ c else 0

/-- The absolute diagonal coefficients of the computed Smith reduction, with zero for rows
beyond the column dimension. -/
def cyclicFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Fin m → ℕ :=
  fun r => (diagonalCoefficient (rectangularSmith A).value r).natAbs

/-- The integer module presented by `A`, namely the quotient of integer column vectors by the
range of `A.mulVecLin`. -/
abbrev PresentationModule {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :=
  (Fin m → ℤ) ⧸ LinearMap.range A.mulVecLin

/-- The class of a standard basis vector transported by the inverse left transformation of the
computed Smith reduction. -/
def smithGenerator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) :
    PresentationModule A :=
  Submodule.Quotient.mk ((rectangularSmith A).leftInverse *ᵥ Pi.single r 1)

/-- Every determinant obtained by selecting `k` rows and `k` columns is divisible by `d`. -/
def MinorsDivisible {m n : ℕ} (k : ℕ) (d : ℤ) (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ (rows : Fin k → Fin m) (cols : Fin k → Fin n), d ∣ (A.submatrix rows cols).det

/-- Embed `Fin k` as the first `k` indices of `Fin m` using `k ≤ m`. -/
def initialIndex {k m : ℕ} (h : k ≤ m) : Fin k → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- The product of the first `k` diagonal coefficients of `A`. -/
def diagonalPrefix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (k : ℕ) (h : k ≤ m) : ℤ :=
  ∏ i : Fin k, diagonalCoefficient A (initialIndex h i)

/-- Apply the computed left transformation to an integer word and reduce each coordinate modulo
its cyclic factor. -/
def smithEncode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin m → ℤ) :
    ∀ r : Fin m, ZMod (cyclicFactors A r) :=
  fun r => (((rectangularSmith A).left *ᵥ v) r : ZMod (cyclicFactors A r))

/-- Cast cyclic coordinates to integers and apply the inverse left transformation of the
computed Smith reduction. -/
def smithDecode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (z : ∀ r : Fin m, ZMod (cyclicFactors A r)) : Fin m → ℤ :=
  (rectangularSmith A).leftInverse *ᵥ (fun r => (ZMod.cast (z r) : ℤ))

/-- Decide whether two integer words have equal coordinates under `smithEncode`. -/
def smithWordEq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (u v : Fin m → ℤ) : Bool :=
  decide (∀ r, smithEncode A u r = smithEncode A v r)

end Qatlib.Concepts.IntWordFraming.WordFraming
