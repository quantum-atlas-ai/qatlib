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

set_option autoImplicit false

namespace Qatlib.Concepts.IntWordFraming.WordFraming

open Matrix

@[noinline] def matrixTable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Vector (Vector ℤ n) m := Vector.ofFn (fun r => Vector.ofFn (A r))

def tableMatrix {m n : ℕ} (rows : Vector (Vector ℤ n) m) : Matrix (Fin m) (Fin n) ℤ :=
  fun r c => rows[r.val][c.val]

def materializeMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) ℤ := tableMatrix (matrixTable A)

def euclidPair (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if Int.gcd a b = 0 then 1 else
    !![Int.gcdA a b, Int.gcdB a b;
       -(b / (Int.gcd a b : ℤ)), a / (Int.gcd a b : ℤ)]

def euclidPairInverse (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if Int.gcd a b = 0 then 1 else
    !![a / (Int.gcd a b : ℤ), -Int.gcdB a b;
       b / (Int.gcd a b : ℤ), Int.gcdA a b]

def rowMix {m n : ℕ} (i j : Fin m) (C : Matrix (Fin 2) (Fin 2) ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℤ := fun r c =>
  if r = i then C 0 0 * A i c + C 0 1 * A j c
  else if r = j then C 1 0 * A i c + C 1 1 * A j c else A r c

structure ColumnEliminationState (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  left : Matrix (Fin m) (Fin m) ℤ
  inverse : Matrix (Fin m) (Fin m) ℤ

def ColumnEliminationState.Encodes {m n : ℕ} (s : ColumnEliminationState m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = s.left * A ∧ s.left * s.inverse = 1 ∧ s.inverse * s.left = 1

def columnStep {m n : ℕ} (p : Fin n) (s : ColumnEliminationState (m+1) n)
    (k : Fin m) : ColumnEliminationState (m+1) n :=
  let a := s.value 0 p
  let b := s.value k.succ p
  { value := rowMix 0 k.succ (euclidPair a b) s.value
    left := rowMix 0 k.succ (euclidPair a b) s.left
    inverse := s.inverse * rowMix 0 k.succ (euclidPairInverse a b) 1 }

def columnReduce {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  (List.finRange m).foldl (columnStep p) ⟨A,1,1⟩

structure RowEliminationState (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  right : Matrix (Fin n) (Fin n) ℤ
  inverse : Matrix (Fin n) (Fin n) ℤ

def RowEliminationState.Encodes {m n : ℕ} (s : RowEliminationState m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = A * s.right ∧ s.right * s.inverse = 1 ∧ s.inverse * s.right = 1

def rowReduce {m n : ℕ} (p : Fin m) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := columnReduce p A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

def firstRowShear {m : ℕ} (v : Fin (m+1) → ℤ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℤ :=
  fun r c => (if r = c then 1 else 0) + if c = 0 then v r else 0

def columnClearCoefficients {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) : Fin (m+1) → ℤ :=
  fun r => if r = 0 then 0 else -(A r p / A 0 p)

def columnClear {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  let v := columnClearCoefficients p A
  ⟨firstRowShear v * A, firstRowShear v, firstRowShear (-v)⟩

def rowClear {m n : ℕ} (p : Fin m) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := columnClear p A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

structure PresentationReduction (m n : ℕ) where
  value : Matrix (Fin m) (Fin n) ℤ
  left : Matrix (Fin m) (Fin m) ℤ
  leftInverse : Matrix (Fin m) (Fin m) ℤ
  right : Matrix (Fin n) (Fin n) ℤ
  rightInverse : Matrix (Fin n) (Fin n) ℤ

def PresentationReduction.Encodes {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  s.value = s.left * A * s.right ∧
    s.left * s.leftInverse = 1 ∧ s.leftInverse * s.left = 1 ∧
    s.right * s.rightInverse = 1 ∧ s.rightInverse * s.right = 1

def PresentationReduction.identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    PresentationReduction m n := ⟨A,1,1,1,1⟩

def ColumnEliminationState.toReduction {m n : ℕ} (s : ColumnEliminationState m n) :
    PresentationReduction m n := ⟨s.value, s.left, s.inverse, 1, 1⟩

def RowEliminationState.toReduction {m n : ℕ} (s : RowEliminationState m n) :
    PresentationReduction m n := ⟨s.value, 1, 1, s.right, s.inverse⟩

def PresentationReduction.then {m n : ℕ} (s t : PresentationReduction m n) :
    PresentationReduction m n :=
  ⟨t.value, t.left * s.left, s.leftInverse * t.leftInverse,
    s.right * t.right, t.rightInverse * s.rightInverse⟩

def clearPivot {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    PresentationReduction (m+1) (n+1) :=
  let c := columnClear 0 A
  let r := rowClear 0 c.value
  c.toReduction.then r.toReduction

def exposeRow {m n : ℕ} (r : Fin (m+1)) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  if r = 0 then ⟨A,1,1⟩ else
    ⟨rowMix 0 r !![1,1;0,1] A,
      rowMix 0 r !![1,1;0,1] 1, rowMix 0 r !![1,-1;0,1] 1⟩

def badPivotEntry {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    Option (Fin (m+1) × Fin (n+1)) :=
  ((List.finRange (m+1)).product (List.finRange (n+1))).find?
    (fun rc => decide (¬ A 0 0 ∣ A rc.1 rc.2))

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

def isolatePivot {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    PresentationReduction (m+1) (n+1) :=
  isolatePivotLoop ((A 0 0).natAbs + 1) A

def PivotIsolated {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : Prop :=
  (∀ r : Fin m, A r.succ 0 = 0) ∧ (∀ c : Fin n, A 0 c.succ = 0) ∧
    ∀ r c, A 0 0 ∣ A r c

def swapRows {m n : ℕ} (r : Fin (m+1)) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n :=
  let e := Equiv.swap 0 r
  ⟨A.submatrix e id, (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix e id,
    (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix e id⟩

def swapColumns {m n : ℕ} (c : Fin (n+1)) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) :=
  let s := swapRows c A.transpose
  ⟨s.value.transpose, s.left.transpose, s.inverse.transpose⟩

def movePivot {m n : ℕ} (rc : Fin (m+1) × Fin (n+1))
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : PresentationReduction (m+1) (n+1) :=
  let s := swapRows rc.1 A
  s.toReduction.then (swapColumns rc.2 s.value).toReduction

def nonzeroEntry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Option (Fin m × Fin n) :=
  ((List.finRange m).product (List.finRange n)).find?
    (fun rc => decide (A rc.1 rc.2 ≠ 0))

def pivotBlock {m n : ℕ} (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m+1)) (Fin (n+1)) ℤ :=
  fun r c => Fin.cases (Fin.cases a (fun _ => 0) c)
    (fun i => Fin.cases 0 (B i) c) r

def pivotSign (a : ℤ) : ℤ := if a < 0 then -1 else 1

def PresentationReduction.lift {m n : ℕ} (a : ℤ) (s : PresentationReduction m n) :
    PresentationReduction (m+1) (n+1) :=
  ⟨pivotBlock (a.natAbs : ℤ) s.value,
    pivotBlock (pivotSign a) s.left, pivotBlock (pivotSign a) s.leftInverse,
    pivotBlock 1 s.right, pivotBlock 1 s.rightInverse⟩

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

def SmithForm : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → Prop
  | 0, _, _ => True
  | _+1, 0, _ => True
  | m+1, n+1, A =>
    (∀ r : Fin m, A r.succ 0 = 0) ∧ (∀ c : Fin n, A 0 c.succ = 0) ∧ 0 ≤ A 0 0 ∧
      (∀ r c, A 0 0 ∣ A r c) ∧ SmithForm (A.submatrix Fin.succ Fin.succ)

def diagonalList : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → List ℤ
  | 0, _, _ => []
  | _+1, 0, _ => []
  | _+1, _+1, A => A 0 0 :: diagonalList (A.submatrix Fin.succ Fin.succ)

def smithFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : List ℕ :=
  (diagonalList (rectangularSmith A).value).map Int.natAbs

def diagonalCoefficient {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) : ℤ :=
  if h : r.val < n then A r ⟨r.val,h⟩ else 0

def diagonalRelationCoefficients {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) : Fin n → ℤ :=
  fun c => if h : c.val < m then v ⟨c.val,h⟩ / A ⟨c.val,h⟩ c else 0

def cyclicFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Fin m → ℕ :=
  fun r => (diagonalCoefficient (rectangularSmith A).value r).natAbs

abbrev PresentationModule {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :=
  (Fin m → ℤ) ⧸ LinearMap.range A.mulVecLin

def smithGenerator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (r : Fin m) :
    PresentationModule A :=
  Submodule.Quotient.mk ((rectangularSmith A).leftInverse *ᵥ Pi.single r 1)

def MinorsDivisible {m n : ℕ} (k : ℕ) (d : ℤ) (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ (rows : Fin k → Fin m) (cols : Fin k → Fin n), d ∣ (A.submatrix rows cols).det

def initialIndex {k m : ℕ} (h : k ≤ m) : Fin k → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

def diagonalPrefix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (k : ℕ) (h : k ≤ m) : ℤ :=
  ∏ i : Fin k, diagonalCoefficient A (initialIndex h i)

def smithEncode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin m → ℤ) :
    ∀ r : Fin m, ZMod (cyclicFactors A r) :=
  fun r => (((rectangularSmith A).left *ᵥ v) r : ZMod (cyclicFactors A r))

def smithDecode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (z : ∀ r : Fin m, ZMod (cyclicFactors A r)) : Fin m → ℤ :=
  (rectangularSmith A).leftInverse *ᵥ (fun r => (ZMod.cast (z r) : ℤ))

def smithWordEq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (u v : Fin m → ℤ) : Bool :=
  decide (∀ r, smithEncode A u r = smithEncode A v r)

end Qatlib.Concepts.IntWordFraming.WordFraming
