/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SmithIntermediateBitGrowth
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Entry and bit bounds for Smith reduction runs

This module tracks integer entry bounds for Smith reduction matrices and their changes of basis.
The recursive bounds `isolatePivotLoopSup` and `rectangularSup` follow the branches taken by the
counted Euclidean routines, providing arithmetic bookkeeping relevant to finite abelian group
decomposition as in [CheungMosca2001].

The final results bound the reduction entries and peak Euclidean-pair input sizes, and combine
these estimates with the counted division bound and correctness of the resulting Smith form.

## Main statements

* `smithIsolatePivotEuclidLoop_entryBound`: entry and peak-bit bounds for a pivot loop with
  specified fuel.
* `smithRectangularEuclid_entryBound`: bounds for the complete rectangular reduction.
* `output1.frontier1`: the bounds together with encoding correctness and Smith form.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib
set_option warningAsError false

/-- The condition that the natural absolute value of every integer matrix entry is at most `b`. -/
def MatrixEntryBound {ι κ : Type*} (A : Matrix ι κ ℤ) (b : ℕ) : Prop :=
  ∀ i j, (A i j).natAbs ≤ b

/-- A common entry bound for a presentation reduction's value matrix, left and right
change-of-basis matrices, and both inverse matrices. -/
def ReductionEntryBound {m n : ℕ} (s : PresentationReduction m n) (b : ℕ) : Prop :=
  MatrixEntryBound s.value b ∧ MatrixEntryBound s.left b ∧
    MatrixEntryBound s.leftInverse b ∧ MatrixEntryBound s.right b ∧
    MatrixEntryBound s.rightInverse b

/-- A common entry bound for a column elimination state's value, left transformation, and
inverse matrices. -/
def ColumnEntryBound {m n : ℕ} (s : ColumnEliminationState m n) (b : ℕ) : Prop :=
  MatrixEntryBound s.value b ∧ MatrixEntryBound s.left b ∧ MatrixEntryBound s.inverse b

/-- A common entry bound for a row elimination state's value, right transformation, and inverse
matrices. -/
def RowEntryBound {m n : ℕ} (s : RowEliminationState m n) (b : ℕ) : Prop :=
  MatrixEntryBound s.value b ∧ MatrixEntryBound s.right b ∧ MatrixEntryBound s.inverse b

/-- An integer matrix entry bound remains valid when the bound is increased. -/
theorem MatrixEntryBound.mono {ι κ : Type*} {A : Matrix ι κ ℤ} {b c : ℕ}
    (h : MatrixEntryBound A b) (hbc : b ≤ c) : MatrixEntryBound A c :=
  fun i j => (h i j).trans hbc

/-- A presentation reduction's common entry bound remains valid when the bound is increased. -/
theorem ReductionEntryBound.mono {m n : ℕ} {s : PresentationReduction m n} {b c : ℕ}
    (h : ReductionEntryBound s b) (hbc : b ≤ c) : ReductionEntryBound s c :=
  ⟨h.1.mono hbc, h.2.1.mono hbc, h.2.2.1.mono hbc, h.2.2.2.1.mono hbc,
    h.2.2.2.2.mono hbc⟩

/-- A column elimination state's common entry bound remains valid when the bound is increased. -/
theorem ColumnEntryBound.mono {m n : ℕ} {s : ColumnEliminationState m n} {b c : ℕ}
    (h : ColumnEntryBound s b) (hbc : b ≤ c) : ColumnEntryBound s c :=
  ⟨h.1.mono hbc, h.2.1.mono hbc, h.2.2.mono hbc⟩

/-- A row elimination state's common entry bound remains valid when the bound is increased. -/
theorem RowEntryBound.mono {m n : ℕ} {s : RowEliminationState m n} {b c : ℕ}
    (h : RowEntryBound s b) (hbc : b ≤ c) : RowEntryBound s c :=
  ⟨h.1.mono hbc, h.2.1.mono hbc, h.2.2.mono hbc⟩

/-- The natural absolute value of a finite integer sum is bounded by the sum of pointwise
natural absolute-value bounds. -/
private theorem natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) (B : ι → ℕ)
    (h : ∀ x ∈ s, (f x).natAbs ≤ B x) :
    (∑ x ∈ s, f x).natAbs ≤ ∑ x ∈ s, B x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact (Int.natAbs_add_le _ _).trans
        (Nat.add_le_add (h x (Finset.mem_insert_self x s))
          (ih fun y hy => h y (Finset.mem_insert_of_mem hy)))

/-- An integer identity matrix has entry bound `b` whenever `1 ≤ b`. -/
theorem matrix_one_entryBound {m b : ℕ} (hb : 1 ≤ b) :
    MatrixEntryBound (1 : Matrix (Fin m) (Fin m) ℤ) b := by
  intro i j
  simp only [Matrix.one_apply]
  split <;> simp_all

/-- Selecting or reindexing rows and columns preserves an integer matrix entry bound. -/
theorem matrix_submatrix_entryBound {ι κ ι' κ' : Type*} {A : Matrix ι κ ℤ}
    (r : ι' → ι) (c : κ' → κ) {b : ℕ} (h : MatrixEntryBound A b) :
    MatrixEntryBound (A.submatrix r c) b :=
  fun i j => h (r i) (c j)

/-- If the factors have entry bounds `c` and `b` and inner dimension `m`, every product entry
has natural absolute value at most `m * (c * b)`. -/
private theorem matrix_mul_entry_le {l m n : ℕ} {A : Matrix (Fin l) (Fin m) ℤ}
    {B : Matrix (Fin m) (Fin n) ℤ} {c b : ℕ}
    (hA : MatrixEntryBound A c) (hB : MatrixEntryBound B b) (i : Fin l) (j : Fin n) :
    ((A * B) i j).natAbs ≤ m * (c * b) := by
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin m, (A i k * B k j).natAbs ≤ c * b := by
    intro k
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hA i k) (hB k j)
  have hsum := natAbs_sum_le (Finset.univ : Finset (Fin m))
    (fun k => A i k * B k j) (fun _ => c * b) (fun k _ => hterm k)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  exact hsum

/-- Two matrices with entry bound `b` have product entry bound `elimSupStep dim b` when their
inner dimension is at most `dim`. -/
theorem matrix_mul_entry_elimSup {dim l m n : ℕ} (hm : m ≤ dim)
    {A : Matrix (Fin l) (Fin m) ℤ} {B : Matrix (Fin m) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hB : MatrixEntryBound B b) :
    MatrixEntryBound (A * B) (elimSupStep dim b) := by
  intro i j
  calc
    ((A * B) i j).natAbs ≤ m * (b * b) := matrix_mul_entry_le hA hB i j
    _ ≤ dim * ((b + 1) * (b + 1)) :=
      Nat.mul_le_mul hm (Nat.mul_le_mul (Nat.le_succ b) (Nat.le_succ b))
    _ = elimSupStep dim b := by rw [elimSupStep, Nat.pow_two]

/-- A product has entry bound `elimSupStep dim b` when its inner dimension is at most `dim` and
its factors have entry bounds at most `b + 1` and `b`, respectively. -/
theorem matrix_mul_entry_elimSup_of_le_succ {dim l m n : ℕ} (hm : m ≤ dim)
    {A : Matrix (Fin l) (Fin m) ℤ} {B : Matrix (Fin m) (Fin n) ℤ} {c b : ℕ}
    (hc : c ≤ b + 1) (hA : MatrixEntryBound A c) (hB : MatrixEntryBound B b) :
    MatrixEntryBound (A * B) (elimSupStep dim b) := by
  intro i j
  calc
    ((A * B) i j).natAbs ≤ m * (c * b) := matrix_mul_entry_le hA hB i j
    _ ≤ dim * ((b + 1) * (b + 1)) :=
      Nat.mul_le_mul hm (Nat.mul_le_mul hc (Nat.le_succ b))
    _ = elimSupStep dim b := by rw [elimSupStep, Nat.pow_two]

/-- The elimination bound after one step is at least one when `dim ≥ 1`. -/
theorem one_le_elimSupStep {dim b : ℕ} (hd : 1 ≤ dim) : 1 ≤ elimSupStep dim b := by
  rw [elimSupStep]
  have hp : 0 < (b + 1) ^ 2 := by positivity
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))

/-- One elimination-bound step does not decrease its input when `dim ≥ 1`. -/
theorem le_elimSupStep {dim b : ℕ} (hd : 1 ≤ dim) : b ≤ elimSupStep dim b := by
  rw [elimSupStep, Nat.pow_two]
  calc
    b ≤ b + 1 := Nat.le_succ b
    _ ≤ (b + 1) * (b + 1) := Nat.le_mul_of_pos_right (b + 1) (by omega)
    _ ≤ dim * ((b + 1) * (b + 1)) := Nat.le_mul_of_pos_left _ hd

/-- One elimination-bound step is at least `b + 1` when `dim ≥ 1`. -/
theorem succ_le_elimSupStep {dim b : ℕ} (hd : 1 ≤ dim) : b + 1 ≤ elimSupStep dim b := by
  rw [elimSupStep, Nat.pow_two]
  calc
    b + 1 ≤ (b + 1) * (b + 1) := Nat.le_mul_of_pos_right (b + 1) (by omega)
    _ ≤ dim * ((b + 1) * (b + 1)) := Nat.le_mul_of_pos_left _ hd

/-- One elimination-bound step is at least `2 * b` when `dim ≥ 2`. -/
theorem two_mul_le_elimSupStep {dim b : ℕ} (hd : 2 ≤ dim) : 2 * b ≤ elimSupStep dim b := by
  rw [elimSupStep, Nat.pow_two]
  calc
    2 * b ≤ 2 * ((b + 1) * (b + 1)) := Nat.mul_le_mul_left 2
      ((Nat.le_succ b).trans (Nat.le_mul_of_pos_right (b + 1) (by omega)))
    _ ≤ dim * ((b + 1) * (b + 1)) := Nat.mul_le_mul_right _ hd

/-- The elimination-bound step is monotone in its input bound. -/
theorem elimSupStep_mono {dim b c : ℕ} (h : b ≤ c) :
    elimSupStep dim b ≤ elimSupStep dim c := by
  exact Nat.mul_le_mul_left dim (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)

/-- The elimination-bound step is monotone in the dimension parameter. -/
theorem elimSupStep_dim_mono {d D b : ℕ} (h : d ≤ D) :
    elimSupStep d b ≤ elimSupStep D b :=
  Nat.mul_le_mul_right ((b + 1) ^ 2) h

/-- Every fixed iterate of the elimination-bound step is monotone in the initial bound. -/
theorem elimSup_iterate_mono {dim : ℕ} : ∀ (k : ℕ) {b c : ℕ}, b ≤ c →
    (elimSupStep dim)^[k] b ≤ (elimSupStep dim)^[k] c := by
  intro k
  induction k with
  | zero => intro b c h; exact h
  | succ k ih =>
      intro b c h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih (elimSupStep_mono h)

/-- Increasing the dimension parameter increases or preserves every iterate of the
elimination-bound step at a fixed initial bound. -/
theorem elimSup_iterate_dim_mono {d D : ℕ} (h : d ≤ D) : ∀ (k : ℕ) (b : ℕ),
    (elimSupStep d)^[k] b ≤ (elimSupStep D)^[k] b := by
  intro k
  induction k with
  | zero => intro b; exact Nat.le_refl b
  | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact (ih (elimSupStep d b)).trans
        (elimSup_iterate_mono k (elimSupStep_dim_mono h))

/-- Every iterate of the elimination-bound step is at least its initial bound when `dim ≥ 1`. -/
theorem le_elimSup_iterate {dim : ℕ} (hd : 1 ≤ dim) : ∀ (k : ℕ) (b : ℕ),
    b ≤ (elimSupStep dim)^[k] b := by
  intro k
  induction k with
  | zero => intro b; exact Nat.le_refl b
  | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply]
      exact (le_elimSupStep hd).trans (ih (elimSupStep dim b))

/-- Iterating the elimination-bound step preserves a lower bound of one when `dim ≥ 1`. -/
theorem one_le_elimSup_iterate {dim : ℕ} (hd : 1 ≤ dim) (k : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    1 ≤ (elimSupStep dim)^[k] b :=
  hb.trans (le_elimSup_iterate hd k b)

/-- The bit size after one additional elimination-bound step is at most twice the preceding bit
size plus `dim + 2`. -/
theorem elimSup_iterate_step_size {dim : ℕ} (k : ℕ) (b : ℕ) :
    ((elimSupStep dim)^[k+1] b).size ≤
      2 * ((elimSupStep dim)^[k] b).size + dim + 2 := by
  rw [Function.iterate_succ_apply']
  exact elimSupStep_size dim _

/-- The identity presentation reduction inherits the input matrix's entry bound whenever that
bound is at least one. -/
theorem reduction_identity_entryBound {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    ReductionEntryBound (PresentationReduction.identity A) b :=
  ⟨hA, matrix_one_entryBound hb, matrix_one_entryBound hb,
    matrix_one_entryBound hb, matrix_one_entryBound hb⟩

/-- Converting a bounded column elimination state to a presentation reduction preserves its
entry bound when the bound is at least one. -/
theorem column_toReduction_entryBound {m n : ℕ} {s : ColumnEliminationState m n} {b : ℕ}
    (hs : ColumnEntryBound s b) (hb : 1 ≤ b) : ReductionEntryBound s.toReduction b :=
  ⟨hs.1, hs.2.1, hs.2.2, matrix_one_entryBound hb, matrix_one_entryBound hb⟩

/-- Converting a bounded row elimination state to a presentation reduction preserves its entry
bound when the bound is at least one. -/
theorem row_toReduction_entryBound {m n : ℕ} {s : RowEliminationState m n} {b : ℕ}
    (hs : RowEntryBound s b) (hb : 1 ≤ b) : ReductionEntryBound s.toReduction b :=
  ⟨hs.1, matrix_one_entryBound hb, matrix_one_entryBound hb, hs.2.1, hs.2.2⟩

/-- Composing two presentation reductions with common entry bound `b` gives bound `elimSupStep
dim b`, provided both dimensions are at most `dim` and `dim ≥ 1`. -/
theorem reduction_then_entryBound {m n dim : ℕ} (hm : m ≤ dim) (hn : n ≤ dim)
    (hd : 1 ≤ dim) {s t : PresentationReduction m n} {b : ℕ}
    (hs : ReductionEntryBound s b) (ht : ReductionEntryBound t b) :
    ReductionEntryBound (s.then t) (elimSupStep dim b) := by
  refine ⟨(ht.1.mono (le_elimSupStep hd)), ?_, ?_, ?_, ?_⟩
  · exact matrix_mul_entry_elimSup hm ht.2.1 hs.2.1
  · exact matrix_mul_entry_elimSup hm hs.2.2.1 ht.2.2.1
  · exact matrix_mul_entry_elimSup hn hs.2.2.2.1 ht.2.2.2.1
  · exact matrix_mul_entry_elimSup hn ht.2.2.2.2 hs.2.2.2.2

/-- A block matrix formed from pivot `a` and matrix `B` has entry bound `b` when both the
pivot's natural absolute value and the entries of `B` are bounded by `b`. -/
private theorem pivotBlock_entryBound {m n : ℕ} {a : ℤ} {B : Matrix (Fin m) (Fin n) ℤ}
    {b : ℕ} (ha : a.natAbs ≤ b) (hB : MatrixEntryBound B b) :
    MatrixEntryBound (pivotBlock a B) b := by
  intro i j
  refine Fin.cases ?_ (fun r => ?_) i
  · refine Fin.cases ?_ (fun c => ?_) j
    · simpa [pivotBlock] using! ha
    · simp [pivotBlock]
  · refine Fin.cases ?_ (fun c => ?_) j
    · simp [pivotBlock]
    · simpa [pivotBlock] using! hB r c

/-- The natural absolute value of the pivot sign is at most one. -/
private theorem pivotSign_natAbs_le (a : ℤ) : (pivotSign a).natAbs ≤ 1 := by
  simp [pivotSign]
  split <;> simp

/-- Lifting a presentation reduction around a pivot preserves bound `b` when the original
reduction and pivot satisfy that bound and `b ≥ 1`. -/
theorem reduction_lift_entryBound {m n : ℕ} {a : ℤ} {s : PresentationReduction m n}
    {b : ℕ} (ha : a.natAbs ≤ b) (hs : ReductionEntryBound s b) (hb : 1 ≤ b) :
    ReductionEntryBound (s.lift a) b := by
  refine ⟨pivotBlock_entryBound ha hs.1, ?_, ?_, ?_, ?_⟩
  · exact pivotBlock_entryBound ((pivotSign_natAbs_le a).trans hb) hs.2.1
  · exact pivotBlock_entryBound ((pivotSign_natAbs_le a).trans hb) hs.2.2.1
  · exact pivotBlock_entryBound hb hs.2.2.2.1
  · exact pivotBlock_entryBound hb hs.2.2.2.2

/-- Every column-clearing coefficient has natural absolute value at most the input matrix's
entry bound. -/
private theorem columnClearCoefficients_natAbs {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) {b : ℕ} (hA : MatrixEntryBound A b) :
    ∀ r, (columnClearCoefficients p A r).natAbs ≤ b := by
  intro r
  simp only [columnClearCoefficients]
  split_ifs
  · simp
  · rw [Int.natAbs_neg]
    have h := Int.abs_ediv_le_abs (A r p) (A 0 p)
    simp only [Int.abs_eq_natAbs] at h
    have h' : (A r p / A 0 p).natAbs ≤ (A r p).natAbs := by exact_mod_cast h
    exact h'.trans (hA r p)

/-- The first-row shear matrix has entry bound `b + 1` when all its coefficient magnitudes are
bounded by `b`. -/
private theorem firstRowShear_entryBound {m : ℕ} {v : Fin (m+1) → ℤ} {b : ℕ}
    (hv : ∀ r, (v r).natAbs ≤ b) : MatrixEntryBound (firstRowShear v) (b+1) := by
  intro r c
  have h := Int.natAbs_add_le (if r = c then (1 : ℤ) else 0) (if c = 0 then v r else 0)
  have h1 : (if r = c then (1 : ℤ) else 0).natAbs ≤ 1 := by split_ifs <;> simp
  have h2 : (if c = 0 then v r else 0).natAbs ≤ b := by
    split_ifs
    · exact hv r
    · simp
  exact h.trans (by omega)

/-- Column clearing produces an elimination state bounded by `elimSupStep dim b` when the input
is bounded by `b` and its row count is at most `dim`. -/
theorem columnClear_entryBound {m n dim : ℕ} (hm : m+1 ≤ dim) (p : Fin n)
    {A : Matrix (Fin (m+1)) (Fin n) ℤ} {b : ℕ} (hA : MatrixEntryBound A b) :
    ColumnEntryBound (columnClear p A) (elimSupStep dim b) := by
  let v := columnClearCoefficients p A
  have hv : ∀ r, (v r).natAbs ≤ b := columnClearCoefficients_natAbs p A hA
  have hs := firstRowShear_entryBound hv
  have hsn : MatrixEntryBound (firstRowShear (-v)) (b+1) := by
    apply firstRowShear_entryBound
    intro r
    simp only [Pi.neg_apply, Int.natAbs_neg]
    exact hv r
  have hd : 1 ≤ dim := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact matrix_mul_entry_elimSup_of_le_succ hm (Nat.le_refl (b+1)) hs hA
  · exact hs.mono (succ_le_elimSupStep hd)
  · exact hsn.mono (succ_le_elimSupStep hd)

/-- Row clearing produces an elimination state bounded by `elimSupStep dim b` when the input is
bounded by `b` and its column count is at most `dim`. -/
theorem rowClear_entryBound {m n dim : ℕ} (hn : n+1 ≤ dim) (p : Fin m)
    {A : Matrix (Fin m) (Fin (n+1)) ℤ} {b : ℕ} (hA : MatrixEntryBound A b) :
    RowEntryBound (rowClear p A) (elimSupStep dim b) := by
  have h := columnClear_entryBound hn p (A := A.transpose) (fun i j => hA j i)
  exact ⟨fun i j => h.1 j i, fun i j => h.2.1 j i, fun i j => h.2.2 j i⟩

/-- Clearing a pivot yields a presentation reduction bounded by three iterates of `elimSupStep
dim`, provided both matrix dimensions are at most `dim`. -/
theorem clearPivot_entryBound {m n dim : ℕ} (hm : m+1 ≤ dim) (hn : n+1 ≤ dim)
    {A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ} {b : ℕ} (hA : MatrixEntryBound A b) :
    ReductionEntryBound (clearPivot A) ((elimSupStep dim)^[3] b) := by
  let c := columnClear 0 A
  let r := rowClear 0 c.value
  have hd : 1 ≤ dim := by omega
  have hc : ColumnEntryBound c (elimSupStep dim b) := columnClear_entryBound hm 0 hA
  have hr : RowEntryBound r (elimSupStep dim (elimSupStep dim b)) :=
    rowClear_entryBound hn 0 hc.1
  have hcR := (column_toReduction_entryBound hc (one_le_elimSupStep hd)).mono
    (le_elimSupStep hd)
  have hrR := row_toReduction_entryBound hr (one_le_elimSupStep hd)
  have h := reduction_then_entryBound hm hn hd hcR hrR
  simpa [clearPivot, c, r, Function.iterate_succ_apply] using! h

/-- Mixing two rows with a 2-by-2 coefficient matrix bounded by `c` sends entry bound `b` to
`max b (2 * (c * b))`. -/
private theorem rowMix_entry_le {m n : ℕ} (i j : Fin m) {C : Matrix (Fin 2) (Fin 2) ℤ}
    {A : Matrix (Fin m) (Fin n) ℤ} {c b : ℕ}
    (hC : MatrixEntryBound C c) (hA : MatrixEntryBound A b) :
    MatrixEntryBound (rowMix i j C A) (max b (2 * (c * b))) := by
  intro r k
  simp only [rowMix]
  split_ifs
  · apply (Int.natAbs_add_le _ _).trans
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact (Nat.add_le_add (Nat.mul_le_mul (hC 0 0) (hA i k))
      (Nat.mul_le_mul (hC 0 1) (hA j k))).trans (by omega)
  · apply (Int.natAbs_add_le _ _).trans
    rw [Int.natAbs_mul, Int.natAbs_mul]
    exact (Nat.add_le_add (Nat.mul_le_mul (hC 1 0) (hA i k))
      (Nat.mul_le_mul (hC 1 1) (hA j k))).trans (by omega)
  · exact (hA r k).trans (Nat.le_max_left _ _)

/-- The integer 2-by-2 matrix with rows `(1, 1)` and `(0, 1)` has entry bound one. -/
private theorem mix_one_entryBound (C : Matrix (Fin 2) (Fin 2) ℤ)
    (h0 : C 0 0 = 1) (h1 : C 0 1 = 1) (h2 : C 1 0 = 0) (h3 : C 1 1 = 1) :
    MatrixEntryBound C 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- Exposing a row produces a column elimination state bounded by `elimSupStep dim b` when the
input bound satisfies `b ≥ 1` and `dim ≥ 2`. -/
theorem exposeRow_entryBound {m n dim : ℕ} (hd : 2 ≤ dim) (r : Fin (m+1))
    {A : Matrix (Fin (m+1)) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    ColumnEntryBound (exposeRow r A) (elimSupStep dim b) := by
  by_cases hr : r = 0
  · subst r
    have h := reduction_identity_entryBound hA hb
    exact ⟨(hA.mono (le_elimSupStep (by omega))),
      (matrix_one_entryBound hb).mono (le_elimSupStep (by omega)),
      (matrix_one_entryBound hb).mono (le_elimSupStep (by omega))⟩
  · have hC : MatrixEntryBound (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) 1 :=
      mix_one_entryBound _ rfl rfl rfl rfl
    have hCi : MatrixEntryBound (!![1,-1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) 1 := by
      intro i j
      fin_cases i <;> fin_cases j <;> decide
    have htwo : max b (2 * (1 * b)) ≤ elimSupStep dim b := by
      have h := two_mul_le_elimSupStep (dim := dim) (b := b) hd
      omega
    simp only [exposeRow, if_neg hr]
    exact ⟨(rowMix_entry_le 0 r hC hA).mono htwo,
      (rowMix_entry_le 0 r hC (matrix_one_entryBound hb)).mono htwo,
      (rowMix_entry_le 0 r hCi (matrix_one_entryBound hb)).mono htwo⟩

/-- The counted column reduction has common entry bound given by `m` elimination-bound iterates,
assuming the input bound is at least one and the row count is at most `dim`. -/
theorem smithColumnReduceCounted_entryBound {m n dim : ℕ} (hm : m+1 ≤ dim) (p : Fin n)
    {A : Matrix (Fin (m+1)) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    ColumnEntryBound (smithColumnReduceCounted p A).1 ((elimSupStep dim)^[m] b) := by
  have h := smithColumnReduceCounted_elimSup p A b hA
  have he := elimSup_iterate_dim_mono hm m b
  rw [max_eq_left hb] at h
  exact ⟨fun i j => (h.1 i j).trans he, fun i j => (h.2.1 i j).trans he,
    fun i j => (h.2.2 i j).trans he⟩

/-- The counted row reduction has common entry bound given by `n` elimination-bound iterates,
assuming the input bound is at least one and the column count is at most `dim`. -/
theorem smithRowReduceCounted_entryBound {m n dim : ℕ} (hn : n+1 ≤ dim) (p : Fin m)
    {A : Matrix (Fin m) (Fin (n+1)) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    RowEntryBound (smithRowReduceCounted p A).1 ((elimSupStep dim)^[n] b) := by
  have h := smithRowReduceCounted_elimSup p A b hA
  have he := elimSup_iterate_dim_mono hn n b
  rw [max_eq_left hb] at h
  exact ⟨fun i j => (h.1 i j).trans he, fun i j => (h.2.1 i j).trans he,
    fun i j => (h.2.2 i j).trans he⟩

/-- The peak Euclidean-pair input size after a counted column fold is bounded by the maximum of
the incoming peak and the bit size of the entry bound iterated once per listed row, when the
row count is at most `dim`. -/
theorem smithColumnFoldCounted_peak_le {m n dim : ℕ} (hm : m+1 ≤ dim) (p : Fin n) :
    ∀ (ks : List (Fin m)) (s : ColumnEliminationState (m+1) n)
      (w : SmithEuclidWork) (b : ℕ), ColumnEntryBound s b →
      (smithColumnFoldCounted p ks s w).2.peakPairInputBits ≤
        max w.peakPairInputBits (((elimSupStep dim)^[ks.length] b).size) := by
  intro ks
  induction ks with
  | nil => intro s w b hs; simp [smithColumnFoldCounted]
  | cons k ks ih =>
      intro s w b hs
      have hd : 1 ≤ dim := by omega
      have hstep : ColumnEntryBound (smithColumnStepCounted p s k).1 (elimSupStep dim b) := by
        have h := smithColumnStepCounted_elimSup p s k b hs.1 hs.2.1 hs.2.2
        exact ⟨fun i j => (h.1 i j).trans (elimSupStep_dim_mono hm),
          fun i j => (h.2.1 i j).trans (elimSupStep_dim_mono hm),
          fun i j => (h.2.2 i j).trans (elimSupStep_dim_mono hm)⟩
      have htail := ih (smithColumnStepCounted p s k).1
        (w.append (smithColumnStepCounted p s k).2) (elimSupStep dim b) hstep
      have hcurrent : (smithColumnStepCounted p s k).2.peakPairInputBits ≤ b.size := by
        change (max (s.value 0 p).natAbs (s.value k.succ p).natAbs).size ≤ b.size
        exact Nat.size_le_size (max_le (hs.1 0 p) (hs.1 k.succ p))
      have hbnum : b ≤ (elimSupStep dim)^[ks.length] (elimSupStep dim b) :=
        (le_elimSupStep hd).trans (le_elimSup_iterate hd ks.length (elimSupStep dim b))
      have hbits : b.size ≤ ((elimSupStep dim)^[ks.length] (elimSupStep dim b)).size :=
        Nat.size_le_size hbnum
      simp only [smithColumnFoldCounted, List.foldl_cons, List.length_cons,
        Function.iterate_succ_apply, SmithEuclidWork.append] at htail ⊢
      omega

/-- The counted column reduction's peak pair-input bit size is at most the bit size of the entry
bound after `m` elimination-bound iterates, under the stated dimension and initial-bound
assumptions. -/
theorem smithColumnReduceCounted_peak_le {m n dim : ℕ} (hm : m+1 ≤ dim) (p : Fin n)
    {A : Matrix (Fin (m+1)) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    (smithColumnReduceCounted p A).2.peakPairInputBits ≤
      ((elimSupStep dim)^[m] b).size := by
  have h := smithColumnFoldCounted_peak_le hm p (List.finRange m) ⟨A,1,1⟩
    SmithEuclidWork.zero b ⟨hA, matrix_one_entryBound hb, matrix_one_entryBound hb⟩
  simpa [smithColumnReduceCounted, List.length_finRange, SmithEuclidWork.zero] using! h

/-- The counted row reduction's peak pair-input bit size is at most the bit size of the entry
bound after `n` elimination-bound iterates, under the stated dimension and initial-bound
assumptions. -/
theorem smithRowReduceCounted_peak_le {m n dim : ℕ} (hn : n+1 ≤ dim) (p : Fin m)
    {A : Matrix (Fin m) (Fin (n+1)) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    (smithRowReduceCounted p A).2.peakPairInputBits ≤
      ((elimSupStep dim)^[n] b).size := by
  simpa [smithRowReduceCounted] using!
    (smithColumnReduceCounted_peak_le hn p (A := A.transpose) (fun i j => hA j i) hb)

/-- Swapping the selected row with the first row preserves the common entry bound when that
bound is at least one. -/
private theorem swapRows_entryBound {m n : ℕ} (r : Fin (m+1))
    {A : Matrix (Fin (m+1)) (Fin n) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) : ColumnEntryBound (swapRows r A) b := by
  simp only [swapRows, ColumnEntryBound]
  exact ⟨matrix_submatrix_entryBound _ _ hA,
    matrix_submatrix_entryBound _ _ (matrix_one_entryBound hb),
    matrix_submatrix_entryBound _ _ (matrix_one_entryBound hb)⟩

/-- Swapping the selected column with the first column preserves the common entry bound when
that bound is at least one. -/
private theorem swapColumns_entryBound {m n : ℕ} (c : Fin (n+1))
    {A : Matrix (Fin m) (Fin (n+1)) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) : RowEntryBound (swapColumns c A) b := by
  have h := swapRows_entryBound c (A := A.transpose) (fun i j => hA j i) hb
  exact ⟨fun i j => h.1 j i, fun i j => h.2.1 j i, fun i j => h.2.2 j i⟩

/-- Moving a selected entry to the pivot position gives a presentation reduction bounded by
`elimSupStep dim b` under the stated dimension bounds and `b ≥ 1`. -/
theorem movePivot_entryBound {m n dim : ℕ} (hm : m+1 ≤ dim) (hn : n+1 ≤ dim)
    (hd : 1 ≤ dim) (rc : Fin (m+1) × Fin (n+1))
    {A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ} {b : ℕ}
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    ReductionEntryBound (movePivot rc A) (elimSupStep dim b) := by
  let s := swapRows rc.1 A
  have hs : ColumnEntryBound s b := swapRows_entryBound rc.1 hA hb
  have ht : RowEntryBound (swapColumns rc.2 s.value) b := swapColumns_entryBound rc.2 hs.1 hb
  simpa only [movePivot, s] using! reduction_then_entryBound hm hn hd
    (column_toReduction_entryBound hs hb) (row_toReduction_entryBound ht hb)

/-- Two presentation reductions whose entry bounds are both at most `b` compose with bound
`elimSupStep dim b`, under the stated dimension assumptions. -/
theorem reduction_then_entryBound_of_le {m n dim : ℕ} (hm : m ≤ dim) (hn : n ≤ dim)
    (hd : 1 ≤ dim) {s t : PresentationReduction m n} {bs bt b : ℕ}
    (hs : ReductionEntryBound s bs) (ht : ReductionEntryBound t bt)
    (hbs : bs ≤ b) (hbt : bt ≤ b) : ReductionEntryBound (s.then t) (elimSupStep dim b) :=
  reduction_then_entryBound hm hn hd (hs.mono hbs) (ht.mono hbt)

/-- The recursive entry-bound expression following the same divisibility tests and reduction
branches as the pivot-isolation loop for a specified fuel value. -/
def isolatePivotLoopSup (dim : ℕ) {m n : ℕ} :
    ℕ → Matrix (Fin (m+1)) (Fin (n+1)) ℤ → ℕ → ℕ
  | 0, _, b => b
  | fuel+1, A, b =>
    let A := tableMatrix (matrixTable A)
    let col := smithCheckAllFin (fun r => A 0 0 ∣ A r 0)
    if col.1 then
      let row := smithCheckAllFin (fun c => A 0 0 ∣ A 0 c)
      if row.1 then
        let s := clearPivot A
        let found := smithFindCounted (fun rc => decide (¬ s.value 0 0 ∣ s.value rc.1 rc.2))
          ((List.finRange (m+1)).product (List.finRange (n+1)))
        match found.1 with
        | none => (elimSupStep dim)^[3] b
        | some rc =>
          let e := exposeRow rc.1 s.value
          let t := smithRowReduceCounted 0 e.value
          (elimSupStep dim)^[3]
            (isolatePivotLoopSup dim fuel t.1.value
              ((elimSupStep dim)^[n] ((elimSupStep dim)^[4] b)))
      else
        let s := smithRowReduceCounted 0 A
        elimSupStep dim (isolatePivotLoopSup dim fuel s.1.value ((elimSupStep dim)^[n] b))
    else
      let s := smithColumnReduceCounted 0 A
      elimSupStep dim (isolatePivotLoopSup dim fuel s.1.value ((elimSupStep dim)^[m] b))

/-- The pivot-isolation bound obtained by initializing `isolatePivotLoopSup` with fuel `(A 0
0).natAbs + 1`. -/
def isolatePivotSup (dim : ℕ) {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (b : ℕ) : ℕ := isolatePivotLoopSup dim ((A 0 0).natAbs+1) A b

/-- The recursive entry-bound expression following pivot search, pivot isolation, and reduction
of the remaining submatrix in rectangular Smith reduction. -/
def rectangularSup (dim : ℕ) : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → ℕ → ℕ
  | 0, _, _, b => b
  | _+1, 0, _, b => b
  | m+1, n+1, A, b =>
    let A := tableMatrix (matrixTable A)
    let found := smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
      ((List.finRange (m+1)).product (List.finRange (n+1)))
    match found.1 with
    | none => b
    | some rc =>
      let s := movePivot rc A
      let t := smithIsolatePivotEuclid s.value
      (elimSupStep dim)^[2]
        (rectangularSup dim (t.1.1.value.submatrix Fin.succ Fin.succ)
          (isolatePivotSup dim s.value (elimSupStep dim b)))

/-- The pivot-loop bound is at least its initial bound for every fuel and input matrix when `dim
≥ 1` and the initial bound is at least one. -/
theorem le_isolatePivotLoopSup {m n dim : ℕ} (hd : 1 ≤ dim) :
    ∀ (fuel : ℕ) (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) {b : ℕ}, 1 ≤ b →
      b ≤ isolatePivotLoopSup dim fuel A b := by
  intro fuel
  induction fuel with
  | zero => intro A b hb; exact Nat.le_refl b
  | succ fuel ih =>
      intro A b hb
      simp only [isolatePivotLoopSup, tableMatrix_matrixTable]
      split
      · split
        · split
          · exact le_elimSup_iterate hd 3 b
          · rename_i rc he
            let t := smithRowReduceCounted 0 (exposeRow rc.1 (clearPivot A).value).value
            let bt := (elimSupStep dim)^[n] ((elimSupStep dim)^[4] b)
            have hb4 : 1 ≤ (elimSupStep dim)^[4] b := one_le_elimSup_iterate hd 4 hb
            have hbt : 1 ≤ bt := one_le_elimSup_iterate hd n hb4
            have hrec : bt ≤ isolatePivotLoopSup dim fuel t.1.value bt := ih t.1.value hbt
            have h0 : b ≤ (elimSupStep dim)^[4] b := le_elimSup_iterate hd 4 b
            have h1 : (elimSupStep dim)^[4] b ≤ bt := le_elimSup_iterate hd n _
            exact h0.trans (h1.trans (hrec.trans (le_elimSup_iterate hd 3 _)))
        · let s := smithRowReduceCounted 0 A
          let bs := (elimSupStep dim)^[n] b
          have hbs : 1 ≤ bs := one_le_elimSup_iterate hd n hb
          have hrec : bs ≤ isolatePivotLoopSup dim fuel s.1.value bs := ih s.1.value hbs
          exact (le_elimSup_iterate hd n b).trans (hrec.trans (le_elimSupStep hd))
      · let s := smithColumnReduceCounted 0 A
        let bs := (elimSupStep dim)^[m] b
        have hbs : 1 ≤ bs := one_le_elimSup_iterate hd m hb
        have hrec : bs ≤ isolatePivotLoopSup dim fuel s.1.value bs := ih s.1.value hbs
        exact (le_elimSup_iterate hd m b).trans (hrec.trans (le_elimSupStep hd))

/-- The full pivot-isolation bound is at least its initial bound when `dim ≥ 1` and the initial
bound is at least one. -/
theorem le_isolatePivotSup {m n dim : ℕ} (hd : 1 ≤ dim)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) {b : ℕ} (hb : 1 ≤ b) :
    b ≤ isolatePivotSup dim A b :=
  le_isolatePivotLoopSup hd ((A 0 0).natAbs+1) A hb

/-- The rectangular reduction bound is at least its initial bound when `dim ≥ 1` and the initial
bound is at least one. -/
theorem le_rectangularSup {dim : ℕ} (hd : 1 ≤ dim) :
    ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {b : ℕ}, 1 ≤ b →
      b ≤ rectangularSup dim A b := by
  intro m
  induction m with
  | zero => intro n A b hb; exact Nat.le_refl b
  | succ m ih =>
      intro n A b hb
      cases n with
      | zero => exact Nat.le_refl b
      | succ n =>
          simp only [rectangularSup, tableMatrix_matrixTable]
          split
          · exact Nat.le_refl b
          · rename_i rc he
            let B := (movePivot rc A).value
            let U := (smithIsolatePivotEuclid B).1.1.value.submatrix Fin.succ Fin.succ
            let bB := isolatePivotSup dim B (elimSupStep dim b)
            have hb1 : 1 ≤ elimSupStep dim b := one_le_elimSupStep hd
            have hB : elimSupStep dim b ≤ bB := le_isolatePivotSup hd B hb1
            have hbB : 1 ≤ bB := hb1.trans hB
            have hU : bB ≤ rectangularSup dim U bB := ih U hbB
            exact (le_elimSupStep hd).trans (hB.trans (hU.trans (le_elimSup_iterate hd 2 _)))

/-- Under the stated dimension and initial-bound assumptions, the counted pivot loop's reduction
entries are bounded by `isolatePivotLoopSup`. Its peak Euclidean-pair input size is at most
the bit size of that bound. -/
theorem smithIsolatePivotEuclidLoop_entryBound {m n dim : ℕ}
    (hm : m+1 ≤ dim) (hn : n+1 ≤ dim) (hd : 2 ≤ dim) :
    ∀ (fuel : ℕ) (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (b : ℕ),
      MatrixEntryBound A b → 1 ≤ b →
      ReductionEntryBound (smithIsolatePivotEuclidLoop fuel A).1.1
          (isolatePivotLoopSup dim fuel A b) ∧
        (smithIsolatePivotEuclidLoop fuel A).2.peakPairInputBits ≤
          (isolatePivotLoopSup dim fuel A b).size := by
  have hd1 : 1 ≤ dim := by omega
  intro fuel
  induction fuel with
  | zero =>
      intro A b hA hb
      exact ⟨reduction_identity_entryBound hA hb, Nat.zero_le _⟩
  | succ fuel ih =>
      intro A b hA hb
      simp only [smithIsolatePivotEuclidLoop, isolatePivotLoopSup, tableMatrix_matrixTable]
      split
      · split
        · split
          · rename_i he
            simp only [he]
            have hs := clearPivot_entryBound hm hn hA
            exact ⟨hs, Nat.zero_le _⟩
          · rename_i rc he
            simp only [he]
            let s := clearPivot A
            let e := exposeRow rc.1 s.value
            let t := smithRowReduceCounted 0 e.value
            let b0 := (elimSupStep dim)^[4] b
            let bt := (elimSupStep dim)^[n] b0
            let tail := smithIsolatePivotEuclidLoop fuel t.1.value
            let B := isolatePivotLoopSup dim fuel t.1.value bt
            have hb3 : 1 ≤ (elimSupStep dim)^[3] b := one_le_elimSup_iterate hd1 3 hb
            have hs : ReductionEntryBound s ((elimSupStep dim)^[3] b) := by
              simpa [s] using! clearPivot_entryBound hm hn hA
            have hb0 : 1 ≤ b0 := one_le_elimSup_iterate hd1 4 hb
            have he : ColumnEntryBound e b0 := by
              simpa [e, b0, Function.iterate_succ_apply] using!
                exposeRow_entryBound hd rc.1 hs.1 hb3
            have hbt : 1 ≤ bt := one_le_elimSup_iterate hd1 n hb0
            have ht : RowEntryBound t.1 bt := by
              simpa [t, bt] using! smithRowReduceCounted_entryBound hn 0 he.1 hb0
            have hrec : ReductionEntryBound tail.1.1 B ∧
                tail.2.peakPairInputBits ≤ B.size := by
              simpa [tail, B] using! ih t.1.value bt ht.1 hbt
            have htp : t.2.peakPairInputBits ≤ bt.size := by
              simpa [t, bt] using! smithRowReduceCounted_peak_le hn 0 he.1 hb0
            have hb0bt : b0 ≤ bt := le_elimSup_iterate hd1 n b0
            have hbtB : bt ≤ B := by
              simpa [B] using! le_isolatePivotLoopSup hd1 fuel t.1.value hbt
            have hb0B : b0 ≤ B := hb0bt.trans hbtB
            have hs0 : (elimSupStep dim)^[3] b ≤ b0 := by
              have h := le_elimSup_iterate hd1 1 ((elimSupStep dim)^[3] b)
              simpa [b0, Function.iterate_succ_apply] using! h
            have h1 : ReductionEntryBound (t.1.toReduction.then tail.1.1)
                (elimSupStep dim B) :=
              reduction_then_entryBound_of_le hm hn hd1
                (row_toReduction_entryBound ht hbt) hrec.1 hbtB (Nat.le_refl B)
            have h2 : ReductionEntryBound (e.toReduction.then (t.1.toReduction.then tail.1.1))
                (elimSupStep dim (elimSupStep dim B)) :=
              reduction_then_entryBound_of_le hm hn hd1
                (column_toReduction_entryBound he hb0) h1
                (hb0B.trans (le_elimSupStep hd1)) (Nat.le_refl _)
            have h3 : ReductionEntryBound
                (s.then (e.toReduction.then (t.1.toReduction.then tail.1.1)))
                ((elimSupStep dim)^[3] B) := by
              have h := reduction_then_entryBound_of_le hm hn hd1 hs h2
                (hs0.trans (hb0B.trans ((le_elimSupStep hd1).trans (le_elimSupStep hd1))))
                (Nat.le_refl _)
              simpa [Function.iterate_succ_apply] using! h
            have htfinal : t.2.peakPairInputBits ≤ ((elimSupStep dim)^[3] B).size :=
              htp.trans (Nat.size_le_size (hbtB.trans (le_elimSup_iterate hd1 3 B)))
            have htailfinal : tail.2.peakPairInputBits ≤ ((elimSupStep dim)^[3] B).size :=
              hrec.2.trans (Nat.size_le_size (le_elimSup_iterate hd1 3 B))
            refine ⟨?_, ?_⟩
            · simpa [s, e, t, tail, B, b0, bt, Function.iterate_succ_apply] using! h3
            · have hp : (t.2.append tail.2).peakPairInputBits ≤
                  ((elimSupStep dim)^[3] B).size := by
                exact max_le htfinal htailfinal
              simpa [t, tail, B, b0, bt, Function.iterate_succ_apply] using! hp
        · let s := smithRowReduceCounted 0 A
          let bs := (elimSupStep dim)^[n] b
          let tail := smithIsolatePivotEuclidLoop fuel s.1.value
          let B := isolatePivotLoopSup dim fuel s.1.value bs
          have hbs : 1 ≤ bs := one_le_elimSup_iterate hd1 n hb
          have hs : RowEntryBound s.1 bs := by
            simpa [s, bs] using! smithRowReduceCounted_entryBound hn 0 hA hb
          have hrec : ReductionEntryBound tail.1.1 B ∧
              tail.2.peakPairInputBits ≤ B.size := by
            simpa [tail, B] using! ih s.1.value bs hs.1 hbs
          have hsp : s.2.peakPairInputBits ≤ bs.size := by
            simpa [s, bs] using! smithRowReduceCounted_peak_le hn 0 hA hb
          have hbsB : bs ≤ B := by
            simpa [B] using! le_isolatePivotLoopSup hd1 fuel s.1.value hbs
          have hcomp : ReductionEntryBound (s.1.toReduction.then tail.1.1)
              (elimSupStep dim B) :=
            reduction_then_entryBound_of_le hm hn hd1
              (row_toReduction_entryBound hs hbs) hrec.1 hbsB (Nat.le_refl B)
          have hsf : s.2.peakPairInputBits ≤ (elimSupStep dim B).size :=
            hsp.trans (Nat.size_le_size (hbsB.trans (le_elimSupStep hd1)))
          have htf : tail.2.peakPairInputBits ≤ (elimSupStep dim B).size :=
            hrec.2.trans (Nat.size_le_size (le_elimSupStep hd1))
          refine ⟨?_, ?_⟩
          · simpa [s, tail, B, bs] using! hcomp
          · have hp : (s.2.append tail.2).peakPairInputBits ≤
                (elimSupStep dim B).size := max_le hsf htf
            simpa [s, tail, B, bs] using! hp
      · let s := smithColumnReduceCounted 0 A
        let bs := (elimSupStep dim)^[m] b
        let tail := smithIsolatePivotEuclidLoop fuel s.1.value
        let B := isolatePivotLoopSup dim fuel s.1.value bs
        have hbs : 1 ≤ bs := one_le_elimSup_iterate hd1 m hb
        have hs : ColumnEntryBound s.1 bs := by
          simpa [s, bs] using! smithColumnReduceCounted_entryBound hm 0 hA hb
        have hrec : ReductionEntryBound tail.1.1 B ∧
            tail.2.peakPairInputBits ≤ B.size := by
          simpa [tail, B] using! ih s.1.value bs hs.1 hbs
        have hsp : s.2.peakPairInputBits ≤ bs.size := by
          simpa [s, bs] using! smithColumnReduceCounted_peak_le hm 0 hA hb
        have hbsB : bs ≤ B := by
          simpa [B] using! le_isolatePivotLoopSup hd1 fuel s.1.value hbs
        have hcomp : ReductionEntryBound (s.1.toReduction.then tail.1.1)
            (elimSupStep dim B) :=
          reduction_then_entryBound_of_le hm hn hd1
            (column_toReduction_entryBound hs hbs) hrec.1 hbsB (Nat.le_refl B)
        have hsf : s.2.peakPairInputBits ≤ (elimSupStep dim B).size :=
          hsp.trans (Nat.size_le_size (hbsB.trans (le_elimSupStep hd1)))
        have htf : tail.2.peakPairInputBits ≤ (elimSupStep dim B).size :=
          hrec.2.trans (Nat.size_le_size (le_elimSupStep hd1))
        refine ⟨?_, ?_⟩
        · simpa [s, tail, B, bs] using! hcomp
        · have hp : (s.2.append tail.2).peakPairInputBits ≤
              (elimSupStep dim B).size := max_le hsf htf
          simpa [s, tail, B, bs] using! hp

/-- The complete counted pivot-isolation routine has reduction entries bounded by
`isolatePivotSup` and peak pair-input size bounded by its bit size, under the stated
dimension and input-bound assumptions. -/
theorem smithIsolatePivotEuclid_entryBound {m n dim : ℕ}
    (hm : m+1 ≤ dim) (hn : n+1 ≤ dim) (hd : 2 ≤ dim)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (b : ℕ)
    (hA : MatrixEntryBound A b) (hb : 1 ≤ b) :
    ReductionEntryBound (smithIsolatePivotEuclid A).1.1 (isolatePivotSup dim A b) ∧
      (smithIsolatePivotEuclid A).2.peakPairInputBits ≤ (isolatePivotSup dim A b).size := by
  simpa [smithIsolatePivotEuclid, isolatePivotSup] using!
    smithIsolatePivotEuclidLoop_entryBound hm hn hd ((A 0 0).natAbs+1) A b hA hb

/-- For `dim ≥ m + n + 2` and input bound `b ≥ 1`, the counted rectangular Smith reduction has
entries bounded by `rectangularSup dim A b` and peak pair-input size at most its bit size. -/
theorem smithRectangularEuclid_entryBound {dim : ℕ} (hd : 2 ≤ dim) :
    ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : ℕ),
      m+n+2 ≤ dim → MatrixEntryBound A b → 1 ≤ b →
      ReductionEntryBound (smithRectangularEuclid A).1.1 (rectangularSup dim A b) ∧
        (smithRectangularEuclid A).2.peakPairInputBits ≤ (rectangularSup dim A b).size := by
  have hd1 : 1 ≤ dim := by omega
  intro m
  induction m with
  | zero =>
      intro n A b hdim hA hb
      exact ⟨reduction_identity_entryBound hA hb, Nat.zero_le _⟩
  | succ m ih =>
      intro n A b hdim hA hb
      cases n with
      | zero => exact ⟨reduction_identity_entryBound hA hb, Nat.zero_le _⟩
      | succ n =>
          have hm : m+1 ≤ dim := by omega
          have hn : n+1 ≤ dim := by omega
          simp only [smithRectangularEuclid, rectangularSup, tableMatrix_matrixTable]
          split
          · rename_i he
            simp only [he]
            exact ⟨reduction_identity_entryBound hA hb, Nat.zero_le _⟩
          · rename_i rc he
            simp only [he]
            let B := movePivot rc A
            let t := smithIsolatePivotEuclid B.value
            let bB := isolatePivotSup dim B.value (elimSupStep dim b)
            let U := t.1.1.value.submatrix Fin.succ Fin.succ
            let tail := smithRectangularEuclid U
            let R := rectangularSup dim U bB
            have hb1 : 1 ≤ elimSupStep dim b := one_le_elimSupStep hd1
            have hmove : ReductionEntryBound B (elimSupStep dim b) := by
              simpa [B] using! movePivot_entryBound hm hn hd1 rc hA hb
            have hB : ReductionEntryBound t.1.1 bB ∧ t.2.peakPairInputBits ≤ bB.size := by
              simpa [t, B, bB] using!
                smithIsolatePivotEuclid_entryBound hm hn hd B.value (elimSupStep dim b)
                  hmove.1 hb1
            have hbB : 1 ≤ bB := hb1.trans (le_isolatePivotSup hd1 B.value hb1)
            have hU : MatrixEntryBound U bB := matrix_submatrix_entryBound _ _ hB.1.1
            have hrec : ReductionEntryBound tail.1.1 R ∧ tail.2.peakPairInputBits ≤ R.size := by
              simpa [tail, R] using! ih U bB (by omega) hU hbB
            have hbR0 : bB ≤ R := by
              simpa [R] using! le_rectangularSup hd1 U hbB
            have hbR : 1 ≤ R := hbB.trans hbR0
            have hlift : ReductionEntryBound (tail.1.1.lift (t.1.1.value 0 0)) R :=
              reduction_lift_entryBound ((hB.1.1 0 0).trans hbR0) hrec.1 hbR
            have hcomp1 : ReductionEntryBound
                (t.1.1.then (tail.1.1.lift (t.1.1.value 0 0))) (elimSupStep dim R) :=
              reduction_then_entryBound_of_le hm hn hd1 hB.1 hlift hbR0 (Nat.le_refl R)
            have hmoveR : elimSupStep dim b ≤ elimSupStep dim R :=
              elimSupStep_mono ((le_elimSupStep hd1).trans
                ((le_isolatePivotSup hd1 B.value hb1).trans hbR0))
            have hcomp2 : ReductionEntryBound
                (B.then (t.1.1.then (tail.1.1.lift (t.1.1.value 0 0))))
                ((elimSupStep dim)^[2] R) := by
              have h := reduction_then_entryBound_of_le hm hn hd1 hmove hcomp1 hmoveR
                (Nat.le_refl _)
              simpa [Function.iterate_succ_apply] using! h
            have htp : t.2.peakPairInputBits ≤ ((elimSupStep dim)^[2] R).size :=
              hB.2.trans (Nat.size_le_size (hbR0.trans (le_elimSup_iterate hd1 2 R)))
            have hsp : tail.2.peakPairInputBits ≤ ((elimSupStep dim)^[2] R).size :=
              hrec.2.trans (Nat.size_le_size (le_elimSup_iterate hd1 2 R))
            refine ⟨?_, ?_⟩
            · simpa [B, t, U, tail, R, bB, Function.iterate_succ_apply] using! hcomp2
            · have hp : (t.2.append tail.2).peakPairInputBits ≤
                  ((elimSupStep dim)^[2] R).size := max_le htp hsp
              simpa [B, t, U, tail, R, bB, Function.iterate_succ_apply] using! hp

namespace output1

/-- The counted rectangular routine satisfies the entry and peak-bit bounds defined by
`rectangularSup (m + n + 2) A (max b 1)` and the stated quotient-remainder count bound. Its
reduction equals `rectangularSmith A`, encodes `A`, and has value in Smith form. -/
theorem frontier1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ b) :
    let dim := m+n+2
    let B := rectangularSup dim A (max b 1)
    ReductionEntryBound (smithRectangularEuclid A).1.1 B ∧
      (smithRectangularEuclid A).2.peakPairInputBits ≤ B.size ∧
      (smithRectangularEuclid A).2.quotRemPairs ≤
        (m+n)*(smithRectangularEuclid A).1.2 .pivotFuelAllocated *
          (2*(smithRectangularEuclid A).2.peakPairInputBits+2) ∧
      (smithRectangularEuclid A).1.1 = rectangularSmith A ∧
      (smithRectangularEuclid A).1.1.Encodes A ∧
      SmithForm (smithRectangularEuclid A).1.1.value := by
  (try dsimp only)
  have hb : 1 ≤ max b 1 := by omega
  have h := smithRectangularEuclid_entryBound (dim := m+n+2) (by omega) A (max b 1)
    (by omega) (fun i j => (hA i j).trans (Nat.le_max_left b 1)) hb
  have hdiv := smithRectangularEuclid_division_bound A
  have hvalue : (smithRectangularEuclid A).1.1 = rectangularSmith A := by simp
  refine ⟨h.1, h.2, hdiv, hvalue, ?_, ?_⟩
  · rw [hvalue]
    exact rectangularSmith_encodes A
  · rw [hvalue]
    exact rectangularSmith_form A

end output1

end Qatlib.Concepts.HspRecovery.ReductionCore
