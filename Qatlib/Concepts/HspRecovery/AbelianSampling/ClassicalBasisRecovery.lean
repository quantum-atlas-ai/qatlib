/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Matrix

abbrev IMat (k : ℕ) := Matrix (Fin k) (Fin k) ℤ

section Span

variable {k m : ℕ}

def rowSpan (R : Matrix (Fin k) (Fin m) ℤ) : Submodule ℤ (Fin m → ℤ) :=
  Submodule.span ℤ (Set.range R)

def colSpan (A : Matrix (Fin k) (Fin m) ℤ) : Submodule ℤ (Fin k → ℤ) :=
  rowSpan Aᵀ

theorem colSpan_transpose (R : Matrix (Fin k) (Fin k) ℤ) : colSpan Rᵀ = rowSpan R := rfl

theorem rowSpan_transpose (A : Matrix (Fin k) (Fin m) ℤ) : rowSpan Aᵀ = colSpan A := rfl

end Span

section Bezout

def bezC (u v : ℤ) : ℤ × ℤ :=
  if v = 0 then ((if u < 0 then (-1 : ℤ) else 1), 0) else
  ((Int.gcdA u v % |v / (Int.gcd u v : ℤ)|),
   Int.gcdB u v - ((Int.gcdA u v % |v / (Int.gcd u v : ℤ)| - Int.gcdA u v)
     / (v / (Int.gcd u v : ℤ))) * (u / (Int.gcd u v : ℤ)))

theorem ediv_mul_cross {g u v : ℤ} (hgu : g ∣ u) (hgv : g ∣ v) : (u / g) * v = (v / g) * u := by
  have hu : (u / g) * g = u := Int.ediv_mul_cancel hgu
  have hv : (v / g) * g = v := Int.ediv_mul_cancel hgv
  linear_combination (v / g) * hu - (u / g) * hv

theorem bezC_spec (u v : ℤ) : (bezC u v).1 * u + (bezC u v).2 * v = (Int.gcd u v : ℤ) := by
  by_cases hv : v = 0
  · subst hv
    unfold bezC
    split
    · rw [Int.gcd_zero_right]
      by_cases hu : u < 0
      · simp only [if_pos hu]; omega
      · simp only [if_neg hu]; omega
    · rename_i hcontra; exact absurd rfl hcontra
  · have hg0 : (0 : ℤ) < (Int.gcd u v : ℤ) :=
      Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_right u hv)
    have hgu : (Int.gcd u v : ℤ) ∣ u := Int.gcd_dvd_left u v
    have hgv : (Int.gcd u v : ℤ) ∣ v := Int.gcd_dvd_right u v
    have hgd0 : v / (Int.gcd u v : ℤ) ≠ 0 := by
      intro h
      apply hv
      calc v = (v / (Int.gcd u v : ℤ)) * (Int.gcd u v : ℤ) := (Int.ediv_mul_cancel hgv).symm
        _ = 0 := by rw [h, zero_mul]
    have hdvd : (v / (Int.gcd u v : ℤ)) ∣
        (Int.gcdA u v % |v / (Int.gcd u v : ℤ)| - Int.gcdA u v) := by
      have hmod : |v / (Int.gcd u v : ℤ)| * (Int.gcdA u v / |v / (Int.gcd u v : ℤ)|)
          + Int.gcdA u v % |v / (Int.gcd u v : ℤ)| = Int.gcdA u v :=
        Int.mul_ediv_add_emod _ _
      rcases lt_or_ge (v / (Int.gcd u v : ℤ)) 0 with hsign | hsign
      · rw [abs_of_neg hsign] at hmod ⊢
        exact ⟨(Int.gcdA u v / -(v / (Int.gcd u v : ℤ))), by linear_combination hmod⟩
      · rw [abs_of_nonneg hsign] at hmod ⊢
        exact ⟨-(Int.gcdA u v / (v / (Int.gcd u v : ℤ))), by linear_combination hmod⟩
    have hA : Int.gcdA u v % |v / (Int.gcd u v : ℤ)| =
        Int.gcdA u v + ((Int.gcdA u v % |v / (Int.gcd u v : ℤ)| - Int.gcdA u v)
          / (v / (Int.gcd u v : ℤ))) * (v / (Int.gcd u v : ℤ)) := by
      rw [Int.ediv_mul_cancel hdvd]; ring
    have hcross : (u / (Int.gcd u v : ℤ)) * v = (v / (Int.gcd u v : ℤ)) * u :=
      ediv_mul_cross hgu hgv
    have hAB : Int.gcdA u v * u + Int.gcdB u v * v = (Int.gcd u v : ℤ) := by
      rw [Int.gcd_eq_gcd_ab]; ring
    simp only [bezC, if_neg hv]
    linear_combination hAB + u * hA
      - ((Int.gcdA u v % |v / (Int.gcd u v : ℤ)| - Int.gcdA u v)
          / (v / (Int.gcd u v : ℤ))) * hcross

theorem bezC_bound (u v : ℤ) : |(bezC u v).1| ≤ |v| + 1 ∧ |(bezC u v).2| ≤ |u| + 1 := by
  by_cases hv : v = 0
  · subst hv
    unfold bezC
    split
    · by_cases hu : u < 0
      · simp only [if_pos hu]; exact ⟨by norm_num, by positivity⟩
      · simp only [if_neg hu]; exact ⟨by norm_num, by positivity⟩
    · rename_i hcontra; exact absurd rfl hcontra
  · have hg0 : (0 : ℤ) < (Int.gcd u v : ℤ) :=
      Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_right u hv)
    have hgu : (Int.gcd u v : ℤ) ∣ u := Int.gcd_dvd_left u v
    have hgv : (Int.gcd u v : ℤ) ∣ v := Int.gcd_dvd_right u v
    have hgd0 : v / (Int.gcd u v : ℤ) ≠ 0 := by
      intro h
      apply hv
      calc v = (v / (Int.gcd u v : ℤ)) * (Int.gcd u v : ℤ) := (Int.ediv_mul_cancel hgv).symm
        _ = 0 := by rw [h, zero_mul]
    have ha : 0 ≤ Int.gcdA u v % |v / (Int.gcd u v : ℤ)| :=
      Int.emod_nonneg _ (abs_ne_zero.mpr hgd0)
    have halt : Int.gcdA u v % |v / (Int.gcd u v : ℤ)| < |v / (Int.gcd u v : ℤ)| := by
      have h := Int.emod_lt (Int.gcdA u v) (abs_ne_zero.mpr hgd0)
      rwa [Int.natAbs_abs, ← Int.abs_eq_natAbs] at h
    have hgcdle : ((Int.gcd u v : ℕ) : ℤ) ≤ |v| := by
      rw [Int.abs_eq_natAbs]
      exact Nat.cast_le.mpr (Int.natAbs_le_of_dvd_ne_zero hgv hv)
    have hdle : |v / (Int.gcd u v : ℤ)| ≤ |v| := by
      have hprod : |v / (Int.gcd u v : ℤ)| * (Int.gcd u v : ℤ) = |v| := by
        calc |v / (Int.gcd u v : ℤ)| * (Int.gcd u v : ℤ)
            = |(v / (Int.gcd u v : ℤ)) * (Int.gcd u v : ℤ)| := by
              rw [abs_mul, abs_of_pos hg0]
          _ = |v| := by rw [Int.ediv_mul_cancel hgv]
      calc |v / (Int.gcd u v : ℤ)| = |v / (Int.gcd u v : ℤ)| * 1 := by ring
        _ ≤ |v / (Int.gcd u v : ℤ)| * (Int.gcd u v : ℤ) :=
            mul_le_mul_of_nonneg_left (by linarith : (1 : ℤ) ≤ (Int.gcd u v : ℤ))
              (abs_nonneg _)
        _ = |v| := hprod
    have haLe : |(bezC u v).1| ≤ |v| := by
      have h1 : |(bezC u v).1| ≤ |v / (Int.gcd u v : ℤ)| := by
        unfold bezC
        rw [if_neg hv, abs_of_nonneg ha]
        exact le_of_lt halt
      exact h1.trans hdle
    have hFirst : |(bezC u v).1| ≤ |v| + 1 := by omega
    refine ⟨hFirst, ?_⟩
    have hspec := bezC_spec u v
    have hbv : (bezC u v).2 * v = (Int.gcd u v : ℤ) - (bezC u v).1 * u := by
      linear_combination hspec
    have haLeNat : (bezC u v).1.natAbs ≤ v.natAbs := by
      have := haLe
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
      exact Nat.cast_le.mp this
    have hgcdNat : (Int.gcd u v : ℕ) ≤ v.natAbs := by
      have hle := hgcdle
      rw [Int.abs_eq_natAbs] at hle
      exact Nat.cast_le.mp hle
    have h1 : (bezC u v).2.natAbs * v.natAbs ≤ v.natAbs + v.natAbs * u.natAbs := by
      have e0 : (bezC u v).2.natAbs * v.natAbs
          = ((Int.gcd u v : ℤ) - (bezC u v).1 * u).natAbs := by
        rw [← Int.natAbs_mul, hbv]
      have e2 := Int.natAbs_add_le ((Int.gcd u v : ℤ)) (-(bezC u v).1 * u)
      rw [neg_mul, Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast] at e2
      have e3 : (bezC u v).1.natAbs * u.natAbs ≤ v.natAbs * u.natAbs :=
        Nat.mul_le_mul haLeNat (Nat.le_refl _)
      rw [e0, sub_eq_add_neg]
      omega
    have hvne : v.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hv
    have h2 : (bezC u v).2.natAbs ≤ u.natAbs + 1 := by
      have h4 : (bezC u v).2.natAbs * v.natAbs ≤ v.natAbs * (u.natAbs + 1) := by
        have e4 : v.natAbs * (u.natAbs + 1) = v.natAbs * u.natAbs + v.natAbs := by ring
        omega
      exact Nat.le_of_mul_le_mul_left (by rw [Nat.mul_comm]; exact h4)
        (Nat.pos_of_ne_zero hvne)
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    have e5 : (((u.natAbs : ℕ) : ℤ)) + 1 = ((u.natAbs + 1 : ℕ) : ℤ) := by norm_num
    rw [e5]
    exact Nat.cast_le.mpr h2

end Bezout

section Canonical

variable {k : ℕ}

def IsCanonicalHNF (H : IMat k) : Prop :=
  (∀ i j : Fin k, (j : ℕ) < (i : ℕ) → H i j = 0) ∧
  (∀ i : Fin k, 0 < H i i) ∧
  (∀ i j : Fin k, (i : ℕ) < (j : ℕ) → 0 ≤ H i j ∧ H i j < H i i)

end Canonical

section Ops

variable {k : ℕ}

def signFixRow (c : Fin k) (R : IMat k) : IMat k :=
  if R c c < 0 then R.updateRow c (fun j => -R c j) else R

def hnfSwapOp (R : IMat k) (c i : Fin k) : IMat k :=
  (R.updateRow c (fun j => (bezC (R i c) (R c c)).2 * R c j
    + (bezC (R i c) (R c c)).1 * R i j)).updateRow i
    (fun j => (R c c / (Int.gcd (R i c) (R c c) : ℤ)) * R i j
      - (R i c / (Int.gcd (R i c) (R c c) : ℤ)) * R c j)

def reduceRowOp (R : IMat k) (i j : Fin k) : IMat k :=
  R.updateRow j (fun c => R j c - (R j i / R i i) * R i c)

theorem hnfSwapOp_c (R : IMat k) {c i : Fin k} (hci : i ≠ c) (j : Fin k) :
    hnfSwapOp R c i c j = (bezC (R i c) (R c c)).2 * R c j
      + (bezC (R i c) (R c c)).1 * R i j := by
  simp only [hnfSwapOp, Matrix.updateRow_apply, if_neg (Ne.symm hci), if_true]

theorem hnfSwapOp_i (R : IMat k) {c i : Fin k} (j : Fin k) :
    hnfSwapOp R c i i j = (R c c / (Int.gcd (R i c) (R c c) : ℤ)) * R i j
      - (R i c / (Int.gcd (R i c) (R c c) : ℤ)) * R c j := by
  simp only [hnfSwapOp, Matrix.updateRow_apply, if_true]

theorem hnfSwapOp_of (R : IMat k) {c i r : Fin k} (hr : r ≠ c) (hri : r ≠ i) (j : Fin k) :
    hnfSwapOp R c i r j = R r j := by
  simp only [hnfSwapOp, Matrix.updateRow_apply, if_neg hri, if_neg hr]

theorem hnfSwapOp_row_of (R : IMat k) {c i r : Fin k} (hr : r ≠ c) (hri : r ≠ i) :
    (hnfSwapOp R c i) r = R r := by
  funext j; exact hnfSwapOp_of R hr hri j

theorem hnfSwapOp_zero (R : IMat k) {c i : Fin k} :
    hnfSwapOp R c i i c = 0 := by
  have hgxy : (Int.gcd (R i c) (R c c) : ℤ) ∣ R c c := Int.gcd_dvd_right _ _
  have hgyy : (Int.gcd (R i c) (R c c) : ℤ) ∣ R i c := Int.gcd_dvd_left _ _
  rw [hnfSwapOp_i R]
  rw [ediv_mul_cross hgxy hgyy]
  ring

theorem rowSpan_congr_rows {R S : IMat k} (hRS : ∀ r, R r ∈ rowSpan S)
    (hSR : ∀ r, S r ∈ rowSpan R) : rowSpan R = rowSpan S := by
  refine le_antisymm ?_ ?_
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hRS)
  · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hSR)

theorem mem_rowSpan_smul_row {R : IMat k} {c : Fin k} {a : ℤ} : a • R c ∈ rowSpan R := by
  rw [rowSpan, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun r => if r = c then a else 0, ?_⟩
  rw [Finset.sum_eq_single c (fun b _ hne => by simp [hne])
    (fun h => absurd (Finset.mem_univ c) h)]
  simp

theorem mem_rowSpan_row {R : IMat k} (c : Fin k) : R c ∈ rowSpan R := by
  simpa using mem_rowSpan_smul_row (a := (1 : ℤ)) (c := c) (R := R)

theorem mem_rowSpan_two {R : IMat k} {c i : Fin k} (a b : ℤ) :
    a • R c + b • R i ∈ rowSpan R :=
  Submodule.add_mem _ mem_rowSpan_smul_row mem_rowSpan_smul_row

theorem mem_rowSpan_sub {R : IMat k} {c i : Fin k} (a b : ℤ) :
    a • R c - b • R i ∈ rowSpan R := by
  have h : a • R c - b • R i = a • R c + (-(b : ℤ)) • R i := by
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [h]
  exact mem_rowSpan_two _ _

theorem int_gcd_pos_of_left {y x : ℤ} (hy : y ≠ 0) : (0 : ℤ) < (Int.gcd y x : ℤ) := by
  have hd : (Int.gcd y x : ℤ) ∣ y := Int.gcd_dvd_left y x
  have hne : (Int.gcd y x : ℤ) ≠ 0 := by
    intro h
    rw [h] at hd
    exact hy (eq_zero_of_zero_dvd hd)
  omega

theorem hnf_unit {y x : ℤ} (hy : y ≠ 0) :
    (x / (Int.gcd y x : ℤ)) * (bezC y x).2 + (y / (Int.gcd y x : ℤ)) * (bezC y x).1
      = 1 := by
  have hg0 : (0 : ℤ) < (Int.gcd y x : ℤ) := int_gcd_pos_of_left hy
  have hgy : (Int.gcd y x : ℤ) ∣ y := Int.gcd_dvd_left y x
  have hgx : (Int.gcd y x : ℤ) ∣ x := Int.gcd_dvd_right y x
  have hspec : (bezC y x).1 * y + (bezC y x).2 * x = (Int.gcd y x : ℤ) := bezC_spec y x
  have key : (Int.gcd y x : ℤ) * ((x / (Int.gcd y x : ℤ)) * (bezC y x).2
      + (y / (Int.gcd y x : ℤ)) * (bezC y x).1) = (Int.gcd y x : ℤ) * 1 := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, Int.mul_ediv_cancel' hgx,
      Int.mul_ediv_cancel' hgy]
    linear_combination hspec
  exact mul_left_cancel₀ hg0.ne' key

theorem rowSpan_signFixRow (c : Fin k) (R : IMat k) :
    rowSpan (signFixRow c R) = rowSpan R := by
  unfold signFixRow
  split
  · set S := R.updateRow c (fun j => -R c j) with hS
    have hc : S c = (-1 : ℤ) • R c := by
      rw [hS, Matrix.updateRow_self]
      funext j; simp
    have hrw : ∀ r : Fin k, r ≠ c → S r = R r := by
      intro r hr; rw [hS, Matrix.updateRow_ne hr]
    refine rowSpan_congr_rows ?_ ?_
    · intro r
      by_cases hr : r = c
      · rw [hr, hc]; exact mem_rowSpan_smul_row
      · rw [hrw r hr]; exact mem_rowSpan_row _
    · intro r
      by_cases hr : r = c
      · have hrc : R c = (-1 : ℤ) • S c := by
          rw [hc]; simp
        rw [hr, hrc]; exact mem_rowSpan_smul_row
      · rw [← hrw r hr]; exact mem_rowSpan_row _
  · rfl

theorem rowSpan_hnfSwapOp (R : IMat k) {c i : Fin k} (hlt : (i : ℕ) < (c : ℕ))
    (hy : R i c ≠ 0) : rowSpan (hnfSwapOp R c i) = rowSpan R := by
  have hci : i ≠ c := fun h => absurd (congrArg Fin.val h) (by omega)
  have hunit : (R c c / (Int.gcd (R i c) (R c c) : ℤ)) * (bezC (R i c) (R c c)).2
      + (R i c / (Int.gcd (R i c) (R c c) : ℤ)) * (bezC (R i c) (R c c)).1 = 1 :=
    hnf_unit hy
  have hrowc : (hnfSwapOp R c i) c
      = (bezC (R i c) (R c c)).2 • R c + (bezC (R i c) (R c c)).1 • R i := by
    funext j
    rw [hnfSwapOp_c R hci j, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
  have hrowi : (hnfSwapOp R c i) i
      = (R c c / (Int.gcd (R i c) (R c c) : ℤ)) • R i
        - (R i c / (Int.gcd (R i c) (R c c) : ℤ)) • R c := by
    funext j
    rw [hnfSwapOp_i R j, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul]
  have hinvc : R c = (R c c / (Int.gcd (R i c) (R c c) : ℤ)) • ((hnfSwapOp R c i) c)
      - (bezC (R i c) (R c c)).1 • ((hnfSwapOp R c i) i) := by
    funext j
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hrowc, hrowi]
    linear_combination -(R c j) * hunit
  have hinvi : R i = (R i c / (Int.gcd (R i c) (R c c) : ℤ)) • ((hnfSwapOp R c i) c)
      + (bezC (R i c) (R c c)).2 • ((hnfSwapOp R c i) i) := by
    funext j
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hrowc, hrowi]
    linear_combination -(R i j) * hunit
  refine rowSpan_congr_rows ?_ ?_
  · intro r
    by_cases hrc : r = c
    · rw [hrc, hrowc]; exact mem_rowSpan_two _ _
    · by_cases hri : r = i
      · rw [hri, hrowi]; exact mem_rowSpan_sub _ _
      · rw [hnfSwapOp_row_of R hrc hri]; exact mem_rowSpan_row _
  · intro r
    by_cases hrc : r = c
    · rw [hrc, hinvc]; exact mem_rowSpan_sub _ _
    · by_cases hri : r = i
      · rw [hri, hinvi]; exact mem_rowSpan_two _ _
      · rw [← hnfSwapOp_row_of R hrc hri]; exact mem_rowSpan_row _

theorem rowSpan_reduceRowOp (R : IMat k) {i j : Fin k} (hij : i ≠ j) :
    rowSpan (reduceRowOp R i j) = rowSpan R := by
  have hrowj : (reduceRowOp R i j) j = R j - (R j i / R i i) • R i := by
    funext c'
    simp [reduceRowOp, Matrix.updateRow_self]
  have hrowr : ∀ r : Fin k, r ≠ j → (reduceRowOp R i j) r = R r := fun r h =>
    Matrix.updateRow_ne h
  refine rowSpan_congr_rows ?_ ?_
  · intro r
    by_cases hr : r = j
    · rw [hr, hrowj]
      exact Submodule.sub_mem _ (mem_rowSpan_row _) mem_rowSpan_smul_row
    · rw [hrowr r hr]; exact mem_rowSpan_row _
  · intro r
    by_cases hr : r = j
    · set S := reduceRowOp R i j with hSdef
      rw [hr]
      have hinv : R j = S j + (R j i / R i i) • S i := by
        rw [hrowj, ← hrowr i hij, sub_add_cancel]
      rw [hinv]
      exact Submodule.add_mem _ (mem_rowSpan_row _) mem_rowSpan_smul_row
    · rw [← hrowr r hr]; exact mem_rowSpan_row _

end Ops

section Invariants

variable {k : ℕ}

def TrailInj (c : ℕ) (R : IMat k) : Prop :=
  ∀ x : Fin k → ℚ, (∀ j : Fin k, c < (j : ℕ) → x j = 0) →
    (∀ r : Fin k, (r : ℕ) ≤ c → ∑ s, (R r s : ℚ) * x s = 0) → x = 0

def ZeroAbove (c : ℕ) (R : IMat k) : Prop :=
  ∀ r j : Fin k, (c : ℕ) ≤ (j : ℕ) → (r : ℕ) < (j : ℕ) → R r j = 0

def PosDiag (c : ℕ) (R : IMat k) : Prop :=
  ∀ r : Fin k, (c : ℕ) ≤ (r : ℕ) → 0 < R r r

def RedBelow (c : ℕ) (R : IMat k) : Prop :=
  ∀ i j : Fin k, (c : ℕ) ≤ (i : ℕ) → (i : ℕ) < (j : ℕ) → 0 ≤ R j i ∧ R j i < R i i

theorem trailInj_of_det_ne_zero (A : IMat k) (hA : A.det ≠ 0) : TrailInj (k - 1) A := by
  intro x _ hxvan
  have hdet : ((algebraMap ℤ ℚ).mapMatrix A).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact fun h => hA (Int.cast_injective h)
  have hmv : ((algebraMap ℤ ℚ).mapMatrix A).mulVec x = 0 := by
    funext r
    exact hxvan r (by have := Fin.isLt r; omega)
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hmv

theorem trailInj_hnfSwapOp (R : IMat k) {c i : Fin k} (hci : i ≠ c)
    (hle : (i : ℕ) ≤ (c : ℕ)) (hy : R i c ≠ 0)
    (hT : TrailInj (c : ℕ) R) : TrailInj (c : ℕ) (hnfSwapOp R c i) := by
  intro x hxsup hxvan
  have hunit : (R c c / (Int.gcd (R i c) (R c c) : ℤ)) * (bezC (R i c) (R c c)).2
      + (R i c / (Int.gcd (R i c) (R c c) : ℤ)) * (bezC (R i c) (R c c)).1 = 1 := hnf_unit hy
  have hSc : ∑ s, ((hnfSwapOp R c i) c s : ℚ) * x s
      = ((bezC (R i c) (R c c)).2 : ℚ) * (∑ s, (R c s : ℚ) * x s)
        + ((bezC (R i c) (R c c)).1 : ℚ) * (∑ s, (R i s : ℚ) * x s) := by
    have he : ∀ s : Fin k, ((hnfSwapOp R c i) c s : ℚ) * x s
        = (((bezC (R i c) (R c c)).2 * R c s + (bezC (R i c) (R c c)).1 * R i s : ℤ) : ℚ) * x s :=
      fun s => by rw [hnfSwapOp_c R hci s]
    rw [Finset.sum_congr rfl (fun s _ => he s)]
    simp only [Int.cast_add, add_mul, Finset.sum_add_distrib, Int.cast_mul, Finset.mul_sum,
      mul_assoc]
  have hSi : ∑ s, ((hnfSwapOp R c i) i s : ℚ) * x s
      = ((R c c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ) * (∑ s, (R i s : ℚ) * x s)
        - ((R i c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ) * (∑ s, (R c s : ℚ) * x s) := by
    have he : ∀ s : Fin k, ((hnfSwapOp R c i) i s : ℚ) * x s
        = (((R c c / (Int.gcd (R i c) (R c c) : ℤ)) * R i s
            - (R i c / (Int.gcd (R i c) (R c c) : ℤ)) * R c s : ℤ) : ℚ) * x s := fun s => by
      rw [hnfSwapOp_i R s]
    rw [Finset.sum_congr rfl (fun s _ => he s)]
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, Int.cast_mul, Finset.mul_sum,
      mul_assoc]
  have hunitQ : ((R c c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ)
        * ((bezC (R i c) (R c c)).2 : ℚ)
      + ((R i c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ) * ((bezC (R i c) (R c c)).1 : ℚ)
      = 1 := by
    exact mod_cast hunit
  have hvan : ∀ r : Fin k, (r : ℕ) ≤ (c : ℕ) → ∑ s, (R r s : ℚ) * x s = 0 := by
    intro r hr
    rcases eq_or_ne r c with hrc | hrc
    · have hq0 := hxvan r hr
      rw [hrc] at hq0
      rw [hSc] at hq0
      have hi0 := hxvan i hle
      rw [hSi] at hi0
      rw [hrc]
      linear_combination -(hunitQ * (∑ s, (R c s : ℚ) * x s))
        + ((R c c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ) * hq0
        - ((bezC (R i c) (R c c)).1 : ℚ) * hi0
    · rcases eq_or_ne r i with hri | hri
      · have hi0 := hxvan r hr
        rw [hri] at hi0
        rw [hSi] at hi0
        have hq0 := hxvan c (by omega)
        rw [hSc] at hq0
        rw [hri]
        linear_combination -(hunitQ * (∑ s, (R i s : ℚ) * x s))
          + ((R i c / (Int.gcd (R i c) (R c c) : ℤ) : ℤ) : ℚ) * hq0
          + ((bezC (R i c) (R c c)).2 : ℚ) * hi0
      · have hx := hxvan r hr
        rw [Finset.sum_congr rfl (fun s _ => by rw [hnfSwapOp_of R hrc hri])] at hx
        exact hx
  exact hT x hxsup hvan

theorem trailInj_signFixRow (n : ℕ) (c : Fin k) (R : IMat k) (hT : TrailInj n R) :
    TrailInj n (signFixRow c R) := by
  intro x hxsup hxvan
  refine hT x hxsup fun r hr => ?_
  have hx := hxvan r hr
  unfold signFixRow at hx
  split at hx
  · rcases eq_or_ne r c with hrc | hrc
    · rw [hrc] at hx ⊢
      have he : ∀ s : Fin k, ((R.updateRow c (fun j => -R c j)) c s : ℚ) * x s
          = -((R c s : ℚ) * x s) := by
        intro s; simp
      rw [Finset.sum_congr rfl (fun s _ => he s), Finset.sum_neg_distrib] at hx
      simpa using hx
    · have he : ∀ s : Fin k, ((R.updateRow c (fun j => -R c j)) r s : ℚ) * x s
          = (R r s : ℚ) * x s := by
        intro s; rw [Matrix.updateRow_ne hrc]
      rw [Finset.sum_congr rfl (fun s _ => he s)] at hx
      exact hx
  · exact hx

theorem trailInj_step (R : IMat k) {c : ℕ} (hc : c < k)
    (hT : TrailInj c R) (hz : ∀ i : Fin k, (i : ℕ) < c → R i ⟨c, hc⟩ = 0)
    (hp : R ⟨c, hc⟩ ⟨c, hc⟩ ≠ 0) : TrailInj (c - 1) R := by
  rcases Nat.eq_zero_or_pos c with hc0 | hc0
  · subst hc0
    rw [Nat.zero_sub]
    exact hT
  · intro x hxsup hxvan
    have hxc : x ⟨c, hc⟩ = 0 := by
      have h1 := hxsup ⟨c, hc⟩ (by have : ((⟨c, hc⟩ : Fin k) : ℕ) = c := rfl; omega)
      exact h1
    have key : ∀ (r : Fin k) (T : ℚ),
        ∑ s, (R r s : ℚ) * (x s + (if s = ⟨c, hc⟩ then T else 0))
          = (∑ s, (R r s : ℚ) * x s) + (R r ⟨c, hc⟩ : ℚ) * T := by
      intro r T
      simp only [mul_add, Finset.sum_add_distrib]
      have h1 : ∑ s, (R r s : ℚ) * (if s = ⟨c, hc⟩ then T else 0) = (R r ⟨c, hc⟩ : ℚ) * T := by
        rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin k)]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h1]
    have hsup : ∀ j : Fin k, c < (j : ℕ) →
        (x j + (if j = ⟨c, hc⟩ then -((∑ s, (R ⟨c, hc⟩ s : ℚ) * x s)
          / ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)) else 0)) = 0 := by
      intro j hj
      have hne : j ≠ ⟨c, hc⟩ := by
        intro h
        have h2 : (j : ℕ) = c := congrArg Fin.val h
        omega
      rw [if_neg hne, add_zero]
      exact hxsup j (by omega)
    have hvan : ∀ r : Fin k, (r : ℕ) ≤ c →
        ∑ s, (R r s : ℚ) * (x s + (if s = ⟨c, hc⟩ then -((∑ s', (R ⟨c, hc⟩ s' : ℚ) * x s')
          / ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)) else 0)) = 0 := by
      intro r hr
      rw [key]
      rcases Nat.lt_or_ge (r : ℕ) c with hlt | hge
      · have h1 : ∑ s, (R r s : ℚ) * x s = 0 := hxvan r (by omega)
        have h2 : (R r ⟨c, hc⟩ : ℚ) = 0 := by exact_mod_cast hz r hlt
        rw [h1, h2, zero_mul, zero_add]
      · have hreq : r = ⟨c, hc⟩ := by
          refine Fin.ext ?_
          have : ((⟨c, hc⟩ : Fin k) : ℕ) = c := rfl
          omega
        subst hreq
        have hA : ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp
        have hcancel : ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)
            * (-((∑ s', (R ⟨c, hc⟩ s' : ℚ) * x s')
              / ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)))
            = -(∑ s', (R ⟨c, hc⟩ s' : ℚ) * x s') := by
          field_simp
        rw [hcancel]
        ring
    have hxt := hT (fun s => x s + (if s = ⟨c, hc⟩ then -((∑ s', (R ⟨c, hc⟩ s' : ℚ) * x s')
      / ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)) else 0)) hsup hvan
    funext j
    rcases eq_or_ne j ⟨c, hc⟩ with hj | hj
    · rw [hj, hxc]
      rfl
    · have hxj : x j = (x j + (if j = ⟨c, hc⟩ then -((∑ s, (R ⟨c, hc⟩ s : ℚ) * x s)
          / ((R ⟨c, hc⟩ ⟨c, hc⟩ : ℤ) : ℚ)) else 0)) := by
        rw [if_neg hj, add_zero]
      rw [hxj, congrFun hxt j]

theorem trailInj_pivot_ne_zero (R : IMat k) {c : ℕ} (hc : c < k) (hT : TrailInj c R)
    (hz : ∀ i : Fin k, (i : ℕ) < c → R i ⟨c, hc⟩ = 0)
    (hp : R ⟨c, hc⟩ ⟨c, hc⟩ = 0) : False := by
  have hvan : ∀ r : Fin k, (r : ℕ) ≤ c →
      ∑ s, (R r s : ℚ) * (if s = ⟨c, hc⟩ then (1 : ℚ) else 0) = 0 := by
    intro r hr
    rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin k)]
    · rcases Nat.lt_or_ge (r : ℕ) c with hlt | hge
      · rw [hz r hlt]
        simp
      · have hreq : r = ⟨c, hc⟩ := by
          refine Fin.ext ?_
          have : ((⟨c, hc⟩ : Fin k) : ℕ) = c := rfl
          omega
        subst hreq
        rw [hp]
        simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := hT (fun s => if s = ⟨c, hc⟩ then (1 : ℚ) else 0) (fun j hj => by
    have hne : j ≠ ⟨c, hc⟩ := by
      intro h
      have h2 : (j : ℕ) = c := congrArg Fin.val h
      omega
    show (if j = ⟨c, hc⟩ then (1 : ℚ) else 0) = 0
    rw [if_neg hne]) hvan
  have h1 := congrFun h ⟨c, hc⟩
  rw [if_pos rfl] at h1
  exact zero_ne_one h1.symm

theorem zeroAbove_hnfSwapOp (R : IMat k) {c i : Fin k} (hlt : (i : ℕ) < (c : ℕ))
    (hZ : ZeroAbove ((c : ℕ) + 1) R) : ZeroAbove ((c : ℕ) + 1) (hnfSwapOp R c i) := by
  have hci : i ≠ c := fun h => absurd (congrArg Fin.val h) (by omega)
  intro r j hj hrj
  rcases eq_or_ne r c with hrc | hrc
  · rw [hrc, hnfSwapOp_c R hci j, hZ (r := c) (j := j) (by omega) (by omega),
      hZ (r := i) (j := j) (by omega) (by omega), mul_zero, mul_zero, add_zero]
  · rcases eq_or_ne r i with hri | hri
    · rw [hri, hnfSwapOp_i R j, hZ (r := i) (j := j) (by omega) (by omega),
        hZ (r := c) (j := j) (by omega) (by omega), mul_zero, mul_zero, sub_zero]
    · rw [hnfSwapOp_of R hrc hri]
      exact hZ r j hj hrj

theorem zeroAbove_signFixRow (c : Fin k) (R : IMat k) (hZ : ZeroAbove ((c : ℕ) + 1) R) :
    ZeroAbove ((c : ℕ) + 1) (signFixRow c R) := by
  intro r j hj hrj
  unfold signFixRow
  split
  · rcases eq_or_ne r c with hrc | hrc
    · rw [hrc, Matrix.updateRow_self, hZ c j (by omega) (by omega), neg_zero]
    · rw [Matrix.updateRow_ne hrc]
      exact hZ r j hj hrj
  · exact hZ r j hj hrj

theorem zeroAbove_reduceRowOp (R : IMat k) {i j : Fin k} (hij : (i : ℕ) < (j : ℕ))
    (hZ : ZeroAbove 0 R) : ZeroAbove 0 (reduceRowOp R i j) := by
  intro r j' hj' hrj'
  rcases eq_or_ne r j with hrj | hrj
  · rw [hrj, reduceRowOp, Matrix.updateRow_self]
    rw [hZ j j' (by omega) (by omega), hZ i j' (by omega) (by omega), mul_zero, sub_zero]
  · rw [reduceRowOp, Matrix.updateRow_ne hrj]
    exact hZ r j' hj' hrj'

end Invariants

section Pipeline

variable {k : ℕ}

def sweepStep (c : Fin k) (R : IMat k) (i : Fin k) : IMat k :=
  if R i c ≠ 0 then hnfSwapOp R c i else R

def stageSweep (c : Fin k) (R : IMat k) : IMat k :=
  ((List.finRange k).filter (fun i : Fin k => decide ((i : ℕ) < (c : ℕ)))).foldl (sweepStep c) R

def stage (c : Fin k) (R : IMat k) : IMat k :=
  signFixRow c (stageSweep c R)

def triAux : ℕ → IMat k → IMat k
  | 0, R => R
  | t + 1, R =>
    if h : k ≤ t then R else stage ⟨k - 1 - t, by have := h; omega⟩ (triAux t R)

def triangularize (A : IMat k) : IMat k := triAux k Aᵀ

theorem sweepStep_zero (c : Fin k) (R : IMat k) (i : Fin k) :
    (sweepStep c R i) i c = 0 := by
  unfold sweepStep
  split
  · exact hnfSwapOp_zero R
  · rename_i h
    exact not_not.mp h

theorem sweepStep_row (c : Fin k) (R : IMat k) (i r : Fin k) (hr : r ≠ c) (hri : r ≠ i) :
    (sweepStep c R i) r = R r := by
  unfold sweepStep
  split
  · exact hnfSwapOp_row_of R hr hri
  · rfl

theorem rowSpan_sweepStep (c : Fin k) (R : IMat k) (i : Fin k) (hlt : (i : ℕ) < (c : ℕ)) :
    rowSpan (sweepStep c R i) = rowSpan R := by
  unfold sweepStep
  split
  · exact rowSpan_hnfSwapOp R hlt (by assumption)
  · rfl

theorem trailInj_sweepStep (c : Fin k) (R : IMat k) (i : Fin k)
    (hlt : (i : ℕ) < (c : ℕ)) (hT : TrailInj (c : ℕ) R) :
    TrailInj (c : ℕ) (sweepStep c R i) := by
  unfold sweepStep
  split
  · exact trailInj_hnfSwapOp R (fun h => absurd (congrArg Fin.val h) (by omega))
      (by omega) (by assumption) hT
  · exact hT

theorem zeroAbove_sweepStep (c : Fin k) (R : IMat k) (i : Fin k) (hlt : (i : ℕ) < (c : ℕ))
    (hZ : ZeroAbove ((c : ℕ) + 1) R) : ZeroAbove ((c : ℕ) + 1) (sweepStep c R i) := by
  unfold sweepStep
  split
  · exact zeroAbove_hnfSwapOp R hlt hZ
  · exact hZ

theorem sweep_fold (c : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ i ∈ l, (i : ℕ) < (c : ℕ)) (hnl : l.Nodup) (hT : TrailInj (c : ℕ) R) :
    TrailInj (c : ℕ) (l.foldl (sweepStep c) R)
    ∧ rowSpan (l.foldl (sweepStep c) R) = rowSpan R
    ∧ (∀ i ∈ l, (l.foldl (sweepStep c) R) i c = 0)
    ∧ (∀ r : Fin k, (∀ i ∈ l, i ≠ r) → r ≠ c → (l.foldl (sweepStep c) R) r = R r) := by
  induction l generalizing R with
  | nil =>
    refine ⟨hT, rfl, fun i => by simp, fun r _ _ => rfl⟩
  | cons i₀ rest ih =>
    have hlt₀ : (i₀ : ℕ) < (c : ℕ) := hl i₀ (List.mem_cons_self ..)
    have hrest : ∀ i ∈ rest, (i : ℕ) < (c : ℕ) := fun i hi => hl i (List.mem_cons_of_mem _ hi)
    have hnlrest : rest.Nodup := (List.nodup_cons.mp hnl).2
    have hb := ih (sweepStep c R i₀) hrest hnlrest
      (trailInj_sweepStep c R i₀ hlt₀ hT)
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    refine ⟨hb1, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, hb2, rowSpan_sweepStep c R i₀ hlt₀]
    · intro i hi
      rcases List.mem_cons.mp hi with heq | hirest
      · have hi₀c : i₀ ≠ c := fun h => absurd (congrArg Fin.val h) (by omega)
        rw [List.foldl_cons, heq,
          hb4 i₀ (fun j hj h => (List.nodup_cons.mp hnl).1 (h ▸ hj)) hi₀c, sweepStep_zero]
      · exact hb3 i hirest
    · intro r hr hrne
      have hrrest : ∀ i ∈ rest, i ≠ r := fun i hi => hr i (List.mem_cons_of_mem _ hi)
      rw [List.foldl_cons, hb4 r hrrest hrne, sweepStep_row c R i₀ r hrne
        ((hr i₀ (by simp)).symm)]

theorem sweep_fold_zeroAbove (c : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ i ∈ l, (i : ℕ) < (c : ℕ)) (hZ : ZeroAbove ((c : ℕ) + 1) R) :
    ZeroAbove ((c : ℕ) + 1) (l.foldl (sweepStep c) R) := by
  induction l generalizing R with
  | nil => exact hZ
  | cons i₀ rest ih =>
    have hlt₀ : (i₀ : ℕ) < (c : ℕ) := hl i₀ (List.mem_cons_self ..)
    exact ih (sweepStep c R i₀) (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      (zeroAbove_sweepStep c R i₀ hlt₀ hZ)

theorem mem_stageSweep_list {c i : Fin k} (hlt : (i : ℕ) < (c : ℕ)) :
    i ∈ (List.finRange k).filter (fun i : Fin k => decide ((i : ℕ) < (c : ℕ))) :=
  List.mem_filter.mpr ⟨List.mem_finRange i, by simp [hlt]⟩

theorem stageSweep_zeros (c : Fin k) (R : IMat k) (hT : TrailInj (c : ℕ) R) :
    ∀ i : Fin k, (i : ℕ) < (c : ℕ) → (stageSweep c R) i c = 0 := by
  have hb := sweep_fold c ((List.finRange k).filter (fun i : Fin k =>
    decide ((i : ℕ) < (c : ℕ)))) R
    (fun i hi => by simpa using (List.mem_filter.mp hi).2)
    (List.Nodup.filter _ (List.nodup_finRange k)) hT
  intro i hi
  exact hb.2.2.1 i (mem_stageSweep_list hi)

theorem stageSweep_zeroAbove (c : Fin k) (R : IMat k) (hZ : ZeroAbove ((c : ℕ) + 1) R) :
    ZeroAbove ((c : ℕ) + 1) (stageSweep c R) :=
  sweep_fold_zeroAbove c ((List.finRange k).filter (fun i : Fin k =>
    decide ((i : ℕ) < (c : ℕ)))) R
    (fun i hi => by simpa using (List.mem_filter.mp hi).2) hZ

theorem stage_pivot_pos (c : Fin k) (R : IMat k) (hT : TrailInj (c : ℕ) R) :
    0 < (stage c R) c c := by
  have hbundle := sweep_fold c ((List.finRange k).filter (fun i : Fin k =>
    decide ((i : ℕ) < (c : ℕ)))) R
    (fun i hi => by simpa using (List.mem_filter.mp hi).2)
    (List.Nodup.filter _ (List.nodup_finRange k)) hT
  have hzeros := stageSweep_zeros c R hT
  have hne : (stageSweep c R) c c ≠ 0 := by
    intro h
    exact trailInj_pivot_ne_zero (stageSweep c R) (Fin.isLt c) hbundle.1
      (fun i hi => hzeros i hi) h
  unfold stage signFixRow
  split
  · rename_i hn
    rw [Matrix.updateRow_self]
    exact neg_pos.mpr hn
  · rcases Int.lt_trichotomy ((stageSweep c R) c c) 0 with h | h | h
    · exact absurd h (by assumption)
    · exact absurd h hne
    · exact h

theorem sweep_fold_rowSpan (c : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ i ∈ l, (i : ℕ) < (c : ℕ)) :
    rowSpan (l.foldl (sweepStep c) R) = rowSpan R := by
  induction l generalizing R with
  | nil => rfl
  | cons i₀ rest ih =>
    rw [List.foldl_cons,
      ih (sweepStep c R i₀) (fun i hi => hl i (List.mem_cons_of_mem _ hi)),
      rowSpan_sweepStep c R i₀ (hl i₀ (List.mem_cons_self ..))]

theorem stageSweep_rowSpan (c : Fin k) (R : IMat k) :
    rowSpan (stageSweep c R) = rowSpan R :=
  sweep_fold_rowSpan c ((List.finRange k).filter (fun i : Fin k =>
    decide ((i : ℕ) < (c : ℕ)))) R
    (fun i hi => by simpa using (List.mem_filter.mp hi).2)

theorem stage_spec (c : Fin k) (R : IMat k) (hT : TrailInj (c : ℕ) R)
    (hZ : ZeroAbove ((c : ℕ) + 1) R) (hP : PosDiag ((c : ℕ) + 1) R) :
    TrailInj ((c : ℕ) - 1) (stage c R) ∧ ZeroAbove (c : ℕ) (stage c R)
    ∧ PosDiag (c : ℕ) (stage c R) ∧ rowSpan (stage c R) = rowSpan R := by
  have hb := sweep_fold c ((List.finRange k).filter (fun i : Fin k =>
    decide ((i : ℕ) < (c : ℕ)))) R
    (fun i hi => by simpa using (List.mem_filter.mp hi).2)
    (List.Nodup.filter _ (List.nodup_finRange k)) hT
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hzeros := stageSweep_zeros c R hT
  have hne : (stageSweep c R) c c ≠ 0 := by
    intro h
    exact trailInj_pivot_ne_zero (stageSweep c R) (Fin.isLt c) hb1
      (fun i hi => hzeros i hi) h
  have hrowsof : ∀ r : Fin k, (c : ℕ) < (r : ℕ) → (stageSweep c R) r = R r := by
    intro r hr
    refine hb4 r (fun i hi => ?_) (fun h => ?_)
    · intro hc
      have hmem := (List.mem_filter.mp hi).2
      simp only [decide_eq_true_eq] at hmem
      omega
    · have hval := congrArg Fin.val h
      omega
  have hstep := trailInj_step (stageSweep c R) (Fin.isLt c) hb1
    (fun i hi => hzeros i hi) hne
  refine ⟨trailInj_signFixRow ((c : ℕ) - 1) c _ hstep, ?_, ?_, ?_⟩
  · intro r j hj hrj
    rcases Nat.eq_or_lt_of_le hj with jeq | jlt
    · have hjc : j = c := Fin.ext jeq.symm
      have hrj' : (r : ℕ) < (c : ℕ) := by omega
      unfold stage signFixRow
      split
      · rcases eq_or_ne r c with hreq | hreq
        · exfalso; omega
        · rw [Matrix.updateRow_ne hreq, hjc, hzeros r hrj']
      · rw [hjc, hzeros r hrj']
    · unfold stage signFixRow
      have hZ2 : ZeroAbove ((c : ℕ) + 1) (signFixRow c (stageSweep c R)) :=
        zeroAbove_signFixRow c _ (stageSweep_zeroAbove c R hZ)
      exact hZ2 r j (by omega) hrj
  · intro r hr
    rcases Nat.eq_or_lt_of_le hr with hreq | hrlt
    · have hrc : r = c := Fin.ext hreq.symm
      rw [hrc]
      exact stage_pivot_pos c R hT
    · unfold stage signFixRow
      split
      · rcases eq_or_ne r c with hreq | hreq
        · exfalso; omega
        · rw [Matrix.updateRow_ne hreq, hrowsof r (by omega)]
          exact hP r (by omega)
      · rw [hrowsof r (by omega)]
        exact hP r (by omega)
  · rw [stage, rowSpan_signFixRow, stageSweep_rowSpan]

theorem triAux_spec (A : IMat k) (hA : A.det ≠ 0) : ∀ t : ℕ, t ≤ k →
    TrailInj (k - 1 - t) (triAux t A) ∧ ZeroAbove (k - t) (triAux t A)
    ∧ PosDiag (k - t) (triAux t A) ∧ rowSpan (triAux t A) = rowSpan A := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨trailInj_of_det_ne_zero A hA, ?_, ?_, rfl⟩
    · intro r j hj hrj
      exact absurd hj (by have := Fin.isLt j; omega)
    · intro r hr
      exact absurd hr (by have := Fin.isLt r; omega)
  | succ t ih =>
    intro ht
    have hltk : t < k := by omega
    have hc : (k - 1 - t : ℕ) < k := by omega
    have hb := ih (by omega)
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    rw [show k - t = (k - 1 - t : ℕ) + 1 from by omega] at hb2 hb3
    have hs := stage_spec (⟨k - 1 - t, hc⟩ : Fin k) (triAux t A) hb1 hb2 hb3
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    have hcoe : (((⟨k - 1 - t, hc⟩ : Fin k) : ℕ)) = k - 1 - t := rfl
    rw [hcoe] at hs1 hs2 hs3
    unfold triAux at ⊢
    rw [dif_neg (by omega)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show k - 1 - (t + 1) = (k - 1 - t) - 1 from by omega]
      exact hs1
    · rw [show k - (t + 1) = (k - 1 - t) from by omega]
      exact hs2
    · rw [show k - (t + 1) = (k - 1 - t) from by omega]
      exact hs3
    · rw [hs4]
      exact hb4

theorem triangularize_zeroAbove (A : IMat k) (hA : A.det ≠ 0) :
    ZeroAbove 0 (triangularize A) := by
  have hT : Aᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hb := triAux_spec Aᵀ hT k (by omega)
  rw [triangularize, ← Nat.sub_self k]
  exact hb.2.1

theorem triangularize_posDiag (A : IMat k) (hA : A.det ≠ 0) :
    PosDiag 0 (triangularize A) := by
  have hT : Aᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hb := triAux_spec Aᵀ hT k (by omega)
  rw [triangularize, ← Nat.sub_self k]
  exact hb.2.2.1

theorem rowSpan_triangularize (A : IMat k) (hA : A.det ≠ 0) :
    rowSpan (triangularize A) = rowSpan Aᵀ :=
  (triAux_spec Aᵀ (by rwa [Matrix.det_transpose]) k (by omega)).2.2.2

end Pipeline

section Reduction

variable {k : ℕ}

def redStep (i : Fin k) (R : IMat k) (j : Fin k) : IMat k :=
  if (i : ℕ) < (j : ℕ) then reduceRowOp R i j else R

def redSweep (i : Fin k) (R : IMat k) : IMat k :=
  ((List.finRange k).filter (fun j : Fin k => decide ((i : ℕ) < (j : ℕ)))).foldl (redStep i) R

def redAux : ℕ → IMat k → IMat k
  | 0, R => R
  | t + 1, R =>
    if h : k ≤ t then R else redSweep ⟨k - 1 - t, by have := h; omega⟩ (redAux t R)

def reduceOffDiagonal (R : IMat k) : IMat k := redAux k R

theorem redStep_entry (i : Fin k) (R : IMat k) (j : Fin k) (hij : (i : ℕ) < (j : ℕ))
    (hpos : 0 < R i i) :
    (redStep i R j) j i = R j i % R i i ∧ 0 ≤ (redStep i R j) j i ∧
      (redStep i R j) j i < R i i := by
  have hd : R i i ≠ 0 := ne_of_gt hpos
  unfold redStep
  rw [if_pos hij, reduceRowOp, Matrix.updateRow_self]
  have hmd := Int.mul_ediv_add_emod (R j i) (R i i)
  rw [mul_comm (R i i) (R j i / R i i)] at hmd
  constructor
  · linarith [hmd]
  · constructor
    · have hem := Int.emod_nonneg (R j i) hd
      linarith [hmd]
    · have hlt := Int.emod_lt (R j i) hd
      rw [Int.natAbs_of_nonneg (by linarith : (0 : ℤ) ≤ R i i)] at hlt
      linarith [hmd]

theorem redStep_row (i : Fin k) (R : IMat k) (j r : Fin k) (hrj : r ≠ j) :
    (redStep i R j) r = R r := by
  unfold redStep
  split
  · exact Matrix.updateRow_ne hrj
  · rfl

theorem redStep_entry_high (i : Fin k) (R : IMat k) (j r : Fin k) (i' : Fin k)
    (hii' : (i : ℕ) < (i' : ℕ)) (hZ : ZeroAbove 0 R) :
    (redStep i R j) r i' = R r i' := by
  unfold redStep
  split
  · by_cases hrj : r = j
    · subst hrj
      rw [reduceRowOp, Matrix.updateRow_self, hZ i i' (by omega) (by omega), mul_zero, sub_zero]
    · rw [reduceRowOp, Matrix.updateRow_ne hrj]
  · rfl

theorem posDiag_redStep (i : Fin k) (R : IMat k) (j : Fin k)
    (hpos : PosDiag 0 R) (hZ : ZeroAbove 0 R) : PosDiag 0 (redStep i R j) := by
  intro r hr
  by_cases hdec : (i : ℕ) < (j : ℕ)
  · rw [redStep, if_pos hdec]
    rcases eq_or_ne r j with hrj | hrj
    · rw [hrj, reduceRowOp, Matrix.updateRow_self, hZ i j (by omega) (by omega), mul_zero,
        sub_zero]
      exact hpos j (by omega)
    · unfold reduceRowOp
      rw [Matrix.updateRow_ne hrj]
      exact hpos r hr
  · rw [redStep, if_neg hdec]
    exact hpos r hr

theorem zeroAbove_redStep (i : Fin k) (R : IMat k) (j : Fin k) (hij : (i : ℕ) < (j : ℕ))
    (hZ : ZeroAbove 0 R) : ZeroAbove 0 (redStep i R j) := by
  intro r j' hj' hrj'
  by_cases hdec : (i : ℕ) < (j : ℕ)
  · rw [redStep, if_pos hdec]
    exact zeroAbove_reduceRowOp R hij hZ r j' hj' hrj'
  · rw [redStep, if_neg hdec]
    exact hZ r j' hj' hrj'

theorem rowSpan_redStep (i : Fin k) (R : IMat k) (j : Fin k) (hij : (i : ℕ) < (j : ℕ)) :
    rowSpan (redStep i R j) = rowSpan R := by
  rw [redStep, if_pos hij]
  exact rowSpan_reduceRowOp R (fun h => absurd (congrArg Fin.val h) (by omega))

theorem redSweep_fold (i : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ j ∈ l, (i : ℕ) < (j : ℕ)) (hnl : l.Nodup) (hpos : PosDiag 0 R)
    (hZ : ZeroAbove 0 R) :
    PosDiag 0 (l.foldl (redStep i) R) ∧ ZeroAbove 0 (l.foldl (redStep i) R)
    ∧ rowSpan (l.foldl (redStep i) R) = rowSpan R
    ∧ (∀ j ∈ l, (i : ℕ) < (j : ℕ) → 0 ≤ (l.foldl (redStep i) R) j i
        ∧ (l.foldl (redStep i) R) j i < R i i)
    ∧ (∀ r : Fin k, (∀ j ∈ l, j ≠ r) → (l.foldl (redStep i) R) r = R r) := by
  induction l generalizing R with
  | nil => exact ⟨hpos, hZ, rfl, fun j hj => absurd hj (by simp), fun r _ => rfl⟩
  | cons j₀ rest ih =>
    have hlt₀ : (i : ℕ) < (j₀ : ℕ) := hl j₀ (List.mem_cons_self ..)
    have hrest : ∀ j ∈ rest, (i : ℕ) < (j : ℕ) := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hnlrest : rest.Nodup := (List.nodup_cons.mp hnl).2
    have hbundle := ih (redStep i R j₀) hrest hnlrest
      (posDiag_redStep i R j₀ hpos hZ) (zeroAbove_redStep i R j₀ hlt₀ hZ)
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbundle
    have hdiagi : (redStep i R j₀) i i = R i i := by
      rw [redStep_row i R j₀ i (by omega)]
    have hb4' : ∀ j ∈ rest, (i : ℕ) < (j : ℕ) →
        0 ≤ (List.foldl (redStep i) (redStep i R j₀) rest) j i
        ∧ (List.foldl (redStep i) (redStep i R j₀) rest) j i < R i i := by
      intro j hj hjlt
      have h := hb4 j hj hjlt
      rw [hdiagi] at h
      exact h
    refine ⟨hb1, hb2, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, hb3, rowSpan_redStep i R j₀ hlt₀]
    · intro j hjmem hjlt
      rcases List.mem_cons.mp hjmem with heq | hirest
      · have hj₀ : j = j₀ := heq
        rw [hj₀, List.foldl_cons,
          hb5 j₀ (fun x hx h => (List.nodup_cons.mp hnl).1 (h ▸ hx))]
        exact (redStep_entry i R j₀ hlt₀ (hpos i (by omega))).2
      · rw [List.foldl_cons]
        exact hb4' j hirest hjlt
    · intro r hr
      have hrrest : ∀ j ∈ rest, j ≠ r := fun j hj => hr j (List.mem_cons_of_mem _ hj)
      rw [List.foldl_cons, hb5 r hrrest, redStep_row i R j₀ r
        ((hr j₀ (by simp)).symm)]

theorem redSweep_fold_high (i : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ j ∈ l, (i : ℕ) < (j : ℕ)) (hZ : ZeroAbove 0 R) (i' : Fin k)
    (hii' : (i : ℕ) < (i' : ℕ)) :
    ∀ r : Fin k, (l.foldl (redStep i) R) r i' = R r i' := by
  induction l generalizing R with
  | nil => intro r; rfl
  | cons j₀ rest ih =>
    intro r
    rw [List.foldl_cons,
      ih (redStep i R j₀) (fun j hj => hl j (List.mem_cons_of_mem _ hj))
        (zeroAbove_redStep i R j₀ (hl j₀ (List.mem_cons_self ..)) hZ) r]
    exact redStep_entry_high i R j₀ r i' hii' hZ

theorem mem_redSweep_list {i j : Fin k} (hlt : (i : ℕ) < (j : ℕ)) :
    j ∈ (List.finRange k).filter (fun j : Fin k => decide ((i : ℕ) < (j : ℕ))) :=
  List.mem_filter.mpr ⟨List.mem_finRange j, by simp [hlt]⟩

theorem redSweep_spec (i : Fin k) (R : IMat k) (hpos : PosDiag 0 R) (hZ : ZeroAbove 0 R)
    (hR : RedBelow ((i : ℕ) + 1) R) :
    PosDiag 0 (redSweep i R) ∧ ZeroAbove 0 (redSweep i R)
    ∧ rowSpan (redSweep i R) = rowSpan R ∧ RedBelow (i : ℕ) (redSweep i R) := by
  have hb := redSweep_fold i ((List.finRange k).filter (fun j : Fin k =>
    decide ((i : ℕ) < (j : ℕ)))) R
    (fun j hj => by simpa using (List.mem_filter.mp hj).2)
    (List.Nodup.filter _ (List.nodup_finRange k)) hpos hZ
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  refine ⟨hb1, hb2, hb3, ?_⟩
  intro i' j hi' hi'j
  rcases Nat.lt_or_ge (i' : ℕ) ((i : ℕ) + 1) with hlt | hge
  · have hieq : i' = i := Fin.ext (by omega)
    rw [hieq] at hi'j ⊢
    have hdiagi : (redSweep i R) i i = R i i := by
      have hrowi := hb5 i (fun j hj => by
        have hmem := (List.mem_filter.mp hj).2
        simp only [decide_eq_true_eq] at hmem
        omega)
      exact congrFun hrowi i
    constructor
    · exact (hb4 j (mem_redSweep_list hi'j) hi'j).1
    · rw [hdiagi]
      exact (hb4 j (mem_redSweep_list hi'j) hi'j).2
  · have h1 : (redSweep i R) j i' = R j i' :=
      redSweep_fold_high i _ R
        (fun j hj => by simpa using (List.mem_filter.mp hj).2) hZ i' (by omega) j
    have h2 : (redSweep i R) i' i' = R i' i' :=
      redSweep_fold_high i _ R
        (fun j hj => by simpa using (List.mem_filter.mp hj).2) hZ i' (by omega) i'
    have hold := hR i' j (by omega) hi'j
    constructor
    · rw [h1]; exact hold.1
    · rw [h1, h2]; exact hold.2

theorem redAux_spec (R : IMat k) (hpos : PosDiag 0 R) (hZ : ZeroAbove 0 R) :
    ∀ t : ℕ, t ≤ k → PosDiag 0 (redAux t R) ∧ ZeroAbove 0 (redAux t R)
    ∧ rowSpan (redAux t R) = rowSpan R ∧ RedBelow (k - t) (redAux t R) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨hpos, hZ, rfl, ?_⟩
    intro i j hi hj
    exact absurd hi (by have := Fin.isLt i; omega)
  | succ t ih =>
    intro ht
    have hltk : t < k := by omega
    have hc : (k - 1 - t : ℕ) < k := by omega
    have hbundle := ih (by omega)
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbundle
    rw [show (k - t : ℕ) = (k - 1 - t : ℕ) + 1 from by omega] at hb4
    have hs := redSweep_spec (⟨k - 1 - t, hc⟩ : Fin k) (redAux t R) hb1 hb2 hb4
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    have hcoe : (((⟨k - 1 - t, hc⟩ : Fin k) : ℕ)) = k - 1 - t := rfl
    rw [hcoe] at hs4
    unfold redAux at ⊢
    rw [dif_neg (by omega)]
    rw [show k - (t + 1) = k - 1 - t from by omega]
    exact ⟨hs1, hs2, hs3.trans hb3, hs4⟩

theorem reduceOffDiagonal_spec (R : IMat k) (hpos : PosDiag 0 R) (hZ : ZeroAbove 0 R) :
    PosDiag 0 (reduceOffDiagonal R) ∧ ZeroAbove 0 (reduceOffDiagonal R)
    ∧ rowSpan (reduceOffDiagonal R) = rowSpan R ∧ RedBelow 0 (reduceOffDiagonal R) := by
  have hb := redAux_spec R hpos hZ k (by omega)
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  rw [Nat.sub_self] at hb4
  exact ⟨hb1, hb2, hb3, hb4⟩

end Reduction

section Assembly

variable {k : ℕ}

def classicalCanonicalize (A : IMat k) : IMat k :=
  (reduceOffDiagonal (triangularize A))ᵀ

theorem classicalCanonicalize_isCanonical (A : IMat k) (hA : A.det ≠ 0) :
    IsCanonicalHNF (classicalCanonicalize A) := by
  obtain ⟨hpos, hZ, _, hred⟩ :=
    reduceOffDiagonal_spec (triangularize A) (triangularize_posDiag A hA)
      (triangularize_zeroAbove A hA)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj
    have h0 := hZ j i (Nat.zero_le _) hj
    unfold classicalCanonicalize
    simp only [Matrix.transpose_apply]
    rw [h0]
  · intro i
    exact hpos i (Nat.zero_le _)
  · intro i j hij
    have hr := hred i j (Nat.zero_le _) hij
    unfold classicalCanonicalize
    simp only [Matrix.transpose_apply]
    exact hr

theorem colSpan_classicalCanonicalize (A : IMat k) (hA : A.det ≠ 0) :
    colSpan (classicalCanonicalize A) = colSpan A := by
  rw [classicalCanonicalize, colSpan_transpose,
    (reduceOffDiagonal_spec (triangularize A) (triangularize_posDiag A hA)
      (triangularize_zeroAbove A hA)).2.2.1,
    rowSpan_triangularize A hA, ← rowSpan_transpose]

end Assembly

section Uniqueness

variable {k : ℕ}

theorem Fin.downward_ind {k : ℕ} {P : Fin k → Prop}
    (step : ∀ i : Fin k, (∀ j : Fin k, (i : ℕ) < (j : ℕ) → P j) → P i) : ∀ i : Fin k, P i := by
  intro i
  have key : ∀ n : ℕ, ∀ i : Fin k, k - 1 - (i : ℕ) ≤ n → P i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      refine step i (fun j hij => absurd hij ?_)
      have := Fin.isLt j
      omega
    | succ n ih =>
      intro i hi
      refine step i (fun j hij => ih j ?_)
      have := Fin.isLt j
      omega
  exact key (k - 1 - (i : ℕ)) i (Nat.le_refl _)

theorem mem_colSpan_column (A : IMat k) (j : Fin k) : (fun i => A i j) ∈ colSpan A := by
  exact Submodule.subset_span (Set.mem_range_self j)

theorem canonical_mulVec_eq_zero {H : IMat k} (hH : IsCanonicalHNF H) {w : Fin k → ℤ}
    (hw : H.mulVec w = 0) : w = 0 := by
  have hzero : ∀ i : Fin k, ∀ j : Fin k, (i : ℕ) ≤ (j : ℕ) → w j = 0 := by
    refine Fin.downward_ind (fun i ih => ?_)
    intro j hij
    rcases Nat.eq_or_lt_of_le hij with jeq | jlt
    · have hji : j = i := Fin.ext (by omega)
      rw [hji]
      have hrow : ∑ s, H i s * w s = 0 := congrFun hw i
      rw [Finset.sum_eq_single i (fun b _ hbi => by
        rcases Nat.lt_trichotomy (b : ℕ) (i : ℕ) with h | h | h
        · rw [hH.1 i b h, zero_mul]
        · exact absurd (Fin.ext h) hbi
        · rw [(ih b (by omega)) b (Nat.le_refl _), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h)] at hrow
      have hd := (Int.mul_eq_zero.mp hrow).resolve_left (ne_of_gt (hH.2.1 i))
      exact hd
    · exact (ih j jlt) j (Nat.le_refl _)
  funext j
  exact hzero j j (Nat.le_refl _)

theorem canonical_mulVec_injective {H : IMat k} (hH : IsCanonicalHNF H) :
    Function.Injective H.mulVec := by
  intro u v huv
  have hz : H.mulVec (u - v) = 0 := by
    funext i
    show ∑ s, H i s * (u - v) s = (0 : Fin k → ℤ) i
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun s _ => mul_sub (H i s) (u s) (v s)),
      Finset.sum_sub_distrib, sub_eq_zero]
    exact congrFun huv i
  exact sub_eq_zero.mp (canonical_mulVec_eq_zero hH hz)

theorem mulVec_indicator (M : IMat k) (j : Fin k) :
    M.mulVec (fun s => if s = j then (1 : ℤ) else 0) = fun i => M i j := by
  funext i
  show ∑ s, M i s * (if s = j then (1 : ℤ) else 0) = M i j
  rw [Finset.sum_eq_single j (fun b _ hb => by
      rw [if_neg hb, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem exists_span_coeff {K : IMat k} {v : Fin k → ℤ} (hv : v ∈ colSpan K) :
    ∃ c : Fin k → ℤ, ∀ i, ∑ t, c t * K i t = v i := by
  rw [colSpan, rowSpan, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  refine ⟨c, fun i => ?_⟩
  have h1 := congrFun hc i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at h1
  exact h1

theorem canonical_span_matrix {H K : IMat k} (hH : IsCanonicalHNF H) (hK : IsCanonicalHNF K)
    (hsub : ∀ j : Fin k, (fun i => H i j) ∈ colSpan K) :
    ∃ U : IMat k, H = K * U ∧ (∀ r j : Fin k, (j : ℕ) < (r : ℕ) → U r j = 0)
      ∧ (∀ r : Fin k, K r r * U r r = H r r) := by
  have hall : ∀ j : Fin k, ∃ c : Fin k → ℤ, ∀ i, ∑ t, c t * K i t = H i j :=
    fun j => exists_span_coeff (hsub j)
  choose U hU using hall
  have hboth : ∀ r : Fin k,
      (∀ j : Fin k, (j : ℕ) < (r : ℕ) → U j r = 0)
      ∧ K r r * U r r = H r r := by
    refine Fin.downward_ind (fun r ih => ⟨fun j hj => ?_, ?_⟩)
    · have hentry : ∑ t, U j t * K r t = H r j := hU j r
      rw [hH.1 r j hj, Finset.sum_eq_single r (fun t _ htr => by
        rcases Nat.lt_trichotomy (t : ℕ) (r : ℕ) with h | h | h
        · rw [hK.1 r t h, mul_zero]
        · exact absurd (Fin.ext h) htr
        · rw [(ih t (by omega)).1 j (by omega), zero_mul])
        (fun h => absurd (Finset.mem_univ r) h)] at hentry
      exact (Int.mul_eq_zero.mp (by rw [mul_comm]; exact hentry)).resolve_left
        (ne_of_gt (hK.2.1 r))
    · have hentry : ∑ t, U r t * K r t = H r r := hU r r
      rw [Finset.sum_eq_single r (fun t _ htr => by
        rcases Nat.lt_trichotomy (t : ℕ) (r : ℕ) with h | h | h
        · rw [hK.1 r t h, mul_zero]
        · exact absurd (Fin.ext h) htr
        · rw [(ih t (by omega)).1 r (by omega), zero_mul])
        (fun h => absurd (Finset.mem_univ r) h), mul_comm] at hentry
      exact hentry
  refine ⟨Matrix.of fun r j => U j r, ?_, fun r j hj => (hboth r).1 j hj,
    fun r => (hboth r).2⟩
  ext i j
  rw [Matrix.mul_apply, ← hU j i]
  exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)

theorem mul_apply_two_terms {K U : IMat k} {i j : Fin k} (hij : (i : ℕ) < (j : ℕ))
    (hKlow : ∀ t : Fin k, (t : ℕ) < (i : ℕ) → K i t = 0)
    (hUhigh : ∀ t : Fin k, (j : ℕ) < (t : ℕ) → U t j = 0)
    (hUmid : ∀ t : Fin k, (i : ℕ) < (t : ℕ) → (t : ℕ) < (j : ℕ) → U t j = 0)
    (hUjj : U j j = 1) :
    (K * U) i j = K i i * U i j + K i j := by
  rw [Matrix.mul_apply]
  have expand : ∀ t : Fin k, K i t * U t j
      = (if t = i then K i i * U i j else 0) + (if t = j then K i j else 0) := by
    intro t
    rcases Nat.lt_trichotomy (t : ℕ) (i : ℕ) with h | h | h
    · rw [hKlow t h, zero_mul]
      rw [if_neg (fun he => by have := congrArg Fin.val he; omega),
        if_neg (fun he => by have := congrArg Fin.val he; omega), zero_add]
    · have hti : t = i := Fin.ext h
      rw [if_pos hti, if_neg (fun he => by have := congrArg Fin.val he; omega), add_zero,
        hti]
    · rcases Nat.lt_trichotomy (t : ℕ) (j : ℕ) with h' | h' | h'
      · rw [hUmid t h h', mul_zero,
          if_neg (fun he => by have := congrArg Fin.val he; omega),
          if_neg (fun he => by have := congrArg Fin.val he; omega), zero_add]
      · have htj : t = j := Fin.ext h'
        rw [if_neg (fun he => by have := congrArg Fin.val he; omega), if_pos htj, htj,
          zero_add, hUjj, mul_one]
      · rw [hUhigh t h', mul_zero,
          if_neg (fun he => by have := congrArg Fin.val he; omega),
          if_neg (fun he => by have := congrArg Fin.val he; omega), zero_add]
  rw [Finset.sum_congr rfl (fun t _ => expand t), Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ i), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ j)]

theorem canonical_unique {H K : IMat k} (hH : IsCanonicalHNF H) (hK : IsCanonicalHNF K)
    (hspan : colSpan H = colSpan K) : H = K := by
  obtain ⟨U, hHU, hU0, hUd⟩ :=
    canonical_span_matrix hH hK (fun j => by rw [← hspan]; exact mem_colSpan_column H j)
  obtain ⟨U', hKU', hU'0, hU'd⟩ :=
    canonical_span_matrix hK hH (fun j => by rw [hspan]; exact mem_colSpan_column K j)
  have h1 : H * (U' * U) = H := by
    rw [← Matrix.mul_assoc, ← hKU', hHU]
  have hprod : U' * U = 1 := by
    ext r j
    have hinj := canonical_mulVec_injective hH
    have he : H.mulVec ((U' * U).mulVec (fun s => if s = j then (1 : ℤ) else 0))
        = H.mulVec (fun s => if s = j then (1 : ℤ) else 0) := by
      rw [Matrix.mulVec_mulVec, h1]
    have hz := hinj he
    have hzr := congrFun hz r
    have e1 := congrFun (mulVec_indicator (U' * U) j) r
    rw [e1] at hzr
    simpa using! hzr
  have hdiagprod : ∀ r : Fin k, U' r r * U r r = 1 := by
    intro r
    have hentry : (U' * U) r r = 1 := by
      rw [hprod, Matrix.one_apply, if_pos rfl]
    rw [Matrix.mul_apply, Finset.sum_eq_single r (fun t _ htr => by
      rcases Nat.lt_trichotomy (t : ℕ) (r : ℕ) with h | h | h
      · rw [hU'0 r t h, zero_mul]
      · exact absurd (Fin.ext h) htr
      · rw [hU0 t r (by omega), mul_zero])
      (fun h => absurd (Finset.mem_univ r) h)] at hentry
    exact hentry
  have hUpos : ∀ r : Fin k, 0 < U r r := by
    intro r
    have hd := hdiagprod r
    have hne : U r r ≠ 0 := fun h => by
      rw [h, mul_zero] at hd
      exact zero_ne_one hd
    have h1' : 0 < K r r * U r r := by rw [hUd r]; exact hH.2.1 r
    have hnn : 0 ≤ U r r := by
      rcases lt_or_ge (U r r) 0 with hneg | hnn
      · exact absurd h1' (by nlinarith [hK.2.1 r, hneg])
      · exact hnn
    omega
  have hU'pos : ∀ r : Fin k, 0 < U' r r := by
    intro r
    have hd := hdiagprod r
    have hne : U' r r ≠ 0 := fun h => by
      rw [h, zero_mul] at hd
      exact zero_ne_one hd
    have h1' : 0 < H r r * U' r r := by rw [hU'd r]; exact hK.2.1 r
    have hnn : 0 ≤ U' r r := by
      rcases lt_or_ge (U' r r) 0 with hneg | hnn
      · exact absurd h1' (by nlinarith [hH.2.1 r, hneg])
      · exact hnn
    omega
  have hU1 : ∀ r : Fin k, U r r = 1 := by
    intro r
    have h1 := hU'pos r
    have h2 := hUpos r
    have h3 := hdiagprod r
    nlinarith
  have hdiag : ∀ r : Fin k, H r r = K r r := by
    intro r; rw [← hUd r, hU1 r, mul_one]
  have hoff : ∀ i : Fin k, ∀ j : Fin k, (i : ℕ) < (j : ℕ) → U i j = 0 ∧ H i j = K i j := by
    refine Fin.downward_ind (fun i ih => ?_)
    intro j hij
    have hent : (K * U) i j = H i j := by rw [hHU]
    have hsplit : H i j = K i i * U i j + K i j := by
      rw [← hent]
      exact mul_apply_two_terms hij (fun t ht => hK.1 i t ht)
        (fun t ht => hU0 t j ht) (fun t hti htj => (ih t hti) j htj |>.1) (hU1 j)
    have hab : (H i j - K i j).natAbs < (K i i).natAbs := by
      have hH1 := (hH.2.2 i j hij).1
      have hH2 := (hH.2.2 i j hij).2
      have hK1 := (hK.2.2 i j hij).1
      have hK2 := (hK.2.2 i j hij).2
      have hdi := hdiag i
      have hKabs : |K i i| = K i i := abs_of_pos (hK.2.1 i)
      have habs : |H i j - K i j| < |K i i| := by
        rw [hKabs]
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      rwa [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Nat.cast_lt] at habs
    have hdvd : K i i ∣ (H i j - K i j) := ⟨U i j, by linarith [hsplit]⟩
    have hzero : H i j - K i j = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hab
    have hUij : U i j = 0 := by
      have : K i i * U i j = 0 := by linarith [hsplit, hzero]
      exact (Int.mul_eq_zero.mp this).resolve_left (ne_of_gt (hK.2.1 i))
    exact ⟨hUij, by linarith [hzero]⟩
  ext i j
  rcases Nat.lt_trichotomy (j : ℕ) (i : ℕ) with h | h | h
  · rw [hH.1 i j h, hK.1 i j h]
  · have hji : j = i := Fin.ext h
    rw [hji, hdiag i]
  · exact ((hoff i) j h).2

theorem classicalCanonicalize_eq {A H : IMat k} (hA : A.det ≠ 0)
    (hH : IsCanonicalHNF H) (hspan : colSpan H = colSpan A) :
    H = classicalCanonicalize A := by
  refine canonical_unique hH (classicalCanonicalize_isCanonical A hA) ?_
  rw [hspan, colSpan_classicalCanonicalize A hA]

end Uniqueness

section Cost

variable {k : ℕ}

def matSup (R : IMat k) : ℕ := Finset.sup (Finset.univ : Finset (Fin k × Fin k))
  (fun p => (R p.1 p.2).natAbs)

theorem matSup_entry {R : IMat k} {i j : Fin k} : (R i j).natAbs ≤ matSup R := by
  unfold matSup
  exact Finset.le_sup (f := fun p => (R p.1 p.2).natAbs) (Finset.mem_univ (i, j))

theorem matSup_le_of {R : IMat k} {B : ℕ} (h : ∀ i j : Fin k, (R i j).natAbs ≤ B) :
    matSup R ≤ B :=
  Finset.sup_le (fun p _ => h p.1 p.2)

def matSupStep (B : ℕ) : ℕ := 4 * ((B + 1) * (B + 1)) + 2

def inputBitLength (A : IMat k) : ℕ :=
  ∑ p : Fin k × Fin k, (Nat.log 2 (A p.1 p.2).natAbs + 1)

def primitiveOpsPerRowOp (k : ℕ) : ℕ := 8 + 8 * k

theorem natAbs_le_mul_self {x B : ℕ} (h : x ≤ B) : x ≤ B * B := by
  rcases Nat.eq_zero_or_pos B with h0 | hp
  · omega
  · exact h.trans (Nat.le_mul_of_pos_left B hp)

theorem matSupStep_mono {B C : ℕ} (h : B ≤ C) : matSupStep B ≤ matSupStep C := by
  unfold matSupStep
  nlinarith

theorem matSupStep_iterate_mono {B C : ℕ} (h : B ≤ C) : ∀ n : ℕ,
    matSupStep^[n] B ≤ matSupStep^[n] C := by
  intro n
  induction n generalizing B C with
  | zero => exact h
  | succ n ih =>
    show matSupStep^[n] (matSupStep B) ≤ matSupStep^[n] (matSupStep C)
    exact ih (matSupStep_mono h)

theorem matSupStep_iterate_ge (B : ℕ) (n : ℕ) : B ≤ matSupStep^[n] B := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    show B ≤ matSupStep^[n] (matSupStep B)
    exact ih.trans (matSupStep_iterate_mono
      (show B ≤ matSupStep B by unfold matSupStep; nlinarith) n)

theorem iterate_add_eq {f : ℕ → ℕ} {B m n r : ℕ} (h : m + n = r) :
    f^[m] (f^[n] B) = f^[r] B := by
  subst h
  exact (Function.iterate_add_apply f m n B).symm

theorem matSupStep_iterate_le {B : ℕ} {m n : ℕ} (hmn : m ≤ n) :
    matSupStep^[m] B ≤ matSupStep^[n] B := by
  have h1 : matSupStep^[m] B ≤ matSupStep^[m] (matSupStep^[n - m] B) :=
    matSupStep_iterate_mono (matSupStep_iterate_ge B (n - m)) m
  rw [← Function.iterate_add_apply] at h1
  rw [show m + (n - m) = n from by omega] at h1
  exact h1

theorem matSup_transpose (R : IMat k) : matSup Rᵀ = matSup R := by
  refine le_antisymm ?_ ?_
  · refine matSup_le_of (fun i j => ?_)
    rw [Matrix.transpose_apply]
    exact matSup_entry
  · refine matSup_le_of (fun i j => ?_)
    exact matSup_entry (R := Rᵀ) (i := j) (j := i)

theorem matSup_signFixRow (c : Fin k) (R : IMat k) :
    matSup (signFixRow c R) ≤ matSup R := by
  refine matSup_le_of (fun i j => ?_)
  unfold signFixRow
  split
  · by_cases h : i = c
    · rw [h, Matrix.updateRow_self]
      simp only [Int.natAbs_neg]
      exact matSup_entry
    · rw [Matrix.updateRow_ne h]
      exact matSup_entry
  · exact matSup_entry

theorem matSup_hnfSwapOp (R : IMat k) (c i : Fin k) :
    matSup (hnfSwapOp R c i) ≤ matSupStep (matSup R) := by
  classical
  refine matSup_le_of (fun r j => ?_)
  set B := matSup R with hBdef
  have hB : ∀ (u v : Fin k), (R u v).natAbs ≤ B := fun u v => matSup_entry
  rcases eq_or_ne i c with hic | hic
  · rw [hic]
    by_cases hrc : r = c
    · rw [hrc]
      simp only [hnfSwapOp, Matrix.updateRow_apply]
      have hzero : (R c c / (Int.gcd (R c c) (R c c) : ℤ)) * R c j
          - (R c c / (Int.gcd (R c c) (R c c) : ℤ)) * R c j = 0 := sub_self _
      rw [hzero]
      exact Nat.zero_le _
    · simp only [hnfSwapOp, Matrix.updateRow_apply, if_neg hrc]
      exact matSup_entry.trans (by rw [hBdef]; unfold matSupStep; nlinarith)
  · rcases eq_or_ne r c with hrc | hrc
    · rw [hrc]
      have hbez := bezC_bound (R i c) (R c c)
      rw [hnfSwapOp_c R hic j]
      have hq : ((bezC (R i c) (R c c)).2).natAbs ≤ B + 1 := by
        have h4 := hbez.2
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h4
        have hy : ((R i c).natAbs : ℤ) ≤ ((B : ℕ) : ℤ) := Nat.cast_le.mpr (hB i c)
        have h5 : (((bezC (R i c) (R c c)).2).natAbs : ℤ) ≤ ((B : ℕ) : ℤ) + 1 := by linarith
        exact Nat.cast_le.mp (by exact_mod_cast h5)
      have hp : ((bezC (R i c) (R c c)).1).natAbs ≤ B + 1 := by
        have h4 := hbez.1
        rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h4
        have hy : ((R c c).natAbs : ℤ) ≤ ((B : ℕ) : ℤ) := Nat.cast_le.mpr (hB c c)
        have h5 : (((bezC (R i c) (R c c)).1).natAbs : ℤ) ≤ ((B : ℕ) : ℤ) + 1 := by linarith
        exact Nat.cast_le.mp (by exact_mod_cast h5)
      have hBcj := hB c j
      have hBij := hB i j
      have t1 : ((bezC (R i c) (R c c)).2 * R c j).natAbs ≤ (B + 1) * B := by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul hq hBcj
      have t2 : ((bezC (R i c) (R c c)).1 * R i j).natAbs ≤ (B + 1) * B := by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul hp hBij
      have t3 := Int.natAbs_add_le ((bezC (R i c) (R c c)).2 * R c j)
        ((bezC (R i c) (R c c)).1 * R i j)
      unfold matSupStep
      set P := (B + 1) * (B + 1) with hP
      set Q := (B + 1) * B with hQ
      have hQP : Q ≤ P := Nat.mul_le_mul_left (B + 1) (Nat.le_succ B)
      omega
    · rcases eq_or_ne r i with hri | hri
      · rw [hri, hnfSwapOp_i R j]
        have hgx : (R c c / (Int.gcd (R i c) (R c c) : ℤ)).natAbs ≤ B := by
          have h1 := Int.abs_ediv_le_abs (R c c) (Int.gcd (R i c) (R c c))
          rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1
          exact (Nat.cast_le.mp h1).trans (hB c c)
        have hgy : (R i c / (Int.gcd (R i c) (R c c) : ℤ)).natAbs ≤ B := by
          have h1 := Int.abs_ediv_le_abs (R i c) (Int.gcd (R i c) (R c c))
          rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1
          exact (Nat.cast_le.mp h1).trans (hB i c)
        have hBij := hB i j
        have hBcj := hB c j
        have t1 : ((R c c / (Int.gcd (R i c) (R c c) : ℤ)) * R i j).natAbs ≤ B * B := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul hgx hBij
        have t2 : ((R i c / (Int.gcd (R i c) (R c c) : ℤ)) * R c j).natAbs ≤ B * B := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul hgy hBcj
        have t3 := Int.natAbs_sub_le ((R c c / (Int.gcd (R i c) (R c c) : ℤ)) * R i j)
          ((R i c / (Int.gcd (R i c) (R c c) : ℤ)) * R c j)
        unfold matSupStep
        set P := (B + 1) * (B + 1) with hP
        have hBB : B * B ≤ P :=
          (Nat.mul_le_mul (Nat.le_succ B) (Nat.le_refl B)).trans
            (Nat.mul_le_mul_left (B + 1) (Nat.le_succ B))
        omega
      · rw [hnfSwapOp_of R hrc hri]
        exact matSup_entry.trans (by rw [hBdef]; unfold matSupStep; nlinarith)

theorem matSup_reduceRowOp (R : IMat k) (i j : Fin k) :
    matSup (reduceRowOp R i j) ≤ matSupStep (matSup R) := by
  classical
  refine matSup_le_of (fun r c' => ?_)
  set B := matSup R with hBdef
  have hB : ∀ (u v : Fin k), (R u v).natAbs ≤ B := fun u v => matSup_entry
  unfold reduceRowOp
  by_cases hrj : r = j
  · rw [hrj, Matrix.updateRow_self]
    have hq : (R j i / R i i).natAbs ≤ B := by
      have h1 := Int.abs_ediv_le_abs (R j i) (R i i)
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1
      exact (Nat.cast_le.mp h1).trans (hB j i)
    have hBij := hB i c'
    have hBji := hB j i
    have t1 : ((R j i / R i i) * R i c').natAbs ≤ B * B := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul hq hBij
    have t2 : (R j c').natAbs ≤ B * B := natAbs_le_mul_self (hB j c')
    have t3 := Int.natAbs_sub_le (R j c') ((R j i / R i i) * R i c')
    have hBB : B * B ≤ (B + 1) * (B + 1) :=
      (Nat.mul_le_mul (Nat.le_succ B) (Nat.le_refl B)).trans
        (Nat.mul_le_mul_left (B + 1) (Nat.le_succ B))
    unfold matSupStep
    set P := (B + 1) * (B + 1) with hP
    omega
  · rw [Matrix.updateRow_ne hrj]
    exact matSup_entry.trans (by rw [hBdef]; unfold matSupStep; nlinarith)

theorem matSup_sweepStep (c : Fin k) (R : IMat k) (i : Fin k) :
    matSup (sweepStep c R i) ≤ matSupStep (matSup R) := by
  unfold sweepStep
  split
  · exact matSup_hnfSwapOp R c i
  · exact Nat.le_trans (Nat.le_refl _) (by
      unfold matSupStep; nlinarith)

theorem matSup_redStep (i : Fin k) (R : IMat k) (j : Fin k) :
    matSup (redStep i R j) ≤ matSupStep (matSup R) := by
  unfold redStep
  split
  · exact matSup_reduceRowOp R i j
  · exact Nat.le_trans (Nat.le_refl _) (by unfold matSupStep; nlinarith)

theorem matSup_foldl_sweep (c : Fin k) (l : List (Fin k)) :
    ∀ R : IMat k, matSup (l.foldl (sweepStep c) R) ≤ matSupStep^[l.length] (matSup R) := by
  induction l with
  | nil => intro R; simp
  | cons i₀ rest ih =>
    intro R
    refine (ih (sweepStep c R i₀)).trans ?_
    rw [show (i₀ :: rest).length = rest.length + 1 from rfl, Function.iterate_succ_apply]
    exact matSupStep_iterate_mono (matSup_sweepStep c R i₀) rest.length

theorem matSup_foldl_red (i : Fin k) (l : List (Fin k)) :
    ∀ R : IMat k, matSup (l.foldl (redStep i) R) ≤ matSupStep^[l.length] (matSup R) := by
  induction l with
  | nil => intro R; simp
  | cons j₀ rest ih =>
    intro R
    refine (ih (redStep i R j₀)).trans ?_
    rw [show (j₀ :: rest).length = rest.length + 1 from rfl, Function.iterate_succ_apply]
    exact matSupStep_iterate_mono (matSup_redStep i R j₀) rest.length

theorem matSup_stageSweep (c : Fin k) (R : IMat k) :
    matSup (stageSweep c R) ≤ matSupStep^[(List.finRange k).length] (matSup R) := by
    refine (matSup_foldl_sweep c ((List.finRange k).filter (fun i : Fin k =>
      decide ((i : ℕ) < (c : ℕ)))) R).trans ?_
    exact matSupStep_iterate_le (List.length_filter_le _ _)

theorem matSup_redSweep (i : Fin k) (R : IMat k) :
    matSup (redSweep i R) ≤ matSupStep^[(List.finRange k).length] (matSup R) := by
    refine (matSup_foldl_red i ((List.finRange k).filter (fun j : Fin k =>
      decide ((i : ℕ) < (j : ℕ)))) R).trans ?_
    exact matSupStep_iterate_le (List.length_filter_le _ _)

theorem matSup_stage (c : Fin k) (R : IMat k) :
    matSup (stage c R) ≤ matSupStep^[(List.finRange k).length] (matSup R) := by
  unfold stage
  exact (matSup_signFixRow c (stageSweep c R)).trans (matSup_stageSweep c R)

theorem matSup_triAux (R : IMat k) : ∀ t : ℕ,
    matSup (triAux t R) ≤ matSupStep^[(List.finRange k).length * t] (matSup R) := by
  intro t
  induction t with
  | zero => exact Nat.le_trans (Nat.le_refl _) (matSupStep_iterate_ge _ _)
  | succ t ih =>
    unfold triAux
    split
    · exact matSupStep_iterate_ge _ _
    · refine (matSup_stage _ _).trans ?_
      rw [show (List.finRange k).length * (t + 1)
          = (List.finRange k).length + (List.finRange k).length * t from by ring,
        Function.iterate_add_apply]
      exact matSupStep_iterate_mono ih _

theorem matSup_redAux (R : IMat k) : ∀ t : ℕ,
    matSup (redAux t R) ≤ matSupStep^[(List.finRange k).length * t] (matSup R) := by
  intro t
  induction t with
  | zero => exact Nat.le_trans (Nat.le_refl _) (matSupStep_iterate_ge _ _)
  | succ t ih =>
    unfold redAux
    split
    · exact matSupStep_iterate_ge _ _
    · refine (matSup_redSweep _ _).trans ?_
      rw [show (List.finRange k).length * (t + 1)
          = (List.finRange k).length + (List.finRange k).length * t from by ring,
        Function.iterate_add_apply]
      exact matSupStep_iterate_mono ih _

theorem classicalCanonicalize_valueBound (A : IMat k) :
    matSup (classicalCanonicalize A) ≤ matSupStep^[2 * k * k] (matSup A) := by
  unfold classicalCanonicalize
  rw [matSup_transpose]
  have htri : matSup (reduceOffDiagonal (triangularize A))
      ≤ matSupStep^[k * k] (matSup (triangularize A)) := by
    unfold triangularize reduceOffDiagonal
    have h1 := matSup_redAux (triAux k Aᵀ) k
    rw [List.length_finRange] at h1
    exact h1
  have htri2 : matSup (triangularize A) ≤ matSupStep^[k * k] (matSup A) := by
    unfold triangularize
    have h2 := matSup_triAux (Aᵀ) k
    rw [List.length_finRange, matSup_transpose] at h2
    exact h2
  have hexp : matSupStep^[k * k] (matSupStep^[k * k] (matSup A))
      = matSupStep^[2 * k * k] (matSup A) := by
    have h1 : matSupStep^[k * k] (matSupStep^[k * k] (matSup A))
        = matSupStep^[k * k + k * k] (matSup A) :=
      (Function.iterate_add_apply matSupStep (k * k) (k * k) (matSup A)).symm
    have h2 : matSupStep^[k * k + k * k] (matSup A)
        = matSupStep^[2 * k * k] (matSup A) := by
      conv_rhs => rw [show (2 * k * k) = k * k + k * k from by ring]
    exact h1.trans h2
  calc matSup (reduceOffDiagonal (triangularize A))
      ≤ matSupStep^[k * k] (matSup (triangularize A)) := htri
    _ ≤ matSupStep^[k * k] (matSupStep^[k * k] (matSup A)) := matSupStep_iterate_mono htri2 _
    _ = matSupStep^[2 * k * k] (matSup A) := hexp

theorem matSup_lt_two_pow_inputBitLength (A : IMat k) :
    matSup A < 2 ^ (inputBitLength A) := by
  have hkey : ∀ p : Fin k × Fin k,
      (A p.1 p.2).natAbs < 2 ^ (Nat.log 2 (A p.1 p.2).natAbs + 1) := by
    intro p
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (A p.1 p.2).natAbs
    simpa using h
  have hsum : ∀ p : Fin k × Fin k,
      (A p.1 p.2).natAbs < 2 ^ (inputBitLength A) := by
    intro p
    refine (hkey p).trans_le ?_
    refine Nat.pow_le_pow_right (by omega) ?_
    unfold inputBitLength
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k × Fin k))
      (fun q => Nat.log 2 (A q.1 q.2).natAbs + 1) (Finset.mem_univ p)]
    exact Nat.le_add_right _ _
  unfold matSup
  rw [Finset.sup_lt_iff (by simp)]
  intro p _
  exact hsum p

theorem det_abs_le (A : IMat k) :
    (A.det).natAbs ≤ Fintype.card (Equiv.Perm (Fin k)) * (matSup A) ^ k := by
  classical
  set B := matSup A with hBdef
  have hB : ∀ (u v : Fin k), (A u v).natAbs ≤ B := fun u v => matSup_entry
  have hunit : ∀ u : ℤˣ, |(u : ℤ)| = 1 := by
    intro u
    rcases Int.isUnit_iff.mp u.isUnit with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hmain : |A.det| ≤ ((Fintype.card (Equiv.Perm (Fin k)) * B ^ k : ℕ)) := by
    rw [Matrix.det_apply']
    calc |∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
          * ∏ i, A (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin k),
            |((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i, A (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm (Fin k), |∏ i, A (σ i) i| := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [abs_mul, hunit, one_mul]
      _ ≤ ∑ σ : Equiv.Perm (Fin k), ((B : ℤ) ^ k) := by
          refine Finset.sum_le_sum (fun σ _ => ?_)
          have habs : |∏ x, A (σ x) x| ≤ ∏ x, |A (σ x) x| := by
            have key : ∀ (s : Finset (Fin k)), |∏ x ∈ s, A (σ x) x| ≤ ∏ x ∈ s, |A (σ x) x| := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp
              | insert a s ha ih =>
                  rw [Finset.prod_insert ha, Finset.prod_insert ha, abs_mul]
                  exact mul_le_mul (le_refl _) ih (abs_nonneg _) (abs_nonneg _)
            exact key Finset.univ
          have hprod : ∏ x, |A (σ x) x| ≤ (∏ x : Fin k, ((B : ℤ))) :=
            Finset.prod_le_prod₀ (fun x _ => abs_nonneg _) (fun x _ => by
              rw [Int.abs_eq_natAbs]
              exact Nat.cast_le.mpr (hB (σ x) x))
          refine habs.trans (hprod.trans_eq ?_)
          simp [Finset.prod_const]
      _ = ((Fintype.card (Equiv.Perm (Fin k)) * B ^ k : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
          push_cast
          ring
  rw [Int.abs_eq_natAbs, Nat.cast_le] at hmain
  exact hmain

end Cost

section Interleaved

variable {k : ℕ}

theorem zeroAbove_mono {R : IMat k} {m n : ℕ} (hmn : m ≤ n) (hZ : ZeroAbove m R) :
    ZeroAbove n R :=
  fun r j hj hrj => hZ r j (hmn.trans hj) hrj

theorem zeroAbove_reduceRowOp_ge (R : IMat k) {i j : Fin k} (_hij : (i : ℕ) < (j : ℕ))
    (hZ : ZeroAbove ((i : ℕ) + 1) R) : ZeroAbove ((i : ℕ) + 1) (reduceRowOp R i j) := by
  intro r j' hj' hrj'
  rcases eq_or_ne r j with hrj | hrj
  · rw [hrj, reduceRowOp, Matrix.updateRow_self]
    rw [hZ j j' (by omega) (by omega), hZ i j' (by omega) (by omega), mul_zero, sub_zero]
  · rw [reduceRowOp, Matrix.updateRow_ne hrj]
    exact hZ r j' hj' hrj'

theorem zeroAbove_redStep_ge (i : Fin k) (R : IMat k) (j : Fin k) (hij : (i : ℕ) < (j : ℕ))
    (hZ : ZeroAbove ((i : ℕ) + 1) R) : ZeroAbove ((i : ℕ) + 1) (redStep i R j) := by
  rw [redStep, if_pos hij]
  exact zeroAbove_reduceRowOp_ge R hij hZ

theorem posDiag_redStep_ge (i : Fin k) (R : IMat k) (j : Fin k) (hij : (i : ℕ) < (j : ℕ))
    (hpos : PosDiag (i : ℕ) R) (hZ : ZeroAbove ((i : ℕ) + 1) R) :
    PosDiag (i : ℕ) (redStep i R j) := by
  intro r hr
  rw [redStep, if_pos hij]
  rcases eq_or_ne r j with hrj | hrj
  · rw [hrj, reduceRowOp, Matrix.updateRow_self, hZ i j (by omega) (by omega), mul_zero,
      sub_zero]
    exact hpos j (by omega)
  · rw [reduceRowOp, Matrix.updateRow_ne hrj]
    exact hpos r hr

theorem redStep_entry_high_ge (i : Fin k) (R : IMat k) (j r i' : Fin k)
    (hii' : (i : ℕ) < (i' : ℕ)) (hZ : ZeroAbove ((i : ℕ) + 1) R) :
    (redStep i R j) r i' = R r i' := by
  unfold redStep
  split
  · by_cases hrj : r = j
    · subst hrj
      rw [reduceRowOp, Matrix.updateRow_self, hZ i i' (by omega) (by omega), mul_zero,
        sub_zero]
    · rw [reduceRowOp, Matrix.updateRow_ne hrj]
  · rfl

theorem redSweep_fold_ge (i : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ j ∈ l, (i : ℕ) < (j : ℕ)) (hnl : l.Nodup) (hpos : PosDiag (i : ℕ) R)
    (hZ : ZeroAbove ((i : ℕ) + 1) R) :
    PosDiag (i : ℕ) (l.foldl (redStep i) R) ∧ ZeroAbove ((i : ℕ) + 1) (l.foldl (redStep i) R)
    ∧ rowSpan (l.foldl (redStep i) R) = rowSpan R
    ∧ (∀ j ∈ l, (i : ℕ) < (j : ℕ) → 0 ≤ (l.foldl (redStep i) R) j i
        ∧ (l.foldl (redStep i) R) j i < R i i)
    ∧ (∀ r : Fin k, (∀ j ∈ l, j ≠ r) → (l.foldl (redStep i) R) r = R r) := by
  induction l generalizing R with
  | nil => exact ⟨hpos, hZ, rfl, fun j hj => absurd hj (by simp), fun r _ => rfl⟩
  | cons j₀ rest ih =>
    have hlt₀ : (i : ℕ) < (j₀ : ℕ) := hl j₀ (List.mem_cons_self ..)
    have hrest : ∀ j ∈ rest, (i : ℕ) < (j : ℕ) := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hnlrest : rest.Nodup := (List.nodup_cons.mp hnl).2
    have hbundle := ih (redStep i R j₀) hrest hnlrest
      (posDiag_redStep_ge i R j₀ hlt₀ hpos hZ) (zeroAbove_redStep_ge i R j₀ hlt₀ hZ)
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hbundle
    have hdiagi : (redStep i R j₀) i i = R i i := by
      rw [redStep_row i R j₀ i (by omega)]
    have hb4' : ∀ j ∈ rest, (i : ℕ) < (j : ℕ) →
        0 ≤ (List.foldl (redStep i) (redStep i R j₀) rest) j i
        ∧ (List.foldl (redStep i) (redStep i R j₀) rest) j i < R i i := by
      intro j hj hjlt
      have h := hb4 j hj hjlt
      rw [hdiagi] at h
      exact h
    refine ⟨hb1, hb2, ?_, ?_, ?_⟩
    · rw [List.foldl_cons, hb3, rowSpan_redStep i R j₀ hlt₀]
    · intro j hjmem hjlt
      rcases List.mem_cons.mp hjmem with heq | hirest
      · have hj₀ : j = j₀ := heq
        rw [hj₀, List.foldl_cons,
          hb5 j₀ (fun x hx h => (List.nodup_cons.mp hnl).1 (h ▸ hx))]
        exact (redStep_entry i R j₀ hlt₀ (hpos i (by omega))).2
      · rw [List.foldl_cons]
        exact hb4' j hirest hjlt
    · intro r hr
      have hrrest : ∀ j ∈ rest, j ≠ r := fun j hj => hr j (List.mem_cons_of_mem _ hj)
      rw [List.foldl_cons, hb5 r hrrest, redStep_row i R j₀ r
        ((hr j₀ (by simp)).symm)]

theorem redSweep_fold_high_ge (i : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ j ∈ l, (i : ℕ) < (j : ℕ)) (hZ : ZeroAbove ((i : ℕ) + 1) R) (i' : Fin k)
    (hii' : (i : ℕ) < (i' : ℕ)) :
    ∀ r : Fin k, (l.foldl (redStep i) R) r i' = R r i' := by
  induction l generalizing R with
  | nil => intro r; rfl
  | cons j₀ rest ih =>
    intro r
    rw [List.foldl_cons,
      ih (redStep i R j₀) (fun j hj => hl j (List.mem_cons_of_mem _ hj))
        (zeroAbove_redStep_ge i R j₀ (hl j₀ (List.mem_cons_self ..)) hZ) r]
    exact redStep_entry_high_ge i R j₀ r i' hii' hZ

theorem redSweep_fold_rows (i : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ j ∈ l, (i : ℕ) < (j : ℕ)) :
    ∀ r : Fin k, (∀ j ∈ l, j ≠ r) → (l.foldl (redStep i) R) r = R r := by
  induction l generalizing R with
  | nil => intro r _; rfl
  | cons j₀ rest ih =>
    intro r hr
    rw [List.foldl_cons,
      ih (redStep i R j₀) (fun j hj => hl j (List.mem_cons_of_mem _ hj)) r
        (fun j hj => hr j (List.mem_cons_of_mem _ hj)),
      redStep_row i R j₀ r ((hr j₀ (by simp)).symm)]

theorem redSweep_row_le (i : Fin k) (R : IMat k) (r : Fin k) (hr : (r : ℕ) ≤ (i : ℕ)) :
    (redSweep i R) r = R r := by
  refine redSweep_fold_rows i ((List.finRange k).filter (fun j : Fin k =>
    decide ((i : ℕ) < (j : ℕ)))) R
    (fun j hj => by simpa using (List.mem_filter.mp hj).2) r ?_
  intro j hj
  have hlt : (i : ℕ) < (j : ℕ) := by simpa using (List.mem_filter.mp hj).2
  have hne : (j : ℕ) ≠ (r : ℕ) := by omega
  exact fun h => hne (congrArg Fin.val h)

theorem redSweep_spec_ge (i : Fin k) (R : IMat k) (hpos : PosDiag (i : ℕ) R)
    (hZ : ZeroAbove ((i : ℕ) + 1) R) (hR : RedBelow ((i : ℕ) + 1) R) :
    PosDiag (i : ℕ) (redSweep i R) ∧ ZeroAbove ((i : ℕ) + 1) (redSweep i R)
    ∧ rowSpan (redSweep i R) = rowSpan R ∧ RedBelow (i : ℕ) (redSweep i R) := by
  have hb := redSweep_fold_ge i ((List.finRange k).filter (fun j : Fin k =>
    decide ((i : ℕ) < (j : ℕ)))) R
    (fun j hj => by simpa using (List.mem_filter.mp hj).2)
    (List.Nodup.filter _ (List.nodup_finRange k)) hpos hZ
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
  refine ⟨hb1, hb2, hb3, ?_⟩
  intro i' j hi' hi'j
  rcases Nat.lt_or_ge (i' : ℕ) ((i : ℕ) + 1) with hlt | hge
  · have hieq : i' = i := Fin.ext (by omega)
    rw [hieq] at hi'j ⊢
    have hdiagi : (redSweep i R) i i = R i i := by
      have hrowi := hb5 i (fun j hj => by
        have hmem := (List.mem_filter.mp hj).2
        simp only [decide_eq_true_eq] at hmem
        omega)
      exact congrFun hrowi i
    constructor
    · exact (hb4 j (mem_redSweep_list hi'j) hi'j).1
    · rw [hdiagi]
      exact (hb4 j (mem_redSweep_list hi'j) hi'j).2
  · have h1 : (redSweep i R) j i' = R j i' :=
      redSweep_fold_high_ge i _ R
        (fun j hj => by simpa using (List.mem_filter.mp hj).2) hZ i' (by omega) j
    have h2 : (redSweep i R) i' i' = R i' i' :=
      redSweep_fold_high_ge i _ R
        (fun j hj => by simpa using (List.mem_filter.mp hj).2) hZ i' (by omega) i'
    have hold := hR i' j (by omega) hi'j
    constructor
    · rw [h1]; exact hold.1
    · rw [h1, h2]; exact hold.2

theorem trailInj_redSweep (i : Fin k) (R : IMat k) (n : ℕ) (hn : n ≤ (i : ℕ))
    (hT : TrailInj n R) : TrailInj n (redSweep i R) := by
  intro x hxsup hxvan
  refine hT x hxsup fun r hr => ?_
  have hrow : (redSweep i R) r = R r := redSweep_row_le i R r (by omega)
  have hsum : ∑ s, ((redSweep i R) r s : ℚ) * x s = ∑ s, (R r s : ℚ) * x s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [congrFun hrow s]
  rw [← hsum]
  exact hxvan r hr

theorem sweep_fold_rows (c : Fin k) (l : List (Fin k)) (R : IMat k)
    (hl : ∀ i ∈ l, (i : ℕ) < (c : ℕ)) :
    ∀ r : Fin k, (∀ i ∈ l, i ≠ r) → r ≠ c → (l.foldl (sweepStep c) R) r = R r := by
  induction l generalizing R with
  | nil => intro r _ _; rfl
  | cons i₀ rest ih =>
    intro r hr hrc
    rw [List.foldl_cons,
      ih (sweepStep c R i₀) (fun i hi => hl i (List.mem_cons_of_mem _ hi)) r
        (fun i hi => hr i (List.mem_cons_of_mem _ hi)) hrc,
      sweepStep_row c R i₀ r hrc ((hr i₀ (by simp)).symm)]

theorem stage_row_gt (c : Fin k) (R : IMat k) (r : Fin k) (hcr : (c : ℕ) < (r : ℕ)) :
    (stage c R) r = R r := by
  have hsweep : (stageSweep c R) r = R r := by
    refine sweep_fold_rows c ((List.finRange k).filter (fun i : Fin k =>
      decide ((i : ℕ) < (c : ℕ)))) R
      (fun i hi => by simpa using (List.mem_filter.mp hi).2) r (fun i hi => ?_) (fun h => ?_)
    · have hlt : (i : ℕ) < (c : ℕ) := by simpa using (List.mem_filter.mp hi).2
      have hne : (i : ℕ) ≠ (r : ℕ) := by omega
      exact fun he => hne (congrArg Fin.val he)
    · have hne : (r : ℕ) ≠ (c : ℕ) := by omega
      exact hne (congrArg Fin.val h)
  unfold stage signFixRow
  split
  · rw [Matrix.updateRow_ne (fun h => by have := congrArg Fin.val h; omega)]
    exact hsweep
  · exact hsweep

theorem redBelow_stage (c : Fin k) (R : IMat k) (hR : RedBelow ((c : ℕ) + 1) R) :
    RedBelow ((c : ℕ) + 1) (stage c R) := by
  intro i j hi hij
  have hrowj : (stage c R) j = R j := stage_row_gt c R j (by omega)
  have hrowi : (stage c R) i = R i := stage_row_gt c R i (by omega)
  have hold := hR i j hi hij
  constructor
  · rw [hrowj]; exact hold.1
  · rw [hrowj, congrFun hrowi i]; exact hold.2

def interleavedStage (c : Fin k) (R : IMat k) : IMat k := redSweep c (stage c R)

theorem interleavedStage_spec (c : Fin k) (R : IMat k) (hT : TrailInj (c : ℕ) R)
    (hZ : ZeroAbove ((c : ℕ) + 1) R) (hP : PosDiag ((c : ℕ) + 1) R)
    (hR : RedBelow ((c : ℕ) + 1) R) :
    TrailInj ((c : ℕ) - 1) (interleavedStage c R)
    ∧ ZeroAbove (c : ℕ) (interleavedStage c R)
    ∧ PosDiag (c : ℕ) (interleavedStage c R)
    ∧ RedBelow (c : ℕ) (interleavedStage c R)
    ∧ rowSpan (interleavedStage c R) = rowSpan R := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := stage_spec c R hT hZ hP
  have hR' : RedBelow ((c : ℕ) + 1) (stage c R) := redBelow_stage c R hR
  have hZ' : ZeroAbove ((c : ℕ) + 1) (stage c R) :=
    zeroAbove_mono (R := stage c R) (by omega) hs2
  have hb := redSweep_spec_ge c (stage c R) hs3 hZ' hR'
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  refine ⟨trailInj_redSweep c _ ((c : ℕ) - 1) (by omega) hs1, ?_, hb1, hb4, hb3.trans hs4⟩
  intro r j hj hrj
  unfold interleavedStage
  rcases Nat.eq_or_lt_of_le hj with jeq | jlt
  · rw [redSweep_row_le c _ r (by omega)]
    exact hs2 r j hj hrj
  · exact hb2 r j (by omega) hrj

def interleavedTriAux : ℕ → IMat k → IMat k
  | 0, R => R
  | t + 1, R =>
    if h : k ≤ t then R else
      interleavedStage ⟨k - 1 - t, by have := h; omega⟩ (interleavedTriAux t R)

theorem interleavedTriAux_spec (A : IMat k) (hA : A.det ≠ 0) : ∀ t : ℕ, t ≤ k →
    TrailInj (k - 1 - t) (interleavedTriAux t A) ∧ ZeroAbove (k - t) (interleavedTriAux t A)
    ∧ PosDiag (k - t) (interleavedTriAux t A) ∧ RedBelow (k - t) (interleavedTriAux t A)
    ∧ rowSpan (interleavedTriAux t A) = rowSpan A := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨trailInj_of_det_ne_zero A hA, ?_, ?_, ?_, rfl⟩
    · intro r j hj hrj
      exact absurd hj (by have := Fin.isLt j; omega)
    · intro r hr
      exact absurd hr (by have := Fin.isLt r; omega)
    · intro i j hi hj
      exact absurd hi (by have := Fin.isLt i; omega)
  | succ t ih =>
    intro ht
    have hltk : t < k := by omega
    have hc : (k - 1 - t : ℕ) < k := by omega
    have hb := ih (by omega)
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hb
    rw [show k - t = (k - 1 - t : ℕ) + 1 from by omega] at hb2 hb3 hb4
    have hs := interleavedStage_spec (⟨k - 1 - t, hc⟩ : Fin k) (interleavedTriAux t A)
      hb1 hb2 hb3 hb4
    obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hs
    have hcoe : (((⟨k - 1 - t, hc⟩ : Fin k) : ℕ)) = k - 1 - t := rfl
    rw [hcoe] at hs1 hs2 hs3 hs4
    unfold interleavedTriAux at ⊢
    rw [dif_neg (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [show k - 1 - (t + 1) = (k - 1 - t) - 1 from by omega]
      exact hs1
    · rw [show k - (t + 1) = (k - 1 - t) from by omega]
      exact hs2
    · rw [show k - (t + 1) = (k - 1 - t) from by omega]
      exact hs3
    · rw [show k - (t + 1) = (k - 1 - t) from by omega]
      exact hs4
    · rw [hs5]
      exact hb5

def interleavedCanonicalize (A : IMat k) : IMat k := (interleavedTriAux k Aᵀ)ᵀ

theorem interleavedCanonicalize_isCanonical (A : IMat k) (hA : A.det ≠ 0) :
    IsCanonicalHNF (interleavedCanonicalize A) := by
  have hT : Aᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hb := interleavedTriAux_spec Aᵀ hT k (by omega)
  rw [Nat.sub_self] at hb
  obtain ⟨_, hZ, hP, hR, _⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h0 := hZ j i (Nat.zero_le _) hij
    unfold interleavedCanonicalize
    simp only [Matrix.transpose_apply]
    rw [h0]
  · intro i
    exact hP i (Nat.zero_le _)
  · intro i j hij
    exact hR i j (Nat.zero_le _) hij

theorem colSpan_interleavedCanonicalize (A : IMat k) (hA : A.det ≠ 0) :
    colSpan (interleavedCanonicalize A) = colSpan A := by
  have hT : Aᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hb := interleavedTriAux_spec Aᵀ hT k (by omega)
  unfold interleavedCanonicalize
  rw [colSpan_transpose, hb.2.2.2.2, ← rowSpan_transpose]

theorem interleavedCanonicalize_eq (A : IMat k) (hA : A.det ≠ 0) :
    interleavedCanonicalize A = classicalCanonicalize A :=
  classicalCanonicalize_eq hA (interleavedCanonicalize_isCanonical A hA)
    (colSpan_interleavedCanonicalize A hA)

theorem matSup_interleavedStage (c : Fin k) (R : IMat k) :
    matSup (interleavedStage c R) ≤ matSupStep^[2 * (List.finRange k).length] (matSup R) := by
  have h1 := matSup_stage c R
  have h2 := matSup_redSweep c (stage c R)
  refine h2.trans ?_
  refine (matSupStep_iterate_mono h1 _).trans_eq ?_
  rw [List.length_finRange, ← Function.iterate_add_apply]
  congr 1
  ring

theorem matSup_interleavedTriAux (R : IMat k) : ∀ t : ℕ,
    matSup (interleavedTriAux t R)
      ≤ matSupStep^[2 * (List.finRange k).length * t] (matSup R) := by
  intro t
  induction t with
  | zero => exact Nat.le_trans (Nat.le_refl _) (matSupStep_iterate_ge _ _)
  | succ t ih =>
    unfold interleavedTriAux
    split
    · exact matSupStep_iterate_ge _ _
    · refine (matSup_interleavedStage _ _).trans ?_
      rw [show 2 * (List.finRange k).length * (t + 1)
          = 2 * (List.finRange k).length + 2 * (List.finRange k).length * t from by ring,
        Function.iterate_add_apply]
      exact matSupStep_iterate_mono ih _

theorem interleavedCanonicalize_valueBound (A : IMat k) :
    matSup (interleavedCanonicalize A) ≤ matSupStep^[2 * k * k] (matSup A) := by
  unfold interleavedCanonicalize
  rw [matSup_transpose]
  have h := matSup_interleavedTriAux (Aᵀ) k
  rw [List.length_finRange, matSup_transpose] at h
  exact h

end Interleaved

section OutputBound

variable {k : ℕ}

theorem adjugate_row_eq (M : IMat k) (c j : Fin k) :
    ∑ r, M.adjugate c r * M r j = (M.det : ℤ) * (if c = j then (1 : ℤ) else 0) := by
  have h : (M.adjugate * M) c j = ((M.det : ℤ) * (if c = j then (1 : ℤ) else 0)) :=
    congrFun (congrFun (Matrix.adjugate_mul M) c) j
  rw [Matrix.mul_apply] at h
  exact h

theorem adjugate_comb_mem_rowSpan (M : IMat k) (c : Fin k) :
    (fun j => ∑ r, M.adjugate c r * M r j) ∈ rowSpan M := by
  have hfun : (fun j => ∑ r, M.adjugate c r * M r j)
      = ∑ r, (fun j => M.adjugate c r * M r j) := by
    funext j
    rw [Finset.sum_apply]
  rw [hfun]
  refine Submodule.sum_mem (rowSpan M) fun r _ => ?_
  have h : (fun j => M.adjugate c r * M r j) = (M.adjugate c r) • (M r) := by
    funext j; simp
  rw [h]
  exact mem_rowSpan_smul_row

theorem canonical_coeff_zero_above {H : IMat k} (hH : IsCanonicalHNF H) {c : Fin k}
    {w : Fin k → ℤ} {v : Fin k → ℤ} (hw : ∀ j : Fin k, ∑ t, w t * H j t = v j)
    (hv : ∀ j : Fin k, (c : ℕ) < (j : ℕ) → v j = 0) :
    ∀ j : Fin k, (c : ℕ) < (j : ℕ) → w j = 0 := by
  refine Fin.downward_ind (fun i ih => ?_)
  intro hci
  have hrow : ∑ t, w t * H i t = 0 := by
    rw [hw i, hv i hci]
  rw [Finset.sum_eq_single i (fun b _ hbi => by
      rcases Nat.lt_trichotomy (b : ℕ) (i : ℕ) with h | h | h
      · rw [hH.1 i b h, mul_zero]
      · exact absurd (Fin.ext h) hbi
      · rw [(ih b (by omega)) (by omega), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)] at hrow
  exact (Int.mul_eq_zero.mp hrow).resolve_right (ne_of_gt (hH.2.1 i))

theorem canonical_diag_dvd_det {A H : IMat k} (hH : IsCanonicalHNF H)
    (hspan : colSpan H = colSpan A) (c : Fin k) : (H c c) ∣ (A.det : ℤ) := by
  set v : Fin k → ℤ := fun j => ∑ r, (Aᵀ.adjugate) c r * (Aᵀ) r j with hvdef
  have hv : v ∈ colSpan A := by
    rw [← rowSpan_transpose]
    exact adjugate_comb_mem_rowSpan Aᵀ c
  obtain ⟨w, hw⟩ := exists_span_coeff (by rw [hspan]; exact hv)
  have hvz : ∀ j : Fin k, (c : ℕ) < (j : ℕ) → v j = 0 := by
    intro j hj
    rw [hvdef]
    show ∑ r, (Aᵀ.adjugate) c r * (Aᵀ) r j = 0
    rw [adjugate_row_eq]
    have hne : ¬(c = j) := fun h => by have := congrArg Fin.val h; omega
    rw [if_neg hne, mul_zero]
  have hw0 := canonical_coeff_zero_above hH hw hvz
  have hc0 : ∑ t, w t * H c t = (A.det : ℤ) := by
    have h1 : ∑ t, w t * H c t = ∑ r, (Aᵀ.adjugate) c r * (Aᵀ) r c := hw c
    rw [adjugate_row_eq, if_pos rfl, mul_one, Matrix.det_transpose] at h1
    exact h1
  rw [Finset.sum_eq_single c (fun b _ hbc => by
      rcases Nat.lt_trichotomy (b : ℕ) (c : ℕ) with h | h | h
      · rw [hH.1 c b h, mul_zero]
      · exact absurd (Fin.ext h) hbc
      · rw [hw0 b (by omega), zero_mul])
    (fun h => absurd (Finset.mem_univ c) h)] at hc0
  exact ⟨w c, hc0.symm.trans (mul_comm _ _)⟩

theorem classicalCanonicalize_diag_dvd_det (A : IMat k) (hA : A.det ≠ 0) (c : Fin k) :
    (classicalCanonicalize A c c) ∣ (A.det : ℤ) :=
  canonical_diag_dvd_det (classicalCanonicalize_isCanonical A hA)
    (colSpan_classicalCanonicalize A hA) c

theorem classicalCanonicalize_diag_le_det (A : IMat k) (hA : A.det ≠ 0) (c : Fin k) :
    (classicalCanonicalize A c c).natAbs ≤ A.det.natAbs :=
  Int.natAbs_le_of_dvd_ne_zero (classicalCanonicalize_diag_dvd_det A hA c) hA

theorem classicalCanonicalize_entry_le_det (A : IMat k) (hA : A.det ≠ 0) (i j : Fin k) :
    (classicalCanonicalize A i j).natAbs ≤ A.det.natAbs := by
  rcases Nat.lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · have hr := (classicalCanonicalize_isCanonical A hA).2.2 i j h
    have hd := classicalCanonicalize_diag_le_det A hA i
    have hx0 : 0 ≤ classicalCanonicalize A i j := hr.1
    have hx1 : classicalCanonicalize A i j < classicalCanonicalize A i i := hr.2
    have he : (classicalCanonicalize A i j).natAbs = classicalCanonicalize A i j :=
      Int.natAbs_of_nonneg hx0
    have hd' : (classicalCanonicalize A i i).natAbs = classicalCanonicalize A i i :=
      Int.natAbs_of_nonneg (le_of_lt ((classicalCanonicalize_isCanonical A hA).2.1 i))
    omega
  · have hij : i = j := Fin.ext h
    rw [hij]
    exact classicalCanonicalize_diag_le_det A hA j
  · rw [(classicalCanonicalize_isCanonical A hA).1 i j h]
    simp

theorem classicalCanonicalize_entry_le (A : IMat k) (hA : A.det ≠ 0) (i j : Fin k) :
    (classicalCanonicalize A i j).natAbs ≤ Fintype.card (Equiv.Perm (Fin k)) * (matSup A) ^ k :=
  (classicalCanonicalize_entry_le_det A hA i j).trans (det_abs_le A)

theorem card_perm_le (k : ℕ) : Fintype.card (Equiv.Perm (Fin k)) ≤ k ^ k := by
  rw [Fintype.card_perm, Fintype.card_fin]
  exact Nat.factorial_le_pow k

theorem inputBitLength_ge_card (A : IMat k) : k * k ≤ inputBitLength A := by
  unfold inputBitLength
  have h1 : ∀ p : Fin k × Fin k, (1 : ℕ) ≤ Nat.log 2 (A p.1 p.2).natAbs + 1 := by
    intro p
    have : (0 : ℕ) ≤ Nat.log 2 (A p.1 p.2).natAbs := Nat.zero_le _
    omega
  have hsum : ∑ _p : Fin k × Fin k, (1 : ℕ) = k * k := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
  calc k * k = ∑ _p : Fin k × Fin k, 1 := hsum.symm
    _ ≤ ∑ p : Fin k × Fin k, (Nat.log 2 (A p.1 p.2).natAbs + 1) :=
        Finset.sum_le_sum (fun p _ => h1 p)

theorem classicalCanonicalize_bitBound (A : IMat k) (hA : A.det ≠ 0) (i j : Fin k) :
    (classicalCanonicalize A i j).natAbs ≤ 2 ^ (2 * (inputBitLength A) ^ 2) := by
  have hn := inputBitLength_ge_card A
  have hB : matSup A < 2 ^ (inputBitLength A) := matSup_lt_two_pow_inputBitLength A
  have hk : k ≤ inputBitLength A := by
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · omega
    · nlinarith [hn]
  have hk2 : k ≤ 2 ^ (inputBitLength A) := hk.trans Nat.lt_two_pow_self.le
  have hksq : k ^ k ≤ 2 ^ (inputBitLength A * inputBitLength A) := by
    have e1 : k ^ k ≤ (2 ^ inputBitLength A) ^ k := Nat.pow_le_pow_left hk2 k
    rw [← Nat.pow_mul] at e1
    exact e1.trans (Nat.pow_le_pow_right Nat.two_pos (Nat.mul_le_mul_left _ hk))
  have hBs : matSup A ^ k ≤ 2 ^ (inputBitLength A * inputBitLength A) := by
    have e1 : matSup A ^ k ≤ (2 ^ inputBitLength A) ^ k :=
      Nat.pow_le_pow_left hB.le k
    rw [← Nat.pow_mul] at e1
    exact e1.trans (Nat.pow_le_pow_right Nat.two_pos (Nat.mul_le_mul_left _ hk))
  refine (classicalCanonicalize_entry_le A hA i j).trans ?_
  calc Fintype.card (Equiv.Perm (Fin k)) * matSup A ^ k
      ≤ k ^ k * matSup A ^ k := Nat.mul_le_mul (card_perm_le k) (Nat.le_refl _)
    _ ≤ 2 ^ (inputBitLength A * inputBitLength A) * 2 ^ (inputBitLength A * inputBitLength A) :=
        Nat.mul_le_mul hksq hBs
    _ = 2 ^ (inputBitLength A * inputBitLength A + inputBitLength A * inputBitLength A) :=
        (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ (2 * (inputBitLength A) ^ 2) := by
        refine Nat.pow_le_pow_right Nat.two_pos ?_
        have hsq : (inputBitLength A) ^ 2 = inputBitLength A * inputBitLength A := by
          rw [Nat.pow_two]
        have hmul : inputBitLength A * k ≤ inputBitLength A * inputBitLength A :=
          Nat.mul_le_mul_left _ hk
        omega

theorem interleavedCanonicalize_entry_le_det (A : IMat k) (hA : A.det ≠ 0) (i j : Fin k) :
    (interleavedCanonicalize A i j).natAbs ≤ A.det.natAbs := by
  rw [interleavedCanonicalize_eq A hA]
  exact classicalCanonicalize_entry_le_det A hA i j

theorem interleavedCanonicalize_bitBound (A : IMat k) (hA : A.det ≠ 0) (i j : Fin k) :
    (interleavedCanonicalize A i j).natAbs ≤ 2 ^ (2 * (inputBitLength A) ^ 2) := by
  rw [interleavedCanonicalize_eq A hA]
  exact classicalCanonicalize_bitBound A hA i j

end OutputBound

end Qatlib.Concepts.HspRecovery.AbelianSampling
