/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9ExtAux
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

variable {N : Type} [Fintype N] [DecidableEq N]

theorem taylor_matrix_entry_norm_le (M : Matrix N N ℂ) (i j : N) : ‖M i j‖ ≤ ‖M‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖^2 = 1 := by
      rw [norm_toEuclidean_sq_eq_re_inner, (normalized_iff_inner_self _).mp (normalized_ket j)]
      rfl
    nlinarith [norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))]
  have hn := l2_norm_mulVec_fromVec_le M (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi :=
      PiLp.norm_apply_le (toEuclidean_fromVec (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i
  change ‖(M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i‖ ≤ ‖toEuclidean_fromVec
      (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j)‖ at hi
  have he : (M *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = M i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  rw [he] at hi
  exact hi.trans hn

theorem taylorV2_entry_norm_le (m k p : ℕ) (M : Matrix N N ℂ) (hM : ‖M‖ ≤ 1)
    (r c : Fin (m*(k+1)+p+1) × N) : ‖taylorStepMatrixV2 m k p M r c‖ ≤ 1 := by
  classical
  by_cases hrc : r=c
  · subst c
    simp [taylorStepMatrixV2]
  · by_cases hs : r.1.val < m*(k+1) ∧ 1 ≤ r.1.val%(k+1) ∧ c.1.val+1=r.1.val
    · have hj : ¬ (r.1.val ≤ m*(k+1) ∧ 0 < r.1.val ∧ (k+1) ∣ r.1.val ∧
          r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val) := by
        intro hj
        have hm := Nat.mod_eq_zero_of_dvd hj.2.2.1
        omega
      have hp : ¬ (m*(k+1) < r.1.val ∧ c.1.val+1=r.1.val) := by omega
      simp only [taylorStepMatrixV2, if_neg hrc, if_pos hs, if_neg hj, if_neg hp,
        zero_sub, sub_zero, norm_neg, norm_div, Complex.norm_natCast]
      have hd : (1 : ℝ) ≤ (r.1.val%(k+1) : ℕ) := by exact_mod_cast hs.2.1
      apply (div_le_one (by linarith : (0 : ℝ) < (r.1.val%(k+1) : ℕ))).mpr
      exact (taylor_matrix_entry_norm_le M r.2 c.2).trans (hM.trans hd)
    · by_cases hj : r.1.val ≤ m*(k+1) ∧ 0 < r.1.val ∧ (k+1) ∣ r.1.val ∧
          r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val
      · have hp : ¬ (m*(k+1) < r.1.val ∧ c.1.val+1=r.1.val) := by omega
        simp only [taylorStepMatrixV2, if_neg hrc, if_neg hs, if_pos hj, if_neg hp,
          zero_sub, sub_zero, norm_neg]
        split_ifs <;> norm_num
      · simp only [taylorStepMatrixV2, if_neg hrc, if_neg hs, if_neg hj, sub_zero]
        split_ifs <;> norm_num

private theorem taylor_label_interval_card (d a b : ℕ) :
    (Finset.univ.filter (fun l : Fin d => a ≤ l.val ∧ l.val < b)).card ≤ b-a := by
  let S := Finset.univ.filter (fun l : Fin d => a ≤ l.val ∧ l.val < b)
  have hsub : S.image Fin.val ⊆ Finset.Ico a b := by
    intro x hx
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ico] using! hl
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective,Nat.card_Ico] at hc
  exact hc

omit [Fintype N] in

private theorem taylorV2_nonzero_support (m k p : ℕ) (M : Matrix N N ℂ)
    (r c : Fin (m*(k+1)+p+1) × N) (hn : taylorStepMatrixV2 m k p M r c ≠ 0) :
    r=c ∨
    (c.1.val+1=r.1.val ∧ M r.2 c.2 ≠ 0) ∨
    (r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val ∧ r.2=c.2) ∨
    (c.1.val+1=r.1.val ∧ r.2=c.2) := by
  by_contra h
  simp only [not_or,not_and] at h
  have hs : (if r.1.val < m*(k+1) ∧ 1 ≤ r.1.val%(k+1) ∧ c.1.val+1=r.1.val
      then M r.2 c.2 / (r.1.val%(k+1) : ℕ) else 0) = (0 : ℂ) := by
    split_ifs with hs
    · rw [not_ne_iff.mp (h.2.1 hs.2.2),zero_div]
    · rfl
  have hj : (if r.1.val ≤ m*(k+1) ∧ 0 < r.1.val ∧ (k+1) ∣ r.1.val ∧
      r.1.val-(k+1) ≤ c.1.val ∧ c.1.val < r.1.val then
      (if r.2=c.2 then (1 : ℂ) else 0) else 0) = 0 := by
    split_ifs with hj he
    · exact False.elim (h.2.2.1 hj.2.2.2.1 hj.2.2.2.2 he)
    · rfl
    · rfl
  have hp : (if m*(k+1) < r.1.val ∧ c.1.val+1=r.1.val then
      (if r.2=c.2 then (1 : ℂ) else 0) else 0) = 0 := by
    split_ifs with hp he
    · exact False.elim (h.2.2.2 hp.2 he)
    · rfl
    · rfl
  exact hn (by simp only [taylorStepMatrixV2,if_neg h.1,hs,hj,hp,sub_zero])

theorem taylorV2_row_sparse (s m k p : ℕ) (M : Matrix N N ℂ)
    (hM : ∀ n, (Finset.univ.filter (fun c => M n c ≠ 0)).card ≤ s)
    (r : Fin (m*(k+1)+p+1) × N) :
    (Finset.univ.filter (fun c => taylorStepMatrixV2 m k p M r c ≠ 0)).card ≤ k+s+3 := by
  classical
  let prev : Fin (m*(k+1)+p+1) := ⟨r.1.val-1,(Nat.sub_le _ _).trans_lt r.1.isLt⟩
  let S := (Finset.univ.filter (fun n => M r.2 n ≠ 0)).image (fun n => (prev,n))
  let J := (Finset.univ.filter (fun l : Fin (m*(k+1)+p+1) =>
    r.1.val-(k+1) ≤ l.val ∧ l.val < r.1.val)).image (fun l => (l,r.2))
  have hsub : (Finset.univ.filter (fun c => taylorStepMatrixV2 m k p M r c ≠ 0)) ⊆
      ({r} ∪ S) ∪ (J ∪ {(prev,r.2)}) := by
    intro c hc
    have hn := (Finset.mem_filter.mp hc).2
    rcases taylorV2_nonzero_support m k p M r c hn with he | he | he | he
    · subst c; simp
    · have hl : c.1=prev := Fin.ext (by dsimp [prev]; omega)
      have hm : c∈S := Finset.mem_image.mpr ⟨c.2,by simp [he.2],
        by apply Prod.ext; exact hl.symm; rfl⟩
      simp only [Finset.mem_union]; exact Or.inl (Or.inr hm)
    · have hm : c∈J := Finset.mem_image.mpr ⟨c.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.1,he.2.1⟩,Prod.ext rfl he.2.2⟩
      simp only [Finset.mem_union]; exact Or.inr (Or.inl hm)
    · have hl : c.1=prev := Fin.ext (by dsimp [prev]; omega)
      have hc : c=(prev,r.2) := Prod.ext hl he.2.symm
      simp only [Finset.mem_union]; exact Or.inr (Or.inr (by simp [hc]))
  have hS : S.card ≤ s := (Finset.card_image_le).trans (hM r.2)
  have hJ : J.card ≤ k+1 := by
    exact Finset.card_image_le.trans ((taylor_label_interval_card _ _ _).trans (by omega))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hleft := Finset.card_union_le ({r} : Finset _) S
  have hright := Finset.card_union_le J ({(prev,r.2)} : Finset _)
  simp only [Finset.card_singleton] at hleft hright
  omega

theorem taylorV2_col_sparse (s m k p : ℕ) (M : Matrix N N ℂ)
    (hM : ∀ n, (Finset.univ.filter (fun r => M r n ≠ 0)).card ≤ s)
    (c : Fin (m*(k+1)+p+1) × N) :
    (Finset.univ.filter (fun r => taylorStepMatrixV2 m k p M r c ≠ 0)).card ≤ k+s+3 := by
  classical
  let next : Fin (m*(k+1)+p+1) :=
    if ht : c.1.val+1 < m*(k+1)+p+1 then ⟨c.1.val+1,ht⟩ else c.1
  let S := (Finset.univ.filter (fun n => M n c.2 ≠ 0)).image (fun n => (next,n))
  let J := (Finset.univ.filter (fun l : Fin (m*(k+1)+p+1) =>
    c.1.val+1 ≤ l.val ∧ l.val < c.1.val+(k+1)+1)).image (fun l => (l,c.2))
  have hnext (r : Fin (m*(k+1)+p+1)) (hr : c.1.val+1=r.val) : r=next := by
    have ht : c.1.val+1 < m*(k+1)+p+1 := by omega
    apply Fin.ext
    simp only [next,dif_pos ht]
    omega
  have hsub : (Finset.univ.filter (fun r => taylorStepMatrixV2 m k p M r c ≠ 0)) ⊆
      ({c} ∪ S) ∪ (J ∪ {(next,c.2)}) := by
    intro r hr
    have hn := (Finset.mem_filter.mp hr).2
    rcases taylorV2_nonzero_support m k p M r c hn with he | he | he | he
    · subst r; simp
    · have hl := hnext r.1 he.1
      have hm : r∈S := Finset.mem_image.mpr ⟨r.2,by simp [he.2],
        by apply Prod.ext; exact hl.symm; rfl⟩
      simp only [Finset.mem_union]; exact Or.inl (Or.inr hm)
    · have hm : r∈J := Finset.mem_image.mpr ⟨r.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩,Prod.ext rfl he.2.2.symm⟩
      simp only [Finset.mem_union]; exact Or.inr (Or.inl hm)
    · have hl := hnext r.1 he.1
      have hr : r=(next,c.2) := Prod.ext hl he.2
      simp only [Finset.mem_union]; exact Or.inr (Or.inr (by simp [hr]))
  have hS : S.card ≤ s := Finset.card_image_le.trans (hM c.2)
  have hJ : J.card ≤ k+1 := by
    exact Finset.card_image_le.trans ((taylor_label_interval_card _ _ _).trans (by omega))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hleft := Finset.card_union_le ({c} : Finset _) S
  have hright := Finset.card_union_le J ({(next,c.2)} : Finset _)
  simp only [Finset.card_singleton] at hleft hright
  omega

theorem taylorV2_sparse_encoding (s m k p : ℕ) (M : Matrix N N ℂ) (hM : ‖M‖ ≤ 1)
    (hr : ∀ n, (Finset.univ.filter (fun c => M n c ≠ 0)).card ≤ s)
    (hc : ∀ n, (Finset.univ.filter (fun r => M r n ≠ 0)).card ≤ s) :
    Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
      (((k+s+3 : ℕ) : ℂ)⁻¹ • taylorStepMatrixV2 m k p M) (1 : Matrix _ _ ℂ)
      (sparseOverlapLeft (taylorStepMatrixV2 m k p M) (k+s+3))
      (sparseOverlapRight (taylorStepMatrixV2 m k p M) (k+s+3)) ∧
    ‖taylorStepMatrixV2 m k p M‖ ≤ (k+s+3 : ℕ) := by
  simpa only [Complex.ofReal_one,mul_one,Nat.cast_add,Nat.cast_ofNat] using!
    sparse_overlap_derived_sparse_entry_norm_consumer _ _ (taylorStepMatrixV2 m k p M)
      (k+s+3) 1 (by norm_num) (by omega) (taylorV2_row_sparse s m k p M hr)
      (taylorV2_col_sparse s m k p M hc) (taylorV2_entry_norm_le m k p M hM)

end Qatlib.Papers.QLinearODE17.StructureCore
