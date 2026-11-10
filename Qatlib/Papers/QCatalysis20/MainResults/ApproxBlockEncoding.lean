/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.Definitions
import Qatlib.Papers.QCatalysis20.MainResults.RoundedProbabilities
import Qatlib.Papers.QCatalysis20.MainResults.PrepSelect
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Papers.QCatalysis20.MainResults.ApproxPrep
variable {J I G : Type} [Fintype J] [Fintype I] [Fintype G]
  [DecidableEq J] [DecidableEq I] [DecidableEq G]

def mass (a : J→ℝ) : ℝ := ∑j,|a j|

def weights (a : J→ℝ) : J→ℝ := fun j=>|a j|/mass a

def signedSelect (a : J→ℝ) (U : J→Matrix I I ℂ) : J→Matrix I I ℂ :=
  fun j=>if a j < 0 then -(U j) else U j

def weighted (p : J→ℝ) (U : J→Matrix I I ℂ) : Matrix I I ℂ := ∑j,(p j:ℂ)•U j

omit [DecidableEq J] in

theorem mass_positive (a : J→ℝ) (ha : ∃j,a j≠0) : 0 < mass a := by
  obtain ⟨j,hj⟩:=ha
  exact Finset.sum_pos' (fun i _=>abs_nonneg (a i)) ⟨j,Finset.mem_univ j,abs_pos.mpr hj⟩

omit [DecidableEq J] in

theorem weights_probability (a : J→ℝ) (ha : 0 < mass a) :
    (∀j,0 ≤ weights a j) ∧ ∑j,weights a j=1 := by
  refine ⟨fun j=>div_nonneg (abs_nonneg _) ha.le,?_⟩
  simp only [weights,← Finset.sum_div]
  exact div_self ha.ne'

omit [Fintype J] [DecidableEq J] in

theorem signedSelect_unitary (a : J→ℝ) (U : J→Matrix I I ℂ)
    (hU : ∀j,U j∈unitaryGroup I ℂ) : ∀j,signedSelect a U j∈unitaryGroup I ℂ := by
  intro j
  unfold signedSelect
  split_ifs
  · rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
    simpa only [Matrix.conjTranspose_neg,neg_mul,mul_neg,neg_neg] using
      (show (U j)ᴴ*U j=1 by simpa only [Matrix.star_eq_conjTranspose] using (hU j).1)
  · exact hU j

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

theorem weighted_exact (a : J→ℝ) (U : J→Matrix I I ℂ) :
    weighted (weights a) (signedSelect a U)=lcuOperator (fun j=>(a j/mass a:ℝ)) U := by
  apply Finset.sum_congr rfl
  intro j _
  unfold weights signedSelect
  split_ifs with h
  · rw [abs_of_neg h]
    simp only [neg_div,Complex.ofReal_neg,smul_neg,neg_smul,neg_neg]
  · rw [abs_of_nonneg (le_of_not_gt h)]

omit [DecidableEq J] in

theorem weighted_error (p w : J→ℝ) (U : J→Matrix I I ℂ)
    (hU : ∀j,U j∈unitaryGroup I ℂ) :
    ‖weighted p U-weighted w U‖ ≤ ∑j,|p j-w j| := by
  have he : weighted p U-weighted w U=∑j,((p j-w j:ℝ):ℂ)•U j := by
    simp only [weighted,← Finset.sum_sub_distrib,Complex.ofReal_sub,sub_smul]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (unitary_norm_le_one (hU j)) (abs_nonneg _)).trans_eq (mul_one _)

theorem actual_rounded_block_encoding {n : ℕ} (μ : ℕ) (a : Fin (n+1)→ℝ)
    (ha : ∃j,a j≠0) (U : Fin (n+1)→Matrix I I ℂ) (hU : ∀j,U j∈unitaryGroup I ℂ)
    (g : Fin (n+1)→G→ℂ) (hg : ∀j,∑k,star (g j k)*g j k=1)
    (zero : Fin (n+1)×G) :
    let p:=Rounding.rounded (Rounding.denominator n μ) (weights a)
    ∃P : Matrix (Fin (n+1)×G) (Fin (n+1)×G) ℂ,
      P∈unitaryGroup _ ℂ ∧ (∀w,P w zero=PrepSelect.garbageColumn p g w) ∧
      BlockEncoding (lcuOperator (fun j=>(a j/mass a:ℝ)) U)
        (PrepSelect.circuit P (fun w=>signedSelect a U w.1))
        (PrepSelect.frame zero) (PrepSelect.frame zero) 1 ((2:ℝ)^(-(μ:ℤ))) := by
  let p:=Rounding.rounded (Rounding.denominator n μ) (weights a)
  obtain ⟨hw,hs⟩:=weights_probability a (mass_positive a ha)
  have hp : ∀j,0 ≤ p j := Rounding.rounded_nonneg (Rounding.denominator_pos n μ) _ hw hs
  have hsum : ∑j,p j=1 := Rounding.rounded_sum _
  obtain ⟨P,hP,hcol⟩:=PrepSelect.exists_prepare (PrepSelect.garbageColumn p g) zero
    (PrepSelect.garbageColumn_normalized p hp hsum g hg)
  refine ⟨P,hP,hcol,PrepSelect.circuit_unitary hP _ (fun w=>signedSelect_unitary a U hU w.1),
    PrepSelect.frame_isometry _,PrepSelect.frame_isometry _,by norm_num,by positivity,?_⟩
  rw [one_smul,PrepSelect.garbage_compression p hp g hg P zero hcol]
  rw [← weighted_exact a U,norm_sub_rev]
  exact (weighted_error p (weights a) (signedSelect a U) (signedSelect_unitary a U hU)).trans
    (Rounding.actual_precision μ (weights a) hw hs)

theorem actual_clean_block_encoding {n : ℕ} (μ : ℕ) (a : Fin (n+1)→ℝ)
    (ha : ∃j,a j≠0) (U : Fin (n+1)→Matrix I I ℂ) (hU : ∀j,U j∈unitaryGroup I ℂ) :
    ∃P : Matrix (Fin (n+1)×Fin 1) (Fin (n+1)×Fin 1) ℂ,
      P∈unitaryGroup _ ℂ ∧ BlockEncoding (lcuOperator (fun j=>(a j/mass a:ℝ)) U)
        (PrepSelect.circuit P (fun w=>signedSelect a U w.1))
        (PrepSelect.frame (0,0)) (PrepSelect.frame (0,0)) 1 ((2:ℝ)^(-(μ:ℤ))) := by
  obtain ⟨P,hP,_,he⟩:=actual_rounded_block_encoding μ a ha U hU (fun (_ : Fin (n+1)) (_ : Fin 1)=>(1:ℂ))
    (fun _=>by simp) (0,0)
  exact ⟨P,hP,he⟩

end Qatlib.Papers.QCatalysis20.MainResults.ApproxPrep
