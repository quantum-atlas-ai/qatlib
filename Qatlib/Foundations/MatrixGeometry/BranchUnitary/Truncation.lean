/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.BranchUnitary.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Foundations.MatrixGeometry.BranchUnitary
open Qatlib.Foundations.MatrixGeometry.LcuFrame
variable {C S : Type*} [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

omit [DecidableEq C] [DecidableEq S] in

theorem coherent_inner (α : C → ℂ) (φ ψ : C → State S) :
    Inner (coherent α φ) (coherent α ψ) =
      ∑ c, ((‖α c‖ ^ 2 : ℝ) : ℂ) * Inner (φ c) (ψ c) := by
  rw [inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hn : (starRingEnd ℂ) (α c) * α c = ((‖α c‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [coherent, map_mul]
  calc
    _ = ((starRingEnd ℂ) (α c) * α c) *
        ((starRingEnd ℂ) (φ c s) * ψ c s) := by ring
    _ = _ := by rw [hn]

theorem branch_real_overlap (U : Matrix S S ℂ) (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (φ : State S) (hφ : Normalized φ) : -1 ≤ (Inner (U *ᵥ φ) φ).re := by
  have hn : ‖Inner (U *ᵥ φ) φ‖ ≤ 1 := by
    rw [← inner_toHilbert]
    calc
      _ ≤ ‖toHilbert (U *ᵥ φ)‖ * ‖toHilbert φ‖ := norm_inner_le_norm _ _
      _ = 1 := by
        rw [(normalized_iff_hilbert _).1 (unitary_normalized U hU φ hφ),
          (normalized_iff_hilbert _).1 hφ]
        norm_num
  have hr := (abs_le.mp (Complex.abs_re_le_norm (Inner (U *ᵥ φ) φ))).1
  linarith

def tailMass (α : C → ℂ) (q : C → ℕ) (cutoff : ℕ) : ℝ :=
  ∑ c, if cutoff < q c then ‖α c‖ ^ 2 else 0

theorem truncation_real_overlap (U : C → Matrix S S ℂ)
    (hU : ∀ c, U c ∈ Matrix.unitaryGroup S ℂ) (α : C → ℂ) (φ : C → State S)
    (hα : ∑ c, ‖α c‖ ^ 2 = 1) (hφ : ∀ c, Normalized (φ c))
    (q : C → ℕ) (cutoff : ℕ) :
    1 - 2 * tailMass α q cutoff ≤
      (Inner (controlled U *ᵥ coherent α φ)
        (controlled (truncated U q cutoff) *ᵥ coherent α φ)).re := by
  rw [controlled_coherent, controlled_coherent, coherent_inner, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hb : ∀ c, ‖α c‖ ^ 2 - 2 * (if cutoff < q c then ‖α c‖ ^ 2 else 0) ≤
      ‖α c‖ ^ 2 * (Inner (U c *ᵥ φ c) (truncated U q cutoff c *ᵥ φ c)).re := by
    intro c
    by_cases h : q c ≤ cutoff
    · have hi : Inner (U c *ᵥ φ c) (U c *ᵥ φ c) = 1 :=
        (normalized_iff_inner _).1 (unitary_normalized _ (hU c) _ (hφ c))
      simp [truncated, h, Nat.not_lt.mpr h, hi]
    · have ht : cutoff < q c := Nat.lt_of_not_ge h
      simp only [truncated, if_neg h, Matrix.one_mulVec, if_pos ht]
      have hp := branch_real_overlap (U c) (hU c) (φ c) (hφ c)
      have hw := sq_nonneg ‖α c‖
      nlinarith
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hb c)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hα, tailMass] using hs

theorem truncation_hilbert_overlap (U : C → Matrix S S ℂ)
    (hU : ∀ c, U c ∈ Matrix.unitaryGroup S ℂ) (α : C → ℂ) (φ : C → State S)
    (hα : ∑ c, ‖α c‖ ^ 2 = 1) (hφ : ∀ c, Normalized (φ c))
    (q : C → ℕ) (cutoff : ℕ) :
    ‖toHilbert (controlled U *ᵥ coherent α φ)‖ = 1 ∧
      ‖toHilbert (controlled (truncated U q cutoff) *ᵥ coherent α φ)‖ = 1 ∧
      1 - 2 * tailMass α q cutoff ≤
        ‖inner ℂ (toHilbert (controlled U *ᵥ coherent α φ))
          (toHilbert (controlled (truncated U q cutoff) *ᵥ coherent α φ))‖ := by
  have hp := coherent_normalized α φ hα hφ
  refine ⟨(normalized_iff_hilbert _).1 (unitary_normalized _ (controlled_unitary U hU) _ hp),
    (normalized_iff_hilbert _).1
      (unitary_normalized _ (truncated_controlled_unitary U hU q cutoff) _ hp), ?_⟩
  rw [inner_toHilbert]
  exact (truncation_real_overlap U hU α φ hα hφ q cutoff).trans (Complex.re_le_norm _)

def meanQueries (α : C → ℂ) (q : C → ℕ) : ℝ := ∑ c, ‖α c‖ ^ 2 * (q c : ℝ)

omit [DecidableEq C] in

theorem tailMass_le_mean (α : C → ℂ) (q : C → ℕ) (cutoff : ℕ) (hcut : 0 < cutoff) :
    tailMass α q cutoff ≤ meanQueries α q / cutoff := by
  have hc : (0 : ℝ) < cutoff := by exact_mod_cast hcut
  apply (le_div_iff₀ hc).2
  unfold tailMass meanQueries
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  by_cases h : cutoff < q c
  · simp only [if_pos h]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact_mod_cast Nat.le_of_lt h
  · simp only [if_neg h, zero_mul]
    positivity

end Qatlib.Foundations.MatrixGeometry.BranchUnitary
