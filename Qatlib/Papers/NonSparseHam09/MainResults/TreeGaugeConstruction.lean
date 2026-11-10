/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Prop1TreeGauge
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {H : Matrix ι ι ℂ}

def edgePhase (H : Matrix ι ι ℂ) (i j : ι) : ℂ :=
  if H i j = 0 then 1 else H i j / (‖H i j‖ : ℂ)

lemma edgePhase_norm_eq_one (H : Matrix ι ι ℂ) (i j : ι) : ‖edgePhase H i j‖ = 1 := by
  by_cases h : H i j = 0
  · simp [edgePhase, h]
  · rw [edgePhase, if_neg h, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (ne_of_gt (norm_pos_iff.mpr h))

lemma edgePhase_of_ne (H : Matrix ι ι ℂ) (i j : ι) (h : H i j ≠ 0) :
    edgePhase H i j = H i j / (‖H i j‖ : ℂ) := by
  rw [edgePhase, if_neg h]

lemma star_mul_self_eq_sq (z : ℂ) : star z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  rw [mul_comm]
  exact RCLike.mul_conj z

lemma self_mul_star_eq_sq (z : ℂ) : z * star z = ((‖z‖ : ℝ) : ℂ) ^ 2 :=
  RCLike.mul_conj z

lemma div_star_mul_self (z : ℂ) (hz : z ≠ 0) :
    (star z / ((‖z‖ : ℝ) : ℂ)) * z = ((‖z‖ : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hrne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  rw [div_mul_eq_mul_div, star_mul_self_eq_sq]
  field_simp

lemma mul_star_div_self (z : ℂ) (hz : z ≠ 0) :
    z * star (z / ((‖z‖ : ℝ) : ℂ)) = ((‖z‖ : ℝ) : ℂ) := by
  have hpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hrne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hsr : star (((‖z‖ : ℝ)) : ℂ) = ((‖z‖ : ℝ) : ℂ) := by
    simp
  rw [star_div₀, hsr, ← mul_div_assoc, self_mul_star_eq_sq]
  field_simp

lemma gauge_cancel_mid (a b c : ℂ) (ha : a * star a = 1) :
    (a * b) * c * star a = b * c := by
  have h : (a * b) * c * star a = (b * c) * (a * star a) := by ring
  rw [h, ha, mul_one]

lemma gauge_cancel_left (a b c : ℂ) (ha : a * star a = 1) :
    a * b * (c * star a) = b * c := by
  have h : a * b * (c * star a) = (b * c) * (a * star a) := by ring
  rw [h, ha, mul_one]

structure RootedForest (H : Matrix ι ι ℂ) where

  parent : ι → ι

  depth : ι → ℕ

  parent_depth : ∀ i, parent i ≠ i → depth (parent i) < depth i

  parent_edge : ∀ i, parent i ≠ i → H i (parent i) ≠ 0

  edge_parent : ∀ i j, i ≠ j → (H i j ≠ 0 ∨ H j i ≠ 0) → j = parent i ∨ i = parent j

  diag_zero : ∀ i, H i i = 0

namespace RootedForest

noncomputable def gauge (F : RootedForest H) (i : ι) : ℂ :=
  if h : F.parent i = i then 1
  else gauge F (F.parent i) * edgePhase H (F.parent i) i
termination_by F.depth i
decreasing_by exact F.parent_depth i h

lemma gauge_eq_root (F : RootedForest H) {i : ι} (h : F.parent i = i) : F.gauge i = 1 := by
  rw [gauge]
  simp only [dif_pos h]

lemma gauge_eq_child (F : RootedForest H) {i : ι} (h : F.parent i ≠ i) :
    F.gauge i = F.gauge (F.parent i) * edgePhase H (F.parent i) i := by
  rw [gauge]
  simp only [dif_neg h]

lemma gauge_norm_eq_one (F : RootedForest H) (i : ι) : ‖F.gauge i‖ = 1 := by
  classical
  have key : ∀ d, ∀ i : ι, F.depth i = d → ‖F.gauge i‖ = 1 := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro i hi
      by_cases h : F.parent i = i
      · rw [F.gauge_eq_root h]
        simp
      · rw [F.gauge_eq_child h, norm_mul, edgePhase_norm_eq_one,
          ih (F.depth (F.parent i)) (by rw [← hi]; exact F.parent_depth i h) (F.parent i) rfl,
          mul_one]
  exact key (F.depth i) i rfl

lemma gauge_mul_star (F : RootedForest H) (i : ι) :
    F.gauge i * star (F.gauge i) = 1 := by
  have hz : F.gauge i * star (F.gauge i) = (‖F.gauge i‖ : ℂ) ^ 2 := RCLike.mul_conj _
  rw [hz, F.gauge_norm_eq_one i]
  norm_num

lemma gauge_entry_identity (F : RootedForest H) (hH : H.IsHermitian) (i j : ι) :
    F.gauge i * H i j * star (F.gauge j) = ((‖H i j‖ : ℝ) : ℂ) := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [F.diag_zero i]
    simp
  · by_cases hz : H i j = 0
    · rw [hz]
      simp
    · have hedge : j = F.parent i ∨ i = F.parent j :=
        F.edge_parent i j hij (Or.inl hz)
      rcases hedge with hj | hi
      · subst hj
        have hp : F.parent i ≠ i := fun he => hij he.symm
        rw [F.gauge_eq_child hp]
        have hpi : H (F.parent i) i ≠ 0 := by
          rw [← hH.apply (F.parent i) i]
          exact star_ne_zero.mpr (F.parent_edge i hp)
        rw [edgePhase_of_ne H (F.parent i) i hpi]
        rw [show H (F.parent i) i = star (H i (F.parent i)) from
          (hH.apply (F.parent i) i).symm, norm_star]
        rw [gauge_cancel_mid (F.gauge (F.parent i)) (star (H i (F.parent i)) / ((‖H i (F.parent i)‖ : ℝ) : ℂ))
          (H i (F.parent i)) (F.gauge_mul_star (F.parent i))]
        exact div_star_mul_self (H i (F.parent i)) hz
      · subst hi
        have hp : F.parent j ≠ j := fun he => hij he
        rw [F.gauge_eq_child hp, star_mul]
        rw [edgePhase_of_ne H (F.parent j) j hz]
        rw [gauge_cancel_left (F.gauge (F.parent j)) (H (F.parent j) j)
          (star (H (F.parent j) j / ((‖H (F.parent j) j‖ : ℝ) : ℂ)))
          (F.gauge_mul_star (F.parent j))]
        exact mul_star_div_self (H (F.parent j) j) hz

end RootedForest

theorem prop1_tree_conj (hH : H.IsHermitian) (F : RootedForest H) :
    Matrix.diagonal F.gauge * H * (Matrix.diagonal F.gauge)ᴴ
      = (absMatrix H).map Complex.ofReal := by
  have hentry : ∀ i j, F.gauge i * H i j * star (F.gauge j) = ((‖H i j‖ : ℝ) : ℂ) :=
    fun i j => F.gauge_entry_identity hH i j
  exact diagonal_gauge_eq_abs F.gauge H hentry

theorem prop1_tree_specNorm (hH : H.IsHermitian) (F : RootedForest H) :
    specNorm ((absMatrix H).map Complex.ofReal) = specNorm H := by
  have hunit : ∀ i, ‖F.gauge i‖ = 1 := fun i => F.gauge_norm_eq_one i
  have hU : Matrix.diagonal F.gauge ∈ Matrix.unitaryGroup ι ℂ :=
    diagonal_mem_unitaryGroup F.gauge hunit
  have hentry : ∀ i j, F.gauge i * H i j * star (F.gauge j) = ((‖H i j‖ : ℝ) : ℂ) :=
    fun i j => F.gauge_entry_identity hH i j
  exact specNorm_abs_of_gauge (Matrix.diagonal F.gauge) H hU
    (diagonal_gauge_eq_abs F.gauge H hentry)

end Qatlib.Papers.NonSparseHam09.MainResults
