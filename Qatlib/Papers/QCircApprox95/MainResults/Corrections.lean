/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.MetricCore
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Foundations.BornMetrics.FiniteStats

namespace Qatlib.Papers.QCircApprox95.MainResults

def signTwo : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def swapTwo : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem sign_unitary : signTwo ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [signTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

theorem swap_unitary : swapTwo ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]

theorem sign_first : norm2k (signTwo - 1) 1 = 0 := by
  norm_num [Subtype.ext_iff, norm2k, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, l2norm, ket, signTwo,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> rfl

theorem product_first : norm2k (signTwo * swapTwo - swapTwo) 1 = 2 := by
  norm_num [Subtype.ext_iff, norm2k, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, l2norm, ket, signTwo, swapTwo,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> rfl

theorem zero_first : norm2k (swapTwo - swapTwo) 1 = 0 := by
  norm_num [Subtype.ext_iff, norm2k, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, l2norm, ket,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> rfl

theorem weak_composition_counterexample :
    ∃ U₁ U₂ V₁ V₂ : Matrix (Fin 2) (Fin 2) ℂ,
      U₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ U₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      V₁ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ V₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      norm2k (U₁ - V₁) 1 = 0 ∧ norm2k (U₂ - V₂) 1 = 0 ∧
      norm2k (U₁ * U₂ - V₁ * V₂) 1 = 2 := by
  exact ⟨signTwo, swapTwo, 1, swapTwo, sign_unitary, swap_unitary,
    Submonoid.one_mem _, swap_unitary, sign_first, zero_first,
    by simpa only [Matrix.one_mul] using product_first⟩

theorem net_bound_counterexample :
    ¬ ∃ C : Finset (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ V ∈ C, ‖U - V‖ ≤ 4) ∧
      (C.card : ℝ) ≤ ((2 : ℝ) / 4) ^ (2 ^ (4 * 1)) := by
  rintro ⟨C, hcover, hcard⟩
  obtain ⟨V, hV, _⟩ := hcover 1 (Submonoid.one_mem _)
  have hpos : 0 < C.card := Finset.card_pos.mpr ⟨V, hV⟩
  have hge : (1 : ℝ) ≤ C.card := by exact_mod_cast hpos
  norm_num at hcard
  linarith

end Qatlib.Papers.QCircApprox95.MainResults
