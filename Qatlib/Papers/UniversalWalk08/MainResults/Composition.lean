/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Qatlib.Papers.UniversalWalk08.MainResults.Composition

set_option autoImplicit false

structure ScatterBlock (E : Type*) where

  T : E

  Tbar : E

  R : E

  Rbar : E

namespace ScatterBlock

variable {E : Type*} [NormedRing E]

noncomputable def compose (S₁ S₂ : ScatterBlock E) : ScatterBlock E where
  T := S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.T
  Tbar := S₂.Tbar * Ring.inverse (1 - S₁.Rbar * S₂.R) * S₁.Tbar
  R := S₁.R + S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.R * S₁.Tbar
  Rbar := S₂.Rbar + S₂.Tbar * Ring.inverse (1 - S₁.Rbar * S₂.R) * S₁.Rbar * S₂.T

def perfect (g : E) : ScatterBlock E :=
  ⟨g, g, 0, 0⟩

theorem compose_perfect_T (S : ScatterBlock E) (g : E) :
    (S.compose (perfect g)).T = S.T * g := by
  simp [compose, perfect, Ring.inverse_one]

theorem compose_perfect_R (S : ScatterBlock E) :
    (S.compose (perfect 0)).R = S.R := by
  simp [compose, perfect, Ring.inverse_one]

theorem perfect_compose_T (g : E) (S : ScatterBlock E) :
    ((perfect g).compose S).T = g * S.T := by
  simp [compose, perfect, Ring.inverse_one]

noncomputable def composeList : List (ScatterBlock E) → ScatterBlock E
  | [] => ⟨1, 1, 0, 0⟩
  | S :: Ss => S.compose (composeList Ss)

theorem composeList_T_of_perfect (gs : List E) :
    (composeList (gs.map perfect)).T = gs.prod := by
  induction gs with
  | nil => simp [composeList]
  | cons g gs ih =>
    simp only [List.map_cons, composeList, perfect_compose_T, ih, List.prod_cons]

theorem composeList_R_of_perfect (gs : List E) :
    (composeList (gs.map perfect)).R = 0 := by
  induction gs with
  | nil => simp [composeList]
  | cons g gs ih =>
    simp only [List.map_cons, composeList]
    have hstep : ((perfect g).compose (composeList (List.map perfect gs))).R = 0 := by
      simp [compose, perfect, ih, Ring.inverse_one]
    exact hstep

theorem composeList_perfect (gs : List E) :
    (composeList (gs.map perfect)).T = gs.prod ∧
      (composeList (gs.map perfect)).R = 0 :=
  ⟨composeList_T_of_perfect gs, composeList_R_of_perfect gs⟩

end ScatterBlock

section NormBounds

variable {E : Type*} [NormedRing E] [NormOneClass E] [HasSummableGeomSeries E]

theorem norm_inverse_one_sub_le {x : E} (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x)‖ ≤ (1 - ‖x‖)⁻¹ := by
  rw [← geom_series_eq_inverse x hx]
  have h := tsum_geometric_le_of_norm_lt_one x hx
  simpa [norm_one] using h

theorem norm_inverse_one_sub_sub_one_le {x : E} (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x) - 1‖ ≤ ‖x‖ * (1 - ‖x‖)⁻¹ := by
  have hmul : Ring.inverse (1 - x) * (1 - x) = 1 := by
    rw [← geom_series_eq_inverse x hx]
    exact geom_series_mul_neg x hx
  have hkey : Ring.inverse (1 - x) - 1 = Ring.inverse (1 - x) * x := by
    have h0 := hmul
    rw [mul_sub, mul_one] at h0
    rw [sub_eq_iff_eq_add] at h0 ⊢
    exact h0.trans (add_comm _ _)
  rw [hkey]
  calc ‖Ring.inverse (1 - x) * x‖
      ≤ ‖Ring.inverse (1 - x)‖ * ‖x‖ := norm_mul_le _ _
    _ ≤ (1 - ‖x‖)⁻¹ * ‖x‖ := by
        gcongr
        exact norm_inverse_one_sub_le hx
    _ = ‖x‖ * (1 - ‖x‖)⁻¹ := by ring

theorem mul_inv_le_of_le {u v : ℝ} (huv : u ≤ v) (hv : v < 1) :
    u * (1 - u)⁻¹ ≤ v * (1 - v)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ h1u h1v]
  nlinarith

theorem norm_compose_T_sub_le (S₁ S₂ : ScatterBlock E) {δ : ℝ}
    (hxδ : ‖S₂.R * S₁.Rbar‖ ≤ δ) (hδ1 : δ < 1) :
    ‖(S₁.compose S₂).T - S₁.T * S₂.T‖ ≤
      ‖S₁.T‖ * ‖S₂.T‖ * (δ * (1 - δ)⁻¹) := by
  have hx1 : ‖S₂.R * S₁.Rbar‖ < 1 := lt_of_le_of_lt hxδ hδ1
  unfold ScatterBlock.compose
  rw [show S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.T - S₁.T * S₂.T =
      S₁.T * (Ring.inverse (1 - S₂.R * S₁.Rbar) - 1) * S₂.T by noncomm_ring]
  have hstep : ‖S₁.T * (Ring.inverse (1 - S₂.R * S₁.Rbar) - 1) * S₂.T‖ ≤
      ‖S₁.T‖ * (‖S₂.R * S₁.Rbar‖ * (1 - ‖S₂.R * S₁.Rbar‖)⁻¹) * ‖S₂.T‖ := by
    calc ‖S₁.T * (Ring.inverse (1 - S₂.R * S₁.Rbar) - 1) * S₂.T‖
        ≤ ‖S₁.T * (Ring.inverse (1 - S₂.R * S₁.Rbar) - 1)‖ * ‖S₂.T‖ := norm_mul_le _ _
      _ ≤ (‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar) - 1‖) * ‖S₂.T‖ := by
          gcongr
          exact norm_mul_le _ _
      _ ≤ (‖S₁.T‖ * (‖S₂.R * S₁.Rbar‖ * (1 - ‖S₂.R * S₁.Rbar‖)⁻¹)) * ‖S₂.T‖ := by
          gcongr
          exact norm_inverse_one_sub_sub_one_le hx1
      _ = ‖S₁.T‖ * (‖S₂.R * S₁.Rbar‖ * (1 - ‖S₂.R * S₁.Rbar‖)⁻¹) * ‖S₂.T‖ := by
          ring
  refine hstep.trans ?_
  have hmono := mul_inv_le_of_le hxδ hδ1
  calc ‖S₁.T‖ * (‖S₂.R * S₁.Rbar‖ * (1 - ‖S₂.R * S₁.Rbar‖)⁻¹) * ‖S₂.T‖
      = ‖S₁.T‖ * ‖S₂.T‖ * (‖S₂.R * S₁.Rbar‖ * (1 - ‖S₂.R * S₁.Rbar‖)⁻¹) := by
        ring
    _ ≤ ‖S₁.T‖ * ‖S₂.T‖ * (δ * (1 - δ)⁻¹) :=
        mul_le_mul_of_nonneg_left hmono (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem norm_compose_R_le {δ₁ δ₂ : ℝ} (S₁ S₂ : ScatterBlock E)
    (hδ₂0 : 0 ≤ δ₂)
    (hR₁ : ‖S₁.R‖ ≤ δ₁) (hRb₁ : ‖S₁.Rbar‖ ≤ δ₁) (hR₂ : ‖S₂.R‖ ≤ δ₂)
    (hT₁ : ‖S₁.T‖ ≤ 1) (hTb₁ : ‖S₁.Tbar‖ ≤ 1)
    (hδ : δ₁ * δ₂ < 1) :
    ‖(S₁.compose S₂).R‖ ≤ δ₁ + δ₂ * (1 - δ₁ * δ₂)⁻¹ := by
  have hxδ : ‖S₂.R * S₁.Rbar‖ ≤ δ₂ * δ₁ := by
    calc ‖S₂.R * S₁.Rbar‖ ≤ ‖S₂.R‖ * ‖S₁.Rbar‖ := norm_mul_le _ _
      _ ≤ δ₂ * δ₁ := mul_le_mul hR₂ hRb₁ (norm_nonneg _) hδ₂0
  have hx1 : ‖S₂.R * S₁.Rbar‖ < 1 := lt_of_le_of_lt hxδ (by linarith)
  have hinv : ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ ≤ (1 - δ₁ * δ₂)⁻¹ := by
    have hpos : 0 < 1 - ‖S₂.R * S₁.Rbar‖ := by
      have := norm_nonneg (S₂.R * S₁.Rbar); linarith
    have hpos' : 0 < 1 - δ₁ * δ₂ := by linarith
    refine (norm_inverse_one_sub_le hx1).trans ?_
    exact (inv_le_inv₀ hpos hpos').mpr (by linarith)
  have hinv0 : 0 ≤ (1 - δ₁ * δ₂)⁻¹ := inv_nonneg.2 (by linarith)
  unfold ScatterBlock.compose
  refine (norm_add_le _ _).trans (add_le_add hR₁ ?_)
  have hnorm : ‖S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.R * S₁.Tbar‖
      ≤ ‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ * ‖S₂.R‖ * ‖S₁.Tbar‖ := by
    calc ‖S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.R * S₁.Tbar‖
        ≤ ‖S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar) * S₂.R‖ * ‖S₁.Tbar‖ :=
          norm_mul_le _ _
      _ ≤ (‖S₁.T * Ring.inverse (1 - S₂.R * S₁.Rbar)‖ * ‖S₂.R‖) * ‖S₁.Tbar‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖) * ‖S₂.R‖) * ‖S₁.Tbar‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            (norm_nonneg _)
      _ = ‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ * ‖S₂.R‖ * ‖S₁.Tbar‖ := by
          ring
  refine hnorm.trans ?_
  have step1 : ‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ ≤
      1 * (1 - δ₁ * δ₂)⁻¹ :=
    mul_le_mul hT₁ hinv (norm_nonneg _) (by norm_num)
  have step2 : ‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ * ‖S₂.R‖ ≤
      1 * (1 - δ₁ * δ₂)⁻¹ * δ₂ :=
    mul_le_mul step1 hR₂ (norm_nonneg _) (mul_nonneg (by norm_num) hinv0)
  have step3 : ‖S₁.T‖ * ‖Ring.inverse (1 - S₂.R * S₁.Rbar)‖ * ‖S₂.R‖ * ‖S₁.Tbar‖ ≤
      1 * (1 - δ₁ * δ₂)⁻¹ * δ₂ * 1 :=
    mul_le_mul step2 hTb₁ (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hinv0) hδ₂0)
  refine step3.trans (le_of_eq ?_)
  ring

end NormBounds

section Matrices

open scoped Matrix.Norms.Operator

theorem matrix_norm_compose_T_sub_le {N : ℕ} [NeZero N]
    (S₁ S₂ : ScatterBlock (Matrix (Fin N) (Fin N) ℂ)) {δ : ℝ}
    (hxδ : ‖S₂.R * S₁.Rbar‖ ≤ δ) (hδ1 : δ < 1) :
    ‖(S₁.compose S₂).T - S₁.T * S₂.T‖ ≤
      ‖S₁.T‖ * ‖S₂.T‖ * (δ * (1 - δ)⁻¹) :=
  norm_compose_T_sub_le S₁ S₂ hxδ hδ1

end Matrices

end Qatlib.Papers.UniversalWalk08.MainResults.Composition
