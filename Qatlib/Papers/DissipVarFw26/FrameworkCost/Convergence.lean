/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipVarFw26.FrameworkCost.PL
import Mathlib.Algebra.Order.Floor.Ring
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped RealInnerProductSpace

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence

open Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent
open Qatlib.Papers.DissipVarFw26.FrameworkCost.PL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem theorem1_geometric_decay
    (C : E → ℝ) (β μ Cstar : ℝ) (hβ : 0 < β) (hsmooth : SmoothGrad C β)
    (hpl : PLCond C μ Cstar) (hmin : ∀ x, Cstar ≤ C x) (_hμ0 : 0 < μ) (hμβ : μ ≤ β)
    (θ0 : E) (t : ℕ) :
    C (gdIter C (1 / β) θ0 t) - Cstar ≤
      Real.exp (-(μ / β * (t : ℝ))) * (C θ0 - Cstar) := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hμη : (1 / β) * μ ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hβ]
    exact hμβ
  have hthis := lemma3_pl_contraction C β (1 / β) μ Cstar hβ hsmooth
    (one_div_pos.mpr hβ) (le_refl _) hpl hmin hμη θ0 t
  have harg : -((1 / β) * μ * (t : ℝ)) = -(μ / β * (t : ℝ)) := by
    simp only [div_eq_mul_inv, one_mul]
    ring
  simpa only [harg] using hthis

theorem theorem1_iteration_bound
    (Δ0 ε β μ : ℝ) (hβ : 0 < β) (hμ0 : 0 < μ) (hΔ0 : 0 < Δ0) (hε : 0 < ε) :
    Real.exp (-(μ / β * ((β / μ) * Real.log (Δ0 / ε)))) * Δ0 ≤ ε := by
  have hμne : μ ≠ 0 := ne_of_gt hμ0
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hpos : 0 < Δ0 / ε := div_pos hΔ0 hε
  have harg : μ / β * ((β / μ) * Real.log (Δ0 / ε)) = Real.log (Δ0 / ε) := by
    have hβμ : β / μ * (μ / β) = 1 := by
      field_simp [ne_of_gt hβ, ne_of_gt hμ0]
    calc μ / β * ((β / μ) * Real.log (Δ0 / ε))
        = (β / μ * (μ / β)) * Real.log (Δ0 / ε) := by ring
      _ = Real.log (Δ0 / ε) := by rw [hβμ, one_mul]
  rw [harg, Real.exp_neg, Real.exp_log hpos]
  have heq : (Δ0 / ε)⁻¹ * Δ0 = ε := by
    field_simp [ne_of_gt hε, ne_of_gt hΔ0]
  calc (Δ0 / ε)⁻¹ * Δ0 = ε := heq
    _ ≤ ε := le_refl ε

theorem theorem1_poly_iterations
    (P Q β μ Δ0 ε : ℝ) (hβ : 0 < β) (hμ0 : 0 < μ) (_hΔ0 : 0 < Δ0) (hε : 0 < ε)
    (hP0 : 0 ≤ P) (hεle : ε ≤ Δ0)
    (hβμ : β / μ ≤ P) (hlog : Real.log (Δ0 / ε) ≤ Q) :
    (β / μ) * Real.log (Δ0 / ε) ≤ P * Q := by
  have hβμ0 : 0 ≤ β / μ := le_of_lt (div_pos hβ hμ0)
  have hlog0 : 0 ≤ Real.log (Δ0 / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    linarith
  exact mul_le_mul hβμ hlog hlog0 hP0

def precisionSteps (β μ Δ0 ε : ℝ) : ℕ :=
  Nat.ceil ((β / μ) * Real.log (Δ0 / ε))

theorem theorem1_actual_precision
    (C : E → ℝ) (β μ Cstar : ℝ) (hβ : 0 < β) (hsmooth : SmoothGrad C β)
    (hpl : PLCond C μ Cstar) (hmin : ∀ x, Cstar ≤ C x) (hμ0 : 0 < μ) (hμβ : μ ≤ β)
    (θ0 : E) (hΔ0 : 0 < C θ0 - Cstar) (ε : ℝ) (hε : 0 < ε) :
    C (gdIter C (1 / β) θ0 (precisionSteps β μ (C θ0 - Cstar) ε)) - Cstar ≤ ε := by
  have ht : (β / μ) * Real.log ((C θ0 - Cstar) / ε) ≤
      (precisionSteps β μ (C θ0 - Cstar) ε : ℝ) := Nat.le_ceil _
  have he := Real.exp_le_exp.mpr
    (neg_le_neg (mul_le_mul_of_nonneg_left ht (div_pos hμ0 hβ).le))
  exact (theorem1_geometric_decay C β μ Cstar hβ hsmooth hpl hmin hμ0 hμβ θ0 _).trans
    ((mul_le_mul_of_nonneg_right he hΔ0.le).trans
      (theorem1_iteration_bound (C θ0 - Cstar) ε β μ hβ hμ0 hΔ0 hε))

theorem precisionSteps_lt_poly (P β μ Δ0 ε : ℝ) (hβ : 0 < β) (hμ : 0 < μ)
    (hε : 0 < ε) (hεle : ε ≤ Δ0) (hβμ : β / μ ≤ P) :
    (precisionSteps β μ Δ0 ε : ℝ) < P * Real.log (Δ0 / ε) + 1 := by
  have hl : 0 ≤ Real.log (Δ0 / ε) := Real.log_nonneg
    ((le_div_iff₀ hε).mpr (by simpa using hεle))
  exact (Nat.ceil_lt_add_one (mul_nonneg (div_pos hβ hμ).le hl)).trans_le
    (add_le_add (mul_le_mul_of_nonneg_right hβμ hl) (le_refl 1))

theorem theorem1_global_convergence
    (C : E → ℝ) (β μ Cstar : ℝ) (hβ : 0 < β) (hsmooth : SmoothGrad C β)
    (hpl : PLCond C μ Cstar) (hmin : ∀ x, Cstar ≤ C x) (hμ0 : 0 < μ) (hμβ : μ ≤ β)
    (θ0 : E) (hΔ0 : 0 < C θ0 - Cstar) :
    (∀ t : ℕ, C (gdIter C (1 / β) θ0 t) - Cstar ≤
        Real.exp (-(μ / β * (t : ℝ))) * (C θ0 - Cstar)) ∧
    (∀ ε : ℝ, 0 < ε →
        C (gdIter C (1 / β) θ0 (precisionSteps β μ (C θ0 - Cstar) ε)) - Cstar ≤ ε) ∧
    (∀ (ε P Q : ℝ), 0 < ε → ε ≤ C θ0 - Cstar → 0 ≤ P →
        β / μ ≤ P → Real.log ((C θ0 - Cstar) / ε) ≤ Q →
        (precisionSteps β μ (C θ0 - Cstar) ε : ℝ) < P * Q + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact theorem1_geometric_decay C β μ Cstar hβ hsmooth hpl hmin hμ0 hμβ θ0 t
  · intro ε hε
    exact theorem1_actual_precision C β μ Cstar hβ hsmooth hpl hmin hμ0 hμβ θ0 hΔ0 ε hε
  · intro ε P Q hε hεle hP0 hβμ hlog
    exact (precisionSteps_lt_poly P β μ (C θ0 - Cstar) ε hβ hμ0 hε hεle hβμ).trans_le
      (add_le_add (mul_le_mul_of_nonneg_left hlog hP0) (le_refl 1))

end Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence
