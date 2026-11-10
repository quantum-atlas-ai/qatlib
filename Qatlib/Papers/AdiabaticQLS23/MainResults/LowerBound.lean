/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Qatlib.Papers.AdiabaticQLS23.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {N : Type*} [Fintype N] [DecidableEq N]

def adiabaticMatrix (c : ℝ) (U : Matrix N N ℂ) : Matrix N N ℂ :=
  1 - (c : ℂ) • U

theorem neumann_series_mul (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (∑' k : ℕ, ((c : ℂ) • U) ^ k) * adiabaticMatrix c U = 1 := by
  unfold adiabaticMatrix
  exact geom_series_mul_neg _ h

theorem adiabaticMatrix_inv_eq_series (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (adiabaticMatrix c U)⁻¹ = ∑' k : ℕ, ((c : ℂ) • U) ^ k :=
  Matrix.inv_eq_left_inv (neumann_series_mul U c h)

theorem smul_pow (c : ℝ) (U : Matrix N N ℂ) (k : ℕ) :
    ((c : ℂ) • U) ^ k = ((c : ℂ) ^ k) • U ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, smul_mul_smul_comm, pow_succ]

theorem adiabaticMatrix_inv_eq_paper_series (U : Matrix N N ℂ) (c : ℝ)
    (h : ‖(c : ℂ) • U‖ < 1) :
    (adiabaticMatrix c U)⁻¹ = ∑' k : ℕ, ((c : ℂ) ^ k) • U ^ k := by
  rw [adiabaticMatrix_inv_eq_series U c h]
  simp_rw [smul_pow]

theorem log_inv_epsilon_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    0 < Real.log (1 / ε) := by
  apply Real.log_pos
  exact (one_lt_div h0).mpr h1

theorem query_lower_bound_chain {T q : ℕ} {κ ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hreduction : (T : ℝ) ≤ q)
    (hκ : κ ≤ (T : ℝ) / Real.log (1 / ε)) :
    κ * Real.log (1 / ε) ≤ q := by
  have hlog : 0 < Real.log (1 / ε) := log_inv_epsilon_pos hε0 hε1
  calc
    κ * Real.log (1 / ε) ≤ ((T : ℝ) / Real.log (1 / ε)) * Real.log (1 / ε) := by
      gcongr
    _ = (T : ℝ) := by field_simp
    _ ≤ q := hreduction

theorem query_lower_bound_chain_scaled {T q κ ε c C : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 ≤ c) (hC : 0 < C)
    (hreduction : c*T ≤ q) (hκ : κ ≤ C*T / Real.log (1/ε)) :
    (c/C)*κ*Real.log (1/ε) ≤ q := by
  have hlog := log_inv_epsilon_pos hε0 hε1
  have hκL := (le_div_iff₀ hlog).mp hκ
  calc
    (c/C)*κ*Real.log (1/ε) = (c/C)*(κ*Real.log (1/ε)) := by ring
    _ ≤ (c/C)*(C*T) := mul_le_mul_of_nonneg_left hκL (div_nonneg hc hC.le)
    _ = c*T := by field_simp
    _ ≤ q := hreduction

end

end Qatlib.Papers.AdiabaticQLS23.MainResults
