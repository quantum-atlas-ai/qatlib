/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Gradient RealInnerProductSpace BigOperators

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation

open Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent
open Qatlib.Papers.DissipVarFw26.FrameworkCost.PL
open Qatlib.Papers.DissipVarFw26.FrameworkCost.Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem lemma4_trajectory_flat_steps
    (gap : ℕ → ℝ) (η G δ0 ε : ℝ) (T : ℕ)
    (hη : 0 < η) (hG : 0 < G)
    (hstep : ∀ t, t < T → gap t - gap (t + 1) ≤ (3 * η / 2) * G)
    (h0 : δ0 ≤ gap 0) (hT : gap T ≤ ε) :
    (2 * (δ0 - ε)) / (3 * η * G) ≤ (T : ℝ) := by

  have htel : Finset.sum (Finset.range T) (fun t => gap t - gap (t + 1)) = gap 0 - gap T := by
    have hh : ∀ n : ℕ,
        Finset.sum (Finset.range n) (fun t => gap t - gap (t + 1)) = gap 0 - gap n := by
      intro n
      induction n with
      | zero => simp
      | succ m ihm => rw [Finset.sum_range_succ, ihm]; ring
    exact hh T
  have hsum : Finset.sum (Finset.range T) (fun t => gap t - gap (t + 1)) ≤
      (T : ℝ) * ((3 * η / 2) * G) := by
    calc Finset.sum (Finset.range T) (fun t => gap t - gap (t + 1))
        ≤ Finset.sum (Finset.range T) (fun _ => (3 * η / 2) * G) := by
          apply Finset.sum_le_sum
          intro t ht
          exact hstep t (Finset.mem_range.mp ht)
      _ = (T : ℝ) * ((3 * η / 2) * G) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hge : δ0 - ε ≤ (T : ℝ) * ((3 * η / 2) * G) := by
    have : gap 0 - gap T ≤ (T : ℝ) * ((3 * η / 2) * G) := by rw [← htel]; exact hsum
    linarith
  rw [div_le_iff₀ (by positivity : 0 < 3 * η * G)]
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  nlinarith [hge, hTnn]

theorem lemma4_exponential_lower
    (gap : ℕ → ℝ) (η m B b δ0 ε : ℝ) (T n : ℕ)
    (hη : 0 < η) (hm : 0 < m) (hB : 0 < B) (hb : 1 < b)
    (hstep : ∀ t, t < T → gap t - gap (t + 1) ≤
      (3 * η / 2) * (m * B * b ^ (-(n : ℝ))))
    (h0 : δ0 ≤ gap 0) (hT : gap T ≤ ε) :
    (2 * (δ0 - ε)) / (3 * η * (m * B * b ^ (-(n : ℝ)))) ≤ (T : ℝ) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hG : 0 < m * B * b ^ (-(n : ℝ)) := by
    have hp : 0 < b ^ (-(n : ℝ)) := Real.rpow_pos_of_pos hb0 _
    positivity
  exact lemma4_trajectory_flat_steps gap η (m * B * b ^ (-(n : ℝ))) δ0 ε T hη hG
    hstep h0 hT

theorem theorem2_separation
    (C : E → ℝ) (βdis μdis Cdis_star : ℝ) (hβd : 0 < βdis)
    (hsmooth_d : SmoothGrad C βdis) (hpl_d : PLCond C μdis Cdis_star)
    (hmin_d : ∀ x, Cdis_star ≤ C x) (hμd0 : 0 < μdis) (hμβ : μdis ≤ βdis)
    (θ0 : E) (ε P : ℝ) (hΔ0 : 0 < C θ0 - Cdis_star) (hε : 0 < ε)
    (hεle : ε ≤ C θ0 - Cdis_star) (hβμ : βdis / μdis ≤ P)
    (gap : ℕ → ℝ) (ηuni Guni δ0 : ℝ) (T : ℕ)
    (hη : 0 < ηuni) (hG : 0 < Guni)
    (hstep : ∀ t, t < T → gap t - gap (t + 1) ≤ (3 * ηuni / 2) * Guni)
    (h0 : δ0 ≤ gap 0) (hT : gap T ≤ ε) :
    (C (gdIter C (1 / βdis) θ0
        (precisionSteps βdis μdis (C θ0 - Cdis_star) ε)) - Cdis_star ≤ ε ∧
      (precisionSteps βdis μdis (C θ0 - Cdis_star) ε : ℝ) <
        P * Real.log ((C θ0 - Cdis_star) / ε) + 1) ∧
    (2 * (δ0 - ε)) / (3 * ηuni * Guni) ≤ (T : ℝ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact theorem1_actual_precision C βdis μdis Cdis_star hβd hsmooth_d hpl_d hmin_d
      hμd0 hμβ θ0 hΔ0 ε hε
  · exact precisionSteps_lt_poly P βdis μdis (C θ0 - Cdis_star) ε
      hβd hμd0 hε hεle hβμ
  · exact lemma4_trajectory_flat_steps gap ηuni Guni δ0 ε T hη hG hstep h0 hT

end Qatlib.Papers.DissipVarFw26.FrameworkCost.Separation
