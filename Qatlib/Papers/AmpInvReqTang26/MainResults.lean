/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.ActualAccess

/-!
# Conditional scaling of inverse-free amplitude lower bounds

These results convert an assumed reduction bound involving a maximum of amplitude and dimension
scales into a lower bound proportional to their minimum. The reduction hypothesis remains
explicit in both the amplification and estimation statements. This development supports the
treatment in [TangWright2025].

## Main statements

* `conditional_amplification_scaling`: conditional `min(d, 1/a^2)` scaling.
* `conditional_estimation_scaling`: conditional `min(d, 1/ε^2)` scaling.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- Assuming the stated reduction bound, there are uniform positive constants giving `n ≥ c *
min(d, 1/a^2)` for amplification algorithms in the specified small-amplitude and
large-dimension regime [TangWright2025]. -/
theorem conditional_amplification_scaling
    (hred : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d anc : ℕ) (a : ℝ) (n : ℕ) (Alg : PreparationAlgorithm (Fin d) (Fin anc)),
        0 < d → 0 < a → a < 0.025 → 4*C < (d:ℝ) →
        SolvesAmplification Alg n a →
        (1 : ℝ) / (12 * (max (a / 0.05) (Real.sqrt (C / (d : ℝ)))) ^ 2) ≤ (n : ℝ)) :
    ∃ c C0 : ℝ, 0 < c ∧ 1 ≤ C0 ∧
      ∀ (d anc : ℕ) (a : ℝ) (n : ℕ) (Alg : PreparationAlgorithm (Fin d) (Fin anc)),
        0 < d → 0 < a → a < 0.025 → 4*C0 < (d:ℝ) →
        SolvesAmplification Alg n a →
        c * min (d : ℝ) (1 / a ^ 2) ≤ (n : ℝ) := by
  obtain ⟨C, hC1, hred'⟩ := hred
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCne : (C : ℝ) ≠ 0 := ne_of_gt hCpos
  have hcC : (0 : ℝ) < 1 / (12 * C) := div_pos (by norm_num) (by nlinarith [hC1])
  refine ⟨min (1 / 4800) (1 / (12 * C)), C, lt_min (by norm_num) hcC, hC1, ?_⟩
  intro d anc a n Alg hd ha haSmall hdLarge hsolves
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
  have hdRne : ((d : ℝ)) ≠ 0 := by exact_mod_cast hd.ne'
  have han : (a : ℝ) ≠ 0 := ha.ne'
  have hn := hred' d anc a n Alg hd ha haSmall hdLarge hsolves
  rcases le_total (a / 0.05) (Real.sqrt (C / (d : ℝ))) with hle | hle
  · have hM : max (a / 0.05) (Real.sqrt (C / (d : ℝ))) = Real.sqrt (C / (d : ℝ)) :=
      max_eq_right hle
    have hCdiag : (0 : ℝ) ≤ C / (d : ℝ) := div_nonneg hCpos.le hdR
    rw [hM, Real.sq_sqrt hCdiag] at hn
    have heq : (1 : ℝ) / (12 * (C / (d : ℝ))) = ((d : ℝ)) / (12 * C) := by
      field_simp
    rw [heq] at hn
    calc min (1 / 4800) (1 / (12 * C)) * min ((d : ℝ)) (1 / a ^ 2)
        ≤ min (1 / 4800) (1 / (12 * C)) * ((d : ℝ)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (le_min (by norm_num) hcC.le)
      _ ≤ ((d : ℝ)) * (1 / (12 * C)) :=
          (mul_le_mul_of_nonneg_right (min_le_right (1 / 4800) (1 / (12 * C))) hdR).trans
            (le_of_eq (mul_comm (1 / (12 * C)) ((d : ℝ))))
      _ = ((d : ℝ)) / (12 * C) := (div_eq_mul_one_div _ _).symm
      _ ≤ (n : ℝ) := hn
  · have hM : max (a / 0.05) (Real.sqrt (C / (d : ℝ))) = a / 0.05 := max_eq_left hle
    rw [hM] at hn
    have heq : (1 : ℝ) / (12 * (a / 0.05) ^ 2) = 1 / (4800 * a ^ 2) := by
      field_simp
      ring
    rw [heq] at hn
    calc min (1 / 4800) (1 / (12 * C)) * min ((d : ℝ)) (1 / a ^ 2)
        ≤ min (1 / 4800) (1 / (12 * C)) * (1 / a ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_min (by norm_num) hcC.le)
      _ ≤ (1 / 4800) * (1 / a ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg zero_le_one (sq_nonneg a))
      _ = 1 / (4800 * a ^ 2) := by field_simp
      _ ≤ (n : ℝ) := hn

/-- Assuming the stated reduction bound, there are uniform positive constants giving `n ≥ c *
min(d, 1/ε^2)` for estimation algorithms in the specified error and dimension regime
[TangWright2025]. -/
theorem conditional_estimation_scaling
    (hred : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d anc : ℕ) (ε : ℝ) (n : ℕ) (Alg : PreparationAlgorithm (Fin d) (Fin anc)),
        0 < d → 0 < ε → ε < 0.025 → 4*C < (d:ℝ) →
        SolvesEstimation Alg n ε →
        (1 : ℝ) / (12 * (max (ε / 0.05) (Real.sqrt (C / (d : ℝ)))) ^ 2) ≤ (n : ℝ)) :
    ∃ c C0 : ℝ, 0 < c ∧ 1 ≤ C0 ∧
      ∀ (d anc : ℕ) (ε : ℝ) (n : ℕ) (Alg : PreparationAlgorithm (Fin d) (Fin anc)),
        0 < d → 0 < ε → ε < 0.025 → 4*C0 < (d:ℝ) →
        SolvesEstimation Alg n ε →
        c * min (d : ℝ) (1 / ε ^ 2) ≤ (n : ℝ) := by
  obtain ⟨C, hC1, hred'⟩ := hred
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCne : (C : ℝ) ≠ 0 := ne_of_gt hCpos
  have hcC : (0 : ℝ) < 1 / (12 * C) := div_pos (by norm_num) (by nlinarith [hC1])
  refine ⟨min (1 / 4800) (1 / (12 * C)), C, lt_min (by norm_num) hcC, hC1, ?_⟩
  intro d anc ε n Alg hd hε heSmall hdLarge hsolves
  have hdR : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.le
  have hdRne : ((d : ℝ)) ≠ 0 := by exact_mod_cast hd.ne'
  have hεn : (ε : ℝ) ≠ 0 := hε.ne'
  have hn := hred' d anc ε n Alg hd hε heSmall hdLarge hsolves
  rcases le_total (ε / 0.05) (Real.sqrt (C / (d : ℝ))) with hle | hle
  · have hM : max (ε / 0.05) (Real.sqrt (C / (d : ℝ))) = Real.sqrt (C / (d : ℝ)) :=
      max_eq_right hle
    have hCdiag : (0 : ℝ) ≤ C / (d : ℝ) := div_nonneg hCpos.le hdR
    rw [hM, Real.sq_sqrt hCdiag] at hn
    have heq : (1 : ℝ) / (12 * (C / (d : ℝ))) = ((d : ℝ)) / (12 * C) := by
      field_simp
    rw [heq] at hn
    calc min (1 / 4800) (1 / (12 * C)) * min ((d : ℝ)) (1 / ε ^ 2)
        ≤ min (1 / 4800) (1 / (12 * C)) * ((d : ℝ)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (le_min (by norm_num) hcC.le)
      _ ≤ ((d : ℝ)) * (1 / (12 * C)) :=
          (mul_le_mul_of_nonneg_right (min_le_right (1 / 4800) (1 / (12 * C))) hdR).trans
            (le_of_eq (mul_comm (1 / (12 * C)) ((d : ℝ))))
      _ = ((d : ℝ)) / (12 * C) := (div_eq_mul_one_div _ _).symm
      _ ≤ (n : ℝ) := hn
  · have hM : max (ε / 0.05) (Real.sqrt (C / (d : ℝ))) = ε / 0.05 := max_eq_left hle
    rw [hM] at hn
    have heq : (1 : ℝ) / (12 * (ε / 0.05) ^ 2) = 1 / (4800 * ε ^ 2) := by
      field_simp
      ring
    rw [heq] at hn
    calc min (1 / 4800) (1 / (12 * C)) * min ((d : ℝ)) (1 / ε ^ 2)
        ≤ min (1 / 4800) (1 / (12 * C)) * (1 / ε ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_min (by norm_num) hcC.le)
      _ ≤ (1 / 4800) * (1 / ε ^ 2) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (div_nonneg zero_le_one (sq_nonneg ε))
      _ = 1 / (4800 * ε ^ 2) := by field_simp
      _ ≤ (n : ℝ) := hn

end Qatlib.Papers.AmpInvReqTang26.MainResults
