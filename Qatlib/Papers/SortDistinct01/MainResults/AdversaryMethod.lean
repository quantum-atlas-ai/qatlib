/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SortDistinct01.MainResults.AdversaryMethod

open Finset

def epsPrime (ε : ℝ) : ℝ := 2 * Real.sqrt (ε * (1 - ε))

theorem adversary_lower_bound {T : ℕ} {W : ℕ → ℝ} {W0 ε' δ : ℝ}
    (hW0 : W 0 = W0) (hWT : W T ≤ ε' * W0)
    (hstep : ∀ j < T, |W j - W (j + 1)| ≤ δ)
    (hδ : 0 < δ) :
    (1 - ε') * W0 / δ ≤ (T : ℝ) := by
  have htelescope : W T - W 0 = ∑ j ∈ Finset.range T, (W (j + 1) - W j) :=
    (Finset.sum_range_sub W T).symm
  have habs : |W T - W 0| ≤ (T : ℝ) * δ := by
    calc |W T - W 0|
        = |∑ j ∈ Finset.range T, (W (j + 1) - W j)| := by rw [htelescope]
      _ ≤ ∑ j ∈ Finset.range T, |W (j + 1) - W j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range T, δ :=
          Finset.sum_le_sum fun j hj => by
            rw [abs_sub_comm]
            exact hstep j (Finset.mem_range.1 hj)
      _ = (T : ℝ) * δ := by simp
  have hlow : W0 - (T : ℝ) * δ ≤ W T := by
    have h := (abs_le.1 habs).1
    rw [hW0] at h
    linarith [h]
  have hmain : (1 - ε') * W0 ≤ (T : ℝ) * δ := by
    have := le_trans hlow hWT
    linarith [this]
  rw [div_le_iff₀ hδ]
  exact hmain

theorem W0_ordered_eq (N : ℕ) :
    (N : ℝ) * ((harmonic N : ℝ) - 1) = (N : ℝ) * (harmonic N : ℝ) - N := by
  ring

theorem theorem1_ordered_search_lower_bound {N T : ℕ} {W : ℕ → ℝ} {ε : ℝ}
    (hN : 1 ≤ N) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hW0 : W 0 = (N : ℝ) * ((harmonic N : ℝ) - 1))
    (hstep : ∀ j < T, |W j - W (j + 1)| ≤ Real.pi * (N : ℝ))
    (hWT : W T ≤ 2 * Real.sqrt (ε * (1 - ε)) * W 0) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * (1 / Real.pi) * ((harmonic N : ℝ) - 1)
      ≤ (T : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : 0 < Real.pi * (N : ℝ) := mul_pos hpi hNpos
  have hWT' : W T ≤ 2 * Real.sqrt (ε * (1 - ε)) * ((N : ℝ) * ((harmonic N : ℝ) - 1)) := by
    rwa [hW0] at hWT
  have h := adversary_lower_bound (W := W) (W0 := (N : ℝ) * ((harmonic N : ℝ) - 1))
    (ε' := 2 * Real.sqrt (ε * (1 - ε))) (δ := Real.pi * (N : ℝ)) hW0 hWT' hstep hδ
  have heq : (1 - 2 * Real.sqrt (ε * (1 - ε))) * ((N : ℝ) * ((harmonic N : ℝ) - 1))
        / (Real.pi * (N : ℝ))
      = (1 - 2 * Real.sqrt (ε * (1 - ε))) * (1 / Real.pi) * ((harmonic N : ℝ) - 1) := by
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rwa [heq] at h

theorem theorem1_exact_case {N T : ℕ} {W : ℕ → ℝ}
    (hN : 1 ≤ N)
    (hW0 : W 0 = (N : ℝ) * ((harmonic N : ℝ) - 1))
    (hstep : ∀ j < T, |W j - W (j + 1)| ≤ Real.pi * (N : ℝ))
    (hWT : W T ≤ 0) :
    (1 / Real.pi) * (Real.log (N : ℝ) - 1) ≤ (T : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : 0 < Real.pi * (N : ℝ) := mul_pos hpi hNpos
  have h := adversary_lower_bound (W := W) (W0 := (N : ℝ) * ((harmonic N : ℝ) - 1))
    (ε' := 0) (δ := Real.pi * (N : ℝ)) hW0 (by simpa using hWT) hstep hδ

  have hlog1 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
    have hh := log_add_one_le_harmonic N
    simpa using hh
  have hHlog : Real.log (N : ℝ) - 1 ≤ (harmonic N : ℝ) - 1 := by linarith
  have h1 : (1 / Real.pi) * (Real.log (N : ℝ) - 1)
      ≤ (1 / Real.pi) * ((harmonic N : ℝ) - 1) := by
    apply mul_le_mul_of_nonneg_left hHlog
    positivity
  have h2 : (1 / Real.pi) * ((harmonic N : ℝ) - 1) ≤ (T : ℝ) := by
    have heq : (1 - (0 : ℝ)) * ((N : ℝ) * ((harmonic N : ℝ) - 1)) / (Real.pi * (N : ℝ))
        = (1 / Real.pi) * ((harmonic N : ℝ) - 1) := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rwa [heq] at h
  linarith

theorem W0_sorting_eq (N : ℕ) :
    (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N)
      = (Nat.factorial N : ℝ) * (N : ℝ) * ((harmonic N : ℝ) - 1) := by
  ring

theorem theorem2_sorting_lower_bound {N T : ℕ} {W : ℕ → ℝ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hW0 : W 0 = (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (hstep : ∀ j < T, |W j - W (j + 1)| ≤ 2 * Real.pi * (Nat.factorial N : ℝ))
    (hWT : W T ≤ 2 * Real.sqrt (ε * (1 - ε)) * W 0) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * ((N : ℝ) / (2 * Real.pi)) * ((harmonic N : ℝ) - 1)
      ≤ (T : ℝ) := by
  have hfpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : 0 < 2 * Real.pi * (Nat.factorial N : ℝ) := by positivity
  have hWT' : W T ≤ 2 * Real.sqrt (ε * (1 - ε))
      * ((Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N)) := by
    rwa [hW0] at hWT
  have h := adversary_lower_bound (W := W)
    (W0 := (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (ε' := 2 * Real.sqrt (ε * (1 - ε)))
    (δ := 2 * Real.pi * (Nat.factorial N : ℝ)) hW0 hWT' hstep hδ
  have heq :
      (1 - 2 * Real.sqrt (ε * (1 - ε)))
          * ((Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
        / (2 * Real.pi * (Nat.factorial N : ℝ))
      = (1 - 2 * Real.sqrt (ε * (1 - ε))) * ((N : ℝ) / (2 * Real.pi))
          * ((harmonic N : ℝ) - 1) := by
    have hfne : (Nat.factorial N : ℝ) ≠ 0 := ne_of_gt hfpos
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rwa [heq] at h

theorem theorem3_element_distinctness_lower_bound {N T : ℕ} {W : ℕ → ℝ} {ε : ℝ}
    (hN : 1 ≤ N) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hW0 : W 0 = (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (hstep : ∀ j < T,
      |W j - W (j + 1)| ≤ 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ))
    (hWT : W T ≤ 2 * Real.sqrt (ε * (1 - ε)) * W 0) :
    (1 - 2 * Real.sqrt (ε * (1 - ε))) * (Real.sqrt (N : ℝ) / (2 * Real.pi))
        * ((harmonic N : ℝ) - 1)
      ≤ (T : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hfpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hδ : 0 < 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) := by positivity
  have hWT' : W T ≤ 2 * Real.sqrt (ε * (1 - ε))
      * ((Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N)) := by
    rwa [hW0] at hWT
  have h := adversary_lower_bound (W := W)
    (W0 := (Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
    (ε' := 2 * Real.sqrt (ε * (1 - ε)))
    (δ := 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) hW0 hWT' hstep hδ
  have heq :
      (1 - 2 * Real.sqrt (ε * (1 - ε)))
          * ((Nat.factorial N : ℝ) * ((N : ℝ) * (harmonic N : ℝ) - N))
        / (2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ))
      = (1 - 2 * Real.sqrt (ε * (1 - ε))) * (Real.sqrt (N : ℝ) / (2 * Real.pi))
          * ((harmonic N : ℝ) - 1) := by
    have hfne : (Nat.factorial N : ℝ) ≠ 0 := ne_of_gt hfpos
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    have hsne : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt hsq
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    ring
  rwa [heq] at h

end Qatlib.Papers.SortDistinct01.MainResults.AdversaryMethod
