/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SymJunta13.MainResults.SourceLemma1
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Large-size binomial bounds and the middle amplitude

The explicit real threshold in Lemma 1 yields a natural-number cutoff.
Taking square roots of the central-binomial weight gives the amplitude
scale used in Sections 5 and 6.
-/

set_option autoImplicit false

open Qatlib.Papers.SymJunta13.MainResults

namespace Qatlib.Papers.SymJunta13.MainResults

/-- Sections 5 and 6 use the square root of the normalized central-binomial weight,
which is between one half and one times the negative-quarter power. -/
theorem krawtchouk_zero_middle_sqrt (k : ℕ) (hk : 1 ≤ k) :
    (1 / 2) * (k : ℝ) ^ (-(1 / 4) : ℝ) ≤
        Real.sqrt ((k.choose (k / 2) : ℝ) / (2 : ℝ) ^ k) ∧
      Real.sqrt ((k.choose (k / 2) : ℝ) / (2 : ℝ) ^ k) ≤ (k : ℝ) ^ (-(1 / 4) : ℝ) := by
  have h := krawtchouk_zero_middle_weight k hk
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have hroot : Real.sqrt (1 / Real.sqrt (k : ℝ)) = (k : ℝ) ^ (-(1 / 4) : ℝ) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hp.le, Real.rpow_neg hp.le, one_div]
    norm_num
  constructor
  · calc
      _ = Real.sqrt ((1 / 4) / Real.sqrt (k : ℝ)) := by
        rw [← hroot, Real.sqrt_div (by norm_num), Real.sqrt_div (by norm_num), Real.sqrt_one]
        norm_num [show Real.sqrt (1 / 4) = 1 / 2 by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        ring
      _ ≤ _ := Real.sqrt_le_sqrt h.1
  · exact (Real.sqrt_le_sqrt h.2).trans_eq hroot

/-- Lemma 1 holds beyond a natural threshold with common positive constants for both shifts. -/
theorem source_lemma1_eventually (C : ℝ) (hC : 0 < C) :
    ∃ (n₀ : ℕ) (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧ ∀ n k : ℕ, n₀ ≤ n →
      1 ≤ k → (k : ℝ) ≤ C * Real.sqrt (n : ℝ) →
      c₁ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤ (n.choose (n / 2 + k) : ℝ) ∧
        (n.choose (n / 2 + k) : ℝ) ≤ c₂ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ∧
        c₁ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) ≤ (n.choose (n / 2 - k) : ℝ) ∧
        (n.choose (n / 2 - k) : ℝ) ≤ c₂ * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) := by
  obtain ⟨c₁, c₂, h₁, h₂, hf⟩ := source_lemma1 C hC
  refine ⟨⌈16 * C ^ 2 + 1⌉₊, c₁, c₂, h₁, h₂, ?_⟩
  intro n k hn hk hkc
  have hn' : ((⌈16 * C ^ 2 + 1⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  exact hf n k hk hkc ((Nat.le_ceil _).trans hn')

end Qatlib.Papers.SymJunta13.MainResults
