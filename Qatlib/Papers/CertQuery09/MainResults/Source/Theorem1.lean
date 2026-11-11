/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.CertQuery09.MainResults.Source.NandCertificate
import Qatlib.Papers.CertQuery09.MainResults.Source.CostRecurrence
import Qatlib.Papers.CertQuery09.MainResults.Source.QueryLowerSum

/-!
# Quadratic-depth upper bounds for certification costs

This module simplifies the explicit recurrence estimates for `QueryCostModel` by bounding `log d
/ sqrt d` uniformly. It proves the quadratic-depth expected-cost envelopes corresponding to the
upper-bound analysis in [AmbainisEtAl2009].

## Main statements

* `log_le_two_sqrt`: bounds the logarithm of a positive natural number.
* `theorem1_upper_bound`: gives a common positive constant for both expected-cost sequences.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CertQuery09.MainResults.Source

/-- For a natural number `d ≥ 1`, `Real.log d ≤ 2 * Real.sqrt d`. -/
theorem log_le_two_sqrt (d : ℕ) (hd : 1 ≤ d) :
    Real.log (d : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
  have hlog := Real.log_le_rpow_div (x := (d : ℝ)) (ε := (1 : ℝ) / 2)
    (by positivity) (by norm_num)
  have hd2 : (d : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (d : ℝ) := by
    simpa using (Real.rpow_div_two_eq_sqrt (x := (d : ℝ)) 1 (by positivity))
  rw [hd2] at hlog
  have h2 : Real.sqrt (d : ℝ) / ((1 : ℝ) / 2) = 2 * Real.sqrt (d : ℝ) := by ring
  linarith

/-- For `d ≥ 2`, every `QueryCostModel` possesses a positive constant bounding `E0 k` by `C * k²
* sqrt (d ^ (k + 1))` and `E1 k` by `C * k² * sqrt (d ^ k)` for all `k ≥ 1`. These are the
recurrence-model upper bounds corresponding to [Ambainis et al., Theorem
1][AmbainisEtAl2009]. -/
theorem theorem1_upper_bound (d : ℕ) (hd : 2 ≤ d) (a b c₁ : ℝ)
    (M : QueryCostModel d a b c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      M.E0 k ≤ C * (k : ℝ) ^ 2 * Real.sqrt ((d : ℝ) ^ (k + 1)) ∧
      M.E1 k ≤ C * (k : ℝ) ^ 2 * Real.sqrt ((d : ℝ) ^ k) := by
  obtain ⟨hC0pos, hmain⟩ :=
    lemma2_expected_query_cost d hd a b c₁ M
  refine ⟨max (max a b) (max c₁ 1) * 3, mul_pos hC0pos (by norm_num), ?_⟩
  have hlogL : Real.log (d : ℝ) / Real.sqrt (d : ℝ) ≤ 2 := by
    have hlog := log_le_two_sqrt d (by omega)
    have hsd : 0 < Real.sqrt (d : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
    rw [div_le_iff₀ hsd]
    linarith
  intro k hk
  obtain ⟨hE0, hE1⟩ := hmain k hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h1kL : 1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ)) ≤ 3 * (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogL (le_of_lt hkpos)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [h, hk1]
  have hfac : (k : ℝ) * (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ))) ≤
      3 * (k : ℝ) ^ 2 := by
    calc (k : ℝ) * (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ)))
        ≤ (k : ℝ) * (3 * (k : ℝ)) := mul_le_mul_of_nonneg_left h1kL (le_of_lt hkpos)
      _ = 3 * (k : ℝ) ^ 2 := by ring
  constructor
  · calc M.E0 k
        ≤ max (max a b) (max c₁ 1) * (k : ℝ) *
            (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ))) *
            Real.sqrt ((d : ℝ) ^ (k + 1)) := hE0
      _ = max (max a b) (max c₁ 1) *
            ((k : ℝ) * (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ)))) *
            Real.sqrt ((d : ℝ) ^ (k + 1)) := by ring
      _ ≤ max (max a b) (max c₁ 1) * (3 * (k : ℝ) ^ 2) *
            Real.sqrt ((d : ℝ) ^ (k + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac hC0pos.le
      _ = max (max a b) (max c₁ 1) * 3 * (k : ℝ) ^ 2 *
            Real.sqrt ((d : ℝ) ^ (k + 1)) := by ring
  · calc M.E1 k
        ≤ max (max a b) (max c₁ 1) * (k : ℝ) *
            (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ))) *
            Real.sqrt ((d : ℝ) ^ k) := hE1
      _ = max (max a b) (max c₁ 1) *
            ((k : ℝ) * (1 + (k : ℝ) * (Real.log (d : ℝ) / Real.sqrt (d : ℝ)))) *
            Real.sqrt ((d : ℝ) ^ k) := by ring
      _ ≤ max (max a b) (max c₁ 1) * (3 * (k : ℝ) ^ 2) *
            Real.sqrt ((d : ℝ) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hfac hC0pos.le
      _ = max (max a b) (max c₁ 1) * 3 * (k : ℝ) ^ 2 *
            Real.sqrt ((d : ℝ) ^ k) := by ring

end Qatlib.Papers.CertQuery09.MainResults.Source
