/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Series truncation and accumulated recurrence residuals

This module expresses the difference between a convergent series and a finite prefix as a
shifted tail. It bounds truncation errors by summable scalar majorants and proves the existence
of a prefix meeting any positive tolerance.

The recurrence `affineTrajectory` supports a separate stability estimate: under nonexpansive
step maps and an exact initial value, trajectory error is bounded by the sum of local residual
bounds.

The mathematical background is discussed in [BerryCosta2024].

## Main statements

* `truncation_error_le`: controls a vector-series tail by a scalar majorant.
* `exists_truncation_error_lt`: gives an arbitrarily accurate finite prefix.
* `residual_error_le`: accumulates local residual bounds along a nonexpansive recurrence.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.DysonError
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]

/-- A summable series minus its first `K` terms equals the series of terms shifted by `K`. -/
theorem series_sub_prefix (f : ℕ → E) (hf : Summable f) (K : ℕ) :
    (∑' n, f n) - ∑ n ∈ Finset.range K, f n = ∑' n, f (n + K) := by
  have h := hf.sum_add_tsum_nat_add K
  rw [← h]
  abel

/-- In a complete normed space, a summable scalar majorant of the term norms bounds the norm of
every truncation tail. -/
theorem truncation_error_le [CompleteSpace E] (f : ℕ → E) (g : ℕ → ℝ) (hg : Summable g)
    (hfg : ∀ n, ‖f n‖ ≤ g n) (K : ℕ) :
    ‖(∑' n, f n) - ∑ n ∈ Finset.range K, f n‖ ≤ ∑' n, g (n + K) := by
  rw [series_sub_prefix f (Summable.of_norm_bounded hg hfg) K]
  exact tsum_of_norm_bounded ((summable_nat_add_iff K).2 hg).hasSum (fun n => hfg (n+K))

/-- Every summable series has a finite prefix whose truncation error is smaller than any
prescribed positive tolerance. -/
theorem exists_truncation_error_lt (f : ℕ → E) (hf : Summable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ‖(∑' n, f n) - ∑ n ∈ Finset.range K, f n‖ < ε := by
  have h := (Metric.tendsto_atTop.1 hf.hasSum.tendsto_sum_nat) ε hε
  obtain ⟨K,hK⟩ := h
  refine ⟨K, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hK K le_rfl

/-- The trajectory starting at `x₀` and recursively applying `F n` followed by addition of `b
n`. -/
def affineTrajectory (F : ℕ → E → E) (b : ℕ → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n+1 => F n (affineTrajectory F b x₀ n) + b n

/-- For nonexpansive step maps and an exact initial value, the error of an approximate
trajectory is at most the sum of its local residual bounds. -/
theorem residual_error_le (F : ℕ → E → E) (b : ℕ → E) (x₀ : E)
    (y : ℕ → E) (δ : ℕ → ℝ) (hinit : y 0 = x₀)
    (hstable : ∀ n x z, ‖F n x - F n z‖ ≤ ‖x-z‖)
    (hres : ∀ n, ‖y (n+1) - (F n (y n) + b n)‖ ≤ δ n) (n : ℕ) :
    ‖y n - affineTrajectory F b x₀ n‖ ≤ ∑ j ∈ Finset.range n, δ j := by
  induction n with
  | zero => simp [affineTrajectory,hinit]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = ‖(y (n+1) - (F n (y n) + b n)) +
            (F n (y n) - F n (affineTrajectory F b x₀ n))‖ := by
        congr 1
        simp only [affineTrajectory]
        abel
      _ ≤ ‖y (n+1) - (F n (y n) + b n)‖ +
            ‖F n (y n) - F n (affineTrajectory F b x₀ n)‖ := norm_add_le _ _
      _ ≤ δ n + ‖y n - affineTrajectory F b x₀ n‖ := add_le_add (hres n) (hstable n _ _)
      _ ≤ _ := by linarith
end Qatlib.Foundations.TimeEvolution.DysonError
