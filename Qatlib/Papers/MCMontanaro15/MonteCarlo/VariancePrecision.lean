/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean

@[expose] public section

/-!
# Additive variance precision for the signed Monte-Carlo estimator

Theorem 5 of [Montanaro2015] states that, given a variance bound
`Var(v(A)) ≤ σ²`, the signed layered estimator reaches *additive* error `ε` with success
probability at least `2 / 3`. The locked library proves the dyadic form
`signed_centered_same_program_mean_guarantee`: for `k ≥ 4` the estimator is within
`8 * σ * 2^(-k)` with probability at least `2 / 3`.

This module makes the source parameterization explicit. Since the dyadic error tends to zero,
there is always a layer count `k ≥ 4` at which `8 * σ * 2^(-k) ≤ ε`; at that `k` the dyadic
guarantee immediately yields additive accuracy `ε`. The constant `8` applies to every variance
scale. The layer count is uniform over sources and payoffs with the prescribed variance bound.
This proves the accuracy conclusion for all positive tolerances, including the source regime
`ε < 4 * σ`. The copy and reflection budgets of Algorithm 3 are outside this result.

## Main statements

* `exists_variance_layer_precision`: for every nonnegative error scale and positive tolerance
  there is a layer count `k ≥ 4` with `c * 2^(-k) ≤ ε`.
* `theorem5_additive_variance_guarantee`: under `Var(f) ≤ σ²`, the signed estimator has additive
  error at most `ε` with probability at least `2 / 3`, for some layer count `k ≥ 4`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Matrix
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open scoped BigOperators

/-- For every nonnegative scale `c` and positive tolerance `ε` there is a layer count `k ≥ 4`
whose dyadic resolution `c * 2^(-k)` is at most `ε`. -/
theorem exists_variance_layer_precision (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ k : ℕ, 4 ≤ k ∧ c * (1 / 2 : ℝ) ^ k ≤ ε := by
  by_cases hc0 : c = 0
  · refine ⟨4, by norm_num, ?_⟩
    rw [hc0, zero_mul]
    exact hε.le
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (show 0 < ε / c by positivity)
        (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨max 4 n, le_max_left _ _, ?_⟩
    have hpow : (1 / 2 : ℝ) ^ max 4 n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have hstep : c * (1 / 2 : ℝ) ^ max 4 n ≤ c * (ε / c) :=
      mul_le_mul_of_nonneg_left (le_trans hpow hn.le) hc
    have heq : c * (ε / c) = ε := by field_simp
    linarith

/-- Under the source variance hypothesis `Var(f) ≤ σ²`, some layer count `k ≥ 4` makes the
signed layered estimator of [Montanaro2015], Theorem 5 accurate to additive error `ε` with
probability at least `2 / 3`. The choice of `k` depends only on `σ` and `ε`. -/
theorem theorem5_additive_variance_guarantee (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ k : ℕ, 4 ≤ k ∧
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
        (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ),
        let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
        (∑ i, BornProb (ApplyGate A (Ket j)) i * (f i - μ) ^ 2) ≤ σ ^ 2 →
        (∑ ω with |signedMeanEstimate k f σ ω - μ| ≤ ε,
            (signedMeanLaw k A j f σ hA).prob ω)
          ≥ 2 / 3 := by
  obtain ⟨k, hk, hprec⟩ :=
    exists_variance_layer_precision (8 * σ) ε (by positivity) hε
  refine ⟨k, hk, ?_⟩
  intro I _ _ _ A j f hA μ hv
  have hmain := signed_centered_same_program_mean_guarantee I k A j f σ hA hk hσ hv
  refine le_trans hmain ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨Finset.mem_univ _, le_trans hω.2 hprec⟩
  · intro ω _ _
    exact (signedMeanLaw k A j f σ hA).nonneg ω

end Qatlib.Papers.MCMontanaro15.MonteCarlo
