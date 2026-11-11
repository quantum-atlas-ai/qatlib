/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.HadamardTest
import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

/-!
# Scaled statistical error bound for tensor-network estimation

Proves the scaled sampling-error estimate used as a statistical component of Theorem 3.4 in
[AradLandau2010]. The theorem `theorem3_4_additive_statistical_core` applies the empirical
sign-mean bound to a positive scale `Δ`.

For positive sample count `N` and tolerance `ε` with `N * ε² ≥ 16`, the probability that the
scaled complex estimate has error at least `Δ * ε` is at most one quarter.

## Main statements

* `theorem3_4_additive_statistical_core`: bounds the scaled empirical-mean failure probability.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Theorem34

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.TensorNetwork08.MainResults.HadamardTest

/-- For positive `Δ`, `N`, and `ε`, mean `μ ∈ [-1, 1]`, and `N * ε² ≥ 16`, the probability that
the scaled empirical sign mean has complex-norm error at least `Δ * ε` is at most one
quarter. See [AradLandau2010]. -/
theorem theorem3_4_additive_statistical_core
    (Δ : ℝ) (hΔ : 0 < Δ)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (hNε : (16 : ℝ) ≤ (N : ℝ) * ε ^ 2) :
    (rademacherDist μ hμ).probEvent
      (fun ω : Fin N → Bool =>
        Δ * ε ≤ ‖(Δ : ℂ) * (FinDist.avg spin ω : ℂ) - (Δ : ℂ) * (μ : ℂ)‖) ≤ 1 / 4 := by
  have hbase := hadamard_test_bias_bound μ hμ N hN ε hε hNε

  have heq :
      (fun ω : Fin N → Bool =>
        Δ * ε ≤ ‖(Δ : ℂ) * (FinDist.avg spin ω : ℂ) - (Δ : ℂ) * (μ : ℂ)‖)
        = (fun ω : Fin N → Bool => ε ≤ |FinDist.avg spin ω - μ|) := by
    funext ω
    have hcast : (Δ : ℂ) * (FinDist.avg spin ω : ℂ) - (Δ : ℂ) * (μ : ℂ)
        = ((Δ * (FinDist.avg spin ω - μ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hΔ]
    apply propext
    constructor
    · intro h
      exact le_of_mul_le_mul_left h hΔ
    · intro h
      exact mul_le_mul_of_nonneg_left h (le_of_lt hΔ)
  simpa only [heq] using hbase

end Qatlib.Papers.TensorNetwork08.MainResults.Theorem34
