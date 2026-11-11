/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Total error of the two approximations (source Section IV C)

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Section IV C ("Total Error").

The source combines the two error sources of the state-preparation analysis: the few-level
approximation of Theorem 1 gives an overlap `1 - ε₁` with the exact state, and the Rabi
oscillation bound of Theorem 2 gives an overlap `1 - ε₂` with the desired one-level state.
Section IV C then states that the inner product between the exact state produced and the
desired state is at least `1 - ε₁ - ε₂ - 2√(ε₁ε₂)`, that this is `1 - O(ε₁ + ε₂)` because
`√(ε₁ε₂) ≤ max{ε₁, ε₂}`, and that the probability of success, being the square of this inner
product, is also `1 - O(ε₁ + ε₂)`.

This module formalises exactly these three steps with explicit constants: the `2νλ`/`3νλ²t`
and `(1/√3)(λ/ω)²` errors of the two theorems are only ever queried through `ε₁, ε₂ ≥ 0` and
their maximum, so the combination is stated at that level of generality.

Boundary: the source does not fix the hidden constants of its `O(ε₁ + ε₂)` notation; the
constants `4` and `8` below are the ones produced by the displayed inequality, and they are
not claimed to be optimal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.FermionQFT17.MainResults.TotalError

/-- Source Section IV C: the cross term `√(ε₁ε₂)` is bounded by `max{ε₁, ε₂}`, which is what
collapses `1 - ε₁ - ε₂ - 2√(ε₁ε₂)` into `1 - O(ε₁ + ε₂)`. -/
theorem sqrt_mul_le_max {e₁ e₂ : ℝ} (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂) :
    Real.sqrt (e₁ * e₂) ≤ max e₁ e₂ := by
  have hmax₁ : e₁ ≤ max e₁ e₂ := le_max_left _ _
  have hmax₂ : e₂ ≤ max e₁ e₂ := le_max_right _ _
  have hmax₀ : 0 ≤ max e₁ e₂ := le_trans h₁ hmax₁
  have hprod : e₁ * e₂ ≤ max e₁ e₂ * max e₁ e₂ :=
    mul_le_mul hmax₁ hmax₂ h₂ hmax₀
  calc Real.sqrt (e₁ * e₂) ≤ Real.sqrt (max e₁ e₂ * max e₁ e₂) := Real.sqrt_le_sqrt hprod
    _ = max e₁ e₂ := Real.sqrt_mul_self hmax₀

/-- Source Section IV C: the combined overlap `1 - ε₁ - ε₂ - 2√(ε₁ε₂)` is at least
`1 - 4ε` whenever `ε` dominates both `ε₁` and `ε₂`. -/
theorem combined_inner_product_lower {e₁ e₂ e : ℝ} (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂)
    (h : max e₁ e₂ ≤ e) :
    1 - 4 * e ≤ 1 - e₁ - e₂ - 2 * Real.sqrt (e₁ * e₂) := by
  have hsqrt := sqrt_mul_le_max h₁ h₂
  have h₁' : e₁ ≤ e := le_trans (le_max_left e₁ e₂) h
  have h₂' : e₂ ≤ e := le_trans (le_max_right e₁ e₂) h
  linarith

/-- Source Section IV C: the success probability, the square of the combined overlap, is at
least `1 - 8ε` under the same domination hypothesis; this is the source's claim that the
probability of success is `1 - O(ε₁ + ε₂)`. -/
theorem combined_success_probability_lower {e₁ e₂ e : ℝ} (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂)
    (h : max e₁ e₂ ≤ e) (h4 : 4 * e ≤ 1) :
    1 - 8 * e ≤ (1 - e₁ - e₂ - 2 * Real.sqrt (e₁ * e₂)) ^ 2 := by
  have hlower := combined_inner_product_lower h₁ h₂ h
  have hnonneg : (0 : ℝ) ≤ 1 - 4 * e := by linarith
  have hsq : (1 - 4 * e) ^ 2 ≤ (1 - e₁ - e₂ - 2 * Real.sqrt (e₁ * e₂)) ^ 2 :=
    pow_le_pow_left₀ hnonneg hlower 2
  set b := 1 - e₁ - e₂ - 2 * Real.sqrt (e₁ * e₂) with hb
  have hexp : (1 - 4 * e) ^ 2 = 1 - 8 * e + 16 * e ^ 2 := by ring
  have h16 : (0 : ℝ) ≤ 16 * e ^ 2 := by positivity
  linarith

/-- Source Section IV C: the squared overlap between the exact state produced and the
desired state is at least `1 - 2ε` whenever the overlap itself is at least `1 - ε` with
`ε ≤ 1`; this is the source's step from the inner-product bound to the probability bound. -/
theorem square_overlap_lower {a e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1)
    (h : 1 - e ≤ a) :
    1 - 2 * e ≤ a ^ 2 := by
  have hsq : (1 - e) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) h 2
  nlinarith [hsq, mul_nonneg he (sub_nonneg.mpr he1)]

end Qatlib.Papers.FermionQFT17.MainResults.TotalError
