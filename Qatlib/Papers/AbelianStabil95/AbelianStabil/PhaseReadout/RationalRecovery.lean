/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.CycleSpectra
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.PrecisionArithmetic
import Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout.MultiscaleBisection

/-!
# Rational recovery of permutation phases

The phase identities characterize roots of unity by integral multiples of their real phase.
`permutation_phase_bounded_rational` applies the bounded-order spectrum of a permutation to
obtain a denominator at most `2 ^ n`, and the remaining lemmas compare bisection precision with
the rational-recovery window. The development follows [Kitaev1995].

## Main statements

* `permutation_phase_bounded_rational`: expresses a permutation eigenphase as an integer divided
  by a bounded positive denominator.
* `bisect_theorem1_precision`: places the bisection error inside the rational-recovery window.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped BigOperators Classical

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

/-- Adding an integer to a real phase leaves `eigenPhase` unchanged, as used in [Kitaev1995]. -/
theorem eigenPhase_periodic (x : ℝ) (m : ℤ) : eigenPhase (x + m) = eigenPhase x := by
  unfold eigenPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  push_cast
  ring

/-- The phase factor `eigenPhase x` equals one exactly when `x` is an integer, as used in
[Kitaev1995]. -/
theorem eigenPhase_eq_one_iff (x : ℝ) : eigenPhase x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold eigenPhase
  rw [Complex.exp_eq_one_iff]
  have hz : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hp) Complex.I_ne_zero
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hm' : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ) := by
      rw [hm]; ring
    have hx : (x : ℂ) = (m : ℂ) := mul_left_cancel₀ hz hm'
    have hreal : (x : ℂ) = ((m : ℝ) : ℂ) := by simpa using hx
    exact Complex.ofReal_inj.mp hreal
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    push_cast
    ring

/-- The `q`th power of `eigenPhase φ` equals one exactly when `q * φ` is an integer, as used in
[Kitaev1995]. -/
theorem eigenPhase_pow_eq_one_iff (φ : ℝ) (q : ℕ) :
    eigenPhase φ ^ q = 1 ↔ ∃ m : ℤ, (q : ℝ) * φ = m := by
  rw [eigenPhase_pow φ q, eigenPhase_eq_one_iff]

/-- A permutation eigenphase on an `n`-bit register with a nonzero eigenvector has an integral
multiple with positive multiplier at most `2 ^ n`. This is the rational-phase property
underlying [Kitaev, 1995, Theorem 1][Kitaev1995]. -/
theorem permutation_phase_bounded_rational {n : ℕ} (p : Equiv.Perm (Reg n))
    (ψ : QState (Reg n)) (φ : ℝ) (hne : ψ ≠ 0)
    (heig : permMatrix p *ᵥ ψ = eigenPhase φ • ψ) :
    ∃ m : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ 2 ^ n ∧ (q : ℝ) * φ = m := by
  obtain ⟨q, hq0, hqle, hpow⟩ :=
    permutationEigenvalueBoundedRoot p ψ (eigenPhase φ) hne heig
  rw [card_reg] at hqle
  obtain ⟨m, hm⟩ := (eigenPhase_pow_eq_one_iff φ q).mp hpow
  exact ⟨m, q, hq0, hqle, hm⟩

/-- The dyadic quantity `2 ^ (-2 * n - 1)` equals the rational-recovery window `1 / (2 * 2 ^ n *
2 ^ n)` used in [Kitaev, 1995, Theorem 1][Kitaev1995]. -/
theorem theorem1_window_eq (n : ℕ) :
    (2 : ℝ) ^ (-((2 * n : ℕ) : ℤ) - 1) = 1 / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hexp : (-((2 * n : ℕ) : ℤ) - 1) = (-((2 * n : ℕ) : ℤ)) + (-1 : ℤ) := by ring
  rw [hexp, zpow_add₀ h2, _root_.zpow_neg, _root_.zpow_natCast, _root_.zpow_neg_one]
  have hpow : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * n = n + n from by omega, pow_add]
  rw [hpow]
  field_simp

/-- The bisection precision for `2 * n + 1` levels is at most the dyadic window `2 ^ (-2 * n -
1)`. -/
theorem bisect_precision_le_theorem1_window (n : ℕ) :
    (2 : ℝ) ^ (-(((2 * n + 1 : ℕ) : ℤ)) - 2) ≤ (2 : ℝ) ^ (-((2 * n : ℕ) : ℤ) - 1) := by
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

/-- The bisection error expression for `2 * n + 1` levels is at most `1 / (2 * 2 ^ n * 2 ^ n)`,
linking the precision in [Kitaev, 1995, Lemma 10][Kitaev1995] to rational recovery. -/
theorem bisect_theorem1_precision (n : ℕ) :
    (1 / 8 : ℝ) * (2 : ℝ) ^ (-(((2 * n + 1 : ℕ) : ℤ)) + 1)
      ≤ 1 / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
  rw [bisect_combine (2 * n + 1), ← theorem1_window_eq n]
  exact bisect_precision_le_theorem1_window n

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
