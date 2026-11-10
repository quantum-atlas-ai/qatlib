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
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.KitaevReadout
open scoped BigOperators Classical

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

theorem eigenPhase_periodic (x : ℝ) (m : ℤ) : eigenPhase (x + m) = eigenPhase x := by
  unfold eigenPhase
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  push_cast
  ring

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

theorem eigenPhase_pow_eq_one_iff (φ : ℝ) (q : ℕ) :
    eigenPhase φ ^ q = 1 ↔ ∃ m : ℤ, (q : ℝ) * φ = m := by
  rw [eigenPhase_pow φ q, eigenPhase_eq_one_iff]

theorem permutation_phase_bounded_rational {n : ℕ} (p : Equiv.Perm (Reg n))
    (ψ : QState (Reg n)) (φ : ℝ) (hne : ψ ≠ 0)
    (heig : permMatrix p *ᵥ ψ = eigenPhase φ • ψ) :
    ∃ m : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ 2 ^ n ∧ (q : ℝ) * φ = m := by
  obtain ⟨q, hq0, hqle, hpow⟩ :=
    permutationEigenvalueBoundedRoot p ψ (eigenPhase φ) hne heig
  rw [card_reg] at hqle
  obtain ⟨m, hm⟩ := (eigenPhase_pow_eq_one_iff φ q).mp hpow
  exact ⟨m, q, hq0, hqle, hm⟩

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

theorem bisect_precision_le_theorem1_window (n : ℕ) :
    (2 : ℝ) ^ (-(((2 * n + 1 : ℕ) : ℤ)) - 2) ≤ (2 : ℝ) ^ (-((2 * n : ℕ) : ℤ) - 1) := by
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

theorem bisect_theorem1_precision (n : ℕ) :
    (1 / 8 : ℝ) * (2 : ℝ) ^ (-(((2 * n + 1 : ℕ) : ℤ)) + 1)
      ≤ 1 / (2 * (2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
  rw [bisect_combine (2 * n + 1), ← theorem1_window_eq n]
  exact bisect_precision_le_theorem1_window n

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
