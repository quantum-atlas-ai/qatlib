/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiracEquation16.Dispersion

open Real

def firstBZ (ℓ p : ℝ) : Prop := -(Real.pi / ℓ) < p ∧ p ≤ Real.pi / ℓ

def dispersionPhase (Nstar ℓ p : ℝ) : ℝ := Nstar * ℓ * p

theorem phase_lt_pi_of_lt_one {Nstar ℓ p : ℝ} (hℓ : 0 < ℓ)
    (hN0 : 0 < Nstar) (hN1 : Nstar < 1) (hp : firstBZ ℓ p) :
    -Real.pi < dispersionPhase Nstar ℓ p ∧ dispersionPhase Nstar ℓ p < Real.pi := by
  unfold firstBZ at hp
  obtain ⟨hp1, hp2⟩ := hp

  have hp1' : -Real.pi / ℓ < p := by simpa [neg_div] using hp1
  have hlow : -Real.pi < p * ℓ := (div_lt_iff₀ hℓ).1 hp1'
  have hhigh : p * ℓ ≤ Real.pi := (le_div_iff₀ hℓ).1 hp2
  unfold dispersionPhase
  constructor
  · have h1 : -Nstar * Real.pi < Nstar * (p * ℓ) := by
      have := mul_lt_mul_of_pos_left hlow hN0
      nlinarith
    have hlt : -Real.pi < -Nstar * Real.pi := by nlinarith [Real.pi_pos]
    nlinarith
  · have h1 : Nstar * (p * ℓ) ≤ Nstar * Real.pi :=
      mul_le_mul_of_nonneg_left hhigh hN0.le
    have hlt : Nstar * Real.pi < Real.pi := by nlinarith [Real.pi_pos]
    nlinarith

theorem scalar_phase_zero_of_lt_one {Nstar ℓ p : ℝ} (hℓ : 0 < ℓ)
    (hN0 : 0 < Nstar) (hN1 : Nstar < 1) (hp : firstBZ ℓ p)
    (hzero : Real.sin (dispersionPhase Nstar ℓ p) = 0) : p = 0 := by
  obtain ⟨h1, h2⟩ := phase_lt_pi_of_lt_one hℓ hN0 hN1 hp
  have hphase : dispersionPhase Nstar ℓ p = 0 :=
    (Real.sin_eq_zero_iff_of_lt_of_lt h1 h2).1 hzero
  unfold dispersionPhase at hphase

  have hNe : Nstar * ℓ ≠ 0 := by positivity
  exact (mul_eq_zero.1 hphase).resolve_left hNe

theorem scalar_phase_half_zero (ℓ p : ℝ) (hℓ : 0 < ℓ) (hp : firstBZ ℓ p)
    (hzero : Real.sin (dispersionPhase (1 / 2) ℓ p) = 0) : p = 0 := by
  exact scalar_phase_zero_of_lt_one hℓ (by norm_num) (by norm_num) hp hzero

theorem dispersionPhase_half_eq_zero_iff (ℓ p : ℝ) (hℓ : 0 < ℓ) (hp : firstBZ ℓ p) :
    dispersionPhase (1 / 2) ℓ p = 0 ↔ p = 0 := by
  constructor
  · intro h
    unfold dispersionPhase at h
    have hNe : (1 / 2 : ℝ) * ℓ ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hNe
  · intro h
    subst h
    unfold dispersionPhase
    ring

theorem scalar_abs_phase_zero (ℓ px py : ℝ) (hℓ : 0 < ℓ) (hpx : px = 0)
    (hpy : firstBZ ℓ py)
    (hzero : Real.sin (dispersionPhase (1 / 2) ℓ (Real.sqrt (px ^ 2 + py ^ 2))) = 0) :
    py = 0 := by

  have hmag : Real.sqrt (px ^ 2 + py ^ 2) = |py| := by
    rw [hpx]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    exact Real.sqrt_sq_eq_abs py
  rw [hmag] at hzero

  unfold firstBZ at hpy
  obtain ⟨hpy1, hpy2⟩ := hpy
  have hb1 : -(Real.pi / ℓ) < |py| := by
    have h0 : (0 : ℝ) ≤ |py| := abs_nonneg py
    have : 0 < Real.pi / ℓ := div_pos Real.pi_pos hℓ
    linarith
  have hb2 : |py| ≤ Real.pi / ℓ := by
    rw [abs_le]
    exact ⟨by linarith, hpy2⟩
  exact abs_eq_zero.1 (scalar_phase_half_zero ℓ |py| hℓ ⟨hb1, hb2⟩ hzero)

theorem eigenvalue_half_eq_one_iff (ℓ p : ℝ) (hℓ : 0 < ℓ) (hp : firstBZ ℓ p) :
    Complex.exp (Complex.I * (dispersionPhase (1 / 2) ℓ p : ℂ)) = 1 ↔ p = 0 := by
  constructor
  · intro h

    have h' : Complex.exp ((dispersionPhase (1 / 2) ℓ p : ℂ) * Complex.I) = 1 := by
      simpa [mul_comm] using h
    have hsin : Real.sin (dispersionPhase (1 / 2) ℓ p) = 0 := by
      have him := congrArg Complex.im h'
      rw [Complex.exp_ofReal_mul_I] at him
      simpa using! him
    exact scalar_phase_half_zero ℓ p hℓ hp hsin
  · intro h
    subst h
    unfold dispersionPhase
    simp

end Qatlib.Papers.DiracEquation16.Dispersion
