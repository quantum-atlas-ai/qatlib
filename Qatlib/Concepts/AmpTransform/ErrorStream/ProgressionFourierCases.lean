/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedProgressionWindow

/-!
# Fourier cases for a finite arithmetic progression

This module evaluates `aqProgressionFourier` by separating resonant, geometric, and vanishing
cases. It also bounds the normalized progression-plus-noise sum, supplying the elementary
Fourier calculations used in the amplified-transform analysis of [Cornwell2014].

## Main statements

* `aq_progression_fourier_resonant`: At a frequency with N dividing P · y, the progression
  Fourier sum is M times the phase at its starting point.
* `aq_progression_fourier_geometric`: At a frequency with N not dividing P · y, the progression
  Fourier sum equals the initial phase times the geometric quotient (1−phaseᴹ)/(1−phase).
* `aq_progression_noise_pairing_norm_le`: The squared norm of the progression Fourier sum plus
  the noise phase sum, divided by M plus the noise cardinality, is at most one. See
  [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.NoiseEnvelope

set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped BigOperators Classical

/-- For N > 0, the Fourier phase `aqPhase N x y` equals one exactly when x · y is divisible by
N. -/
theorem aq_phase_eq_one_iff (N x y : ℕ) (hN : 0 < N) :
    aqPhase N x y=1 ↔ (x*y)%N=0 := by
  have he : aqPhase N x y=primRoot N^(-((x*y : ℕ) : ℤ)) := by
    rw [primRoot_zpow_eq_exp]
    unfold aqPhase
    congr 1
    push_cast
    ring
  rw [he, primRoot_zpow_eq_one_iff hN, dvd_neg, Int.natCast_dvd_natCast,
    Nat.dvd_iff_mod_eq_zero]

/-- The phase at s+rP factors as the phase at s times the r-th power of the phase at P. -/
theorem aq_phase_progression_factor (N s P y r : ℕ) :
    aqPhase N (s+r*P) y=aqPhase N s y*(aqPhase N P y)^r := by
  unfold aqPhase
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At a frequency with N dividing P · y, the progression Fourier sum is M times the phase at
its starting point. -/
theorem aq_progression_fourier_resonant (N s M P y : ℕ) (_hM : 0 < M)
    (hN : 0 < N) (hy : (P*y)%N=0) :
    aqProgressionFourier N s M P y=(M : ℂ)*aqPhase N s y := by
  unfold aqProgressionFourier
  simp_rw [aq_phase_progression_factor, (aq_phase_eq_one_iff N P y hN).mpr hy,
    one_pow, mul_one]
  simp

/-- At a frequency with N not dividing P · y, the progression Fourier sum equals the initial
phase times the geometric quotient (1−phaseᴹ)/(1−phase). -/
theorem aq_progression_fourier_geometric (N s M P y : ℕ) (_hM : 0 < M)
    (hN : 0 < N) (hy : (P*y)%N ≠ 0) :
    aqProgressionFourier N s M P y=aqPhase N s y*
      ((1-(aqPhase N P y)^M)/(1-aqPhase N P y)) := by
  have hp : aqPhase N P y ≠ 1 := fun he => hy ((aq_phase_eq_one_iff N P y hN).mp he)
  unfold aqProgressionFourier
  simp_rw [aq_phase_progression_factor]
  rw [← Finset.mul_sum, geom_sum_eq hp]
  congr 1
  rw [show 1-(aqPhase N P y)^M = -((aqPhase N P y)^M-1) by ring,
    show 1-aqPhase N P y = -(aqPhase N P y-1) by ring, neg_div_neg_eq]

/-- The progression Fourier sum vanishes when N divides M · P · y but does not divide P · y. -/
theorem aq_progression_fourier_annihilated (N s M P y : ℕ) (hN : 0 < N)
    (hyP : (P*y)%N ≠ 0) (hyMP : (M*P*y)%N=0) :
    aqProgressionFourier N s M P y=0 := by
  by_cases hM : M=0
  · simp [hM, aqProgressionFourier]
  have hp : (aqPhase N P y)^M=aqPhase N (M*P) y := by
    unfold aqPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [aq_progression_fourier_geometric N s M P y (by omega) hN hyP, hp,
    (aq_phase_eq_one_iff N (M*P) y hN).mpr hyMP]
  simp

/-- The squared norm of the progression Fourier sum plus the noise phase sum, divided by M plus
the noise cardinality, is at most one. See [Cornwell2014]. -/
theorem aq_progression_noise_pairing_norm_le (N s M P y : ℕ) (G : Finset (Fin N)) :
    ‖(aqProgressionFourier N s M P y+∑ z ∈ G, aqPhase N z.val y)/
      ((M+G.card : ℕ) : ℂ)‖^2 ≤ 1 := by
  have hu (x : ℕ) : ‖aqPhase N x y‖=1 := by
    simp [aqPhase, Complex.norm_exp]
  have hA : ‖aqProgressionFourier N s M P y‖ ≤ (M : ℝ) := by
    unfold aqProgressionFourier
    exact (norm_sum_le _ _).trans_eq (by simp only [hu, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one])
  have hG : ‖∑ z ∈ G, aqPhase N z.val y‖ ≤ (G.card : ℝ) := by
    exact (norm_sum_le _ _).trans_eq (by simp only [hu, Finset.sum_const,
      nsmul_eq_mul, mul_one])
  by_cases hT : M+G.card=0
  · simp [hT]
  have ht : (0:ℝ) < ((M+G.card : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M+G.card)
  have hn : ‖aqProgressionFourier N s M P y+∑ z ∈ G, aqPhase N z.val y‖ ≤
      ((M+G.card : ℕ) : ℝ) := by
    exact (norm_add_le _ _).trans ((add_le_add hA hG).trans_eq (by push_cast; rfl))
  have hdiv : ‖(aqProgressionFourier N s M P y+∑ z ∈ G, aqPhase N z.val y)/
      ((M+G.card : ℕ) : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_one ht).mpr hn
  simpa only [one_pow] using! pow_le_pow_left₀ (norm_nonneg _) hdiv 2

end Qatlib.Concepts.AmpTransform.ErrorStream
