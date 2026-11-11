/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch

/-!
# Exact two-mode resonance bounds

This module evaluates Hamiltonian evolution on a scaled difference of eigenvectors with energies
`1 + δp` and `1 - δm`. At time `Real.pi / (δp + δm)`, the difference becomes their sum up to a
phase, giving amplitude and squared-amplitude lower bounds used for the search lemma of
[ChakrabortyEtAl2016].

## Main statements

* `resonant_symmetric_evolution`: exact difference-to-sum evolution.
* `resonant_sharp_probability`: squared-amplitude lower bound from lower bounds on both
  overlaps.
* `resonant_sharp_gap_probability`: specialization to `spectralGapParam c`.

## References

* [Chakraborty et al., 2016][ChakrabortyEtAl2016]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialWalk15.MainResults.Lemma1SharpResonance

variable {I : Type} [Fintype I] [DecidableEq I]

/-- For eigenvectors at energies `1 + δp` and `1 - δm` with positive shifts, evolution for time
`Real.pi / (δp + δm)` maps their difference scaled by `1 / Real.sqrt 2` to their similarly
scaled sum times the upper-mode phase [ChakrabortyEtAl2016]. -/
theorem resonant_symmetric_evolution (H : Matrix I I ℂ) (up um : QState I)
    (δp δm : ℝ) (hp : 0 < δp) (hm : 0 < δm)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um) :
    HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)) =
      (Complex.exp ((-Complex.I*((Real.pi/(δp+δm) : ℝ) : ℂ))*((1+δp : ℝ) : ℂ))) •
        (((Real.sqrt 2)⁻¹ : ℂ) • (up + um)) := by
  set t : ℝ := Real.pi/(δp+δm) with ht
  have hup' : HamiltonianEvolution H t *ᵥ up =
      Complex.exp ((-Complex.I*(t : ℂ))*((1+δp : ℝ) : ℂ)) • up :=
    hamiltonianEvolution_eigenvector H up (1+δp) t hup
  have hum' : HamiltonianEvolution H t *ᵥ um =
      Complex.exp ((-Complex.I*(t : ℂ))*((1-δm : ℝ) : ℂ)) • um :=
    hamiltonianEvolution_eigenvector H um (1-δm) t hum
  have hflip : Complex.exp ((-Complex.I*(t : ℂ))*((1-δm : ℝ) : ℂ)) =
      -Complex.exp ((-Complex.I*(t : ℂ))*((1+δp : ℝ) : ℂ)) := by
    dsimp only [t, ht]
    exact rank_one_resonant_phase_flip δp δm hp hm
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hup', hum', hflip]
  set P : ℂ := Complex.exp ((-Complex.I*(t : ℂ))*((1+δp : ℝ) : ℂ)) with hP
  have hstep : P • up - (-P) • um = P • (up + um) := by
    rw [neg_smul, sub_neg_eq_add, smul_add]
  rw [hstep, smul_smul, smul_smul, mul_comm]

/-- At the resonant time, the transition-amplitude norm from the scaled eigenvector difference
is `‖rp + rm‖ / Real.sqrt 2` when the marked-state overlaps with the two eigenvectors are
the real numbers `rp` and `rm`. -/
theorem resonant_symmetric_amplitude (H : Matrix I I ℂ) (w up um : QState I)
    (δp δm rp rm : ℝ) (hp : 0 < δp) (hm : 0 < δm)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Inner w up = (rp : ℂ)) (hwm : Inner w um = (rm : ℂ)) :
    ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ =
      (Real.sqrt 2)⁻¹ * ‖rp + rm‖ := by
  rw [resonant_symmetric_evolution H up um δp δm hp hm hup hum]
  rw [inner_smul_state, inner_smul_state, inner_add_state, hwu, hwm]
  set t : ℝ := Real.pi/(δp+δm) with ht
  set P : ℂ := Complex.exp ((-Complex.I*(t : ℂ))*((1+δp : ℝ) : ℂ)) with hP
  have hParg : (-Complex.I*(t : ℂ))*((1+δp : ℝ) : ℂ) =
      ((-(t*(1+δp)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hPnorm : ‖P‖ = 1 := by
    rw [hP, hParg, Complex.norm_exp_ofReal_mul_I]
  have hcnorm : ‖(((Real.sqrt 2)⁻¹ : ℂ))‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsum : ‖((rp : ℂ) + (rm : ℂ))‖ = ‖rp + rm‖ := by
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_mul, norm_mul, hPnorm, hcnorm, hsum, one_mul]

/-- If both real marked-state overlaps are at least a nonnegative `r`, the resonant
transition-amplitude norm from the eigenvector difference scaled by `1 / Real.sqrt 2` is at
least `Real.sqrt 2 * r`. -/
theorem resonant_sharp_amplitude (H : Matrix I I ℂ) (w up um : QState I)
    (δp δm r rp rm : ℝ) (hp : 0 < δp) (hm : 0 < δm) (hr : 0 ≤ r)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Inner w up = (rp : ℂ)) (hwm : Inner w um = (rm : ℂ))
    (hrp : r ≤ rp) (hrm : r ≤ rm) :
    Real.sqrt 2 * r ≤
      ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ := by
  rw [resonant_symmetric_amplitude H w up um δp δm rp rm hp hm hup hum hwu hwm]
  have hsumpos : ‖rp + rm‖ = rp + rm := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hsumpos]
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two]; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have heq : (Real.sqrt 2)⁻¹ * (2 * r) = Real.sqrt 2 * r := by
    rw [inv_mul_eq_div, div_eq_iff hpos.ne']
    nlinarith [hsq]
  rw [← heq]
  have hfac : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hfac

/-- If both real marked-state overlaps are at least a nonnegative `r`, the squared resonant
transition-amplitude norm from the eigenvector difference scaled by `1 / Real.sqrt 2` is at
least `2 * r ^ 2`. -/
theorem resonant_sharp_probability (H : Matrix I I ℂ) (w up um : QState I)
    (δp δm r rp rm : ℝ) (hp : 0 < δp) (hm : 0 < δm) (hr : 0 ≤ r)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Inner w up = (rp : ℂ)) (hwm : Inner w um = (rm : ℂ))
    (hrp : r ≤ rp) (hrm : r ≤ rm) :
    2 * r ^ 2 ≤
      ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ ^ 2 := by
  have hamp := resonant_sharp_amplitude H w up um δp δm r rp rm hp hm hr
    hup hum hwu hwm hrp hrm
  have hlhs : 0 ≤ Real.sqrt 2 * r := by positivity
  have hsquare : (Real.sqrt 2 * r) * (Real.sqrt 2 * r) ≤
      ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ *
      ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ :=
    mul_self_le_mul_self hlhs hamp
  have hsq : (Real.sqrt 2 * r) * (Real.sqrt 2 * r) = 2 * r ^ 2 := by
    rw [← pow_two, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsq] at hsquare
  simpa only [pow_two] using hsquare

/-- If `spectralGapParam c` is nonnegative and both real marked-state overlaps are at least its
half-square-root `Real.sqrt (spectralGapParam c / 2)`, the squared resonant amplitude is at
least `spectralGapParam c` [ChakrabortyEtAl2016]. -/
theorem resonant_sharp_gap_probability (H : Matrix I I ℂ) (w up um : QState I)
    (c δp δm rp rm : ℝ) (hp : 0 < δp) (hm : 0 < δm)
    (hν : 0 ≤ spectralGapParam c)
    (hup : H *ᵥ up = ((1+δp : ℝ) : ℂ) • up)
    (hum : H *ᵥ um = ((1-δm : ℝ) : ℂ) • um)
    (hwu : Inner w up = (rp : ℂ)) (hwm : Inner w um = (rm : ℂ))
    (hrp : Real.sqrt (spectralGapParam c / 2) ≤ rp)
    (hrm : Real.sqrt (spectralGapParam c / 2) ≤ rm) :
    spectralGapParam c ≤
      ‖Inner w (HamiltonianEvolution H (Real.pi/(δp+δm)) *ᵥ
        (((Real.sqrt 2)⁻¹ : ℂ) • (up - um)))‖ ^ 2 := by
  have hr : 0 ≤ Real.sqrt (spectralGapParam c / 2) := Real.sqrt_nonneg _
  have hprob := resonant_sharp_probability H w up um δp δm
    (Real.sqrt (spectralGapParam c / 2)) rp rm hp hm hr hup hum hwu hwm hrp hrm
  have hsq : 2 * (Real.sqrt (spectralGapParam c / 2)) ^ 2 = spectralGapParam c := by
    rw [Real.sq_sqrt (by linarith)]
    ring
  rwa [hsq] at hprob

end Qatlib.Papers.SpatialWalk15.MainResults.Lemma1SharpResonance
