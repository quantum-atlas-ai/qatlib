/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Opposite azimuthal modes in the CK helicity spectrum

The modal expression in Irvine and Bouwmeester separates into
a signed difference of squared amplitudes and a pairing of the
opposite azimuthal indices. The result below integrates this
expression over positive frequencies for a finite angular set.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HelicitySpec

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-- The stationary contribution of the two curl signs at one angular mode. -/
noncomputable def ckSignedModeNorm (plus minus : ℤ → ℂ) (m : ℤ) : ℝ :=
  ‖plus m‖ ^ 2 - ‖minus m‖ ^ 2

/-- Within each curl sign the time-dependent term pairs opposite
azimuthal indices, with opposite signs for the two branches. -/
def ckOppositeModeProduct (plus minus : ℤ → ℂ) (m : ℤ) : ℂ :=
  plus m * plus (-m) - minus m * minus (-m)

/-- The real modal expression combines the stationary contribution
with the negative real part of the paired term at twice the frequency. -/
noncomputable def ckSpectralHelicityAt (plus minus : ℤ → ℂ) (m : ℤ) (ω t : ℝ) : ℝ :=
  ckSignedModeNorm plus minus m -
    (ckOppositeModeProduct plus minus m *
      Complex.exp (-(2 : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))).re

/-- The real-part expression equals the half-weighted oscillatory
term together with its complex conjugate in the published formula. -/
theorem ckSpectralHelicityAt_eq_conj (plus minus : ℤ → ℂ) (m : ℤ) (ω t : ℝ) :
    let z := ckOppositeModeProduct plus minus m *
      Complex.exp (-(2 : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
    (ckSpectralHelicityAt plus minus m ω t : ℂ) =
      (ckSignedModeNorm plus minus m : ℂ) - (z + conj z) / 2 := by
  let z := ckOppositeModeProduct plus minus m *
    Complex.exp (-(2 : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
  have hz : z + conj z = (2 : ℂ) * (z.re : ℂ) := by
    rw [two_mul]
    apply Complex.ext <;> simp
  change ((ckSignedModeNorm plus minus m - z.re : ℝ) : ℂ) = _ - (z + conj z) / 2
  rw [hz, Complex.ofReal_sub]
  ring

/-- An absent factor in each opposite-index product removes all time
dependence at the corresponding angular mode and frequency. -/
theorem ckSpectralHelicityAt_eq_signed_of_unpaired (plus minus : ℤ → ℂ) (m : ℤ) (ω t : ℝ)
    (hp : plus m = 0 ∨ plus (-m) = 0) (hn : minus m = 0 ∨ minus (-m) = 0) :
    ckSpectralHelicityAt plus minus m ω t = ckSignedModeNorm plus minus m := by
  have hplus : plus m * plus (-m) = 0 := mul_eq_zero.mpr hp
  have hminus : minus m * minus (-m) = 0 := mul_eq_zero.mpr hn
  simp [ckSpectralHelicityAt, ckOppositeModeProduct, hplus, hminus]

/-- The magnitude of the modal helicity has a time-independent
bound in terms of the squared amplitudes of both opposite indices. -/
theorem abs_ckSpectralHelicityAt_le (plus minus : ℤ → ℂ) (m : ℤ) (ω t : ℝ) :
    |ckSpectralHelicityAt plus minus m ω t| ≤
      2 * (‖plus m‖ ^ 2 + ‖plus (-m)‖ ^ 2 + ‖minus m‖ ^ 2 + ‖minus (-m)‖ ^ 2) := by
  let q := ckOppositeModeProduct plus minus m
  let phase := Complex.exp (-(2 : ℂ) * Complex.I * (ω : ℂ) * (t : ℂ))
  have hPhase : ‖phase‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hPaired : |(q * phase).re| ≤ ‖q‖ := by
    simpa only [norm_mul, hPhase, mul_one] using Complex.abs_re_le_norm (q * phase)
  have hProd : ‖q‖ ≤ ‖plus m‖ * ‖plus (-m)‖ + ‖minus m‖ * ‖minus (-m)‖ := by
    simpa only [q, ckOppositeModeProduct, norm_mul] using
      norm_sub_le (plus m * plus (-m)) (minus m * minus (-m))
  have hSigned : |ckSignedModeNorm plus minus m| ≤ ‖plus m‖ ^ 2 + ‖minus m‖ ^ 2 := by
    have h := norm_sub_le (‖plus m‖ ^ 2) (‖minus m‖ ^ 2)
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (sq_nonneg ‖plus m‖), abs_of_nonneg (sq_nonneg ‖minus m‖)] at h
    exact h
  change |ckSignedModeNorm plus minus m - (q * phase).re| ≤ _
  have hAll : |ckSignedModeNorm plus minus m - (q * phase).re| ≤
      |ckSignedModeNorm plus minus m| + |(q * phase).re| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (ckSignedModeNorm plus minus m) (q * phase).re
  nlinarith [sq_nonneg (‖plus m‖ - ‖plus (-m)‖), sq_nonneg (‖minus m‖ - ‖minus (-m)‖),
    sq_nonneg ‖plus (-m)‖, sq_nonneg ‖minus (-m)‖]

/-- Weighted square integrability of the two curl signs at the
opposite indices gives absolute convergence of their modal integral. -/
theorem integrableOn_ckSpectralHelicityAt (plus minus : ℤ → ℝ → ℂ) (m : ℤ) (t : ℝ)
    (hp : ∀ j, Measurable (plus j)) (hn : ∀ j, Measurable (minus j))
    (hpm : IntegrableOn (fun k : ℝ => ‖plus m k‖ ^ 2 / k ^ 3) (Ioi 0))
    (hpn : IntegrableOn (fun k : ℝ => ‖plus (-m) k‖ ^ 2 / k ^ 3) (Ioi 0))
    (hnm : IntegrableOn (fun k : ℝ => ‖minus m k‖ ^ 2 / k ^ 3) (Ioi 0))
    (hnn : IntegrableOn (fun k : ℝ => ‖minus (-m) k‖ ^ 2 / k ^ 3) (Ioi 0)) :
    IntegrableOn (fun k : ℝ =>
      ckSpectralHelicityAt (fun j => plus j k) (fun j => minus j k) m k t / k ^ 3) (Ioi 0) := by
  let f := fun k : ℝ =>
    ckSpectralHelicityAt (fun j => plus j k) (fun j => minus j k) m k t / k ^ 3
  have hPhase : Continuous (fun k : ℝ =>
      Complex.exp (-(2 : ℂ) * Complex.I * (k : ℂ) * (t : ℂ))) := by fun_prop
  have hs : Measurable (fun k : ℝ => ‖plus m k‖ ^ 2 - ‖minus m k‖ ^ 2) :=
    ((hp m).norm.pow_const 2).sub ((hn m).norm.pow_const 2)
  have hProd : Measurable (fun k : ℝ => plus m k * plus (-m) k - minus m k * minus (-m) k) :=
    ((hp m).mul (hp (-m))).sub ((hn m).mul (hn (-m)))
  have hf : Measurable f :=
    (hs.sub (Complex.continuous_re.measurable.comp (hProd.mul hPhase.measurable))).div
      (measurable_id.pow_const 3)
  refine ((((hpm.add hpn).add hnm).add hnn).const_mul (2 : ℝ)).mono' hf.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun k (hk : 0 < k) => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hk 3)]
  calc
    _ ≤ (2 * (‖plus m k‖ ^ 2 + ‖plus (-m) k‖ ^ 2 + ‖minus m k‖ ^ 2 + ‖minus (-m) k‖ ^ 2)) /
        k ^ 3 := div_le_div_of_nonneg_right (abs_ckSpectralHelicityAt_le _ _ m k t) (pow_nonneg hk.le 3)
    _ = _ := by simp only [Pi.add_apply]; ring

/-- A finite angular set of CK coefficients determines the spectral
helicity expression with the positive-frequency radial weight. -/
noncomputable def ckSpectralHelicity (modes : Finset (ℕ × ℤ))
    (plus minus : ℕ → ℤ → ℝ → ℂ) (t : ℝ) : ℝ :=
  ∫ k in Ioi (0 : ℝ), (∑ p ∈ modes,
    ckSpectralHelicityAt (fun m => plus p.1 m k) (fun m => minus p.1 m k) p.2 k t) / k ^ 3

/-- The full finite angular spectrum is integrable when every
angular coefficient and its opposite has a weighted square integral. -/
theorem integrableOn_ckSpectralHelicity (modes : Finset (ℕ × ℤ))
    (plus minus : ℕ → ℤ → ℝ → ℂ) (t : ℝ)
    (hmp : ∀ l m, Measurable (plus l m)) (hmn : ∀ l m, Measurable (minus l m))
    (hp : ∀ l m, IntegrableOn (fun k : ℝ => ‖plus l m k‖ ^ 2 / k ^ 3) (Ioi 0))
    (hn : ∀ l m, IntegrableOn (fun k : ℝ => ‖minus l m k‖ ^ 2 / k ^ 3) (Ioi 0)) :
    IntegrableOn (fun k : ℝ => (∑ p ∈ modes,
      ckSpectralHelicityAt (fun m => plus p.1 m k) (fun m => minus p.1 m k) p.2 k t) / k ^ 3) (Ioi 0) := by
  simp only [Finset.sum_div]
  exact integrable_finsetSum modes fun p _ =>
    integrableOn_ckSpectralHelicityAt (plus p.1) (minus p.1) p.2 t (hmp p.1) (hmn p.1)
      (hp p.1 p.2) (hp p.1 (-p.2)) (hn p.1 p.2) (hn p.1 (-p.2))

/-- In the absence of opposite azimuthal products the frequency
integral is the weighted signed difference of the modal norms. -/
theorem ckSpectralHelicity_eq_signed_of_unpaired (modes : Finset (ℕ × ℤ))
    (plus minus : ℕ → ℤ → ℝ → ℂ) (t : ℝ)
    (hp : ∀ p ∈ modes, ∀ k > 0, plus p.1 p.2 k = 0 ∨ plus p.1 (-p.2) k = 0)
    (hn : ∀ p ∈ modes, ∀ k > 0, minus p.1 p.2 k = 0 ∨ minus p.1 (-p.2) k = 0) :
    ckSpectralHelicity modes plus minus t =
      ∫ k in Ioi (0 : ℝ), (∑ p ∈ modes,
        ckSignedModeNorm (fun m => plus p.1 m k) (fun m => minus p.1 m k) p.2) / k ^ 3 := by
  unfold ckSpectralHelicity
  refine setIntegral_congr_fun measurableSet_Ioi fun k hk => ?_
  apply congrArg (fun h : ℝ => h / k ^ 3)
  exact Finset.sum_congr rfl fun p hp' =>
    ckSpectralHelicityAt_eq_signed_of_unpaired _ _ p.2 k t (hp p hp' k hk) (hn p hp' k hk)

end Qatlib.Papers.KnottedLight08.HelicitySpec
