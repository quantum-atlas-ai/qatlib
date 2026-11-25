/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselCoefficientBridge
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Bessel

@[expose] public section

/-!
# The physical Bessel profiles of the wave coupling force

[Saenz2021HydroSpinLattices] models each droplet's wave field by the
zeroth-order Bessel function `J₀`: the coupling force of equation (17) is
the negative gradient of `J₀(k_F |x - x_j|)`, so the azimuthal force
profile is the slope `J₀'`, the curvature coefficient of equation (25) is
`α = ℱ k_F r J₀''(k_F L)`, and the gradient coefficient of equation (26)
is `β = (ℱ r / L) J₀'(k_F L)`; the identity `J₁ = -J₀'` connects the
`J₁`-kernel of equations (13)-(16) to the `J₀'`-profile of equation (17).
See [the article](https://doi.org/10.1038/s41586-021-03682-1).

This file instantiates the abstract profile of the coefficient bridge with
Mathlib's `Complex.besselJ`: `besselJ0Profile` is the real part of `J₀`
along the real axis, and `besselJ0Slope` and `besselJ0Curv` are its
derivative and second derivative, which exist at every real point because
integer-order Bessel functions are entire (`Complex.analyticAt_besselJ_int`
and `AnalyticAt.deriv`, transported to the real line by
`HasDerivAt.real_of_complex`). The main theorem below then instantiates the
bridge: the wave force with the `J₀'` profile has the generalized Kuramoto
form with the literal coefficients `α = ℱ k_F r J₀''(k_F L)` and
`β = (ℱ r / L) J₀'(k_F L)` of equations (25), (26), and a remainder
controlled by any Lipschitz constant of `J₀''` near `k_F L`; such a
constant exists on every compact interval (mean value theorem plus the
extreme value theorem), giving the fully instantiated existential bound.

The companion module `Qatlib.Papers.HydroSpinLatt21.GKModel.BesselDerivative`
proves the identity `J₀' = -J₁` connecting the two force profiles. The amplitude
normalizations `A`, `T_F` and numerical profile evaluation remain outside this
development.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HydroSpinLatt21.GKModel

open Complex

/-! ## Real Bessel profiles along the real axis -/

/-- The `J₀` wave profile of equation (17), as the real part of Mathlib's
integer-order Bessel function `J₀` along the real axis. -/
def besselJ0Profile : ℝ → ℝ := fun x => (Complex.besselJ ((0:ℤ) : ℂ) (x : ℂ)).re

/-- The slope profile `J₀'` of the coupling force in equation (17). -/
def besselJ0Slope : ℝ → ℝ := fun x => deriv besselJ0Profile x

/-- The curvature profile `J₀''`, whose value at `k_F L` is the Bessel
factor of the coefficient `α` in equation (25). -/
def besselJ0Curv : ℝ → ℝ := fun x => deriv besselJ0Slope x

/-- The `J₁` Bessel function along the real axis, used in equations (13)–(16). -/
def besselJ1Profile : ℝ → ℝ := fun x => (Complex.besselJ 1 (x : ℂ)).re

/-! ## Differentiability from entire analyticity -/

/-- The `J₀` profile is differentiable at every real point, with derivative
the real part of the complex derivative of `besselJ`. -/
theorem hasDerivAt_besselJ0Profile (x : ℝ) :
    HasDerivAt besselJ0Profile ((deriv (Complex.besselJ ((0:ℤ) : ℂ)) (x : ℂ)).re) x :=
  ((Complex.analyticAt_besselJ_int 0 x).differentiableAt.hasDerivAt).real_of_complex

/-- The slope profile is the real part of the complex derivative of
`besselJ` along the real axis. -/
theorem besselJ0Slope_eq (x : ℝ) :
    besselJ0Slope x = (deriv (Complex.besselJ ((0:ℤ) : ℂ)) (x : ℂ)).re :=
  (hasDerivAt_besselJ0Profile x).deriv

/-- The slope profile `J₀'` is differentiable at every real point. -/
theorem hasDerivAt_besselJ0Slope_complex (x : ℝ) :
    HasDerivAt besselJ0Slope ((deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ))) (x : ℂ)).re) x := by
  have h := ((Complex.analyticAt_besselJ_int 0 x).deriv.differentiableAt.hasDerivAt).real_of_complex
  rw [funext (fun y => besselJ0Slope_eq y)]
  exact h

/-- The curvature profile is the real part of the second complex derivative
of `besselJ` along the real axis. -/
theorem besselJ0Curv_eq (x : ℝ) :
    besselJ0Curv x = (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ))) (x : ℂ)).re :=
  (hasDerivAt_besselJ0Slope_complex x).deriv

/-- The slope profile `J₀'` is differentiable with derivative `J₀''` at
every real point: the derivative orders required by equations (25), (26)
hold by construction. -/
theorem hasDerivAt_besselJ0Slope (x : ℝ) :
    HasDerivAt besselJ0Slope (besselJ0Curv x) x := by
  rw [besselJ0Curv_eq]
  exact hasDerivAt_besselJ0Slope_complex x

/-- The curvature profile `J₀''` is differentiable at every real point. -/
theorem hasDerivAt_besselJ0Curv_complex (x : ℝ) :
    HasDerivAt besselJ0Curv
      ((deriv (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ)))) (x : ℂ)).re) x := by
  have h := ((Complex.analyticAt_besselJ_int 0 x).deriv.deriv.differentiableAt.hasDerivAt).real_of_complex
  rw [funext (fun y => besselJ0Curv_eq y)]
  exact h

/-- The derivative of the curvature profile is the real part of the third
complex derivative of `besselJ` along the real axis. -/
theorem deriv_besselJ0Curv_eq (x : ℝ) :
    deriv besselJ0Curv x = (deriv (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ)))) (x : ℂ)).re :=
  (hasDerivAt_besselJ0Curv_complex x).deriv

/-- The real slope of the zeroth-order Bessel profile is everywhere differentiable. -/
theorem differentiable_besselJ0Slope : Differentiable ℝ besselJ0Slope :=
  fun x => (hasDerivAt_besselJ0Slope x).differentiableAt

/-- The real curvature of the zeroth-order Bessel profile is everywhere differentiable. -/
theorem differentiable_besselJ0Curv : Differentiable ℝ besselJ0Curv :=
  fun x => (hasDerivAt_besselJ0Curv_complex x).differentiableAt

/-- The derivative of the curvature profile is continuous, so the curvature
profile is Lipschitz on compact intervals. -/
theorem continuous_deriv_besselJ0Curv : Continuous (deriv besselJ0Curv) := by
  have hdiff : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => (deriv (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ)))) (y : ℂ)).re)
        ((deriv (deriv (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ))))) (x : ℂ)).re) x := fun x =>
    ((Complex.analyticAt_besselJ_int 0 x).deriv.deriv.deriv.differentiableAt.hasDerivAt).real_of_complex
  have hcont : Continuous (fun y : ℝ =>
      (deriv (deriv (deriv (Complex.besselJ ((0:ℤ) : ℂ)))) (y : ℂ)).re) :=
    Differentiable.continuous (fun x => (hdiff x).differentiableAt)
  rw [funext (fun y => deriv_besselJ0Curv_eq y)]
  exact hcont

/-! ## Lipschitz control of the curvature profile -/

/-- The curvature profile `J₀''` is Lipschitz on every compact interval: by
the mean value theorem a constant is given by the maximum of `|J₀'''|` on
the interval, which exists by the extreme value theorem. -/
theorem exists_lipschitz_on_besselJ0Curv (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc a b, ∀ w ∈ Set.Icc a b,
      |besselJ0Curv z - besselJ0Curv w| ≤ M * |z - w| := by
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨x₀, _hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_refl a, le_of_lt hab⟩
      (f := fun c => |deriv besselJ0Curv c|)
      (Continuous.continuousOn (continuous_abs.comp continuous_deriv_besselJ0Curv))
    have main : ∀ z w : ℝ, z ∈ Set.Icc a b → w ∈ Set.Icc a b → w < z →
        |besselJ0Curv z - besselJ0Curv w|
          ≤ |deriv besselJ0Curv x₀| * |z - w| := by
      intro z w hz hw h
      have hcc : ContinuousOn besselJ0Curv (Set.Icc w z) :=
        Continuous.continuousOn (Differentiable.continuous differentiable_besselJ0Curv)
      have hdd : DifferentiableOn ℝ besselJ0Curv (Set.Ioo w z) :=
        differentiable_besselJ0Curv.differentiableOn
      obtain ⟨c, hc, hcslope⟩ :=
        exists_deriv_eq_slope (f := besselJ0Curv) (a := w) (b := z) h hcc hdd
      have hcM : |deriv besselJ0Curv c| ≤ |deriv besselJ0Curv x₀| :=
        hmax ⟨by linarith [hw.1, hc.1], by linarith [hz.2, hc.2]⟩
      have key : besselJ0Curv z - besselJ0Curv w = deriv besselJ0Curv c * (z - w) := by
        rw [hcslope, div_mul_cancel₀ _ (sub_ne_zero_of_ne (ne_of_gt h))]
      calc |besselJ0Curv z - besselJ0Curv w|
          = |deriv besselJ0Curv c| * |z - w| := by rw [key, abs_mul]
        _ ≤ |deriv besselJ0Curv x₀| * |z - w| :=
            mul_le_mul_of_nonneg_right hcM (abs_nonneg _)
    refine ⟨|deriv besselJ0Curv x₀|, abs_nonneg _, ?_⟩
    intro z hz w hw
    rcases lt_trichotomy w z with h | h | h
    · exact main z w hz hw h
    · rw [← h]
      simp
    · have hsw := main w z hw hz h
      rw [abs_sub_comm (besselJ0Curv w) (besselJ0Curv z), abs_sub_comm w z] at hsw
      exact hsw
  · refine ⟨0, le_refl 0, ?_⟩
    intro z hz w hw
    have hzw : z = w :=
      le_antisymm (by linarith [hz.2, hw.1, hab]) (by linarith [hw.2, hz.1, hab])
    rw [hzw]
    simp

/-- A Lipschitz constant for `J₀''` on the neighbourhood of `k_F L` used by
the coefficient bridge. -/
theorem exists_bridge_lipschitz_besselJ0Curv (k r L : ℝ) :
    ∃ M2 : ℝ, 0 ≤ M2 ∧ ∀ z, |z - k * L| ≤ 4 * k * r →
      |besselJ0Curv z - besselJ0Curv (k * L)| ≤ M2 * |z - k * L| := by
  obtain ⟨M, hM, hlip⟩ :=
    exists_lipschitz_on_besselJ0Curv (k * L - 4 * k * r) (k * L + 4 * k * r)
  refine ⟨M, hM, ?_⟩
  intro z hz
  have h4 : (0:ℝ) ≤ 4 * k * r := le_trans (abs_nonneg (z - k * L)) hz
  have hlo := (abs_le.1 hz).1
  have hhi := (abs_le.1 hz).2
  have hzin : z ∈ Set.Icc (k * L - 4 * k * r) (k * L + 4 * k * r) :=
    ⟨by linarith, by linarith⟩
  have hkin : k * L ∈ Set.Icc (k * L - 4 * k * r) (k * L + 4 * k * r) :=
    ⟨by linarith, by linarith⟩
  exact hlip z hzin (k * L) hkin

/-! ## The instantiated coefficient bridge -/

/-- The wave force of equation (17) with the physical slope profile `J₀'`
has the generalized Kuramoto form with the literal coefficients of
equations (25), (26): `α = ℱ k_F r J₀''(k_F L)` and
`β = (ℱ r / L) J₀'(k_F L)`, plus the explicit non-gradient single-spin term
`-ℱ J₀'(k_F L) sin φᵢ` and the controlled remainder of the abstract
bridge. -/
theorem left_azimuth_force_bessel_approx_gk_force (F k r L φi φj M2 : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) (hM : 0 ≤ M2)
    (hlip : ∀ z, |z - k * L| ≤ 4 * k * r →
      |besselJ0Curv z - besselJ0Curv (k * L)| ≤ M2 * |z - k * L|) :
    |leftAzimuthForce F besselJ0Slope k r L φi φj
        - (gkPairForce (F * k * r * besselJ0Curv (k * L))
            (F * r / L * besselJ0Slope (k * L)) φi φj
          - F * besselJ0Slope (k * L) * Real.sin φi)|
      ≤ |F| * (2 * |besselJ0Slope (k * L)| * r / L
        + 2 * |besselJ0Curv (k * L)| * k * r ^ 2 / L
        + 4 * |besselJ0Curv (k * L)| * k * r ^ 2 / L * (1 + r / L)
        + 9 * M2 * (k * r) ^ 2 * (1 + r / L)
        + 6 * r / L * (1 + r / L) * (|besselJ0Slope (k * L)|
            + 3 * |besselJ0Curv (k * L)| * k * r
            + 9 * M2 * (k * r) ^ 2)) :=
  left_azimuth_force_approx_gk_force F besselJ0Slope besselJ0Curv k r L φi φj M2
    hL hr hrL hk hM hasDerivAt_besselJ0Slope hlip

/-- Fully instantiated existential form: in the small-orbit regime the
`J₀'`-profile wave force matches the generalized Kuramoto force with the
coefficients `α = ℱ k_F r J₀''(k_F L)` and `β = (ℱ r / L) J₀'(k_F L)` up to
a controlled remainder, whose Lipschitz constant exists by compactness. -/
theorem exists_bessel_remainder_bound (F k r L φi φj : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) (hk : 0 < k) :
    ∃ M2 : ℝ, 0 ≤ M2 ∧
      |leftAzimuthForce F besselJ0Slope k r L φi φj
        - (gkPairForce (F * k * r * besselJ0Curv (k * L))
            (F * r / L * besselJ0Slope (k * L)) φi φj
          - F * besselJ0Slope (k * L) * Real.sin φi)|
      ≤ |F| * (2 * |besselJ0Slope (k * L)| * r / L
        + 2 * |besselJ0Curv (k * L)| * k * r ^ 2 / L
        + 4 * |besselJ0Curv (k * L)| * k * r ^ 2 / L * (1 + r / L)
        + 9 * M2 * (k * r) ^ 2 * (1 + r / L)
        + 6 * r / L * (1 + r / L) * (|besselJ0Slope (k * L)|
            + 3 * |besselJ0Curv (k * L)| * k * r
            + 9 * M2 * (k * r) ^ 2)) := by
  obtain ⟨M2, hM2, hlip⟩ := exists_bridge_lipschitz_besselJ0Curv k r L
  exact ⟨M2, hM2,
    left_azimuth_force_bessel_approx_gk_force F k r L φi φj M2 hL hr hrL hk hM2 hlip⟩

end Qatlib.Papers.HydroSpinLatt21.GKModel

end
