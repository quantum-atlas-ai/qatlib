/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfoilLift19.LiftForce.StationaryMadelung

import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Rectangular force contours for a stationary Gross–Pitaevskii wave

[Musser2019Superfoil], equations (1) and (5),
[DOI](https://doi.org/10.1103/PhysRevLett.123.154502).
The stationary equation in a constant potential implies equality of the
stress forces on two nested rectangular contours. The wave equation and
differentiability certificates apply in the fluid between the contours.
The phase can be given by local charts whose gradients agree with the
velocity data, so the hypothesis allows circulation around the inner box.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfoilLift19.LiftForce

open Qatlib.Papers.SuperfoilLift19.QuantumCirc (polarWave)
open scoped Topology

/-- The equation (5) stress evaluated on a wave's amplitude, amplitude
partials, and phase-gradient data. -/
noncomputable def polarStress (mass gint hbar : ℝ) (A : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ) (ddA : ℝ × ℝ → Fin 2 → Fin 2 → ℝ) :
    ℝ × ℝ → Fin 2 → Fin 2 → ℝ :=
  stressTensor mass gint hbar (fun x => A x ^ 2) (fun x j => hbar / mass * dφ x j)
    (amplitudeQuantumStress A dA ddA)

/-- A local real phase for a given complex wave and amplitude, with the
prescribed phase derivatives in both Cartesian directions. -/
def HasLocalPolarPhase (ψ : ℝ × ℝ → ℂ) (A : ℝ × ℝ → ℝ)
    (dφ : ℝ × ℝ → Fin 2 → ℝ) (U : Set (ℝ × ℝ)) : Prop :=
  ∀ x ∈ U, ∃ S : Set (ℝ × ℝ), IsOpen S ∧ x ∈ S ∧ S ⊆ U ∧
    ∃ φ : ℝ × ℝ → ℝ, Set.EqOn ψ (fun y => polarWave (A y) (φ y)) S ∧
      ∀ y ∈ S, ∀ j, HasDerivAt (fun s => φ (axisLine y j s)) (dφ y j) 0

/-- The derivative along a Cartesian line is the Fréchet derivative
evaluated on the corresponding basis vector. -/
private theorem deriv_axisLine_fderiv {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (j : Fin 2) :
    deriv (fun s => f (axisLine x j s)) 0 =
      fderiv ℝ f x (if j = 0 then (1, 0) else (0, 1)) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (axisLine x j 0) := by
    rw [axisLine_zero]
    exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 (hasDerivAt_axisLine x j 0)).deriv

/-- The force on the two rectangles agrees when the stress has zero
Cartesian divergence in the fluid shell. Only the stress values and
derivatives in that shell enter the result. -/
theorem rectangleForce_eq_of_shell
    {T : ℝ × ℝ → Fin 2 → Fin 2 → ℝ} {a b c d : ℝ × ℝ} (k : Fin 2)
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (hCont : ∀ j, ContinuousOn (fun y => T y j k) (rectangularShell c d a b))
    (hDiff : ∀ x ∈ rectangularShellInterior c d a b, ∀ j,
      DifferentiableAt ℝ (fun y => T y j k) x)
    (hDiv : ∀ x ∈ rectangularShellInterior c d a b,
      (∑ j : Fin 2, deriv (fun s => T (axisLine x j s) j k) 0) = 0) :
    rectangleForce T k a b = rectangleForce T k c d := by
  classical
  let D (j : Fin 2) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
    if x ∈ rectangularShellInterior c d a b then fderiv ℝ (fun y => T y j k) x else 0
  have hD (x : ℝ × ℝ) (hx : x ∈ rectangularShellInterior c d a b) (j : Fin 2) :
      HasFDerivAt (fun y => T y j k) (D j x) x := by
    simpa only [D, ite_eq_left hx] using (hDiff x hx j).hasFDerivAt
  have hzero (x : ℝ × ℝ) : D 0 x (1, 0) + D 1 x (0, 1) = 0 := by
    by_cases hx : x ∈ rectangularShellInterior c d a b
    · have h := hDiv x hx
      rw [Fin.sum_univ_two, deriv_axisLine_fderiv (hDiff x hx 0),
        deriv_axisLine_fderiv (hDiff x hx 1)] at h
      simpa [D, hx] using h
    · simp [D, hx]
  have hzeroFun : (fun x => D 0 x (1, 0) + D 1 x (0, 1)) = fun _ => 0 := funext hzero
  have hInt : MeasureTheory.IntegrableOn (fun x => D 0 x (1, 0) + D 1 x (0, 1))
      (rectangularShell c d a b) MeasureTheory.volume := by
    rw [hzeroFun]
    exact MeasureTheory.integrable_zero _ _ _
  exact flux_wall_eq_far_field_on_shell h1 h2 h3 h4 h5 h6 (hCont 0) (hCont 1)
    (fun x hx => hD x hx 0) (fun x hx => hD x hx 1) hInt (fun x _ => hzero x)

/-- A positive-amplitude stationary Gross–Pitaevskii wave in a constant
potential has the same equation (5) stress force on both contours.
The phase need only exist in charts in the open fluid shell. -/
theorem stationary_gpe_rectangleForce
    (mass gint hbar mu V : ℝ) (hmass : 0 < mass) (hhbar : hbar ≠ 0)
    (ψ : ℝ × ℝ → ℂ) (A : ℝ × ℝ → ℝ)
    (dA dφ : ℝ × ℝ → Fin 2 → ℝ)
    (ddA ddφ dLap : ℝ × ℝ → Fin 2 → Fin 2 → ℝ)
    {a b c d : ℝ × ℝ} (k : Fin 2)
    (h1 : c.1 < a.1) (h2 : a.1 < b.1) (h3 : b.1 < d.1)
    (h4 : c.2 < a.2) (h5 : a.2 < b.2) (h6 : b.2 < d.2)
    (hCont : ∀ j, ContinuousOn (fun y => polarStress mass gint hbar A dA dφ ddA y j k)
      (rectangularShell c d a b))
    (hDiff : ∀ x ∈ rectangularShellInterior c d a b, ∀ j,
      DifferentiableAt ℝ (fun y => polarStress mass gint hbar A dA dφ ddA y j k) x)
    (hEq : ∀ x ∈ rectangularShellInterior c d a b,
      0 < A x ∧ StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V) ψ x)
    (hPhase : HasLocalPolarPhase ψ A dφ (rectangularShellInterior c d a b))
    (hA : ∀ x ∈ rectangularShellInterior c d a b, ∀ j,
      HasDerivAt (fun s => A (axisLine x j s)) (dA x j) 0)
    (hDA : ∀ x ∈ rectangularShellInterior c d a b, ∀ j i,
      HasDerivAt (fun s => dA (axisLine x j s) i) (ddA x j i) 0)
    (hDφ : ∀ x ∈ rectangularShellInterior c d a b, ∀ j i,
      HasDerivAt (fun s => dφ (axisLine x j s) i) (ddφ x j i) 0)
    (hsym : ∀ x ∈ rectangularShellInterior c d a b, ∀ j, ddφ x k j = ddφ x j k)
    (hThird : ∀ x ∈ rectangularShellInterior c d a b, ∀ j,
      HasDerivAt (fun s => ddA (axisLine x j s) j k) (dLap x k j) 0)
    (hLap : ∀ x ∈ rectangularShellInterior c d a b, ∀ j,
      HasDerivAt (fun s => ddA (axisLine x k s) j j) (dLap x k j) 0) :
    rectangleForce (polarStress mass gint hbar A dA dφ ddA) k a b =
      rectangleForce (polarStress mass gint hbar A dA dφ ddA) k c d := by
  refine rectangleForce_eq_of_shell k h1 h2 h3 h4 h5 h6 hCont hDiff ?_
  intro x hx
  obtain ⟨S, hS, hxS, hSU, φ, hWave, hφ⟩ := hPhase x hx
  have hLocal : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < A (axisLine x k s) ∧
      StationaryGrossPitaevskiiAt mass gint hbar mu (fun _ => V)
        (fun y => polarWave (A y) (φ y)) (axisLine x k s) := by
    filter_upwards [eventually_mem_axisLine hS hxS k] with s hs
    obtain ⟨hPos, hGPE⟩ := hEq _ (hSU hs)
    refine ⟨hPos, ?_⟩
    unfold StationaryGrossPitaevskiiAt at *
    rw [← hWave hs, ← waveLaplacian_eq_on_open hS hWave hs]
    exact hGPE
  exact stationary_gpe_stress_divergence_on mass gint hbar mu V hmass hhbar
    A φ dA dφ ddA ddφ x k hS hxS (dLap x k)
    (fun y hy => hA y (hSU hy)) hφ (fun y hy => hDA y (hSU hy))
    (fun y hy => hDφ y (hSU hy)) (hsym x hx) (hThird x hx) (hLap x hx) hLocal

end Qatlib.Papers.SuperfoilLift19.LiftForce
