/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarKinematics

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Madelung velocity balance from the Gross–Pitaevskii equation

The gradient of the phase equation is the acceleration of the actual
phase-gradient velocity. The amplitude Laplacian is retained in the
force potential.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open Filter
open scoped BigOperators Topology

/-- A component of the Madelung velocity in Cartesian coordinates. -/
noncomputable def gpeVelocity (ν : ℝ) (φ : GpeSpacetime → ℝ)
    (t : ℝ) (x : GpeSpace) (i : Fin 3) : ℝ :=
  ν * gpePartial (fun y => φ (t, y)) x i

/-- The material acceleration is the sum of the time derivative and
the transport of the same velocity component by the spatial velocity. -/
noncomputable def gpeAcceleration (ν : ℝ) (φ : GpeSpacetime → ℝ)
    (t : ℝ) (x : GpeSpace) (i : Fin 3) : ℝ :=
  deriv (fun s => gpeVelocity ν φ s x i) t +
    ∑ j : Fin 3, gpeVelocity ν φ t x j *
      gpePartial (fun y => gpeVelocity ν φ t y i) x j

/-- Taking a Cartesian partial commutes with multiplication by a real constant. -/
private theorem gpePartial_const_mul (ν : ℝ) (f : GpeSpace → ℝ) (x : GpeSpace) (i : Fin 3) :
    gpePartial (fun y => ν * f y) x i = ν * gpePartial f x i := by
  simpa only [gpePartial, Function.comp_def, smul_eq_mul] using
    deriv_fun_const_smul_field (x := (0 : ℝ)) ν (f ∘ gpeCoordinateLine x i)

/-- Differentiability of a spacetime scalar implies differentiability
of its spatial line section at the point. -/
private theorem differentiableAt_gpeCoordinateSection {f : GpeSpacetime → ℝ}
    {t : ℝ} {x : GpeSpace} (hf : DifferentiableAt ℝ f (t, x)) (i : Fin 3) :
    DifferentiableAt ℝ (fun s => f (t, gpeCoordinateLine x i s)) 0 := by
  have hc : DifferentiableAt ℝ (fun s => (t, gpeCoordinateLine x i s)) 0 := by
    unfold gpeCoordinateLine
    fun_prop
  have h0 : (t, gpeCoordinateLine x i 0) = (t, x) := by simp [gpeCoordinateLine]
  exact (h0.symm ▸ hf).comp 0 hc

/-- For a smooth phase the material acceleration is the gradient of the
scaled phase rate plus half the squared velocity. -/
theorem gpeAcceleration_eq_phaseGradient (ν : ℝ) (φ : GpeSpacetime → ℝ)
    (hφ : ContDiff ℝ 2 φ) (t : ℝ) (x : GpeSpace) (i : Fin 3) :
    gpeAcceleration ν φ t x i =
      gpePartial (fun y => ν * deriv (fun s => φ (s, y)) t +
        ν ^ 2 / 2 * gpeGradDot (fun z => φ (t, z)) (fun z => φ (t, z)) y) x i := by
  let T := fun p : GpeSpacetime => fderiv ℝ φ p gpeTimeAxis
  let P (p : GpeSpacetime) (j : Fin 3) := fderiv ℝ φ p (gpeSpatialAxis j)
  let S := fun p : GpeSpacetime => ∑ j : Fin 3, P p j * P p j
  let A := fun y : GpeSpace => deriv (fun s => φ (s, y)) t
  let B := fun y : GpeSpace => gpeGradDot (fun z => φ (t, z)) (fun z => φ (t, z)) y
  have h₁ := hφ.differentiable (by norm_num)
  have h₂ := (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hT : DifferentiableAt ℝ T (t, x) :=
    (ContinuousLinearMap.apply ℝ ℝ gpeTimeAxis).differentiableAt.comp (t, x) (h₂ (t, x))
  have hP (j : Fin 3) : DifferentiableAt ℝ (fun p => P p j) (t, x) :=
    (ContinuousLinearMap.apply ℝ ℝ (gpeSpatialAxis j)).differentiableAt.comp (t, x) (h₂ (t, x))
  have hS : DifferentiableAt ℝ S (t, x) := by
    unfold S
    exact DifferentiableAt.fun_sum fun j _ => (hP j).fun_mul (hP j)
  have hA (y : GpeSpace) : A y = T (t, y) := gpeTime_slice_eq_fderiv (h₁ (t, y))
  have hB (y : GpeSpace) : B y = S (t, y) := by
    simp only [B, gpeGradDot, S, gpePartial_slice_eq_fderiv (h₁ (t, y)), P]
  have hLineA : DifferentiableAt ℝ (fun s => A (gpeCoordinateLine x i s)) 0 := by
    simp_rw [hA]
    exact differentiableAt_gpeCoordinateSection hT i
  have hLineB : DifferentiableAt ℝ (fun s => B (gpeCoordinateLine x i s)) 0 := by
    simp_rw [hB]
    exact differentiableAt_gpeCoordinateSection hS i
  change gpeAcceleration ν φ t x i = gpePartial (fun y => ν * A y + ν ^ 2 / 2 * B y) x i
  have hDer : gpePartial (fun y => ν * A y + ν ^ 2 / 2 * B y) x i =
      ν * gpePartial A x i + (ν ^ 2 / 2) * gpePartial B x i := by
    have ha : gpePartial (fun y => ν * A y + ν ^ 2 / 2 * B y) x i =
        gpePartial (fun y => ν * A y) x i + gpePartial (fun y => ν ^ 2 / 2 * B y) x i := by
      simpa only [gpePartial, Function.comp_def] using
        deriv_fun_add (hLineA.const_mul ν) (hLineB.const_mul (ν ^ 2 / 2))
    rw [ha, gpePartial_const_mul, gpePartial_const_mul]
  have ht : deriv (fun s => gpeVelocity ν φ s x i) t = ν * gpePartial A x i := by
    change _ = ν * gpePartial (fun y => deriv (fun s => φ (s, y)) t) x i
    rw [← gpe_mixedTimePartial φ hφ t x i]
    simpa only [gpeVelocity, smul_eq_mul] using
      deriv_fun_const_smul_field (x := t) ν (fun s => gpePartial (fun y => φ (s, y)) x i)
  unfold gpeAcceleration
  rw [ht, hDer]
  simp only [gpeVelocity, gpePartial_const_mul]
  change _ = _ + ν ^ 2 / 2 * gpePartial
    (fun y => gpeGradDot (fun z => φ (t, z)) (fun z => φ (t, z)) y) x i
  rw [gpe_partial_gradDot_self φ hφ]
  simp only [Fin.sum_univ_three]
  ring

/-- The Gross–Pitaevskii equation on a nonvanishing spatial neighborhood
gives the Madelung velocity equation at its center. -/
theorem gpe_velocity_equation_near (ℏ m g : ℝ) (A φ : GpeSpacetime → ℝ)
    (hA : ContDiff ℝ 2 A) (hφ : ContDiff ℝ 2 φ) (t : ℝ) (x : GpeSpace)
    (hh : ℏ ≠ 0) (hm : m ≠ 0) (hne : ∀ᶠ y in 𝓝 x, A (t, y) ≠ 0)
    (hGPE :
      let ψ := gpePolarState (fun s y => A (s, y)) (fun s y => φ (s, y))
      ∀ᶠ y in 𝓝 x, Complex.I * (ℏ : ℂ) * deriv (fun s => ψ s y) t =
        -((ℏ ^ 2 / (2 * m) : ℝ) : ℂ) * gpeLaplacian (ψ t) y +
          (g : ℂ) * (Complex.normSq (ψ t y) : ℂ) * ψ t y)
    (i : Fin 3) :
    gpeAcceleration (ℏ / m) φ t x i =
      gpePartial (fun y => -(g / m) * A (t, y) ^ 2 +
        ℏ ^ 2 / (2 * m ^ 2) * gpeLaplacian (fun z => A (t, z)) y / A (t, y)) x i := by
  let R := fun (s : ℝ) (y : GpeSpace) => A (s, y)
  let θ := fun (s : ℝ) (y : GpeSpace) => φ (s, y)
  have hsR : ContDiff ℝ 2 (R t) := hA.comp (by fun_prop : ContDiff ℝ 2 (fun y : GpeSpace => (t, y)))
  have hsθ : ContDiff ℝ 2 (θ t) := hφ.comp (by fun_prop : ContDiff ℝ 2 (fun y : GpeSpace => (t, y)))
  have htR (y : GpeSpace) : DifferentiableAt ℝ (fun s => R s y) t :=
    (hA.differentiable (by norm_num) (t, y)).comp t
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => (s, y)) t)
  have htθ (y : GpeSpace) : DifferentiableAt ℝ (fun s => θ s y) t :=
    (hφ.differentiable (by norm_num) (t, y)).comp t
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => (s, y)) t)
  have hF :
      (fun y => ℏ / m * deriv (fun s => θ s y) t +
        (ℏ / m) ^ 2 / 2 * gpeGradDot (θ t) (θ t) y) =ᶠ[𝓝 x]
      fun y => -(g / m) * R t y ^ 2 +
        ℏ ^ 2 / (2 * m ^ 2) * gpeLaplacian (R t) y / R t y := by
    filter_upwards [hne, hGPE] with y hy hEq
    have hp := (gpe_polar_balances ℏ m g R θ t y hh hm hy
      (htR y) (htθ y) hsR hsθ hEq).2
    apply mul_left_cancel₀ hm
    calc
      _ = ℏ * deriv (fun s => θ s y) t +
          ℏ ^ 2 / (2 * m) * gpeGradDot (θ t) (θ t) y := by
        field_simp [hm]
      _ = -(g * R t y ^ 2) + ℏ ^ 2 / (2 * m) * gpeLaplacian (R t) y / R t y := by
        linear_combination hp
      _ = _ := by
        have hRy : R t y ≠ 0 := hy
        field_simp [hm, hRy]
  rw [gpeAcceleration_eq_phaseGradient (ℏ / m) φ hφ]
  change gpePartial (fun y => ℏ / m * deriv (fun s => θ s y) t +
    (ℏ / m) ^ 2 / 2 * gpeGradDot (θ t) (θ t) y) x i =
      gpePartial (fun y => -(g / m) * R t y ^ 2 +
        ℏ ^ 2 / (2 * m ^ 2) * gpeLaplacian (R t) y / R t y) x i
  have hc : Continuous (gpeCoordinateLine x i) := by unfold gpeCoordinateLine; fun_prop
  have h0 : gpeCoordinateLine x i 0 = x := by simp [gpeCoordinateLine]
  have hLine : Tendsto (gpeCoordinateLine x i) (𝓝 0) (𝓝 x) := by
    simpa only [h0] using (hc.continuousAt (x := (0 : ℝ))).tendsto
  simpa only [gpePartial, Function.comp_def] using (hF.comp_tendsto hLine).deriv_eq

/-- A nonvanishing smooth polar solution on a spatial slice satisfies
the Euler velocity equation with the quantum force potential. -/
theorem gpe_velocity_equation (ℏ m g : ℝ) (A φ : GpeSpacetime → ℝ)
    (hA : ContDiff ℝ 2 A) (hφ : ContDiff ℝ 2 φ) (t : ℝ)
    (hh : ℏ ≠ 0) (hm : m ≠ 0) (hne : ∀ y : GpeSpace, A (t, y) ≠ 0)
    (hGPE :
      let ψ := gpePolarState (fun s y => A (s, y)) (fun s y => φ (s, y))
      ∀ y : GpeSpace, Complex.I * (ℏ : ℂ) * deriv (fun s => ψ s y) t =
        -((ℏ ^ 2 / (2 * m) : ℝ) : ℂ) * gpeLaplacian (ψ t) y +
          (g : ℂ) * (Complex.normSq (ψ t y) : ℂ) * ψ t y)
    (x : GpeSpace) (i : Fin 3) :
    gpeAcceleration (ℏ / m) φ t x i =
      gpePartial (fun y => -(g / m) * A (t, y) ^ 2 +
        ℏ ^ 2 / (2 * m ^ 2) * gpeLaplacian (fun z => A (t, z)) y / A (t, y)) x i :=
  gpe_velocity_equation_near ℏ m g A φ hA hφ t x hh hm (Eventually.of_forall hne)
    (Eventually.of_forall hGPE) i

end Qatlib.Papers.SuperfluidHel18.Madelung
