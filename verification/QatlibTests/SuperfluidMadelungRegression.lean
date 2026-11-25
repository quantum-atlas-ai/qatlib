/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.VelocityBalance

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! An exact exponential-amplitude wave exercises the nonzero quantum term
in the Gross–Pitaevskii polar balance. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.SuperfluidHel18.Madelung
open Filter
open scoped BigOperators Topology

/-- The amplitude `exp x₀` and phase `t/2` solve the equation with
unit mass and Planck parameter and zero nonlinear coefficient. The
test uses the nonzero amplitude Laplacian at the spatial origin. -/
example :
    let A : ℝ → GpeSpace → ℝ := fun _ x => Real.exp (x 0)
    let θ : ℝ → GpeSpace → ℝ := fun t _ => t / 2
    gpeLaplacian (A 0) 0 = 1 ∧
      deriv (fun t => (A t 0) ^ 2) 0 +
        gpeDivergence (fun y i => A 0 y ^ 2 * (1 * gpePartial (θ 0) y i)) 0 = 0 ∧
      deriv (fun t => θ t 0) 0 + (1 / 2 : ℝ) * gpeGradDot (θ 0) (θ 0) 0 -
        (1 / 2 : ℝ) * gpeLaplacian (A 0) 0 / A 0 0 = 0 := by
  let A : ℝ → GpeSpace → ℝ := fun _ x => Real.exp (x 0)
  let θ : ℝ → GpeSpace → ℝ := fun t _ => t / 2
  have hA : ContDiff ℝ 2 (A 0) := by unfold A; fun_prop
  have hθ : ContDiff ℝ 2 (θ 0) := contDiff_const
  have hA0 : A 0 0 = 1 := by simp [A]
  have htA : DifferentiableAt ℝ (fun t => A t 0) 0 := differentiableAt_const _
  have htθ : DifferentiableAt ℝ (fun t => θ t 0) 0 := by unfold θ; fun_prop
  have hx₀ : A 0 ∘ gpeCoordinateLine 0 0 = Real.exp := by
    funext s
    simp [A, gpeCoordinateLine, Function.comp_apply, smul_eq_mul]
  have hx₁ : A 0 ∘ gpeCoordinateLine 0 1 = fun _ => 1 := by
    funext s
    simp [A, gpeCoordinateLine, Function.comp_apply, smul_eq_mul]
  have hx₂ : A 0 ∘ gpeCoordinateLine 0 2 = fun _ => 1 := by
    funext s
    simp [A, gpeCoordinateLine, Function.comp_apply, smul_eq_mul]
  have hLA : gpeLaplacian (A 0) 0 = 1 := by
    simp [gpeLaplacian, Fin.sum_univ_three, hx₀, hx₁, hx₂, Real.deriv_exp]
  have hPθ (i : Fin 3) : gpePartial (θ 0) 0 i = 0 := by
    simp [θ, gpePartial, Function.comp_def]
  have hLθ : gpeLaplacian (θ 0) 0 = 0 := by
    simp [θ, gpeLaplacian, Function.comp_def, deriv_const']
  have hdA : deriv (fun t => A t 0) 0 = 0 := by simp [A]
  have hdθ : deriv (fun t => θ t 0) 0 = 1 / 2 := by simp [θ]
  have hD : deriv (fun t => gpePolarState A θ t 0) 0 = Complex.I / 2 := by
    have h := deriv_gpePolarWave (fun t => A t 0) (fun t => θ t 0) 0 htA htθ
    rw [hdA, hdθ, hA0] at h
    simpa [gpePolarState, θ, div_eq_mul_inv] using h
  have hL : gpeLaplacian (gpePolarState A θ 0) 0 = 1 := by
    have hθ0 : θ 0 0 = 0 := by simp [θ]
    rw [gpeLaplacian_polarState A θ 0 0 hA hθ, hA0, hLA, hLθ, hθ0]
    simp [gpeGradDot, hPθ]
  have hGpe : Complex.I * (1 : ℂ) * deriv (fun t => gpePolarState A θ t 0) 0 =
      -(((1 : ℝ) ^ 2 / (2 * 1) : ℝ) : ℂ) * gpeLaplacian (gpePolarState A θ 0) 0 +
      (0 : ℂ) * (Complex.normSq (gpePolarState A θ 0 0) : ℂ) * gpePolarState A θ 0 0 := by
    rw [hD, hL]
    norm_num [← mul_div_assoc, Complex.I_mul_I]
  obtain ⟨hDensity, hPhase⟩ := gpe_polar_balances 1 1 0 A θ 0 0 (by norm_num) (by norm_num)
    (by rw [hA0]; norm_num) htA htθ hA hθ hGpe
  refine ⟨hLA, ?_, ?_⟩
  · change deriv (fun t => (A t 0) ^ 2) 0 +
      gpeDivergence (fun y i => A 0 y ^ 2 * (1 * gpePartial (θ 0) y i)) 0 = 0
    rw [gpeDivergence_densityVelocity 1 (A 0) (θ 0) 0 (hA.of_le (by norm_num)) hθ]
    simpa only [div_one] using hDensity
  · change deriv (fun t => θ t 0) 0 + (1 / 2 : ℝ) * gpeGradDot (θ 0) (θ 0) 0 -
      (1 / 2 : ℝ) * gpeLaplacian (A 0) 0 / A 0 0 = 0
    simpa only [one_mul, one_pow, mul_one, zero_mul, add_zero] using hPhase

#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.deriv_deriv_gpePolarWave
#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpe_polar_balances
#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpeDivergence_densityVelocity

/-- A quadratic phase has both nonzero temporal and convective
acceleration at the selected spacetime point. -/
example : gpeAcceleration 1 (fun p => p.1 * p.2 0 + (p.2 0) ^ 2 / 2) 1 0 0 = 2 := by
  let φ : GpeSpacetime → ℝ := fun p => p.1 * p.2 0 + (p.2 0) ^ 2 / 2
  have hφ : ContDiff ℝ 2 φ := by unfold φ; fun_prop
  change gpeAcceleration 1 φ 1 0 0 = 2
  rw [gpeAcceleration_eq_phaseGradient 1 φ hφ]
  have ht (y : GpeSpace) : deriv (fun s => φ (s, y)) 1 = y 0 := by
    have h := (((hasDerivAt_id (1 : ℝ)).mul_const (y 0)).add_const ((y 0) ^ 2 / 2)).deriv
    simpa only [φ, id_eq, one_mul] using h
  have hx₀ (y : GpeSpace) : gpePartial (fun z => φ (1, z)) y 0 = 1 + y 0 := by
    let w := fun s : ℝ => y 0 + s
    have hw : HasDerivAt w 1 0 := (hasDerivAt_id (0 : ℝ)).const_add (y 0)
    have he : (fun z => φ (1, z)) ∘ gpeCoordinateLine y 0 =
        fun s => w s + (w s) ^ 2 / 2 := by
      funext s
      simp [φ, gpeCoordinateLine, w, Function.comp_apply, smul_eq_mul]
    rw [gpePartial, he, (hw.fun_add ((hw.fun_pow 2).div_const 2)).deriv]
    norm_num [w]
  have hx₁ (y : GpeSpace) : gpePartial (fun z => φ (1, z)) y 1 = 0 := by
    simp [gpePartial, φ, gpeCoordinateLine, Function.comp_def, smul_eq_mul]
  have hx₂ (y : GpeSpace) : gpePartial (fun z => φ (1, z)) y 2 = 0 := by
    simp [gpePartial, φ, gpeCoordinateLine, Function.comp_def, smul_eq_mul]
  have hGrad (y : GpeSpace) :
      gpeGradDot (fun z => φ (1, z)) (fun z => φ (1, z)) y = (1 + y 0) ^ 2 := by
    simp only [gpeGradDot, Fin.sum_univ_three, hx₀, hx₁, hx₂, zero_mul, add_zero, pow_two]
  simp_rw [ht, hGrad, one_mul, one_pow]
  have he : (fun y : GpeSpace => y 0 + (1 / 2 : ℝ) * (1 + y 0) ^ 2) ∘
      gpeCoordinateLine 0 0 = fun s => s + (1 / 2 : ℝ) * (1 + s) ^ 2 := by
    funext s
    simp [gpeCoordinateLine, Function.comp_apply, smul_eq_mul]
  rw [gpePartial, he]
  have h := hasDerivAt_id (0 : ℝ)
  have h' := (h.const_add 1).fun_pow 2
  convert (h.fun_add (h'.const_mul (1 / 2 : ℝ))).deriv using 1 <;> norm_num [id]

#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpe_mixedTimePartial
#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpe_partial_gradDot_self
#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpe_velocity_equation

/-- The steady linear wave has a zero plane. The velocity equation
applies near a point on its positive side. -/
example : gpeAcceleration 1 (fun _ => 0) 0 ![1, 0, 0] 0 = 0 := by
  let A : GpeSpacetime → ℝ := fun p => p.2 0
  let φ : GpeSpacetime → ℝ := fun _ => 0
  let x : GpeSpace := ![1, 0, 0]
  let R : ℝ → GpeSpace → ℝ := fun s y => A (s, y)
  let θ : ℝ → GpeSpace → ℝ := fun s y => φ (s, y)
  let ψ := gpePolarState R θ
  have hA : ContDiff ℝ 2 A := by unfold A; fun_prop
  have hφ : ContDiff ℝ 2 φ := contDiff_const
  have hR : ContDiff ℝ 2 (R 0) := by unfold R A; fun_prop
  have hθ : ContDiff ℝ 2 (θ 0) := contDiff_const
  have hne : ∀ᶠ y in 𝓝 x, A (0, y) ≠ 0 := by
    have hEval : Continuous (fun y : GpeSpace => y 0) := by fun_prop
    have hOpen : IsOpen {y : GpeSpace | y 0 ≠ 0} :=
      (isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).preimage hEval
    exact hOpen.mem_nhds (by simp [x])
  have hLap (y : GpeSpace) : gpeLaplacian (R 0) y = 0 := by
    have h (j : Fin 3) : deriv (deriv (R 0 ∘ gpeCoordinateLine y j)) 0 = 0 := by
      let v := (Pi.single j (1 : ℝ) : GpeSpace) 0
      have he : R 0 ∘ gpeCoordinateLine y j = fun s => y 0 + s * v := by
        funext s
        simp [R, A, gpeCoordinateLine, Function.comp_apply, v, smul_eq_mul]
      have hder : deriv (fun s => y 0 + s * v) = fun _ => v := by
        funext s
        have hd := (((hasDerivAt_id s).mul_const v).const_add (y 0)).deriv
        simpa only [id_eq, one_mul] using hd
      rw [he, hder, deriv_const]
    simp only [gpeLaplacian, h, Finset.sum_const_zero]
  have hLapθ (y : GpeSpace) : gpeLaplacian (θ 0) y = 0 := by
    simp [gpeLaplacian, θ, φ, Function.comp_def, deriv_const']
  have hθP (y : GpeSpace) (i : Fin 3) : gpePartial (θ 0) y i = 0 := by
    simp [gpePartial, θ, φ, Function.comp_def]
  have hLapψ (y : GpeSpace) : gpeLaplacian (ψ 0) y = 0 := by
    change gpeLaplacian (gpePolarState R θ 0) y = 0
    rw [gpeLaplacian_polarState R θ 0 y hR hθ, hLap y, hLapθ y]
    simp [gpeGradDot, hθP]
  have htψ (y : GpeSpace) : deriv (fun s => ψ s y) 0 = 0 := by
    simp [ψ, gpePolarState, gpePolarWave, R, θ, A, φ]
  have he := gpe_velocity_equation_near 1 1 0 A φ hA hφ 0 x (by norm_num) (by norm_num)
    hne (Eventually.of_forall fun y => by
      change _ * deriv (fun s => ψ s y) 0 = _ * gpeLaplacian (ψ 0) y + _
      rw [htψ y, hLapψ y]
      simp) 0
  have hForce :
      (fun y => -(0 / (1 : ℝ)) * A (0, y) ^ 2 +
        (1 : ℝ) ^ 2 / (2 * 1 ^ 2) * gpeLaplacian (fun z => A (0, z)) y / A (0, y)) =
      fun _ : GpeSpace => 0 := by
    funext y
    change -(0 / (1 : ℝ)) * R 0 y ^ 2 +
      (1 : ℝ) ^ 2 / (2 * 1 ^ 2) * gpeLaplacian (R 0) y / R 0 y = 0
    simp [hLap y]
  rw [hForce] at he
  simpa only [div_one, gpePartial, Function.comp_def, deriv_const, φ, x] using he

#print axioms Qatlib.Papers.SuperfluidHel18.Madelung.gpe_velocity_equation_near
