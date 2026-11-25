/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.PolarDerivatives

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Gross–Pitaevskii equation in polar variables

[Kedia2018SuperfluidHelicity], Section II, equation (1),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The density equation and the phase equation with quantum pressure follow
from the actual Cartesian derivatives of a nonvanishing smooth polar wave.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open scoped BigOperators

/-- The spatial coordinates used for the polar Gross–Pitaevskii equation. -/
abbrev GpeSpace := Fin 3 → ℝ

/-- A Cartesian line through a point, parametrized by signed displacement
in one coordinate direction. -/
noncomputable def gpeCoordinateLine (x : GpeSpace) (i : Fin 3) (s : ℝ) : GpeSpace :=
  x + s • Pi.single i 1

/-- A first Cartesian partial derivative of a spatial field. -/
noncomputable def gpePartial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : GpeSpace → F) (x : GpeSpace) (i : Fin 3) : F :=
  deriv (f ∘ gpeCoordinateLine x i) 0

/-- The Cartesian Laplacian, obtained by summing the second derivatives
along the three coordinate lines. -/
noncomputable def gpeLaplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : GpeSpace → F) (x : GpeSpace) : F :=
  ∑ i : Fin 3, deriv (deriv (f ∘ gpeCoordinateLine x i)) 0

/-- The Euclidean dot product of the Cartesian gradients of two scalar fields. -/
noncomputable def gpeGradDot (f g : GpeSpace → ℝ) (x : GpeSpace) : ℝ :=
  ∑ i : Fin 3, gpePartial f x i * gpePartial g x i

/-- The complex wavefunction determined by the real amplitude and phase. -/
noncomputable def gpePolarState (A θ : ℝ → GpeSpace → ℝ) (t : ℝ) (x : GpeSpace) : ℂ :=
  gpePolarWave (fun s => A s x) (fun s => θ s x) t

/-- The Laplacian of the actual polar wave separates into the real
amplitude curvature and the imaginary phase transport. -/
theorem gpeLaplacian_polarState (A θ : ℝ → GpeSpace → ℝ) (t : ℝ) (x : GpeSpace)
    (hA : ContDiff ℝ 2 (A t)) (hθ : ContDiff ℝ 2 (θ t)) :
    gpeLaplacian (gpePolarState A θ t) x =
      (((gpeLaplacian (A t) x - A t x * gpeGradDot (θ t) (θ t) x : ℝ) : ℂ) +
        Complex.I * ((2 * gpeGradDot (A t) (θ t) x +
          A t x * gpeLaplacian (θ t) x : ℝ) : ℂ)) *
            Complex.exp ((θ t x : ℂ) * Complex.I) := by
  have hline (i : Fin 3) : ContDiff ℝ 2 (gpeCoordinateLine x i) := by
    unfold gpeCoordinateLine
    fun_prop
  have hzero (i : Fin 3) : gpeCoordinateLine x i 0 = x := by simp [gpeCoordinateLine]
  have hpart (i : Fin 3) :
      deriv (deriv (gpePolarState A θ t ∘ gpeCoordinateLine x i)) 0 =
        (((deriv (deriv (A t ∘ gpeCoordinateLine x i)) 0 -
          A t x * (gpePartial (θ t) x i) ^ 2 : ℝ) : ℂ) +
          Complex.I * ((2 * gpePartial (A t) x i * gpePartial (θ t) x i +
            A t x * deriv (deriv (θ t ∘ gpeCoordinateLine x i)) 0 : ℝ) : ℂ)) *
              Complex.exp ((θ t x : ℂ) * Complex.I) := by
    change deriv (deriv (gpePolarWave (A t ∘ gpeCoordinateLine x i)
      (θ t ∘ gpeCoordinateLine x i))) 0 = _
    rw [deriv_deriv_gpePolarWave _ _ _ (hA.comp (hline i)) (hθ.comp (hline i))]
    simp only [Function.comp_apply, hzero, gpePartial]
  unfold gpeLaplacian gpeGradDot
  simp_rw [hpart]
  simp only [Fin.sum_univ_three]
  push_cast
  ring

/-- Taking the real and imaginary components of the phase-cancelled
equation gives the two real Madelung balances. -/
private theorem gpe_polar_coefficients (ℏ m g R Rt Θt LA LΘ C S : ℝ)
    (hh : ℏ ≠ 0) (hm : m ≠ 0) (hR : R ≠ 0)
    (he : Complex.I * (ℏ : ℂ) * ((Rt : ℂ) + Complex.I * (R * Θt : ℝ)) =
      -((ℏ ^ 2 / (2 * m) : ℝ) : ℂ) *
        (((LA - R * S : ℝ) : ℂ) + Complex.I * (2 * C + R * LΘ : ℝ)) +
        ((g * R ^ 3 : ℝ) : ℂ)) :
    2 * R * Rt + ℏ / m * (2 * R * C + R ^ 2 * LΘ) = 0 ∧
      ℏ * Θt + ℏ ^ 2 / (2 * m) * S + g * R ^ 2 -
        ℏ ^ 2 / (2 * m) * LA / R = 0 := by
  have hi : ℏ * Rt = -(ℏ ^ 2 / (2 * m)) * (2 * C + R * LΘ) := by
    simpa only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.neg_im,
      Complex.neg_re, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      neg_zero, sub_zero, zero_sub, neg_mul] using
      congrArg Complex.im he
  have hr : -(ℏ * (R * Θt)) =
      -(ℏ ^ 2 / (2 * m)) * (LA - R * S) + g * R ^ 3 := by
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      neg_zero, sub_zero, zero_sub, neg_mul] using
      congrArg Complex.re he
  constructor
  · have hRt : Rt = -(ℏ / (2 * m)) * (2 * C + R * LΘ) := by
      apply (mul_left_cancel₀ hh)
      rw [hi]
      field_simp [hm]
    rw [hRt]
    field_simp [hm]
    ring
  · apply sub_eq_zero.mpr
    apply (eq_div_iff hR).2
    linear_combination -hr

/-- A smooth nonvanishing polar solution of the actual Gross–Pitaevskii
equation satisfies the Cartesian density continuity balance and the
phase equation with its amplitude Laplacian term. -/
theorem gpe_polar_balances (ℏ m g : ℝ) (A θ : ℝ → GpeSpace → ℝ) (t : ℝ) (x : GpeSpace)
    (hh : ℏ ≠ 0) (hm : m ≠ 0) (hR : A t x ≠ 0)
    (htA : DifferentiableAt ℝ (fun s => A s x) t)
    (htθ : DifferentiableAt ℝ (fun s => θ s x) t)
    (hsA : ContDiff ℝ 2 (A t)) (hsθ : ContDiff ℝ 2 (θ t))
    (hGPE : Complex.I * (ℏ : ℂ) * deriv (fun s => gpePolarState A θ s x) t =
      -((ℏ ^ 2 / (2 * m) : ℝ) : ℂ) * gpeLaplacian (gpePolarState A θ t) x +
        (g : ℂ) * (Complex.normSq (gpePolarState A θ t x) : ℂ) * gpePolarState A θ t x) :
    deriv (fun s => (A s x) ^ 2) t +
      ℏ / m * (2 * A t x * gpeGradDot (A t) (θ t) x +
        (A t x) ^ 2 * gpeLaplacian (θ t) x) = 0 ∧
      ℏ * deriv (fun s => θ s x) t + ℏ ^ 2 / (2 * m) * gpeGradDot (θ t) (θ t) x +
        g * (A t x) ^ 2 - ℏ ^ 2 / (2 * m) * gpeLaplacian (A t) x / A t x = 0 := by
  let u := Complex.exp ((θ t x : ℂ) * Complex.I)
  have hu : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [u, Complex.norm_exp, Complex.mul_re]
  have ht :
      deriv (fun s => gpePolarState A θ s x) t =
        (((deriv (fun s => A s x) t : ℝ) : ℂ) +
          Complex.I * (A t x * deriv (fun s => θ s x) t : ℝ)) * u :=
    deriv_gpePolarWave (fun s => A s x) (fun s => θ s x) t htA htθ
  have hψ : gpePolarState A θ t x = (A t x : ℂ) * u := rfl
  have hψSq : Complex.normSq (gpePolarState A θ t x) = (A t x) ^ 2 := by
    simp [hψ, Complex.normSq_mul, hu, Complex.normSq_ofReal, pow_two]
  rw [ht, gpeLaplacian_polarState A θ t x hsA hsθ, hψSq, hψ] at hGPE
  have hCoeff :
      Complex.I * (ℏ : ℂ) * (((deriv (fun s => A s x) t : ℝ) : ℂ) +
        Complex.I * (A t x * deriv (fun s => θ s x) t : ℝ)) =
        -((ℏ ^ 2 / (2 * m) : ℝ) : ℂ) *
          (((gpeLaplacian (A t) x - A t x * gpeGradDot (θ t) (θ t) x : ℝ) : ℂ) +
            Complex.I * ((2 * gpeGradDot (A t) (θ t) x +
              A t x * gpeLaplacian (θ t) x : ℝ) : ℂ)) + (g * (A t x) ^ 3 : ℝ) := by
    apply mul_right_cancel₀ (Complex.exp_ne_zero ((θ t x : ℂ) * Complex.I))
    change _ * u = _ * u
    push_cast at hGPE ⊢
    linear_combination hGPE
  obtain ⟨hDensity, hPhase⟩ := gpe_polar_coefficients ℏ m g (A t x)
    (deriv (fun s => A s x) t) (deriv (fun s => θ s x) t)
    (gpeLaplacian (A t) x) (gpeLaplacian (θ t) x)
    (gpeGradDot (A t) (θ t) x) (gpeGradDot (θ t) (θ t) x) hh hm hR hCoeff
  refine ⟨?_, hPhase⟩
  rw [(htA.hasDerivAt.fun_pow 2).deriv]
  simpa using hDensity

end Qatlib.Papers.SuperfluidHel18.Madelung
