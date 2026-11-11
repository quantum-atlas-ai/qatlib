/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GinibrePerm26.MainResults.LinearOpticsComplexityModelsDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma C.4 of Koehler–Leung: quaternionic Gaussian left–right symmetry

Source: F. Koehler, P. K. Leung, *Anticoncentration of the Permanent in Ginibre
Ensembles*, arXiv:2607.20329v1, Lemma C.4 (Appendix C.2).

The lemma states that for fixed `d₁, …, dₚ ∈ ℍ` and independent standard
quaternionic Gaussians `g₁, …, gₚ, h₁, …, hₚ`,

  `∑ⱼ gⱼ dⱼ  =ᵈ  ∑ⱼ dⱼ hⱼ`,

i.e. multiplying the Gaussian factors on the right by the fixed coefficients is
distributionally the same as multiplying them on the left.  The source proof
observes that both sides are centred real Gaussian vectors in `ℍ ≅ ℝ⁴` with
covariance `(1/4) (∑ⱼ ‖dⱼ‖²) I₄`; the formal proof below replaces the covariance
computation by the equivalent characteristic-function computation: for a fixed
`q`, the maps `x ↦ q * x` and `x ↦ x * q` are both scaled orthogonal maps of the
underlying real space (`‖q * x‖ = ‖x * q‖ = ‖q‖ ‖x‖`), so they push the standard
Gaussian `stdGaussian ℍ` to the same law.  Independence then promotes the
one-factor identity to the sum over `j`.

The standard quaternionic Gaussian of the source has real coordinates
`N(0, 1/4)`; in the model vocabulary this is `kGaussianLaw ℍ`, i.e. `stdGaussian ℍ`
scaled by `1/√β = 1/2`.
-/

namespace Qatlib.Papers.GinibrePerm26.MainResults

open Qatlib.Papers.GinibrePerm26.MainResults
open MeasureTheory ProbabilityTheory

set_option autoImplicit false

open scoped Quaternion RealInnerProductSpace InnerProductSpace

noncomputable section

/-! ## Cyclicity of the real part of a quaternion product -/

/-- The real part of a quaternion product is invariant under swapping the
factors: `Re (a * b) = Re (b * a)`.  This is the component form of the
symmetry of the underlying Euclidean scalar product on `ℍ ≅ ℝ⁴`. -/
theorem quaternion_re_mul_comm (a b : ℍ) : (a * b).re = (b * a).re := by
  rw [Quaternion.re_mul, Quaternion.re_mul]
  ring

/-- Adjoint identity for left multiplication by a quaternion:
`⟪q * x, t⟫_ℝ = ⟪x, star q * t⟫_ℝ`. -/
theorem inner_quaternion_leftMul (q x t : ℍ) :
    ⟪q * x, t⟫_ℝ = ⟪x, star q * t⟫_ℝ := by
  simp only [Quaternion.inner_def, star_mul, star_star]
  rw [show (q * x * star t).re = (star t * (q * x)).re from quaternion_re_mul_comm _ _]
  rw [← mul_assoc]
  exact quaternion_re_mul_comm (star t * q) x

/-- Adjoint identity for right multiplication by a quaternion:
`⟪x * q, t⟫_ℝ = ⟪x, t * star q⟫_ℝ`. -/
theorem inner_quaternion_rightMul (q x t : ℍ) :
    ⟪x * q, t⟫_ℝ = ⟪x, t * star q⟫_ℝ := by
  simp only [Quaternion.inner_def, star_mul, star_star]
  rw [mul_assoc]

/-! ## One-factor symmetry for the standard Gaussian on `ℍ` -/

/-- The characteristic function of the pushforward of `stdGaussian ℍ` under left
multiplication by `q` is the Gaussian characteristic function with scale
`‖q‖`: `E exp (i⟪q * X, t⟫) = exp (-(‖q‖ ‖t‖)² / 2)`. -/
theorem charFun_map_quaternion_leftMul (q t : ℍ) :
    charFun (Measure.map (fun x : ℍ => q * x) (stdGaussian ℍ)) t
      = Complex.exp (-(((‖q‖ * ‖t‖) ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [charFun_apply, MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_quaternion_leftMul]
  rw [← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [norm_mul, Quaternion.norm_star]
  push_cast
  ring

/-- The same characteristic function for right multiplication by `q`. -/
theorem charFun_map_quaternion_rightMul (q t : ℍ) :
    charFun (Measure.map (fun x : ℍ => x * q) (stdGaussian ℍ)) t
      = Complex.exp (-(((‖q‖ * ‖t‖) ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [charFun_apply, MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_quaternion_rightMul]
  rw [← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [norm_mul, Quaternion.norm_star, mul_comm (‖t‖) (‖q‖)]
  push_cast
  ring

/-- For a fixed quaternion `q`, left multiplication and right multiplication
push the standard Gaussian on `ℍ` to the same law.  This is the one-factor
content of Lemma C.4: both are scaled orthogonal maps with the same scale. -/
theorem quaternion_stdGaussian_leftRight (q : ℍ) :
    Measure.map (fun x : ℍ => q * x) (stdGaussian ℍ)
      = Measure.map (fun x : ℍ => x * q) (stdGaussian ℍ) :=
  Measure.ext_of_charFun <| funext fun t =>
    (charFun_map_quaternion_leftMul q t).trans (charFun_map_quaternion_rightMul q t).symm

/-! ## The same identity for the standard quaternionic Gaussian -/

/-- The model's standard quaternionic Gaussian is `stdGaussian ℍ` scaled by
`1 / √β`, matching real coordinates `N(0, 1/4)`. -/
theorem kGaussianLaw_quaternion_eq :
    kGaussianLaw ℍ =
      Measure.map (fun x : ℍ => ((Real.sqrt (Module.finrank ℝ ℍ : ℝ))⁻¹) • x)
        (stdGaussian ℍ) :=
  rfl

/-- The model's standard quaternionic Gaussian is a probability measure. -/
instance isProbabilityMeasure_kGaussianLaw_quaternion : IsProbabilityMeasure (kGaussianLaw ℍ) := by
  rw [kGaussianLaw_quaternion_eq]
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- For a fixed quaternion `q`, left multiplication and right multiplication
push the standard quaternionic Gaussian `kGaussianLaw ℍ` to the same law. -/
theorem map_quaternion_mulLeft_kGaussian (q : ℍ) :
    Measure.map (fun x : ℍ => q * x) (kGaussianLaw ℍ)
      = Measure.map (fun x : ℍ => x * q) (kGaussianLaw ℍ) := by
  set c : ℝ := (Real.sqrt (Module.finrank ℝ ℍ : ℝ))⁻¹ with hc
  have hpoint : ∀ x : ℍ, q * (c • x) = c • (q * x) := by
    intro x
    rw [← Quaternion.coe_mul_eq_smul (r := c) (a := x),
      ← Quaternion.coe_mul_eq_smul (r := c) (a := q * x),
      ← mul_assoc, ← Quaternion.coe_commutes (r := c) (a := q), mul_assoc]
  have hpoint' : ∀ x : ℍ, (c • x) * q = c • (x * q) := by
    intro x
    rw [← Quaternion.coe_mul_eq_smul (r := c) (a := x),
      ← Quaternion.coe_mul_eq_smul (r := c) (a := x * q),
      mul_assoc]
  rw [kGaussianLaw_quaternion_eq, ← hc]
  calc
    Measure.map (fun x : ℍ => q * x)
        (Measure.map (fun x : ℍ => c • x) (stdGaussian ℍ))
        = Measure.map (fun x : ℍ => q * (c • x)) (stdGaussian ℍ) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = Measure.map (fun x : ℍ => c • (q * x)) (stdGaussian ℍ) := by
          congr 1
          funext x
          exact hpoint x
    _ = Measure.map (fun y : ℍ => c • y)
          (Measure.map (fun x : ℍ => q * x) (stdGaussian ℍ)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = Measure.map (fun y : ℍ => c • y)
          (Measure.map (fun x : ℍ => x * q) (stdGaussian ℍ)) := by
          rw [quaternion_stdGaussian_leftRight q]
    _ = Measure.map (fun x : ℍ => c • (x * q)) (stdGaussian ℍ) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = Measure.map (fun x : ℍ => (c • x) * q) (stdGaussian ℍ) := by
          congr 1
          funext x
          exact (hpoint' x).symm
    _ = Measure.map (fun x : ℍ => x * q)
          (Measure.map (fun x : ℍ => c • x) (stdGaussian ℍ)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl

/-! ## Lemma C.4: distributional left–right symmetry of the Gaussian sum -/

/-- Lemma C.4 of Koehler–Leung (arXiv:2607.20329v1, Appendix C.2): for fixed
quaternions `d` and independent standard quaternionic Gaussians `g` and `h`,
the sums `∑ⱼ gⱼ dⱼ` and `∑ⱼ dⱼ hⱼ` have the same law. -/
theorem quaternionGaussian_leftRight_symmetry (p : ℕ) (d : Fin p → ℍ) :
    Measure.map (fun g : Fin p → ℍ => ∑ j, g j * d j)
        (Measure.pi fun _ : Fin p => kGaussianLaw ℍ)
      = Measure.map (fun h : Fin p → ℍ => ∑ j, d j * h j)
        (Measure.pi fun _ : Fin p => kGaussianLaw ℍ) := by
  have hprod :
      Measure.map (fun g : Fin p → ℍ => fun j => g j * d j)
          (Measure.pi fun _ : Fin p => kGaussianLaw ℍ)
        = Measure.map (fun h : Fin p → ℍ => fun j => d j * h j)
            (Measure.pi fun _ : Fin p => kGaussianLaw ℍ) := by
    rw [Measure.pi_map_pi (f := fun j (x : ℍ) => x * d j) (by fun_prop),
      Measure.pi_map_pi (f := fun j (x : ℍ) => d j * x) (by fun_prop)]
    congr 1
    funext j
    exact (map_quaternion_mulLeft_kGaussian (d j)).symm
  calc
    Measure.map (fun g : Fin p → ℍ => ∑ j, g j * d j)
        (Measure.pi fun _ : Fin p => kGaussianLaw ℍ)
        = Measure.map (fun y : Fin p → ℍ => ∑ j, y j)
            (Measure.map (fun g : Fin p → ℍ => fun j => g j * d j)
              (Measure.pi fun _ : Fin p => kGaussianLaw ℍ)) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = Measure.map (fun y : Fin p → ℍ => ∑ j, y j)
            (Measure.map (fun h : Fin p → ℍ => fun j => d j * h j)
              (Measure.pi fun _ : Fin p => kGaussianLaw ℍ)) := by rw [hprod]
    _ = Measure.map (fun h : Fin p → ℍ => ∑ j, d j * h j)
            (Measure.pi fun _ : Fin p => kGaussianLaw ℍ) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl

end

end Qatlib.Papers.GinibrePerm26.MainResults
