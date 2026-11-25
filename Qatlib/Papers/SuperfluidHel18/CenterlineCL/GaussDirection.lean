/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussLinking

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The unit-chord map of the Gauss linking integral

[Kedia2018SuperfluidHelicity], Section II and Eq. (6),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The Euclidean Gauss kernel is the normalized oriented area density of the
unit chord between the two curves. This identifies the specific analytic
integral used for centerline helicity with the area integral of its Gauss
map, including the orientation and the factor `4π`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open MeasureTheory
open scoped ContDiff Real

/-- The unit Euclidean chord directed from the second curve to the first. -/
noncomputable def gaussDirection (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ) : Fin 3 → ℝ :=
  (euclideanLength (γ₁ s - γ₂ t))⁻¹ • (γ₁ s - γ₂ t)

/-- The Euclidean chord length is positive when the two endpoints differ. -/
private theorem euclideanLength_pos_of_ne {a b : Fin 3 → ℝ} (hab : a ≠ b) :
    0 < euclideanLength (a - b) :=
  (norm_pos_iff.mpr (sub_ne_zero.mpr hab)).trans_le (norm_le_euclideanLength _)

/-- Away from coincidence, the Gauss direction has Euclidean length one. -/
theorem euclideanLength_gaussDirection
    (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ) (h : γ₁ s ≠ γ₂ t) :
    euclideanLength (gaussDirection γ₁ γ₂ s t) = 1 := by
  have hp := euclideanLength_pos_of_ne h
  rw [gaussDirection, euclideanLength_smul, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']

/-- The Cartesian squared length agrees with the square of the Euclidean norm. -/
theorem euclideanLength_sq_eq_dot3 (v : Fin 3 → ℝ) :
    euclideanLength v ^ 2 = dot3 v v := by
  rw [euclideanLength, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [dot3, pow_two]

/-- At distinct endpoints the normalized chord lies on the Cartesian
unit sphere. -/
theorem gaussDirection_dot_self (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ)
    (h : γ₁ s ≠ γ₂ t) :
    dot3 (gaussDirection γ₁ γ₂ s t) (gaussDirection γ₁ γ₂ s t) = 1 := by
  rw [← euclideanLength_sq_eq_dot3, euclideanLength_gaussDirection _ _ _ _ h, one_pow]

/-- The direction varies continuously with both parameters for disjoint
continuous curves. -/
theorem continuous_gaussDirection (γ₁ γ₂ : ℝ → (Fin 3 → ℝ))
    (h₁ : Continuous γ₁) (h₂ : Continuous γ₂) (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) :
    Continuous (fun p : ℝ × ℝ => gaussDirection γ₁ γ₂ p.1 p.2) := by
  let c := fun p : ℝ × ℝ => γ₁ p.1 - γ₂ p.2
  have hc : Continuous c := (h₁.comp continuous_fst).sub (h₂.comp continuous_snd)
  have hn (p : ℝ × ℝ) : euclideanLength (c p) ≠ 0 :=
    (euclideanLength_pos_of_ne (hdisj p.1 p.2)).ne'
  exact ((continuous_euclideanLength.comp hc).inv₀ hn).smul hc

/-- Euclidean length is smooth at every nonzero Cartesian chord. -/
theorem contDiffAt_euclideanLength {n : ℕ∞ω} {c : Fin 3 → ℝ} (hne : c ≠ 0) :
    ContDiffAt ℝ n euclideanLength c := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have he : e c ≠ 0 := fun h => hne (e.injective (h.trans e.map_zero.symm))
  exact (contDiffAt_norm ℝ he).comp c e.contDiff.contDiffAt

/-- Positive-length normalization is differentiable along a
differentiable nonzero chord. -/
private theorem differentiableAt_inv_euclideanLength (c : ℝ → (Fin 3 → ℝ)) (s : ℝ)
    (hc : DifferentiableAt ℝ c s) (hne : c s ≠ 0) :
    DifferentiableAt ℝ (fun u => (euclideanLength (c u))⁻¹) s := by
  have hn := (contDiffAt_euclideanLength (n := 1) hne).differentiableAt (by norm_num)
  exact (hn.comp s hc).inv ((norm_pos_iff.mpr hne).trans_le (norm_le_euclideanLength _)).ne'

/-- The terms created by differentiating the scalar normalization are
parallel to the chord, so their scalar triple products vanish. -/
private theorem normalized_chord_triple (c u v : Fin 3 → ℝ) (a b d : ℝ) :
    dot3 (cross3 ((-a) • v + b • c) (a • u + d • c)) (a • c) =
      a ^ 3 * dot3 (cross3 u v) c := by
  simp [dot3, cross3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- In the orientation with the second parameter followed by the first,
the Gauss map's spherical area density divided by `4π` is the actual
Gauss linking kernel. -/
theorem gaussDirection_area_density (γ₁ γ₂ : ℝ → (Fin 3 → ℝ)) (s t : ℝ)
    (h₁ : DifferentiableAt ℝ γ₁ s) (h₂ : DifferentiableAt ℝ γ₂ t)
    (hdisj : γ₁ s ≠ γ₂ t) :
    dot3 (cross3 (deriv (fun v => gaussDirection γ₁ γ₂ s v) t)
      (deriv (fun u => gaussDirection γ₁ γ₂ u t) s)) (gaussDirection γ₁ γ₂ s t) /
        (4 * π) = gaussKernel γ₁ γ₂ s t := by
  let c₁ := fun u => γ₁ u - γ₂ t
  let c₂ := fun v => γ₁ s - γ₂ v
  let a₁ := fun u => (euclideanLength (c₁ u))⁻¹
  let a₂ := fun v => (euclideanLength (c₂ v))⁻¹
  have hne : γ₁ s - γ₂ t ≠ 0 := sub_ne_zero.mpr hdisj
  have hD₁ : HasDerivAt c₁ (deriv γ₁ s) s := h₁.hasDerivAt.sub_const _
  have hD₂ : HasDerivAt c₂ (-deriv γ₂ t) t := h₂.hasDerivAt.const_sub _
  have hN₁ : HasDerivAt a₁ (deriv a₁ s) s :=
    (differentiableAt_inv_euclideanLength c₁ s hD₁.differentiableAt hne).hasDerivAt
  have hN₂ : HasDerivAt a₂ (deriv a₂ t) t :=
    (differentiableAt_inv_euclideanLength c₂ t hD₂.differentiableAt hne).hasDerivAt
  have hs : HasDerivAt (fun u => gaussDirection γ₁ γ₂ u t)
      (a₁ s • deriv γ₁ s + deriv a₁ s • c₁ s) s := by
    have h := hN₁.smul hD₁
    change HasDerivAt (fun u => gaussDirection γ₁ γ₂ u t) _ s at h
    exact h.congr_deriv (by rw [add_comm])
  have ht : HasDerivAt (fun v => gaussDirection γ₁ γ₂ s v)
      ((-a₂ t) • deriv γ₂ t + deriv a₂ t • c₂ t) t := by
    have h := hN₂.smul hD₂
    change HasDerivAt (fun v => gaussDirection γ₁ γ₂ s v) _ t at h
    exact h.congr_deriv (by rw [smul_neg, neg_smul])
  rw [hs.deriv, ht.deriv]
  change dot3 (cross3 ((-a₁ s) • deriv γ₂ t + deriv a₂ t • c₁ s)
    (a₁ s • deriv γ₁ s + deriv a₁ s • c₁ s)) (a₁ s • c₁ s) / (4 * π) = _
  rw [normalized_chord_triple]
  unfold gaussKernel a₁ c₁
  rw [inv_pow]
  ring

/-- For disjoint differentiable curves, the entire Gauss linking integral
is the integral of the normalized oriented Gauss-map area density. -/
theorem gaussLinking_eq_direction_area (γ₁ γ₂ : ℝ → (Fin 3 → ℝ))
    (h₁ : Differentiable ℝ γ₁) (h₂ : Differentiable ℝ γ₂)
    (hdisj : ∀ s t, γ₁ s ≠ γ₂ t) :
    gaussLinking γ₁ γ₂ =
      ∫ p, dot3 (cross3 (deriv (fun t => gaussDirection γ₁ γ₂ p.1 t) p.2)
        (deriv (fun s => gaussDirection γ₁ γ₂ s p.2) p.1))
          (gaussDirection γ₁ γ₂ p.1 p.2) / (4 * π) ∂gaussMeasure := by
  unfold gaussLinking
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p =>
    (gaussDirection_area_density γ₁ γ₂ p.1 p.2 (h₁ _) (h₂ _) (hdisj _ _)).symm

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
