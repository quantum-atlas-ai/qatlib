/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.ElectricCircles
public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticFiberPair

import Mathlib.Tactic.Ring

/-!
# The Gauss linking value of distinct compact electric fibers

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The same proper rotation that identifies the electric and magnetic
fields preserves the Gauss kernel. The magnetic linking values
therefore give the actual electric linking values on every slice.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussKernel gaussLinking euclideanLength)
open MeasureTheory

/-- The inverse spatial quarter-turn conjugated to the Euclidean
coordinate representation used by the Gauss integral. -/
private def inverseQuarterTurn : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  cartesianCoordinates.symm.trans (electricToMagnetic.symm.trans cartesianCoordinates)

/-- The inverse quarter-turn exchanges the first two coordinates with
one change of sign. -/
private theorem inverseQuarterTurn_apply (x : Fin 3 → ℝ) :
    inverseQuarterTurn x = ![x 1, -x 0, x 2] := rfl

/-- A proper quarter-turn preserves Euclidean chord lengths. -/
private theorem euclideanLength_inverseQuarterTurn (x : Fin 3 → ℝ) :
    euclideanLength (inverseQuarterTurn x) = euclideanLength x := by
  rw [inverseQuarterTurn_apply]
  simp only [euclideanLength, PiLp.norm_eq_of_L2, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  congr 1
  change x 1 ^ 2 + (-x 0) ^ 2 + x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
  ring

/-- A proper quarter-turn preserves the oriented scalar triple product. -/
private theorem triple_inverseQuarterTurn (a b c : Fin 3 → ℝ) :
    dot3 (cross3 (inverseQuarterTurn a) (inverseQuarterTurn b)) (inverseQuarterTurn c) =
      dot3 (cross3 a b) c := by
  simp [inverseQuarterTurn_apply, dot3, cross3]
  ring

/-- The Gauss integral is invariant under the common inverse
quarter-turn of the two differentiable curves. -/
private theorem gaussLinking_inverseQuarterTurn (γ σ : ℝ → (Fin 3 → ℝ))
    (hγ : Differentiable ℝ γ) (hσ : Differentiable ℝ σ) :
    gaussLinking (inverseQuarterTurn ∘ γ) (inverseQuarterTurn ∘ σ) = gaussLinking γ σ := by
  let L := inverseQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap
  have hdγ (s : ℝ) : deriv (inverseQuarterTurn ∘ γ) s = inverseQuarterTurn (deriv γ s) :=
    (L.hasFDerivAt.comp_hasDerivAt s (hγ s).hasDerivAt).deriv
  have hdσ (s : ℝ) : deriv (inverseQuarterTurn ∘ σ) s = inverseQuarterTurn (deriv σ s) :=
    (L.hasFDerivAt.comp_hasDerivAt s (hσ s).hasDerivAt).deriv
  unfold gaussLinking
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change gaussKernel (inverseQuarterTurn ∘ γ) (inverseQuarterTurn ∘ σ) p.1 p.2 =
      gaussKernel γ σ p.1 p.2
    simp only [gaussKernel, hdγ, hdσ, Function.comp_apply, ← map_sub,
      triple_inverseQuarterTurn, euclideanLength_inverseQuarterTurn]

/-- The actual magnetic circle remains differentiable when written in
Gauss coordinate representation. -/
private theorem differentiable_magneticCircle_coords (u v t : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    Differentiable ℝ (cartesianCoordinates ∘ magneticCircleAt u v t) := by
  intro s
  obtain ⟨μ, _, _, h⟩ := hasDerivAt_magnetic_circle_at u v t s hd
  let L := cartesianCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s h).differentiableAt

/-- The actual pole curve remains differentiable after the same
coordinate representation. -/
private theorem differentiable_magneticPole_coords (t : ℝ) :
    Differentiable ℝ (cartesianCoordinates ∘ magneticPoleCircleAt t) := by
  intro s
  obtain ⟨μ, _, _, h⟩ := hasDerivAt_magnetic_pole_circle_at t s
  let L := cartesianCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s h).differentiableAt

/-- The literal electric affine circle in Gauss coordinates is the
rotated, relabeled magnetic curve. -/
private theorem electricCircleAt_coords (u v t : ℝ) :
    (cartesianCoordinates ∘ electricCircleAt u v t) =
      inverseQuarterTurn ∘ (cartesianCoordinates ∘ magneticCircleAt v (-u) t) := by
  funext s
  simp only [electricCircleAt, inverseQuarterTurn, Function.comp_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- The electric pole in Gauss coordinates is the rotated magnetic pole. -/
private theorem electricPoleCircleAt_coords (t : ℝ) :
    (cartesianCoordinates ∘ electricPoleCircleAt t) =
      inverseQuarterTurn ∘ (cartesianCoordinates ∘ magneticPoleCircleAt t) := by
  funext s
  simp only [electricPoleCircleAt, inverseQuarterTurn, Function.comp_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- The Gauss linking integral of a finite nonzero oriented electric
fiber and the oriented electric pole equals one on every time slice. -/
theorem gaussLinking_electric_circle_pole_eq_one (u v t : ℝ) (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ electricCircleAt u v t)
      (cartesianCoordinates ∘ electricPoleCircleAt t) = 1 := by
  have hd : 0 < v ^ 2 + (-u) ^ 2 := by simpa only [neg_sq, add_comm] using huv
  rw [electricCircleAt_coords, electricPoleCircleAt_coords,
    gaussLinking_inverseQuarterTurn _ _ (differentiable_magneticCircle_coords _ _ _ hd)
      (differentiable_magneticPole_coords t)]
  exact gaussLinking_magnetic_circle_pole_eq_one v (-u) t hd

/-- The Gauss linking integral of two distinct finite nonzero
oriented electric fibers equals one on every time slice. -/
theorem gaussLinking_electric_circles_eq_one (u v p q t : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) (hpq : 0 < p ^ 2 + q ^ 2)
    (hne : ((u : ℂ) + Complex.I * (v : ℂ)) ≠ ((p : ℂ) + Complex.I * (q : ℂ))) :
    gaussLinking (cartesianCoordinates ∘ electricCircleAt u v t)
      (cartesianCoordinates ∘ electricCircleAt p q t) = 1 := by
  have hd₁ : 0 < v ^ 2 + (-u) ^ 2 := by simpa only [neg_sq, add_comm] using huv
  have hd₂ : 0 < q ^ 2 + (-p) ^ 2 := by simpa only [neg_sq, add_comm] using hpq
  have hlabel : ((v : ℂ) + Complex.I * ((-u : ℝ) : ℂ)) ≠
      ((q : ℂ) + Complex.I * ((-p : ℝ) : ℂ)) := by
    intro h
    rw [← rotated_electric_label u v, ← rotated_electric_label p q] at h
    exact hne (mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h)
  rw [electricCircleAt_coords, electricCircleAt_coords,
    gaussLinking_inverseQuarterTurn _ _ (differentiable_magneticCircle_coords _ _ _ hd₁)
      (differentiable_magneticCircle_coords _ _ _ hd₂)]
  exact gaussLinking_magnetic_circles_eq_one v (-u) q (-p) t hd₁ hd₂ hlabel

end Qatlib.Papers.KnottedLight08.NullLinking
