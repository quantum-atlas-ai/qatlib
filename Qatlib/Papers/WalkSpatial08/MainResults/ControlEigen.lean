/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.ControlledWalkDefs
import Mathlib.Analysis.Complex.Exponential

/-!
# Eigenvectors of the controlled walk

This module defines `Capp`, the two-component action of a controlled walk conjugated by a real
control rotation. It verifies the lifted eigenvector identity for a walk eigenvector and the
negative-eigenvalue identity on the complementary rotated control component.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `Capp_eigen_ket1`: lifting a walk eigenvector through the rotated control state.
* `Capp_eigen_ket0`: negation on the complementary control component when the walk preserves
  zero.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

variable {ι : Type*}

/-- The two-component transformation obtained by rotating the control components, applying
negation on one component and `W` on the other, and rotating back. -/
def Capp (W : (ι → ℂ) → (ι → ℂ)) (θ : ℝ)
    (x : (ι → ℂ) × (ι → ℂ)) : (ι → ℂ) × (ι → ℂ) :=
  ( fun i =>
      (Real.cos θ : ℂ) *
          (-((Real.cos θ : ℂ) * x.1 i - (Real.sin θ : ℂ) * x.2 i)) +
        (Real.sin θ : ℂ) *
          (W (fun j => (Real.sin θ : ℂ) * x.1 j + (Real.cos θ : ℂ) * x.2 j) i),
    fun i =>
      (Real.sin θ : ℂ) *
          ((Real.cos θ : ℂ) * x.1 i - (Real.sin θ : ℂ) * x.2 i) +
        (Real.cos θ : ℂ) *
          (W (fun j => (Real.sin θ : ℂ) * x.1 j + (Real.cos θ : ℂ) * x.2 j) i) )

/-- The squares of the real sine and cosine, embedded in the complex numbers, sum to one. -/
theorem sincos_sq_add (θ : ℝ) :
    (Real.sin θ : ℂ) * (Real.sin θ : ℂ) + (Real.cos θ : ℂ) * (Real.cos θ : ℂ) = 1 := by
  have h : (Real.sin θ) * (Real.sin θ) + (Real.cos θ) * (Real.cos θ) = (1 : ℝ) := by
    linear_combination Real.sin_sq_add_cos_sq θ
  exact_mod_cast h

/-- A vector with `W` eigenvalue `exp (I * θ)` lifts to the rotated control pair `(sin θ * Φ,
cos θ * Φ)` with the same eigenvalue. See [Main result: O(sqrt(N log N)) two-dimensional
spatial search][Tulsi2008]. -/
theorem Capp_eigen_ket1 (W : (ι → ℂ) → (ι → ℂ)) (θ : ℝ) (Φ : ι → ℂ)
    (hW : W Φ = fun i => Complex.exp (Complex.I * (θ : ℂ)) * Φ i) :
    Capp W θ (fun i => (Real.sin θ : ℂ) * Φ i, fun i => (Real.cos θ : ℂ) * Φ i)
      = (fun i => Complex.exp (Complex.I * (θ : ℂ)) * ((Real.sin θ : ℂ) * Φ i),
         fun i => Complex.exp (Complex.I * (θ : ℂ)) * ((Real.cos θ : ℂ) * Φ i)) := by
  have hy1 :
      (fun j => (Real.sin θ : ℂ) * ((Real.sin θ : ℂ) * Φ j) +
        (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) * Φ j)) = Φ := by
    funext j
    have hs := sincos_sq_add θ
    calc (Real.sin θ : ℂ) * ((Real.sin θ : ℂ) * Φ j) +
          (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) * Φ j)
        = ((Real.sin θ : ℂ) * (Real.sin θ : ℂ) +
            (Real.cos θ : ℂ) * (Real.cos θ : ℂ)) * Φ j := by ring
      _ = 1 * Φ j := by rw [hs]
      _ = Φ j := by ring
  apply Prod.ext
  · funext i
    simp only [Capp, hy1, hW]
    ring
  · funext i
    simp only [Capp, hy1, hW]
    ring

/-- If `W` maps zero to zero, `Capp` negates the rotated control pair `(cos θ * ψ, -sin θ * ψ)`.
See [Main result: O(sqrt(N log N)) two-dimensional spatial search][Tulsi2008]. -/
theorem Capp_eigen_ket0 (W : (ι → ℂ) → (ι → ℂ)) (θ : ℝ) (ψ : ι → ℂ)
    (hW0 : W (fun _ => 0) = fun _ => 0) :
    Capp W θ (fun i => (Real.cos θ : ℂ) * ψ i, fun i => -((Real.sin θ : ℂ) * ψ i))
      = (fun i => -((Real.cos θ : ℂ) * ψ i), fun i => (Real.sin θ : ℂ) * ψ i) := by
  have hy0p : ∀ j, (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) * ψ j) -
      (Real.sin θ : ℂ) * (-((Real.sin θ : ℂ) * ψ j)) = ψ j := by
    intro j
    have hs := sincos_sq_add θ
    calc (Real.cos θ : ℂ) * ((Real.cos θ : ℂ) * ψ j) -
          (Real.sin θ : ℂ) * (-((Real.sin θ : ℂ) * ψ j))
        = ((Real.sin θ : ℂ) * (Real.sin θ : ℂ) +
            (Real.cos θ : ℂ) * (Real.cos θ : ℂ)) * ψ j := by ring
      _ = 1 * ψ j := by rw [hs]
      _ = ψ j := by ring
  have hy1 :
      (fun j => (Real.sin θ : ℂ) * ((Real.cos θ : ℂ) * ψ j) +
        (Real.cos θ : ℂ) * (-((Real.sin θ : ℂ) * ψ j))) = fun _ => 0 := by
    funext j; ring
  apply Prod.ext
  · funext i
    simp only [Capp, hy1, hW0]
    rw [hy0p i]
    ring
  · funext i
    simp only [Capp, hy1, hW0]
    rw [hy0p i]
    ring

end Qatlib.Papers.WalkSpatial08.MainResults
