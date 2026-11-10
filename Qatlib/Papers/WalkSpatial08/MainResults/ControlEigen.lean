/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.ControlledWalkDefs
import Mathlib.Analysis.Complex.Exponential
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

variable {ι : Type*}

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

theorem sincos_sq_add (θ : ℝ) :
    (Real.sin θ : ℂ) * (Real.sin θ : ℂ) + (Real.cos θ : ℂ) * (Real.cos θ : ℂ) = 1 := by
  have h : (Real.sin θ) * (Real.sin θ) + (Real.cos θ) * (Real.cos θ) = (1 : ℝ) := by
    linear_combination Real.sin_sq_add_cos_sq θ
  exact_mod_cast h

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
