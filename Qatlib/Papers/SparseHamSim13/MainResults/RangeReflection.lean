/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseHamSim13.MainResults.ObliviousAmplification.TwoDSubspace
public import Qatlib.Papers.SparseHamSim13.MainResults.ObliviousAmplification.ObliviousAmplitudeAmplification
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# Projection and reflection on the embedded data register

The orthogonality in Lemma 3.7 is equivalent to vanishing under the
orthogonal projection onto the embedded data register. Reflection in
that range fixes the embedded data and negates both orthogonal branches.
These actions instantiate the abstract rotation theorem of Lemma 3.6.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open Qatlib.Papers.SparseHamSim13.MainResults

namespace Qatlib.Papers.SparseHamSim13.MainResults

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The projection onto the embedded register kills precisely the vectors
orthogonal to every embedded data state. -/
theorem range_projection_zero_iff (A : E →ₗᵢ[ℂ] H)
    [(LinearMap.range A.toLinearMap).HasOrthogonalProjection] (x : H) :
    (LinearMap.range A.toLinearMap).starProjection x = 0 ↔ ∀ w, ⟪A w, x⟫_ℂ = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h w
    exact h (A w) ⟨w, rfl⟩
  · intro h z hz
    obtain ⟨w, rfl⟩ := hz
    exact h w

/-- Lemma 3.6 with the actual reflection in the embedded data range.
The two orthogonal branches are negated by that reflection, by the input
projection condition and Lemma 3.7 respectively. -/
theorem oblivious_rotation_with_range_reflection
    (A : E →ₗᵢ[ℂ] H) [(LinearMap.range A.toLinearMap).HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℂ] H) (V : E ≃ₗᵢ[ℂ] E) (Φ : E →ₗ[ℂ] H) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hU : ∀ ψ, U (A ψ) = (Real.sin θ : ℂ) • A (V ψ) + (Real.cos θ : ℂ) • Φ ψ)
    (hproj : ∀ ψ, (LinearMap.range A.toLinearMap).starProjection (Φ ψ) = 0)
    (hΦ : ∀ ψ w, ⟪Φ ψ, Φ w⟫_ℂ = ⟪ψ, w⟫_ℂ) :
    let R := (LinearMap.range A.toLinearMap).reflection
    let S := R.trans (U.symm.trans (R.trans (U.trans (LinearIsometryEquiv.neg ℂ))))
    ∀ (ℓ : ℤ) (ψ : E), (S ^ ℓ) (U (A ψ)) =
      (Real.sin ((2 * (ℓ : ℝ) + 1) * θ) : ℂ) • A (V ψ) +
      (Real.cos ((2 * (ℓ : ℝ) + 1) * θ) : ℂ) • Φ ψ := by
  dsimp only
  let K := LinearMap.range A.toLinearMap
  have horth ψ : ∀ w, ⟪A w, Φ ψ⟫_ℂ = 0 :=
    (range_projection_zero_iff A (Φ ψ)).mp (hproj ψ)
  have hs : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hcosSq : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  have hp : Real.sin θ ^ 2 < 1 := by
    linarith [sq_pos_of_pos hc]
  have hperp (ψ w : E) :
      ⟪A w, U.symm ((Real.cos θ : ℂ) • A (V ψ) - (Real.sin θ : ℂ) • Φ ψ)⟫_ℂ = 0 := by
    have h := (twoD_subspace_lemma A U V Φ (Real.sin θ ^ 2) (sq_pos_of_pos hs) hp
      (by simpa only [Real.sqrt_sq hs.le, hcosSq, Real.sqrt_sq hc.le] using hU) horth hΦ).2 ψ w
    simpa only [Real.sqrt_sq hs.le, hcosSq, Real.sqrt_sq hc.le] using h
  refine lemma_3_6_oblivious_amplitude_amplification A U V Φ K.reflection _
    θ hθ0 hθ1 hU horth hΦ ?_ ?_ ?_ ?_
  · intro ψ
    exact K.reflection_mem_subspace_eq_self ⟨ψ, rfl⟩
  · intro ψ
    exact K.reflection_mem_subspace_orthogonalComplement_eq_neg
      ((Submodule.starProjection_apply_eq_zero_iff K).mp (hproj ψ))
  · intro ψ
    refine K.reflection_mem_subspace_orthogonalComplement_eq_neg
      ((Submodule.starProjection_apply_eq_zero_iff K).mp ?_)
    exact (range_projection_zero_iff A _).mpr (hperp ψ)
  · intro x
    rfl

end Qatlib.Papers.SparseHamSim13.MainResults
