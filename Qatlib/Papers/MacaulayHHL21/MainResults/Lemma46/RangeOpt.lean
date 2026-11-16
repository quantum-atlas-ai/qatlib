/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46.GramHelpers
public import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46.SourceLemma46

@[expose] public section


/-!
# Sharp affine norm when the Gram equation is solvable

This is the nonzero case of Lemma 4.6 of arXiv:2111.00405v1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open scoped BigOperators ComplexOrder
open Matrix
open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46

/-- Any solution of the all-ones Gram equation gives the sharp affine norm after normalization. -/
theorem gram_range_opt {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ)
    (u : Fin k → ℂ) (hu : (Vᴴ * V) *ᵥ u = fun _ => 1) :
    let G := Vᴴ * V
    let ones : Matrix (Fin k) (Fin k) ℂ := Matrix.of (fun _ _ => 1)
    let one : Fin k → ℂ := fun _ => 1
    ∃ γstar : ℝ, 0 ≤ γstar ∧ PSD (G - γstar • ones) ∧
      (∀ γ : ℝ, PSD (G - γ • ones) → γ ≤ γstar) ∧
      (γstar ≠ 0 →
        γstar = 1 / (star one ⬝ᵥ u).re ∧
        l2Norm (V *ᵥ (((star one ⬝ᵥ u).re)⁻¹ : ℂ) • u) ^ 2 = γstar) := by
  dsimp only
  let d := l2NormSq (V *ᵥ u)
  have hd : 0 < d := gram_image_pos hk V hu
  have hden : (star (fun _ : Fin k => (1 : ℂ)) ⬝ᵥ u).re = d := by
    change (ip (fun _ => 1) u).re = d
    rw [ip_one, gram_sum_real V hu]
    rfl
  refine ⟨d⁻¹, (inv_pos.mpr hd).le, ?_, ?_, ?_⟩
  · intro z
    change 0 ≤ (ip z (((Vᴴ * V) - d⁻¹ • Matrix.of (fun _ _ => (1 : ℂ))) *ᵥ z)).re
    rw [gram_rank_one]
    exact sub_nonneg.mpr (gram_rank_bound hk V hu z)
  · intro γ hγ
    let w : Fin k → ℂ := ((d⁻¹ : ℝ) : ℂ) • u
    have hsum : (∑ i, w i) = 1 := gram_normal_sum hk V hu
    have hnorm : l2NormSq (V *ᵥ w) = d⁻¹ := gram_normal_norm hk V hu
    have h := hγ w
    change 0 ≤ (ip w (((Vᴴ * V) - γ • Matrix.of (fun _ _ => (1 : ℂ))) *ᵥ w)).re at h
    rw [gram_rank_one, hnorm, hsum] at h
    simpa using sub_nonneg.mp h
  · intro _
    change d⁻¹ = 1 / (star (fun _ : Fin k => (1 : ℂ)) ⬝ᵥ u).re ∧
      l2Norm (V *ᵥ (((star (fun _ : Fin k => (1 : ℂ)) ⬝ᵥ u).re)⁻¹ : ℂ) • u) ^ 2 = d⁻¹
    rw [hden]
    constructor
    · exact (one_div d).symm
    · rw [l2Norm_sq]
      simpa only [Complex.ofReal_inv] using gram_normal_norm hk V hu

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
