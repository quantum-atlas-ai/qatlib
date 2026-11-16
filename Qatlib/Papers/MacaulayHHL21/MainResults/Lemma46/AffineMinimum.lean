/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46.RangeOpt
public import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46.AffineKernel
public import Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46.SourceLemma46

@[expose] public section


/-!
# Shortest vector in a complex affine hull

Fixed source: arXiv:2111.00405v1, Lemma 4.6, PDF pages 10–11, equations (12)–(13).
The source's finite-dimensional statement is retained. The proof separates the
case where the affine hull contains zero from the case where the Gram equation
with all-ones right-hand side is solvable. In the latter case, Cauchy-Schwarz
proves the sharp rank-one positive-semidefinite bound, and the Moore-Penrose
solution attains it.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix
open Qatlib.Papers.MacaulayHHL21.MainResults
open Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46

/-- Lemma 4.6: characterize the zero affine minimum, the sharp PSD bound,
and the nonzero minimum through the Gram pseudoinverse. -/
theorem lemma46_affine_min {n k : ℕ} (hk : 0 < k)
    (V : Matrix (Fin n) (Fin k) ℂ) :
    ∃ w : Fin k → ℂ, (∑ i, w i) = 1 ∧
      ∀ x : Fin k → ℂ, (∑ i, x i) = 1 →
        l2Norm (V *ᵥ w) ^ 2 ≤ l2Norm (V *ᵥ x) ^ 2 := by
  by_cases hr : ∃ x : Fin k → ℂ, (Vᴴ * V) *ᵥ x = fun _ => 1
  · let u := matrixPseudoinverse (Vᴴ * V) *ᵥ (fun _ : Fin k => (1 : ℂ))
    have hu : (Vᴴ * V) *ᵥ u = fun _ => 1 := pinv_solves _ _ hr
    refine ⟨(((l2NormSq (V *ᵥ u))⁻¹ : ℝ) : ℂ) • u,
      gram_normal_sum hk V hu, ?_⟩
    intro x hx
    rw [l2Norm_sq, l2Norm_sq, gram_normal_norm hk V hu]
    have h := gram_rank_bound hk V hu x
    simpa only [hx, norm_one, one_pow, mul_one] using h
  · obtain ⟨w, hsum, hw⟩ := (affine_kernel V).mpr hr
    refine ⟨w, hsum, ?_⟩
    intro x _
    rw [hw]
    simp [l2Norm, l2NormSq]

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma46
