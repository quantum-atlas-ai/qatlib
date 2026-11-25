/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ApproxDegree20.MainResults.Spectral.SensitivityAdjacency

@[expose] public section

/-!
# Average sensitivity is bounded by the spectral sensitivity

Source: arXiv:2010.12629v1, Appendix A.4, Lemma 35 (page 32): for every total Boolean function
`f`, the average sensitivity `E_x[s_x(f)]` is at most the spectral sensitivity `λ(f)`.

The vector of all ones `w` satisfies `(A w)_x = s_x(f)`, because the `x`-th row of the
sensitivity graph has exactly `s_x(f)` unit entries.  Hence `‖A w‖² = ∑_x s_x(f)²` and
Cauchy–Schwarz gives `∑_x s_x(f) ≤ 2^n ‖A‖`, which is the claim after dividing by `2^n`.

Boundary: total Boolean functions on an arbitrary finite coordinate type `I`.  The paper's
example `λ(parity_n) = n` is not formalised here; only the inequality is proved.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds (sensAdjacency spectralSensitivity)
open Qatlib.Papers.ApproxDegree20.MainResults.Definitions
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ApproxDegree20.MainResults.Spectral

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The average sensitivity is at most the spectral sensitivity. -/
theorem avgSensitivity_le_spectralSensitivity (f : (I → Bool) → Bool) :
    avgSensitivity f ≤ spectralSensitivity f := by
  classical
  set N : ℝ := (Fintype.card (I → Bool) : ℝ) with hN
  have hNpos : 0 < N := by
    have hpos : 0 < Fintype.card (I → Bool) :=
      Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
    rw [hN]
    exact_mod_cast hpos
  set w : QState (I → Bool) := fun _ => 1 with hw
  have hwval : ∀ y : I → Bool, w y = 1 := fun y => by simp [hw]
  have hwnorm : ‖toEuclidean_fromVec w‖ ^ 2 = N := by
    rw [norm_toEuclidean_fromVec_sq]
    simp [hwval, hN]
  have hAw : ∀ x : I → Bool, (sensAdjacency f *ᵥ w) x = ((sensitivityAt f x : ℝ) : ℂ) := by
    intro x
    simp only [Matrix.mulVec, dotProduct]
    have h1 : (∑ y, sensAdjacency f x y * w y)
        = ∑ y, ((‖sensAdjacency f x y‖ : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hwval y, mul_one]
      simp only [sensAdjacency]
      split_ifs <;> simp
    rw [h1, ← Complex.ofReal_sum, rowSum_sensAdjacency]
  have hCS : (∑ x, (sensitivityAt f x : ℝ)) ^ 2
      ≤ N * ∑ x, (sensitivityAt f x : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (I → Bool))
      (fun _ : I → Bool => (1 : ℝ)) (fun x => (sensitivityAt f x : ℝ))
    simpa [hN, Finset.sum_const, nsmul_eq_mul] using h
  have hnorm2 : (∑ x, (sensitivityAt f x : ℝ) ^ 2)
      ≤ spectralSensitivity f ^ 2 * N := by
    have h1 : ‖toEuclidean_fromVec (sensAdjacency f *ᵥ w)‖ ^ 2
        = ∑ x, (sensitivityAt f x : ℝ) ^ 2 := by
      rw [norm_toEuclidean_fromVec_sq]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hAw x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h3 : ‖toEuclidean_fromVec (sensAdjacency f *ᵥ w)‖ ^ 2
        ≤ spectralSensitivity f ^ 2 * ‖toEuclidean_fromVec w‖ ^ 2 := by
      have h2 : (0 : ℝ) ≤ spectralSensitivity f * ‖toEuclidean_fromVec w‖ :=
        mul_nonneg (spectralSensitivity_nonneg f) (norm_nonneg _)
      have h4 := (sq_le_sq₀ (norm_nonneg _) h2).mpr
        (l2_norm_mulVec_fromVec_le (sensAdjacency f) w)
      rwa [mul_pow] at h4
    rwa [h1, hwnorm] at h3
  have hsum : (∑ x, (sensitivityAt f x : ℝ)) ≤ N * spectralSensitivity f := by
    have hnn : (0 : ℝ) ≤ ∑ x, (sensitivityAt f x : ℝ) :=
      Finset.sum_nonneg fun x _ => by positivity
    have hsq : (∑ x, (sensitivityAt f x : ℝ)) ^ 2
        ≤ (N * spectralSensitivity f) ^ 2 := by
      calc (∑ x, (sensitivityAt f x : ℝ)) ^ 2
          ≤ N * ∑ x, (sensitivityAt f x : ℝ) ^ 2 := hCS
        _ ≤ N * (spectralSensitivity f ^ 2 * N) :=
            mul_le_mul_of_nonneg_left hnorm2 (by positivity)
        _ = (N * spectralSensitivity f) ^ 2 := by ring
    exact (sq_le_sq₀ hnn (mul_nonneg (by positivity) (spectralSensitivity_nonneg f))).mp hsq
  rw [avgSensitivity]
  rw [div_le_iff₀ hNpos]
  calc (∑ x, (sensitivityAt f x : ℝ)) ≤ N * spectralSensitivity f := hsum
    _ = spectralSensitivity f * N := by ring

end Qatlib.Papers.ApproxDegree20.MainResults.Spectral
