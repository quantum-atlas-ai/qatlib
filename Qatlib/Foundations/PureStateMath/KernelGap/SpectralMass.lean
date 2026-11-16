/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Foundations.PureStateMath.KernelGap.RankOneGap
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-!
# Actual inverse-eigenvalue spectral mass from a nonzero kernel witness

For a rank-one perturbation and an orthonormal eigenfamily, construct the
inverse-weighted low-eigenvalue vector using the conjugated target overlaps.
The kernel-gap inequality and actual frame identities prove the inverse mass
bound. Zero eigenvalues have zero target overlap and cannot enter the sum.
The bound is stronger than the factor-four estimate in arXiv:0904.2759v1.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.KernelGap

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The actual target overlap with a frame column. -/
def colOverlap (t : I → ℂ) (W : Matrix I J ℂ) (i : J) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner t (fun r => W r i)

omit [DecidableEq I] in
/-- A frame eigen-equation gives the eigen-equation for every actual column. -/
theorem colAction (A : Matrix I I ℂ) (W : Matrix I J ℂ) (lam : J → ℝ)
    (heig : A * W = W * Matrix.diagonal (fun i => (lam i : ℂ))) (i : J) :
    A *ᵥ (fun r => W r i) = fun r => (lam i : ℂ) * W r i := by
  ext r
  change (A * W) r i = (lam i : ℂ) * W r i
  rw [heig, Matrix.mul_diagonal]
  exact mul_comm _ _

omit [DecidableEq I] [DecidableEq J] in
/-- Pairing an actual frame expansion distributes over its coefficients. -/
theorem innerFrame (t : I → ℂ) (W : Matrix I J ℂ) (a : J → ℂ) :
    Qatlib.Foundations.PureStateMath.Inner t (W *ᵥ a) = ∑ i, colOverlap t W i * a i := by
  simp only [colOverlap, Qatlib.Foundations.PureStateMath.Inner,
    Matrix.mulVec, dotProduct, Pi.star_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by ring

/-- Positive overlap budget excludes target overlap with a zero eigenvalue column. -/
theorem zeroColOverlap (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (t φ : I → ℂ) (δ : ℝ) (hδ : 0 < δ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (W : Matrix I J ℂ) (lam : J → ℝ)
    (heig : (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
      W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (i : J) (hi : lam i = 0) : colOverlap t W i = 0 := by
  have hb := gapBound X hX t φ δ hn hker hover (fun r => W r i)
  have he := colAction (X + Matrix.vecMulVec t (fun i => star (t i))) W lam heig i
  rw [he, hi] at hb
  have hb0 : δ * ‖colOverlap t W i‖ ^ 2 ≤ 0 := by
    simpa [sqNorm, colOverlap] using hb
  by_contra h
  have hp := mul_pos hδ (sq_pos_of_pos (norm_pos_iff.mpr h))
  linarith

/-- The exact weighted spectral mass in the source inverse-eigenvalue sum. -/
def invMass (t : I → ℂ) (W : Matrix I J ℂ) (lam : J → ℝ) (Λ : ℝ) : ℝ :=
  ∑ i, if lam i ≤ Λ ∧ colOverlap t W i ≠ 0 then ‖colOverlap t W i‖ ^ 2 / lam i else 0

/-- A nonzero kernel witness bounds the actual inverse-eigenvalue mass, with no zero denominators. -/
theorem invMassBound (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (t φ : I → ℂ) (δ : ℝ) (hδ : 0 < δ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (W : Matrix I J ℂ) (lam : J → ℝ) (hW : Wᴴ * W = 1)
    (heig : (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
      W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (hlam : ∀ i, 0 ≤ lam i) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    δ * invMass t W lam Λ ≤ Λ := by
  classical
  let flag (i : J) := lam i ≤ Λ ∧ colOverlap t W i ≠ 0
  have hpos (i : J) (hi : flag i) : 0 < lam i := by
    by_contra h
    have hz : lam i = 0 := le_antisymm (le_of_not_gt h) (hlam i)
    exact hi.2 (zeroColOverlap X hX t φ δ hδ hn hker hover W lam heig i hz)
  let a : J → ℂ := fun i => if flag i then star (colOverlap t W i) / (lam i : ℂ) else 0
  let ξ := W *ᵥ a
  let S := invMass t W lam Λ
  have hinner : Qatlib.Foundations.PureStateMath.Inner t ξ = (S : ℂ) := by
    rw [innerFrame]
    dsimp only [S, invMass]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : flag i
    · simp only [a, hi, ite_true]
      have hc : colOverlap t W i * star (colOverlap t W i) =
          ((‖colOverlap t W i‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [RCLike.star_def, Complex.normSq_eq_norm_sq] using
          Complex.mul_conj (colOverlap t W i)
      change colOverlap t W i * (star (colOverlap t W i) / (lam i : ℂ)) = _
      rw [← mul_div_assoc, hc]
      simp [hi.1, hi.2]
    · have hni : ¬(lam i ≤ Λ ∧ colOverlap t W i ≠ 0) := hi
      simp [a, hi, hni]
  have hact : (X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ =
      W *ᵥ (fun i => (lam i : ℂ) * a i) := by
    dsimp only [ξ]
    rw [Matrix.mulVec_mulVec, heig, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    exact Matrix.mulVec_diagonal _ _ _
  have hnorm : sqNorm ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ) ≤ Λ * S := by
    rw [hact, orthoSqNorm W hW]
    dsimp only [sqNorm, S, invMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : flag i
    · have hp := hpos i hi
      have hne : (lam i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
      have he : (lam i : ℂ) * a i = star (colOverlap t W i) := by
        simp only [a, hi, ite_true]
        field_simp
      rw [he, norm_star]
      have ht : ‖colOverlap t W i‖ ^ 2 ≤ Λ * (‖colOverlap t W i‖ ^ 2 / lam i) := by
        calc
          _ = lam i * (‖colOverlap t W i‖ ^ 2 / lam i) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hi.1 (div_nonneg (sq_nonneg _) hp.le)
      simpa [hi.1, hi.2] using ht
    · have hni : ¬(lam i ≤ Λ ∧ colOverlap t W i ≠ 0) := hi
      simp [a, hi, hni]
  have hS : 0 ≤ S := by
    dsimp only [S, invMass]
    apply Finset.sum_nonneg
    intro i _
    split_ifs with hi
    · exact div_nonneg (sq_nonneg _) (hpos i hi).le
    · exact le_rfl
  have hb := gapBound X hX t φ δ hn hker hover ξ
  rw [hinner] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  have hsq : δ * S ^ 2 ≤ Λ * S := hb.trans hnorm
  change δ * S ≤ Λ
  by_cases hz : S = 0
  · simpa only [hz, mul_zero] using hΛ
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    have hh : (δ * S) * S ≤ Λ * S := by nlinarith only [hsq]
    exact (mul_le_mul_iff_left₀ hp).mp hh

end Qatlib.Foundations.PureStateMath.KernelGap
