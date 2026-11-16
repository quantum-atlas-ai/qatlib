/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Finite-vector kernel and spectral gap bounds

This module proves the first inequality of Lemma 8.10 of arXiv:0904.2759v1
with the essential nonzero kernel witness made explicit. The legacy statement
omitted that condition and is refuted below on a one-dimensional space.
The source PSD specialization and original-contract counterexamples live in the paper module.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.KernelGap

/-- The squared Euclidean norm used in the source rank-one perturbation inequality. -/
def sqNorm {I : Type*} [Fintype I] (v : I → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The squared overlap is bounded by the product of squared Euclidean norms. -/
theorem innerSqBound (u v : I → ℂ) :
    ‖Qatlib.Foundations.PureStateMath.Inner u v‖ ^ 2 ≤ sqNorm u * sqNorm v := by
  have htri : ‖Qatlib.Foundations.PureStateMath.Inner u v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    rw [inner_apply]
    calc
      _ ≤ ∑ i, ‖(starRingEnd ℂ) (u i) * v i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, RCLike.norm_conj]
  have hnon : 0 ≤ ∑ i, ‖u i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖u i‖) (fun i => ‖v i‖)
  have htriSq : ‖Qatlib.Foundations.PureStateMath.Inner u v‖ ^ 2 ≤ (∑ i, ‖u i‖ * ‖v i‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hnon).2 htri
  exact htriSq.trans hsq

omit [DecidableEq I] in
/-- A nonzero amplitude vector has strictly positive squared Euclidean norm. -/
theorem sqNormPos (u : I → ℂ) (hu : u ≠ 0) : 0 < sqNorm u := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  have hp : 0 < ‖u i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
  exact hp.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg ‖u j‖)
    (Finset.mem_univ i))

omit [DecidableEq I] in
/-- The rank-one matrix `t tᴴ` acts by the actual inner product with `t`. -/
theorem rankOneAct (t v : I → ℂ) :
    Matrix.vecMulVec t (fun i => star (t i)) *ᵥ v = Qatlib.Foundations.PureStateMath.Inner t v • t := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Qatlib.Foundations.PureStateMath.Inner, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Pairing a rank-one perturbation with a kernel vector removes the Hermitian part. -/
theorem kernelPair (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (t φ ξ : I → ℂ) (hker : X *ᵥ φ = 0) :
    Qatlib.Foundations.PureStateMath.Inner φ ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ) =
      Qatlib.Foundations.PureStateMath.Inner φ t * Qatlib.Foundations.PureStateMath.Inner t ξ := by
  have hmove : Qatlib.Foundations.PureStateMath.Inner φ (X *ᵥ ξ) = 0 := by
    have h := inner_mulVec_left_rect X φ ξ
    rw [hX.eq, hker] at h
    simpa [Qatlib.Foundations.PureStateMath.Inner] using h.symm
  rw [Matrix.add_mulVec, rankOneAct]
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hmove ⊢
  rw [hmove, zero_add, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring

/-- A nonzero Hermitian kernel witness proves the first inequality of Lemma 8.10. -/
theorem gapBound (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (t φ : I → ℂ) (δ : ℝ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2) (ξ : I → ℂ) :
    δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤
      sqNorm ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ) := by
  let y := (X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ
  have hpair := kernelPair X hX t φ ξ hker
  have hnorm : ‖Qatlib.Foundations.PureStateMath.Inner φ t‖ = ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ := by
    have hconj : Qatlib.Foundations.PureStateMath.Inner φ t = star (Qatlib.Foundations.PureStateMath.Inner t φ) := by
      simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, star_sum, star_mul, star_star]
    rw [hconj, norm_star]
  have hcs := innerSqBound φ y
  have heq : ‖Qatlib.Foundations.PureStateMath.Inner φ y‖ ^ 2 = ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2 * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 := by
    rw [hpair, norm_mul, mul_pow, hnorm]
  have hm := mul_le_mul_of_nonneg_right hover (sq_nonneg ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖)
  have hp := sqNormPos φ hn
  have hall : sqNorm φ * (δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2) ≤ sqNorm φ * sqNorm y := by
    rw [heq] at hcs
    nlinarith [hm]
  change δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤ sqNorm y
  exact (mul_le_mul_iff_right₀ hp).mp hall


/-- A matrix with orthonormal columns preserves the actual squared vector norm. -/
theorem orthoSqNorm {J : Type*} [Fintype J] [DecidableEq J]
    (W : Matrix I J ℂ) (hW : Wᴴ * W = 1) (a : J → ℂ) :
    sqNorm (W *ᵥ a) = sqNorm a := by
  have h : (sqNorm (W *ᵥ a) : ℂ) = (sqNorm a : ℂ) := by
    calc
      _ = Qatlib.Foundations.PureStateMath.Inner (W *ᵥ a) (W *ᵥ a) := by
        rw [inner_self, ← Complex.ofReal_sum]; rfl
      _ = Qatlib.Foundations.PureStateMath.Inner a a := by
        rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
      _ = _ := by rw [inner_self, ← Complex.ofReal_sum]; rfl
  exact_mod_cast h

/-- A vector supported on nonnegative eigenvalues at most a cutoff obeys the norm bound. -/
theorem lowEigBound {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix I I ℂ) (W : Matrix I J ℂ) (lam : J → ℝ)
    (hW : Wᴴ * W = 1)
    (heig : A * W = W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (hlam : ∀ i, 0 ≤ lam i) (κ : ℝ)
    (a : J → ℂ) (hsupp : ∀ i, κ < lam i → a i = 0) :
    sqNorm (A *ᵥ (W *ᵥ a)) ≤ κ ^ 2 * sqNorm (W *ᵥ a) := by
  have hact : A *ᵥ (W *ᵥ a) = W *ᵥ (fun i => (lam i : ℂ) * a i) := by
    rw [Matrix.mulVec_mulVec, heig, ← Matrix.mulVec_mulVec]
    congr 1
    ext i
    exact Matrix.mulVec_diagonal _ _ _
  rw [hact, orthoSqNorm W hW, orthoSqNorm W hW]
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : κ < lam i
  · simp [hsupp i hi]
  · have hle : lam i ≤ κ := le_of_not_gt hi
    have hs : (lam i) ^ 2 ≤ κ ^ 2 := (sq_le_sq₀ (hlam i) ((hlam i).trans hle)).2 hle
    simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      mul_le_mul_of_nonneg_right hs (sq_nonneg ‖a i‖)

end Qatlib.Foundations.PureStateMath.KernelGap
