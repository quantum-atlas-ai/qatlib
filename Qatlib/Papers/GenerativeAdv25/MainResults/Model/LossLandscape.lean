/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# GenerativeAdv25 — the least-squares Pauli-coefficient loss: strong convexity and
global optimality of local minima

Fixed paper version: arXiv:2509.09033v1, Appendix G.2.a, Eqs. (S.2.36)–(S.2.37),
Theorem 10 and Corollary 1.

The learning algorithm estimates Pauli coefficients `α` by least squares against `N`
empirical data vectors `d_ℓ` (Eq. (S.2.37)); the loss is

`ℒ(α) = (1/N) ∑_ℓ ‖α − d_ℓ‖²`.

* `lsLoss d α` — the loss;
* `meanData d` — the sample average `(1/N) ∑_ℓ d_ℓ`, the unique minimizer `α*`;
* `lsLoss_eq_min` — Eq. (S.2.36): `ℒ(α) = ‖α − α*‖² + ℒ(α*)`, i.e. the loss is a
  shifted squared norm plus a constant;
* `StronglyConvex2` — 2-strong convexity along segments (the Hessian `2I` statement);
* `IsLocalMin`, `IsCriticalPoint`, `IsUniqueGlobalMin` — the notions used in Corollary 1;
* `theorem10_strong_convexity` — Theorem 10;
* `corollary1_global_min`, `corollary1_local_min_global`, `corollary1_critical_point` —
  the three assertions of Corollary 1.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GenerativeAdv25.MainResults

/-- A real parameter vector with `M` coordinates. -/
abbrev ParamVec (M : ℕ) := Fin M → ℝ

/-- The Euclidean inner product. -/
def dotProd {M : ℕ} (u v : ParamVec M) : ℝ := ∑ i, u i * v i

/-- The squared Euclidean norm. -/
def sqNorm {M : ℕ} (v : ParamVec M) : ℝ := ∑ i, v i ^ 2

/-- The squared norm is nonnegative. -/
theorem sqNorm_nonneg {M : ℕ} (v : ParamVec M) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-- The squared norm vanishes only on the zero vector. -/
theorem sqNorm_eq_zero {M : ℕ} {v : ParamVec M} (h : sqNorm v = 0) : v = 0 := by
  funext i
  have hle : v i ^ 2 ≤ sqNorm v := by
    rw [sqNorm]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [h] at hle
  have h2 : v i ^ 2 = 0 := le_antisymm hle (sq_nonneg (v i))
  have h3 : v i = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
  simpa using h3

/-- The squared norm is strictly positive off the zero vector. -/
theorem sqNorm_pos {M : ℕ} {v : ParamVec M} (h : v ≠ 0) : 0 < sqNorm v :=
  lt_of_le_of_ne (sqNorm_nonneg v) (fun h0 => h (sqNorm_eq_zero h0.symm))

/-- The parallelogram expansion of the squared norm. -/
theorem sqNorm_add {M : ℕ} (u v : ParamVec M) :
    sqNorm (fun i => u i + v i) = sqNorm u + 2 * dotProd u v + sqNorm v := by
  have key : ∀ i : Fin M, (u i + v i) ^ 2 = u i ^ 2 + 2 * (u i * v i) + v i ^ 2 :=
    fun i => by ring
  simp only [sqNorm, dotProd, key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The squared norm of a scalar multiple. -/
theorem sqNorm_smul {M : ℕ} (c : ℝ) (v : ParamVec M) :
    sqNorm (fun i => c * v i) = c ^ 2 * sqNorm v := by
  have key : ∀ i : Fin M, (c * v i) ^ 2 = c ^ 2 * v i ^ 2 := fun i => by ring
  simp only [sqNorm, key, ← Finset.mul_sum]

/-- **The segment identity for the squared norm:** along the segment
`t ↦ t u + (1-t) v` the squared norm is the affine interpolation minus the contraction
term `t(1-t)‖u-v‖²`.  This is the equality underlying strong convexity with modulus `2`. -/
theorem sqNorm_affine {M : ℕ} (u v : ParamVec M) (t : ℝ) :
    sqNorm (fun i => t * u i + (1 - t) * v i)
      = t * sqNorm u + (1 - t) * sqNorm v
        - t * (1 - t) * sqNorm (fun i => u i - v i) := by
  have key : ∀ i : Fin M,
      (t * u i + (1 - t) * v i) ^ 2
        = t * u i ^ 2 + (1 - t) * v i ^ 2 - t * (1 - t) * (u i - v i) ^ 2 :=
    fun i => by ring
  simp only [sqNorm, key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The sample average `(1/N) ∑_ℓ d_ℓ` (Eq. (S.2.37)). -/
def meanData {M N : ℕ} (d : Fin N → ParamVec M) : ParamVec M :=
  fun i => (N : ℝ)⁻¹ * ∑ ℓ, d ℓ i

/-- The least-squares loss `ℒ(α) = (1/N) ∑_ℓ ‖α − d_ℓ‖²` (Eq. (S.2.36), left side). -/
def lsLoss {M N : ℕ} (d : Fin N → ParamVec M) (α : ParamVec M) : ℝ :=
  (N : ℝ)⁻¹ * ∑ ℓ, sqNorm (fun i => α i - d ℓ i)

/-- The constant term of the loss decomposition, `ℒ(α*)` of Eq. (S.2.36). -/
def lsConst {M N : ℕ} (d : Fin N → ParamVec M) : ℝ :=
  (N : ℝ)⁻¹ * ∑ ℓ, sqNorm (fun i => meanData d i - d ℓ i)

/-- The sample deviations from the mean average to zero, coordinatewise. -/
theorem sum_meanData_sub {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0)
    (i : Fin M) : (∑ ℓ, (meanData d i - d ℓ i)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp only [meanData]
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul, sub_self]

/-- The inner product distributes over a sum in its second argument. -/
theorem dotProd_sum_right {M : ℕ} {ι : Type*} [Fintype ι] (u : ParamVec M)
    (w : ι → ParamVec M) :
    dotProd u (fun i => ∑ ℓ, w ℓ i) = ∑ ℓ, dotProd u (w ℓ) := by
  simp only [dotProd, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The inner product against the zero vector vanishes. -/
theorem dotProd_zero_right {M : ℕ} (u : ParamVec M) : dotProd u (0 : ParamVec M) = 0 := by
  simp [dotProd]

/-- **Eq. (S.2.36):** the loss decomposes as `ℒ(α) = ‖α − α*‖² + ℒ(α*)`, where `α*` is the
sample mean (`meanData`).  The cross term cancels because the sample deviations from the
mean average to zero. -/
theorem lsLoss_eq_min {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0)
    (α : ParamVec M) :
    lsLoss d α = sqNorm (fun i => α i - meanData d i) + lsLoss d (meanData d) := by
  have hterm : ∀ ℓ : Fin N, sqNorm (fun i => α i - d ℓ i)
      = sqNorm (fun i => α i - meanData d i)
        + 2 * dotProd (fun i => α i - meanData d i) (fun i => meanData d i - d ℓ i)
        + sqNorm (fun i => meanData d i - d ℓ i) := by
    intro ℓ
    have h : (fun i => α i - d ℓ i)
        = (fun i => (α i - meanData d i) + (meanData d i - d ℓ i)) := by
      funext i; ring
    rw [h, sqNorm_add]
  simp only [lsLoss, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : (∑ ℓ, dotProd (fun i => α i - meanData d i)
      (fun i => meanData d i - d ℓ i)) = 0 := by
    rw [← dotProd_sum_right]
    have hz : (fun i => ∑ ℓ, (meanData d i - d ℓ i)) = (0 : ParamVec M) := by
      funext i
      exact sum_meanData_sub d hN i
    rw [hz, dotProd_zero_right]
  have hQ : (∑ _ℓ : Fin N, sqNorm (fun i => α i - meanData d i))
      = (N : ℝ) * sqNorm (fun i => α i - meanData d i) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hQ, hcross]
  have hmain : (N : ℝ)⁻¹ * ((N : ℝ) * sqNorm (fun i => α i - meanData d i) + 2 * 0
        + ∑ ℓ, sqNorm (fun i => meanData d i - d ℓ i))
      = sqNorm (fun i => α i - meanData d i)
        + (N : ℝ)⁻¹ * ∑ ℓ, sqNorm (fun i => meanData d i - d ℓ i) := by
    field_simp
    ring
  exact hmain

/-- The loss at the sample mean is the constant `lsConst`. -/
theorem lsLoss_mean {M N : ℕ} (d : Fin N → ParamVec M) (_hN : (N : ℝ) ≠ 0) :
    lsLoss d (meanData d) = lsConst d := rfl

/-- Along the ray `x + t(α* − x)` the loss decays as `(1-t)²` times the offset from the
minimum: the explicit descent direction used in Corollary 1. -/
theorem lsLoss_ray {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0)
    (x : ParamVec M) (t : ℝ) :
    lsLoss d (fun i => x i + t * (meanData d i - x i))
      = (1 - t) ^ 2 * sqNorm (fun i => x i - meanData d i) + lsLoss d (meanData d) := by
  rw [lsLoss_eq_min d hN]
  congr 1
  have h : (fun i => (x i + t * (meanData d i - x i)) - meanData d i)
      = (fun i => (1 - t) * (x i - meanData d i)) := by
    funext i; ring
  rw [h, sqNorm_smul]

/-- `2`-strong convexity along segments: `f(tx + (1-t)y) ≤ t f(x) + (1-t) f(y) -
t(1-t)‖x - y‖²`.  Equivalently the Hessian dominates `2I`, i.e. the smallest eigenvalue is
at least `2` (Theorem 10). -/
def StronglyConvex2 {M : ℕ} (f : ParamVec M → ℝ) : Prop :=
  ∀ x y : ParamVec M, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (fun i => t * x i + (1 - t) * y i)
      ≤ t * f x + (1 - t) * f y - t * (1 - t) * sqNorm (fun i => x i - y i)

/-- **Theorem 10 (Strong convexity):** the least-squares loss `ℒ(α)` is `2`-strongly convex
in the parameter space, since `ℒ(α) = ‖α − α*‖² + const` and `‖·‖²` has Hessian `2I`. -/
theorem theorem10_strong_convexity {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0) :
    StronglyConvex2 (lsLoss d) := by
  intro x y t _ht0 _ht1
  rw [show lsLoss d (fun i => t * x i + (1 - t) * y i)
        = sqNorm (fun i => (t * x i + (1 - t) * y i) - meanData d i)
          + lsLoss d (meanData d) from lsLoss_eq_min d hN _]
  rw [lsLoss_eq_min d hN x, lsLoss_eq_min d hN y]
  have hfun : (fun i => (t * x i + (1 - t) * y i) - meanData d i)
      = (fun i => t * (x i - meanData d i) + (1 - t) * (y i - meanData d i)) := by
    funext i; ring
  rw [hfun, sqNorm_affine]
  rw [show (fun i => (x i - meanData d i) - (y i - meanData d i))
      = (fun i => x i - y i) by funext i; ring]
  have ht : t + (1 - t) = 1 := by ring
  nlinarith

/-- A unique global minimizer. -/
def IsUniqueGlobalMin {M : ℕ} (f : ParamVec M → ℝ) (x : ParamVec M) : Prop :=
  (∀ y, f x ≤ f y) ∧ (∀ y, (∀ z, f y ≤ f z) → y = x)

/-- A local minimum in the Euclidean ball of some radius. -/
def IsLocalMin {M : ℕ} (f : ParamVec M → ℝ) (x : ParamVec M) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ y, sqNorm (fun i => y i - x i) < ε → f x ≤ f y

/-- A critical point: there is no first-order descent direction. -/
def IsCriticalPoint {M : ℕ} (f : ParamVec M → ℝ) (x : ParamVec M) : Prop :=
  ∀ v : ParamVec M, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → f x ≤ f (fun i => x i + t * v i)

/-- `α* = meanData d` is a global minimizer. -/
theorem corollary1_global_min {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0) :
    IsUniqueGlobalMin (lsLoss d) (meanData d) := by
  constructor
  · intro y
    rw [lsLoss_eq_min d hN y]
    have := sqNorm_nonneg (fun i => y i - meanData d i)
    linarith
  · intro y hy
    have h1 : sqNorm (fun i => y i - meanData d i) ≤ 0 := by
      have h2 := hy (meanData d)
      rw [lsLoss_eq_min d hN y] at h2
      linarith
    have h3 : sqNorm (fun i => y i - meanData d i) = 0 :=
      le_antisymm h1 (sqNorm_nonneg _)
    funext i
    have h4 := congrFun (sqNorm_eq_zero h3) i
    simpa using sub_eq_zero.mp h4

/-- **Corollary 1 (1):** every local minimum of `ℒ` is global. -/
theorem corollary1_local_min_global {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0) :
    ∀ x, IsLocalMin (lsLoss d) x → ∀ y, lsLoss d x ≤ lsLoss d y := by
  intro x hx y
  have hxμ : x = meanData d := by
    by_contra hne
    obtain ⟨ε, hε0, hε⟩ := hx
    have hQpos : 0 < sqNorm (fun i => x i - meanData d i) :=
      sqNorm_pos (fun h0 => hne (by funext i; exact sub_eq_zero.mp (congrFun h0 i)))
    have hQsym : sqNorm (fun i => meanData d i - x i) = sqNorm (fun i => x i - meanData d i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    obtain ⟨t, ht0, ht1, ht2⟩ :
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t ^ 2 * sqNorm (fun i => meanData d i - x i) < ε := by
      obtain ⟨c, hc0, hcQ⟩ := exists_pos_mul_lt hε0 (sqNorm (fun i => x i - meanData d i))
      refine ⟨min c (1 / 2), ?_, ?_, ?_⟩
      · exact lt_min hc0 (by norm_num)
      · calc min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
          _ < 1 := by norm_num
      · have h1 : min c (1 / 2) ≤ c := min_le_left _ _
        have h2 : min c (1 / 2) ≤ 1 / 2 := min_le_right _ _
        have h3 : 0 < min c (1 / 2) := lt_min hc0 (by norm_num)
        have hQnn : 0 ≤ sqNorm (fun i => x i - meanData d i) := le_of_lt hQpos
        have hsq : min c (1 / 2) ^ 2 ≤ min c (1 / 2) := by nlinarith
        have hmul : min c (1 / 2) ^ 2 * sqNorm (fun i => x i - meanData d i)
            ≤ c * sqNorm (fun i => x i - meanData d i) := by nlinarith
        rw [hQsym]
        nlinarith [hmul, hcQ]
    have ht2lt : (1 - t) ^ 2 < 1 := by nlinarith [ht0, ht1]
    have hlt : lsLoss d (fun i => x i + t * (meanData d i - x i)) < lsLoss d x := by
      rw [lsLoss_ray d hN x t, lsLoss_eq_min d hN x]
      nlinarith [hQpos, ht2lt]
    have hball : sqNorm (fun i => (x i + t * (meanData d i - x i)) - x i) < ε := by
      have heq : (fun i => (x i + t * (meanData d i - x i)) - x i)
          = (fun i => t * (meanData d i - x i)) := by funext i; ring
      rw [heq, sqNorm_smul]
      exact ht2
    have hle := hε (fun i => x i + t * (meanData d i - x i)) hball
    linarith
  rw [hxμ]
  exact (corollary1_global_min d hN).1 y

/-- **Corollary 1 (2):** every critical point of `ℒ` is the unique global minimizer `α*`. -/
theorem corollary1_critical_point {M N : ℕ} (d : Fin N → ParamVec M) (hN : (N : ℝ) ≠ 0) :
    ∀ x, IsCriticalPoint (lsLoss d) x → x = meanData d := by
  intro x hx
  by_contra hne
  have hQpos : 0 < sqNorm (fun i => x i - meanData d i) :=
    sqNorm_pos (fun h0 => hne (by funext i; exact sub_eq_zero.mp (congrFun h0 i)))
  obtain ⟨ε, hε0, hε⟩ := hx (fun i => meanData d i - x i)
  obtain ⟨t, ht0, htε, ht1⟩ : ∃ t : ℝ, 0 < t ∧ t < ε ∧ t < 1 := by
    refine ⟨min (ε / 2) (1 / 2), ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by norm_num)
    · calc min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    · calc min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
        _ < 1 := by norm_num
  have ht2lt : (1 - t) ^ 2 < 1 := by nlinarith [ht0, ht1]
  have h1 : lsLoss d x ≤ lsLoss d (fun i => x i + t * (meanData d i - x i)) := hε t ht0 htε
  have h2 : lsLoss d (fun i => x i + t * (meanData d i - x i)) < lsLoss d x := by
    rw [lsLoss_ray d hN x t, lsLoss_eq_min d hN x]
    nlinarith [hQpos, ht2lt]
  linarith

end Qatlib.Papers.GenerativeAdv25.MainResults
