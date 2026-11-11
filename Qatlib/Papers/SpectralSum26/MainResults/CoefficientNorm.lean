/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ℓ¹ coefficient norm of Chebyshev polynomials

Paper: Edenhofer–Hasegawa–Le Gall, arXiv:2509.20183v3, Lemma A.1.

For a real polynomial `p`, write `‖p‖₁` for the sum of the absolute values of
its coefficients.  The Chebyshev polynomials satisfy
`‖T_k‖₁ ≤ (1 + √2)^k`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SpectralSum26.MainResults.CoefficientNorm

open Polynomial
open scoped BigOperators

/-- The ℓ¹ norm of the coefficients of a real polynomial. -/
noncomputable def l1 (p : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

/-- The coefficient ℓ¹ norm is nonnegative. -/
theorem l1_nonneg (p : Polynomial ℝ) : 0 ≤ l1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Extending the coefficient range does not change the ℓ¹ norm. -/
theorem l1_eq_sum_range {p : Polynomial ℝ} {N : ℕ} (hN : p.natDegree ≤ N) :
    l1 p = ∑ i ∈ Finset.range (N + 1), |p.coeff i| := by
  unfold l1
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN)) ?_
  intro i hi hnot
  rw [Finset.mem_range] at hi hnot
  have hdeg : p.natDegree < i := by omega
  rw [coeff_eq_zero_of_natDegree_lt hdeg, abs_zero]

/-- Negation preserves the ℓ¹ norm. -/
theorem l1_neg (p : Polynomial ℝ) : l1 (-p) = l1 p := by
  simp [l1]

/-- The ℓ¹ norm of a sum is at most the sum of the ℓ¹ norms. -/
theorem l1_add_le (p q : Polynomial ℝ) : l1 (p + q) ≤ l1 p + l1 q := by
  let N := max p.natDegree q.natDegree
  have hp : p.natDegree ≤ N := le_max_left _ _
  have hq : q.natDegree ≤ N := le_max_right _ _
  have hpq : (p + q).natDegree ≤ N :=
    (natDegree_add_le p q).trans (max_le_max le_rfl le_rfl)
  rw [l1_eq_sum_range hpq, l1_eq_sum_range hp, l1_eq_sum_range hq]
  calc
    ∑ i ∈ Finset.range (N + 1), |(p + q).coeff i|
        = ∑ i ∈ Finset.range (N + 1), |p.coeff i + q.coeff i| := by
          simp only [coeff_add]
    _ ≤ ∑ i ∈ Finset.range (N + 1), (|p.coeff i| + |q.coeff i|) :=
          Finset.sum_le_sum fun i _ => abs_add_le _ _
    _ = ∑ i ∈ Finset.range (N + 1), |p.coeff i| +
          ∑ i ∈ Finset.range (N + 1), |q.coeff i| := by
          rw [Finset.sum_add_distrib]

/-- The ℓ¹ norm is subadditive under subtraction. -/
theorem l1_sub_le (p q : Polynomial ℝ) : l1 (p - q) ≤ l1 p + l1 q := by
  simpa [sub_eq_add_neg, l1_neg] using l1_add_le p (-q)

/-- Multiplying by `X` shifts the coefficient support and preserves the ℓ¹ norm. -/
theorem l1_X_mul (p : Polynomial ℝ) : l1 (X * p) = l1 p := by
  by_cases hp : p = 0
  · simp [hp, l1]
  · change (∑ i ∈ Finset.range ((X * p).natDegree + 1), |(X * p).coeff i|) = l1 p
    rw [natDegree_X_mul hp]
    rw [Finset.sum_range_succ']
    simp only [coeff_X_mul_zero, abs_zero, add_zero, coeff_X_mul]
    rfl

/-- Scaling a polynomial by a real constant scales its ℓ¹ norm by the absolute value. -/
theorem l1_smul (c : ℝ) (p : Polynomial ℝ) : l1 (c • p) = |c| * l1 p := by
  rw [l1_eq_sum_range (N := p.natDegree) (natDegree_smul_le c p)]
  rw [l1_eq_sum_range (N := p.natDegree) (le_refl p.natDegree)]
  simp_rw [coeff_smul, smul_eq_mul, abs_mul]
  rw [← Finset.mul_sum]

/-- The ℓ¹ norm of `2 * X * p` is at most twice the ℓ¹ norm of `p`. -/
theorem l1_two_X_mul_le (p : Polynomial ℝ) : l1 (2 * X * p) ≤ 2 * l1 p := by
  have h : (2 * X * p : Polynomial ℝ) = (2 : ℝ) • (X * p) := by
    rw [smul_eq_C_mul]
    norm_num [Polynomial.C_ofNat]
    ring
  rw [h, l1_smul, l1_X_mul]
  norm_num

/-- Lemma A.1: `‖T_k‖₁ ≤ (1 + √2)^k` for every `k`. -/
theorem chebyshev_l1_le (k : ℕ) :
    l1 (Chebyshev.T ℝ k) ≤ (1 + Real.sqrt 2) ^ k := by
  have hbase0 : l1 (Chebyshev.T ℝ 0) ≤ (1 + Real.sqrt 2) ^ 0 := by
    rw [Chebyshev.T_zero]
    have hone : l1 (1 : Polynomial ℝ) = 1 := by simp [l1]
    rw [hone]
    simp
  have hbase1 : l1 (Chebyshev.T ℝ 1) ≤ (1 + Real.sqrt 2) ^ 1 := by
    rw [Chebyshev.T_one]
    have hX : l1 (X : Polynomial ℝ) = 1 := by
      unfold l1
      rw [natDegree_X]
      norm_num [Finset.sum_range_succ, coeff_X]
    rw [hX]
    have hle : (1 : ℝ) ≤ 1 + Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
    simpa using hle
  refine Nat.twoStepInduction (motive := fun k =>
    l1 (Chebyshev.T ℝ k) ≤ (1 + Real.sqrt 2) ^ k) hbase0 hbase1 ?_ k
  · intro n ih ih1
    have harg : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    rw [harg, Chebyshev.T_add_two]
    have hstep : l1 ((2 : Polynomial ℝ) * X * Chebyshev.T ℝ (n + 1) -
        Chebyshev.T ℝ n) ≤ 2 * l1 (Chebyshev.T ℝ (n + 1)) + l1 (Chebyshev.T ℝ n) := by
      refine (l1_sub_le _ _).trans ?_
      have h2 : l1 ((2 : Polynomial ℝ) * X * Chebyshev.T ℝ (n + 1)) ≤
          2 * l1 (Chebyshev.T ℝ (n + 1)) := l1_two_X_mul_le _
      linarith
    refine hstep.trans ?_
    have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    have ih1' : l1 (Chebyshev.T ℝ ((n : ℤ) + 1)) ≤
        (1 + Real.sqrt 2) ^ (n + 1) := by
      rw [hcast]
      exact ih1
    have hmono : 2 * l1 (Chebyshev.T ℝ ((n : ℤ) + 1)) + l1 (Chebyshev.T ℝ (n : ℤ)) ≤
        2 * (1 + Real.sqrt 2) ^ (n + 1) + (1 + Real.sqrt 2) ^ n := by
      linarith [ih, ih1']
    refine hmono.trans ?_
    have hR : 2 * (1 + Real.sqrt 2) ^ (n + 1) + (1 + Real.sqrt 2) ^ n =
        (1 + Real.sqrt 2) ^ n * (3 + 2 * Real.sqrt 2) := by
      rw [pow_succ]
      ring
    rw [hR]
    have hfac : (3 + 2 * Real.sqrt 2 : ℝ) = (1 + Real.sqrt 2) ^ 2 := by
      rw [pow_two]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hfac, pow_add]

end Qatlib.Papers.SpectralSum26.MainResults.CoefficientNorm
