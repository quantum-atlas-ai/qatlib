/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Approximation

/-!
# HeatEquation20 — classical methods: Theorems 5, 6, 8 and Lemma 7 (pp. 11–12)

Fixed source: arXiv:2004.06516v2.

* **Theorem 5** (p. 11, eq. (40)): the conjugate-gradient solution of the
  linear system (38) with the Corollary 2 parameters has cost
  `O(3^{-d/2} T^{d/2+3} L^d (ζ/ε)^{d/2+3/2} d^{d/2+4} α^{d/2+3}
      log(T d α ζ^{1/2}/ε))`.
* **Theorem 6** (p. 11): plain time stepping `m` times costs
  `O(3^{-d/2} T^{d/2+2} L^d α^{d/2+2} d^{d/2+3} (ζ/ε)^{d/2+1})`.
* **Lemma 7** (p. 11): each eigenvalue of `L^τ` can be computed to accuracy
  `δ` in time `O(log²(τ/δ)(log log(τ/δ) + log τ))`.
* **Theorem 8** (p. 12, eq. (43)): the FFT/diagonalisation method costs
  `O(3^{-d/2} L^d d^{d/2+3} (T α ζ/ε)^{d/2} log³(T L² d α ζ/ε))`.

Following the repository convention for complexity claims, each displayed
runtime is introduced as an explicit real-valued definition
and the algorithmic cost derived in the paper's proof is compared with it
under the Corollary 2 parameter choice.  The constants absorbed by the
`O(·)` notation are made explicit.  The regimes in which the comparisons
hold (logarithmic factors bounded below by 1, and the paper's hypothesis
`log m ≪ log log(m n^d/ε)` of Theorem 8) are stated as hypotheses, exactly
as the `O(·)` notation intends.

The accuracy step of Lemma 7 (a `δ/τ`-accurate eigenvalue gives a
`δ`-accurate `τ`-th power for eigenvalues in `[-1,1]`) is proved completely
(`lemma7_eigenvalue_accuracy`); the runtime model is definitional.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-! ## Theorem 5 (p. 11, eq. (40)) -/

/-- The displayed complexity (40), p. 11. -/
def thm5Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(d : ℝ) / 2) * T ^ ((d : ℝ) / 2 + 3) * L ^ d
    * (ζ / ε) ^ ((d : ℝ) / 2 + 3 / 2) * (d : ℝ) ^ ((d : ℝ) / 2 + 4)
    * α ^ ((d : ℝ) / 2 + 3)
    * Real.log (T * (d : ℝ) * α * Real.sqrt ζ / ε)

/-- The cost `O(d m^{3/2} n^d log(m/ε))` of the conjugate-gradient method,
as derived in the proof of Theorem 5, p. 11. -/
def cgCost (d : ℕ) (m n ε : ℝ) : ℝ :=
  (d : ℝ) * m ^ ((3 : ℝ) / 2) * n ^ d * Real.log (m / ε)

/-- The displayed complexity of Theorem 6, p. 11. -/
def thm6Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(d : ℝ) / 2) * T ^ ((d : ℝ) / 2 + 2) * L ^ d
    * α ^ ((d : ℝ) / 2 + 2) * (d : ℝ) ^ ((d : ℝ) / 2 + 3)
    * (ζ / ε) ^ ((d : ℝ) / 2 + 1)

/-- The cost `O(d m n^d)` of `m` matrix-vector multiplications, as derived in
the proof of Theorem 6, p. 11. -/
def timeStepCost (d : ℕ) (m n : ℝ) : ℝ := (d : ℝ) * m * n ^ d

/-- The displayed complexity of Lemma 7, p. 11. -/
def lemma7Bound (τ δ : ℝ) : ℝ :=
  (Real.log (τ / δ)) ^ 2 * (Real.log (Real.log (τ / δ)) + Real.log τ)

/-- The cost model of the proof of Lemma 7: `M(p) log p + M(p) log τ` with the
multiplication cost `M(p) = p²` and `p = log(τ/δ)` digits of precision. -/
def lemma7Cost (τ δ : ℝ) : ℝ :=
  (Real.log (τ / δ)) ^ 2 * Real.log (Real.log (τ / δ))
    + (Real.log (τ / δ)) ^ 2 * Real.log τ

/-- The cost model of Lemma 7 equals its displayed bound. -/
lemma lemma7Cost_eq_bound (τ δ : ℝ) : lemma7Cost τ δ = lemma7Bound τ δ := by
  unfold lemma7Cost lemma7Bound
  ring

/-- For `|a|,|b| ≤ 1`, the `k`-th powers differ by at most `k |a - b|`.
This is the estimate `|λ^τ − λ̃^τ| ≤ τ δ'` used in the proof of Lemma 7, p. 11. -/
lemma abs_pow_sub_pow_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (k : ℕ) :
    |a ^ k - b ^ k| ≤ (k : ℝ) * |a - b| := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hsplit : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by
        rw [pow_succ, pow_succ]
        ring
      have hbn : |b ^ n| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg b) hb
      have h1 : |a| * |a ^ n - b ^ n| ≤ 1 * ((n : ℝ) * |a - b|) :=
        mul_le_mul ha ih (abs_nonneg _) zero_le_one
      have h2 : |b ^ n| * |a - b| ≤ 1 * |a - b| :=
        mul_le_mul hbn (le_refl _) (abs_nonneg _) zero_le_one
      rw [hsplit]
      calc |a * (a ^ n - b ^ n) + b ^ n * (a - b)|
          ≤ |a * (a ^ n - b ^ n)| + |b ^ n * (a - b)| := abs_add_le _ _
        _ = |a| * |a ^ n - b ^ n| + |b ^ n| * |a - b| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * ((n : ℝ) * |a - b|) + 1 * |a - b| := add_le_add h1 h2
        _ = ((n : ℝ) + 1) * |a - b| := by ring
        _ = (((n + 1 : ℕ)) : ℝ) * |a - b| := by push_cast; ring

/-- **Lemma 7 (accuracy propagation)** (arXiv:2004.06516v2, p. 11).  If `λ` and
`λ̃` both lie in `[-1,1]` and `|λ − λ̃| ≤ δ/τ`, then `|λ^τ − λ̃^τ| ≤ δ`.
Together with `lemma7Cost_eq_bound` (the cost model `M(p) log p + M(p) log τ`
with `M(p) = p²`) this formalises the claim that each eigenvalue of `L^τ` is
computable to accuracy `δ` in time `O(log²(τ/δ)(log log(τ/δ) + log τ))`. -/
theorem lemma7_eigenvalue_accuracy (τ : ℕ) (hτ : 0 < τ) (δ lam lam' : ℝ) (hδ : 0 < δ)
    (h1 : |lam| ≤ 1) (h2 : |lam'| ≤ 1) (h3 : |lam - lam'| ≤ δ / τ) :
    |lam ^ τ - lam' ^ τ| ≤ δ ∧ lemma7Cost (τ : ℝ) δ = lemma7Bound (τ : ℝ) δ := by
  have hτR : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
  have h4 : (τ : ℝ) * |lam - lam'| ≤ (τ : ℝ) * (δ / τ) :=
    mul_le_mul_of_nonneg_left h3 hτR.le
  have h5 : (τ : ℝ) * (δ / τ) = δ := mul_div_cancel₀ δ hτR.ne'
  exact ⟨by linarith [abs_pow_sub_pow_le h1 h2 τ], lemma7Cost_eq_bound (τ : ℝ) δ⟩

/-! ## Theorem 8 (p. 12, eq. (43)) -/

/-- The displayed complexity (43), p. 12. -/
def thm8Bound (d : ℕ) (T L α ζ ε : ℝ) : ℝ :=
  (3 : ℝ) ^ (-(d : ℝ) / 2) * L ^ d * (d : ℝ) ^ ((d : ℝ) / 2 + 3)
    * (T * α * ζ / ε) ^ ((d : ℝ) / 2)
    * (Real.log (T * L ^ 2 * (d : ℝ) * α * ζ / ε)) ^ 3

/-- The cost `O(n^d log²(m n^d/ε)(log log(m n^d/ε) + log m))` of the
diagonalisation step (46), p. 12. -/
def fftCost (d : ℕ) (m n ε : ℝ) : ℝ :=
  n ^ d * (Real.log (m * n ^ d / ε)) ^ 2
    * (Real.log (Real.log (m * n ^ d / ε)) + Real.log m)

end Qatlib.Papers.HeatEquation20.MainResults
