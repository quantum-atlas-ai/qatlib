/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel
import Qatlib.Papers.UnambigMeas25.MainResults.Combinatorics.CosetCount

set_option backward.isDefEq.respectTransparency false

/-!
# The average-number-of-parities setting — Section 4.3

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file states Theorem 6 (p. 24), Corollary 1 (p. 24), Proposition 4 (p. 24),
Proposition 20 (p. 24–25), Proposition 21 (p. 25), Corollary 3 (p. 26),
Propositions 23–25 (p. 26–27) and Corollaries 4–6 (p. 37–38).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.Average

open Matrix BigOperators
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-! ### The two average-setting upper bounds -/

/-- The dual solution `b_i = 2 |i|_H` of the Hamming solution (Proposition 23). -/
def hammingDual {n : ℕ} (i : F2 n) : ℝ := 2 * (hammingWeight i : ℝ)

/-- The dual solution `b_i = 2 |i + 1|_H` of the co-Hamming solution (Proposition 24). -/
def coHammingDual {n : ℕ} (i : F2 n) : ℝ := 2 * (hammingWeight (i + onesVec n) : ℝ)

/-- The spike dual solution of Proposition 25. -/
def spikeDual (n : ℕ) (i : F2 n) : ℝ :=
  if i = 0 then (2 : ℝ) ^ n + (n : ℝ) - 1 else (n : ℝ) - 1

/-- **Theorem 6** (arXiv:2510.07298v2, p. 24).  `ρ_Av(S) ≤ 2 ∑_i |i|_H |α̂_i|²`.

Source: Theorem 6, p. 24.  Proof: `b_i = 2|i|_H` is a feasible dual solution
(Proposition 20) and `σ^L_Av(S;b) = 2∑|i|_H|α̂_i|²`. -/
def theorem6 {n : ℕ} (S : SymFamily n) : Prop :=
  rho S CAv ≤ 2 * ∑ i : F2 n, (hammingWeight i : ℝ) * Complex.normSq (S.hat i)
  -- Paper: arXiv:2510.07298v2, Theorem 6, p. 24.
  -- Key steps: Proposition 20 shows `b_i = 2|i|_H` satisfies Constraint (3);
  -- then `rho S CAv ≤ sigmaL S CAv ≤ sigmaValue S b = 2 ∑ |i|_H |α̂_i|²`.
  -- Gap: the weak-duality step `rho ≤ sigmaL` and Proposition 20 are not proved.
  -- Suggested tactic: prove `sigmaL_le_sigmaValue` for feasible `b`, then
  -- `linarith` with `proposition20`.

/-- **Corollary 1** (arXiv:2510.07298v2, p. 24).  If `ε = ∑_{i ∉ B_d}|α̂_i|²`,
then `ρ_Av(S) ≤ 2d(1−ε) + 2nε`.

Source: Corollary 1, p. 24.  Proof: split the sum of Theorem 6 into `|i|_H ≤ d`
and `|i|_H > d`, bounding the second part by `n ε`. -/
def corollary1 {n : ℕ} (S : SymFamily n) (d : ℕ) : Prop :=
  rho S CAv ≤ 2 * (d : ℝ) * (1 - epsilonOut S d) + 2 * (n : ℝ) * epsilonOut S d
  -- Paper: arXiv:2510.07298v2, Corollary 1, p. 24.
  -- Key steps: on `B_d` use `|i|_H ≤ d` and mass `1 - ε`; on the complement use
  -- `|i|_H ≤ n` and mass `ε`; combine with Theorem 6.
  -- Gap: algebraic rearrangement of the two sums and the identity
  -- `∑_{i} |α̂_i|² = 1` (which follows from normalisation of `S.ψ`).
  -- Suggested tactic: `calc` with `Finset.sum_split`-style estimates and
  -- `nlinarith`.

/-- **Proposition 4** (arXiv:2510.07298v2, p. 24).  The spike bound
`ρ_Av(S) ≤ (2^n+n−1)|α̂_0|² + (n−1)∑_{i≠0}|α̂_i|²`. -/
def proposition4 {n : ℕ} (S : SymFamily n) : Prop :=
  rho S CAv ≤
      ((2 : ℝ) ^ n + (n : ℝ) - 1) * Complex.normSq (S.hat 0) +
        ((n : ℝ) - 1) *
          ∑ i ∈ Finset.univ.erase (0 : F2 n), Complex.normSq (S.hat i)
  -- Paper: arXiv:2510.07298v2, Proposition 4, p. 24.
  -- Key steps: the spike dual solution `b_0 = 2^n + n - 1`, `b_i = n - 1`
  -- satisfies Constraint (3) (Proposition 21); its objective is the right side.
  -- Gap: `rho ≤ sigmaL` and Proposition 21.
  -- Suggested tactic: transfer `proposition21` through `rho_le_sigmaL`.

/-! ### The two dual solutions (Propositions 20 and 21) -/

/-- **Proposition 20** (arXiv:2510.07298v2, p. 24–25).  For every dual coset
`D_H(s)` (encoded by its canonical generator `G`), `∑_{i ∈ D_H(s)} 2|i|_H ≥ k 2^k`.

The proof in `MainResults.Combinatorics.CosetCount.coset_weight_sum` avoids the
paper's explicit choice of independent columns: it double-counts the weight sum
by coordinates, uses the translation involution `i ↦ i + w` (`w_j = 1`, `w` in
the kernel) to balance each non-constant coordinate, and bounds the number of
constant-zero coordinates by `n - k` through `|ker G| = 2^k` and an injection
into the functions on the complement. -/
theorem proposition20 {n k : ℕ} (hk : k ≤ n) (G : Lam n (n - k))
    (s : Fin (n - k) → ZMod 2) :
    (k : ℝ) * (2 : ℝ) ^ k ≤
      cosetSum (fun i => 2 * (hammingWeight i : ℝ)) G s := by
  have h1 : cosetSum (fun i => 2 * (hammingWeight i : ℝ)) G s
      = (2 : ℝ) * ∑ i ∈ CosetCount.fibreSet G.1 s, (hammingWeight i : ℝ) := by
    simp only [cosetSum, CosetCount.fibreSet, ← Finset.sum_filter, ← Finset.mul_sum]
  have h2 := CosetCount.coset_weight_sum G s
  have hnk : n - (n - k) = k := by omega
  rw [hnk] at h2
  rw [h1]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
    positivity
  · have hk2 : ((2 : ℝ)) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
      rw [show k = (k - 1) + 1 from by omega, pow_succ,
        show (k - 1) + 1 - 1 = k - 1 from by omega]
      ring
    rw [hk2, ← Nat.cast_sum (CosetCount.fibreSet G.1 s) (fun i => hammingWeight i)]
    calc (k : ℝ) * (2 * (2 : ℝ) ^ (k - 1))
        = (2 : ℝ) * ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 : ℝ) * (((∑ i ∈ CosetCount.fibreSet G.1 s, hammingWeight i : ℕ)) : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h2) (by norm_num)
