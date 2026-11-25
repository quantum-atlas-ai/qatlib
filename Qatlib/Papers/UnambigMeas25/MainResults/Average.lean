/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel
public import Qatlib.Papers.UnambigMeas25.MainResults.Combinatorics.CosetCount

@[expose] public section

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

end Qatlib.Papers.UnambigMeas25.MainResults.Average

section

/-!
## Feasibility of the spike dual solution

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025), Proposition 21, p. 25.

The spike dual solution of the average setting is `b_0 = 2^n + n - 1` and
`b_i = n - 1` for `i ≠ 0`. This module proves Proposition 21, that is, that it
satisfies the dual constraint (3) of Section 4.1 for the average score `CAv`:
`spikeDual_feasible_CAv : DualFeasible CAv (spikeDual n)`.

The only counting input is `Combinatorics.CosetCount.card_fibreSet`, which gives
`2^k` elements in every dual coset of a full-rank parity check `G ∈ Λ_{n-k}`.
Splitting the coset sum into the `i ≠ 0` part, of total mass `(n-1) 2^k`, and the
extra mass `2^n` at `i = 0`, which is present only when the coset is the kernel
(`s = 0`), reduces constraint (3) to `k ≤ n - 1` on a nonzero coset and to
`2^k ≤ 2^n` on the kernel.

Boundary: this is the feasibility half of Proposition 21 only. The resulting
spike bound of Proposition 4 additionally requires weak duality in the form
`ρ ≤ σ^L`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults

open Matrix BigOperators
open Qatlib.Papers.UnambigMeas25.MainResults
open Qatlib.Papers.UnambigMeas25.MainResults.Average
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-! ### The spike solution as a constant plus an origin mass -/

/-- The spike dual solution is the constant `n - 1` plus the extra mass `2^n`
carried by the origin. -/
lemma spikeDual_eq_const_add_indicator (n : ℕ) (i : F2 n) :
    spikeDual n i = ((n : ℝ) - 1) + (if i = 0 then (2 : ℝ) ^ n else 0) := by
  by_cases hi : i = 0
  · simp only [spikeDual, hi, ite_true]
    ring
  · simp only [spikeDual, hi, ite_false]
    ring

/-- The coset sum of the spike solution: every dual coset contributes
`(n - 1) 2^k`, and the kernel coset additionally contributes the origin mass
`2^n`. -/
lemma cosetSum_spikeDual {n k : ℕ} (G : Lam n (n - k))
    (s : Fin (n - k) → ZMod 2) :
    cosetSum (spikeDual n) G s =
      ((n : ℝ) - 1) * ((CosetCount.fibreSet G.1 s).card : ℝ) +
        (2 : ℝ) ^ n * (if s = 0 then 1 else 0) := by
  have hsum : cosetSum (spikeDual n) G s
      = ∑ i ∈ CosetCount.fibreSet G.1 s, spikeDual n i := by
    simp only [cosetSum, CosetCount.fibreSet, ← Finset.sum_filter]
  rw [hsum, Finset.sum_congr rfl (fun i _ => spikeDual_eq_const_add_indicator n i),
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have horigin : (∑ i ∈ CosetCount.fibreSet G.1 s, (if i = 0 then (2 : ℝ) ^ n else 0))
      = (2 : ℝ) ^ n * (if s = 0 then 1 else 0) := by
    rw [Finset.sum_ite_eq' (CosetCount.fibreSet G.1 s) (0 : F2 n)
      (fun _ => (2 : ℝ) ^ n)]
    have hmem : (0 : F2 n) ∈ CosetCount.fibreSet G.1 s ↔ s = 0 := by
      rw [CosetCount.mem_fibreSet]
      have hzero : matVec G.1 (0 : F2 n) = 0 := by
        simp [matVec]
      rw [hzero]
      exact eq_comm
    have hmem' : (if (0 : F2 n) ∈ CosetCount.fibreSet G.1 s then (2 : ℝ) ^ n else 0)
        = if s = 0 then (2 : ℝ) ^ n else 0 := by
      by_cases hs : s = 0
      · rw [ite_eq_left (hmem.mpr hs), ite_eq_left hs]
      · rw [ite_eq_right (fun hc => hs (hmem.mp hc)), ite_eq_right hs]
    rw [hmem']
    by_cases hs : s = 0 <;> simp [hs]
  rw [horigin]
  ring

/-! ### Proposition 21 -/

/-- **Proposition 21** (arXiv:2510.07298v2, p. 25).  The spike dual solution
`b_0 = 2^n + n - 1`, `b_i = n - 1` (`i ≠ 0`) is a feasible solution of the dual
program of the average setting, i.e. it satisfies constraint (3) of Section 4.1
with respect to `CAv`. -/
theorem spikeDual_feasible_CAv (n : ℕ) : DualFeasible CAv (spikeDual n) := by
  refine ⟨fun i => ?_, fun k hk G s => ?_⟩
  · rw [spikeDual_eq_const_add_indicator]
    split_ifs with hi
    · have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · have hn : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with hzero | hpos
        · exfalso
          apply hi
          subst hzero
          exact Subsingleton.elim i 0
        · exact hpos
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
  · have hcos := cosetSum_spikeDual (n := n) (k := k) G s
    have hcard : (CosetCount.fibreSet G.1 s).card = 2 ^ k := by
      have h := CosetCount.card_fibreSet (n := n) (m := n - k) G s
      have hnk : n - (n - k) = k := by omega
      rw [hnk] at h
      exact h
    have hC : CAv k = (k : ℝ) := rfl
    rw [hC, hcos, hcard]
    have hpowcast : (((2 : ℕ) ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hpowcast]
    split_ifs with hs
    · have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hk
      have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hstep : (k : ℝ) * (2 : ℝ) ^ k ≤ (n : ℝ) * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hkn (le_of_lt h2k)
      nlinarith [hstep, hpow, h2k]
    · have hnk : n - k ≠ 0 := by
        rintro h0
        apply hs
        funext r
        exact absurd r.2 (by omega)
      have hn1 : 1 ≤ n := by omega
      have hk1 : k ≤ n - 1 := by omega
      have hk1' : (k : ℝ) ≤ (n : ℝ) - 1 := by
        have hcast : (k : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hk1
        rwa [Nat.cast_sub hn1, Nat.cast_one] at hcast
      have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hstep : (k : ℝ) * (2 : ℝ) ^ k ≤ ((n : ℝ) - 1) * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hk1' (le_of_lt h2k)
      nlinarith [hstep]

end Qatlib.Papers.UnambigMeas25.MainResults

end
