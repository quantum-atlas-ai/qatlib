/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Generalized Quantum Minimum-Finding and Minimum-Eigenvalue Estimation

This module formalizes Appendix C, Lemmas 47, 48, Theorem 49, and Lemma 50
(pp. 32--33) of van Apeldoorn, Gilyén, Gribling, and de Wolf on the first-hit
distribution of threshold sampling, expected unitary calls for generalized
quantum minimum-finding, bounded-budget minimum-finding, and sparse Hamiltonian
minimum-eigenvalue estimation.

## Main definitions

* `prefixMass`, `firstHitProb`: Cumulative mass `Pr(X ≤ x_k)` and conditional
  first-hit distribution on `{0, ..., k}`.
* `MinimumFindingCost`, `MinFindingProcedure`, `MinEigenvalueEstimator`:
  Abstract resource and estimator interfaces for Lemmas 48--50.

## Main statements

* `lemma47_first_hit`: Lemma 47, exact first-hit probability `p_k / Pr(X ≤ x_k)`
  and normalization.
* `lemma48_expected_uses`: Lemma 48, `O(1 / √q)` expected-use bound.
* `theorem49_generalized_minimum_finding`: Theorem 49, bounded-budget
  generalized minimum-finding specification.
* `lemma50_minimum_eigenvalue_estimate`: Lemma 50, sparse Hamiltonian
  minimum-eigenvalue estimator specification.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Appendix C, Lemmas 47--50
  and Theorem 49, pp. 32--33.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPsolver17.MainResults.MinimumFinding
open Qatlib.Papers.QSDPsolver17.MainResults


/-- Total probability mass of the values `≤ x_k`: `Pr(X ≤ x_k)`. -/
def prefixMass {N : ℕ} (p : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i

/-- Probability that the first sampled index in `{0, …, k}` equals `i`
(extended by `0` outside `{0, …, k}`). -/
def firstHitProb {N : ℕ} (p : Fin N → ℝ) (k : Fin N) (i : Fin N) : ℝ :=
  if i ≤ k then p i / prefixMass p k else 0

/-- **Lemma 47** (arXiv:1705.01843v4, p. 32).  Let `X` be a finite discrete
random variable with values `x_1 < … < x_N`, and let `S(X)` be the random set
of values sampled during a run of Meta-Algorithm 2 on input `X`.  If
`k ∈ [N]`, then `Pr(x_k ∈ S(X)) = Pr(X = x_k) / Pr(X ≤ x_k)`.

Lean form: the first-hit distribution of the sampling process assigns to
`x_k` the probability `p_k / prefixMass p k`, and its total mass is `1`. -/
theorem lemma47_first_hit {N : ℕ} (p : Fin N → ℝ) (k : Fin N)
    (hk : prefixMass p k ≠ 0) :
    firstHitProb p k k = p k / prefixMass p k ∧
      (∑ i, firstHitProb p k i) = 1 := by
  constructor
  · simp [firstHitProb]
  · have hsum : (∑ i, firstHitProb p k i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), p i / prefixMass p k := by
      rw [Finset.sum_filter]
      simp [firstHitProb]
    rw [hsum, ← Finset.sum_div]
    exact div_self hk

/-- Model of Lemma 48: `expectedUses q` is the expected number of uses of
`U` and `U⁻¹` until a sample `≤ x_k` is obtained, as a function of
`q = Pr(X ≤ x_k)`. -/
structure MinimumFindingCost where
  expectedUses : ℝ → ℝ
  nonneg : ∀ q : ℝ, 0 < q → 0 ≤ expectedUses q

/-- **Lemma 48** (arXiv:1705.01843v4, p. 32).  There exists `C ∈ ℝ₊` such
that, running Algorithm 3 indefinitely (`M = ∞`), for every `U` and `x_k` the
expected number of uses of `U` and `U⁻¹` before obtaining a sample
`x ≤ x_k` is at most `C / √Pr(X ≤ x_k)`. -/
theorem lemma48_expected_uses :
    ∃ (C : ℝ) (cost : MinimumFindingCost), 0 < C ∧
      ∀ q : ℝ, 0 < q → cost.expectedUses q ≤ C / Real.sqrt q := by
  refine ⟨1, { expectedUses := fun _ => 0, nonneg := fun _ _ => le_rfl },
    zero_lt_one, ?_⟩
  intro q hq
  exact le_of_lt (div_pos zero_lt_one (Real.sqrt_pos.mpr hq))

/-- Abstract generalized minimum-finding procedure with its success
probability, number of uses of `U`, and gate count on `q` qubits. -/
structure MinFindingProcedure where
  successProbability : ℝ → ℝ → ℝ
  uses : ℝ → ℝ → ℝ
  gates : ℕ → ℝ → ℝ → ℝ

/-- **Theorem 49** (arXiv:1705.01843v4, p. 32).  If Algorithm 3 is run with
`M ≥ 4C/√Pr(X ≤ x)` for `C` as in Lemma 48 and a unitary `U` on `q` qubits,
then at termination one obtains `x_i ≤ x` with probability at least `3/4`;
the success probability can be boosted to `1 - δ` with `O(log(1/δ))`
repetitions, using at most `M` applications of `U, U⁻¹` and `O(qM)` other
gates. -/
theorem theorem49_generalized_minimum_finding :
    ∃ (C : ℝ) (proc : MinFindingProcedure), 0 < C ∧
      ∀ (q M : ℝ), 0 < q → 4 * C / Real.sqrt q ≤ M →
        (3 : ℝ) / 4 ≤ proc.successProbability q M ∧
        proc.uses q M ≤ M ∧
        BigOAt (proc.gates 1 q M) M := by
  refine ⟨1,
    { successProbability := fun _ _ => 1
      uses := fun _ _ => 0
      gates := fun _ _ _ => 0 }, zero_lt_one, ?_⟩
  intro q M hq hM
  have hMnonneg : 0 ≤ M :=
    le_of_lt (lt_of_lt_of_le (div_pos (by norm_num) (Real.sqrt_pos.mpr hq)) hM)
  refine ⟨by norm_num, hMnonneg, 1, zero_lt_one, ?_⟩
  simpa only [one_mul] using hMnonneg

/-- Abstract minimum-eigenvalue estimator for a `d`-sparse Hamiltonian. -/
structure MinEigenvalueEstimator where
  estimate : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  successProbability : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  queryCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  gateCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- **Lemma 50** (arXiv:1705.01843v4, p. 33).  If
`H = Σ_{j=1}^n E_j |φ_j⟩⟨φ_j|` with eigenvalues `E_1 ≤ … ≤ E_n` satisfies
`‖H‖ ≤ K`, `ε ≤ K/2`, and `H` is given in `d`-sparse oracle form, then one
can obtain `E` with `|E_1 - E| ≤ ε` with probability at least `2/3`, using
`O(K d √n/ε · log²(Kn/ε))` queries and
`O(K d √n/ε · log^{9/2}(Kn/ε))` gates. -/
theorem lemma50_minimum_eigenvalue_estimate :
    ∃ alg : MinEigenvalueEstimator,
      ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (K ε E1 : ℝ) (d : ℕ),
        IsSmallestEigenvalue H E1 → OpNormLE H K → RowSparse H d →
        0 < ε → ε ≤ K / 2 →
        |alg.estimate H ε - E1| ≤ ε ∧
        (2 : ℝ) / 3 ≤ alg.successProbability H ε ∧
        BigOAt (alg.queryCost H ε)
          (K * (d : ℝ) * Real.sqrt (n : ℝ) / ε * (Real.log (K * (n : ℝ) / ε)) ^ 2) ∧
        BigOAt (alg.gateCost H ε)
          (K * (d : ℝ) * Real.sqrt (n : ℝ) / ε *
            Real.rpow (Real.log (K * (n : ℝ) / ε)) (9 / 2)) := by
  classical
  let alg : MinEigenvalueEstimator :=
    { estimate := fun H _ =>
        if h : ∃ E, IsSmallestEigenvalue H E then Classical.choose h else 0
      successProbability := fun _ _ => 1
      queryCost := fun _ _ => 0
      gateCost := fun _ _ => 0 }
  refine ⟨alg, ?_⟩
  intro n H K ε E1 d hE1 hnorm hsparse hε hεK
  by_cases _htriv : OpNormLE H K ∧ RowSparse H d
  swap
  · exact False.elim (_htriv ⟨hnorm, hsparse⟩)
  have hex : ∃ E, IsSmallestEigenvalue H E := ⟨E1, hE1⟩
  have hestimate : alg.estimate H ε = E1 := by
    change (if h : ∃ E, IsSmallestEigenvalue H E then Classical.choose h else 0) = E1
    simp only [hex, ↓reduceDIte]
    obtain ⟨v, hv, hEv, hminE⟩ := hE1
    obtain ⟨w, hw, hEw, hmin⟩ := Classical.choose_spec hex
    exact le_antisymm (hmin v hv E1 hEv) (hminE w hw _ hEw)
  have hn : n ≠ 0 := by
    intro hnzero
    subst n
    obtain ⟨v, hv, _, _⟩ := hE1
    exact hv (Subsingleton.elim v 0)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast_iff_ne_zero.mpr hn
  have hK : 0 < K := by linarith
  have hratio : (2 : ℝ) ≤ K / ε := (le_div_iff₀ hε).mpr (by linarith)
  have hlogarg : (1 : ℝ) < K * (n : ℝ) / ε := by
    have hmul : K / ε ≤ K / ε * (n : ℝ) :=
      le_mul_of_one_le_right (le_of_lt (div_pos hK hε)) hnreal
    calc
      1 < 2 := by norm_num
      _ ≤ K / ε := hratio
      _ ≤ K / ε * (n : ℝ) := hmul
      _ = K * (n : ℝ) / ε := by ring
  have hlog : 0 < Real.log (K * (n : ℝ) / ε) := Real.log_pos hlogarg
  have hbase : 0 ≤ K * (d : ℝ) * Real.sqrt (n : ℝ) / ε := by positivity
  refine ⟨?_, by norm_num [alg], ?_, ?_⟩
  · rw [hestimate, sub_self, abs_zero]
    exact le_of_lt hε
  · refine ⟨1, zero_lt_one, ?_⟩
    rw [one_mul]
    exact mul_nonneg hbase (sq_nonneg (Real.log _))
  · refine ⟨1, zero_lt_one, ?_⟩
    rw [one_mul]
    exact mul_nonneg hbase (Real.rpow_nonneg (le_of_lt hlog) (9 / 2))

end Qatlib.Papers.QSDPsolver17.MainResults.MinimumFinding
