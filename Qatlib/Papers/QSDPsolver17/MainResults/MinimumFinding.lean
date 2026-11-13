/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# MinimumFinding

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
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

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma48_expected_uses`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma48_expected_uses_statement : Prop :=
    ∃ (C : ℝ) (cost : MinimumFindingCost), 0 < C ∧
      ∀ q : ℝ, 0 < q → cost.expectedUses q ≤ C / Real.sqrt q

/-- Abstract generalized minimum-finding procedure with its success
probability, number of uses of `U`, and gate count on `q` qubits. -/
structure MinFindingProcedure where
  successProbability : ℝ → ℝ → ℝ
  uses : ℝ → ℝ → ℝ
  gates : ℕ → ℝ → ℝ → ℝ

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem49_generalized_minimum_finding`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem49_generalized_minimum_finding_statement : Prop :=
    ∃ (C : ℝ) (proc : MinFindingProcedure), 0 < C ∧
      ∀ (q M : ℝ), 0 < q → 4 * C / Real.sqrt q ≤ M →
        (3 : ℝ) / 4 ≤ proc.successProbability q M ∧
        proc.uses q M ≤ M ∧
        BigOAt (proc.gates 1 q M) M

/-- Abstract minimum-eigenvalue estimator for a `d`-sparse Hamiltonian. -/
structure MinEigenvalueEstimator where
  estimate : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  successProbability : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  queryCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  gateCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma50_minimum_eigenvalue_estimate`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma50_minimum_eigenvalue_estimate_statement : Prop :=
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
            Real.rpow (Real.log (K * (n : ℝ) / ε)) (9 / 2))

end Qatlib.Papers.QSDPsolver17.MainResults.MinimumFinding
