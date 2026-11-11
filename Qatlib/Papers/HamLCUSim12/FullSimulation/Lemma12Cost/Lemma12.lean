/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesCorrectedHami

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12 (Eqs. (67)-(68)) — exponential count of the simulation

Fixed source: arXiv:1202.5822v1, Lemma 12, p.13, Eqs. (67)-(68):
with `M_{k,k}` the multi-product of Definition 1 for `H = Σ_j H_j`, `k ≥ 1`, and the
parameters
1. `γ = (1/k) log ⌈exp([1 + log(η)/2 + (1/2k) log(2(2k)^{5/2})] k)⌉`,
2. `ε̃ = min(1, ε, β, m h t k^{-4k})`,
3. `r = ⌈max{(4m(5/3)^{k-1}ht)^{1+1/4k}/(ε̃/5)^{1/4k}, 13 log(2/β)}⌉`,

the simulation uses at most
`N_exp ≤ 1000 m 5^{k-1} k^{9/4} e^{(1+log(η)/2)k} r` exponentials `e^{-iH_j t}`.

The frozen module `Lemma12IntegerNodesCorrected` proves the arithmetic skeleton of
this lemma under the corrected integer-node construction
`N = ⌈e^{(k+1)γ_req}⌉`, `γ = log N/(k+1)` (Definition 1 requires `e^{γ(k+1)} ∈ ℤ`;
the printed `γ` only guarantees `e^{γk} ∈ ℤ`, see the frozen source adjudication
CW-SOURCE-2).  It proves the `e^{γk}` bound of Eq. (68), the coefficient-sum and κ
consequences, the rounding of `r`, and the final count of Eq. (67).

The two theorems here are (i) the frozen corrected contract itself
(`lemma12_cost_bound_and_nodes`) and (ii) the extraction of its final conjunct, which
is exactly Eq. (67) (`lemma12_exponential_count`).  Both are fully proved by reusing
the frozen contract; the *error/success* conclusions of Lemma 12 (which depend on
Lemmas 4, 8-11) are deliberately not part of the frozen contract and are not claimed
here.
-/

set_option autoImplicit false
noncomputable section

open Real
open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma12Cost

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Fixed arXiv:1202.5822v1, Lemma 12 (frozen corrected contract): the integer-node
multi-product simulation satisfies all arithmetic conclusions of Lemma 12 — integrality
and distinctness of the nodes, the `γ` bounds, the `e^{γk}` bound of Eq. (68), the
coefficient/κ consequences, the rounding of `r`, and the Eq. (67) exponential count. -/
theorem lemma12_cost_bound_and_nodes : Lemma12IntegerNodesCorrected :=
  lemma12IntegerNodesCorrected

/-- Fixed arXiv:1202.5822v1, Lemma 12 Eq. (67): the simulation uses at most
`1000 m 5^{k-1} k^{9/4} e^{(1+log(η)/2)k} r` exponentials, extracted from the frozen
corrected contract (its final conjunct). -/
theorem lemma12_exponential_count (η : ℝ) (hlo : 305 / 1000 < η) (hhi : η < 312 / 1000)
    (k : ℕ) (hk : 1 ≤ k) (m h t ε β : ℝ) (hm : 1 ≤ m) (hh : 0 < h) (ht : 0 < t)
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) (C : ℕ → ℝ)
    (hsum : ∑ q ∈ Finset.Icc 1 (k + 1), C q = 1)
    (hcoef : ∀ q ∈ Finset.Icc 1 k,
      |C q| ≤ 2 ^ (1 / 2 : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ)
        * exp (2 * (k : ℝ) * (1 + log η / 2 - correctedGamma η k))) :
    10 * m * ((5 : ℝ) ^ (k - 1)) * (k : ℝ) * ((integerNode η k : ℤ) : ℝ)
        * ((retryCount m h t ε β k : ℤ) : ℝ)
      ≤ 1000 * m * ((5 : ℝ) ^ (k - 1)) * (k : ℝ) ^ (9 / 4 : ℝ)
        * exp ((1 + log η / 2) * (k : ℝ)) * ((retryCount m h t ε β k : ℤ) : ℝ) := by
  have h := lemma12IntegerNodesCorrected η hlo hhi k hk m h t ε β hm hh ht hε hβ hβ1 C
    hsum hcoef
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcost⟩ := h
  exact hcost.2

end Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma12Cost
