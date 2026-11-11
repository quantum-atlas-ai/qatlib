/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.Lemma2Shots

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults.Theorem1Restriction

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024), Claim `c001` = Theorem 1 (main text p. 6).

Theorem 1: let `H ⊆ G`; let `ℋ` be the size of a circuit for the `H`-QFT, `ℛ` the
size of a circuit preparing `ρ_G^α` (Eq. (8)) and `𝒟` the size of a circuit
implementing a controlled action of the regular representation of `G`. Then there
is an `O((ℋ+ℛ+𝒟)(d_α/d_β)²)` quantum algorithm that, given irrep labels
`(α, β)`, computes `mult(r_H^β, r_G^α↓_H^G)` with constant success probability.

Proof route (paper): run the sampling circuit of Section "Restriction" once per
shot, i.e. prepare `ρ_G^α`, apply the `H`-QFT and the controlled action, and
measure the `H`-irrep label; the outcome is `β` with probability
`mult · d_β/d_α` (Eq. (10)). Lemma 2 then estimates the multiplicity from
`O((d_α/d_β)²)` shots. The total gate count is the number of shots times the
per-shot cost `ℋ+ℛ+𝒟`.

Formalisation: `RestrictionShotCost H R D` bundles the three circuit sizes; a
shot costs at most `H+R+D` gates; Lemma 2 supplies the shot count. The
representation-theoretic objects themselves (irreps, restriction, the two
circuits) are not available in the library, so the theorem is stated in the
paper's cost/multiplicity vocabulary: the conclusion is exactly the paper's
"`O((H+R+D)(d_α/d_β)²)` algorithm computing the multiplicity with constant
probability", with the explicit constants `33` and `1/2`.

This claim is fully proved from `Lemma2Shots.lean`; no `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-- **Theorem 1 (c001).** There is a shot count `N = O((d_α/d_β)²)` and a per-shot
cost model for the restriction circuit such that

* `N` shots determine `mult(r_H^β, r_G^α↓_H^G)` with probability at least `1/2`, and
* the total gate count is at most `33 (d_α/d_β)² (ℋ+ℛ+𝒟)`.

Paper: fixed arXiv:2407.17649, Theorem 1, with Eq. (10) and Lemma 2. -/
theorem theorem1_restriction (H R D dα dβ mult : ℕ)
    (hdα : 0 < dα) (hdβ : 0 < dβ) (hmult : 0 < mult) (hm : mult * dβ ≤ dα) :
    ∃ (N : ℕ) (cost : RestrictionShotCost H R D), 0 < N ∧
      (N : ℝ) ≤ 33 * ((dα : ℝ) / (dβ : ℝ)) ^ 2 ∧
      probEvent (bernoulliLaw (restrictionProb dα dβ mult hdα hm))
        (fun ω : Fin N → Bool =>
          frequencyEstimate ((dβ : ℝ) / (dα : ℝ)) ω = mult) ≥ 1 / 2 ∧
      ((runCost cost N : ℕ) : ℝ) ≤
        33 * ((H + R + D : ℕ) : ℝ) * ((dα : ℝ) / (dβ : ℝ)) ^ 2 := by
  obtain ⟨N, hN, hbound, hprob⟩ := lemma2_shots dα dβ mult hdα hdβ hmult hm
  refine ⟨N, ⟨H, R, D, le_rfl, le_rfl, le_rfl⟩, hN, hbound, hprob, ?_⟩
  have hcost : ((runCost ⟨H, R, D, le_rfl, le_rfl, le_rfl⟩ N : ℕ) : ℝ) ≤
      (N : ℝ) * (((H + R + D : ℕ)) : ℝ) := by
    exact_mod_cast runCost_le ⟨H, R, D, le_rfl, le_rfl, le_rfl⟩ N
  have hHD : (0 : ℝ) ≤ (((H + R + D : ℕ)) : ℝ) := by positivity
  have hmul : (N : ℝ) * (((H + R + D : ℕ)) : ℝ) ≤
      (33 * ((dα : ℝ) / (dβ : ℝ)) ^ 2) * (((H + R + D : ℕ)) : ℝ) :=
    mul_le_mul_of_nonneg_right hbound hHD
  nlinarith [hcost, hmul]

end Qatlib.Papers.RepMultiplic24.MainResults
