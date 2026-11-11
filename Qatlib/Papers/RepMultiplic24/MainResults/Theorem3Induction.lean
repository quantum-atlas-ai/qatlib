/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.Lemma2Shots

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults.Theorem3Induction

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024), Claim `c003` = Theorem 3 (main text p. 8-9).

Theorem 3: let `H ⊆ G`. If there is a quantum circuit for the `G`-QFT with `𝒢`
gates and a circuit with `R` gates preparing `ρ_H^β` (Eq. (8)), then there is an
`O((𝒢+ℛ)(d_β|G|/d_α|H|)²)` quantum algorithm that, given irrep labels
`(α, β)`, computes `mult(r_G^α, r_H^β↑_H^G)` with high probability.

Proof route (paper): prepare `ρ_H^β`, apply the `G`-QFT and measure the `G`-irrep
label; the outcome is `α` with probability `mult·|H|d_α/(|G|d_β)` (Eq. (17)).
Lemma 2 applied with this `p` and `ε = |H|d_α/(|G|d_β)` gives
`O(1/ε²) = O((d_β|G|/d_α|H|)²)` shots; each shot costs at most `𝒢+ℛ` gates.

Formalisation: `InductionShotCost G R` bundles the `G`-QFT and state-preparation
sizes; a shot costs at most `G+R`. The theorem is stated in the paper's
cost/multiplicity vocabulary (the induced representation itself is outside the
library), with explicit constants `33` and `1/2`.

This claim is fully proved from `Lemma2Shots.lean`; no `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-- Cost of one shot of the induction algorithm of Theorem 3: a `G`-QFT plus the
preparation of `ρ_H^β` (Eq. (8)). -/
structure InductionShotCost (G R : ℕ) where
  /-- Gates for the `G`-QFT. -/
  qftGates : ℕ
  /-- Gates for preparing `ρ_H^β`. -/
  prepareGates : ℕ
  qft_le : qftGates ≤ G
  prepare_le : prepareGates ≤ R

/-- Gate cost of one shot. -/
def InductionShotCost.perShot {G R : ℕ} (c : InductionShotCost G R) : ℕ :=
  c.qftGates + c.prepareGates

/-- The `InductionShotCost.perShot_le` result for the RepMultiplic24 paper model. -/
theorem InductionShotCost.perShot_le {G R : ℕ} (c : InductionShotCost G R) :
    c.perShot ≤ G + R := by
  have h1 := c.qft_le
  have h2 := c.prepare_le
  unfold InductionShotCost.perShot
  exact Nat.add_le_add h1 h2

/-- Gate cost of a complete run. -/
def InductionShotCost.runCost {G R : ℕ} (c : InductionShotCost G R) (shots : ℕ) : ℕ :=
  shots * c.perShot

/-- The `InductionShotCost.runCost_le` result for the RepMultiplic24 paper model. -/
theorem InductionShotCost.runCost_le {G R : ℕ} (c : InductionShotCost G R) (shots : ℕ) :
    c.runCost shots ≤ shots * (G + R) := by
  unfold InductionShotCost.runCost
  exact Nat.mul_le_mul_left _ c.perShot_le

/-- **Theorem 3 (c003).** There is a shot count `N = O((d_β|G|/d_α|H|)²)` and a
per-shot cost model for the induction circuit such that

* `N` shots determine `mult(r_G^α, r_H^β↑_H^G)` with probability at least `1/2`, and
* the total gate count is at most `33 (𝒢+ℛ)(d_β|G|/d_α|H|)²`.

Paper: fixed arXiv:2407.17649, Theorem 3, with Eq. (17) and Lemma 2. -/
theorem theorem3_induction (G H R dα dβ mult : ℕ)
    (hG : 0 < G) (hH : 0 < H) (hdα : 0 < dα) (hdβ : 0 < dβ) (hmult : 0 < mult)
    (hm : mult * (H * dα) ≤ G * dβ) :
    ∃ (N : ℕ) (cost : InductionShotCost G R), 0 < N ∧
      (N : ℝ) ≤ 33 * (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 ∧
      probEvent (bernoulliLaw (inductionProb dα dβ mult G H hG hdβ hm))
        (fun ω : Fin N → Bool =>
          frequencyEstimate (((H : ℝ) * (dα : ℝ)) / ((G : ℝ) * (dβ : ℝ))) ω = mult) ≥ 1 / 2 ∧
      ((cost.runCost N : ℕ) : ℝ) ≤ 33 * ((G + R : ℕ) : ℝ) *
        (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 := by
  have hG' : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
  have hH' : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hα : (0 : ℝ) < (dα : ℝ) := by exact_mod_cast hdα
  have hβ : (0 : ℝ) < (dβ : ℝ) := by exact_mod_cast hdβ
  set ε : ℝ := ((H : ℝ) * (dα : ℝ)) / ((G : ℝ) * (dβ : ℝ)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hGHdβ : (0 : ℝ) < (G : ℝ) * (dβ : ℝ) := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hGHdβ]
    have hmul1 : 1 ≤ mult := hmult
    have hle0 : H * dα ≤ mult * (H * dα) := by
      calc H * dα = 1 * (H * dα) := by ring
        _ ≤ mult * (H * dα) := Nat.mul_le_mul_right _ hmul1
    have hle : H * dα ≤ G * dβ := le_trans hle0 hm
    exact_mod_cast hle
  have hpm : ((inductionProb dα dβ mult G H hG hdβ hm : I) : ℝ) = (mult : ℝ) * ε := by
    rw [hεdef]
    simp only [inductionProb]
    rw [mul_div_assoc]
  obtain ⟨N, hN, hbound, hprob⟩ :=
    shots_constant_probability (inductionProb dα dβ mult G H hG hdβ hm) hε hpm
  -- `33/ε² = 33 ((d_β|G|)/(d_α|H|))²`
  have hratio : (33 : ℝ) / ε ^ 2 =
      33 * (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 := by
    rw [hεdef]
    field_simp
  have hεsq : (1 : ℝ) ≤ 1 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hs := mul_self_le_mul_self (le_of_lt hε) hε1
    nlinarith [hs]
  have hN33 : (N : ℝ) ≤
      33 * (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 := by
    rw [← hratio]
    set t : ℝ := 1 / ε ^ 2 with ht
    have ht1 : (1 : ℝ) ≤ t := by rw [ht]; exact hεsq
    have h32 : (32 : ℝ) / ε ^ 2 = 32 * t := by rw [ht]; ring
    have h33 : (33 : ℝ) / ε ^ 2 = 33 * t := by rw [ht]; ring
    rw [h33]
    rw [h32] at hbound
    linarith
  refine ⟨N, ⟨G, R, le_rfl, le_rfl⟩, hN, hN33, hprob, ?_⟩
  · have hcost : ((InductionShotCost.runCost ⟨G, R, le_rfl, le_rfl⟩ N : ℕ) : ℝ) ≤
        (N : ℝ) * (((G + R : ℕ)) : ℝ) := by
      exact_mod_cast InductionShotCost.runCost_le ⟨G, R, le_rfl, le_rfl⟩ N
    have hGR : (0 : ℝ) ≤ (((G + R : ℕ)) : ℝ) := by positivity
    have hmul : (N : ℝ) * (((G + R : ℕ)) : ℝ) ≤
        33 * (((G + R : ℕ)) : ℝ) *
          (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 := by
      calc (N : ℝ) * (((G + R : ℕ)) : ℝ)
          ≤ (33 * (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2) *
              (((G + R : ℕ)) : ℝ) := mul_le_mul_of_nonneg_right hN33 hGR
        _ = 33 * (((G + R : ℕ)) : ℝ) *
              (((dβ : ℝ) * (G : ℝ)) / ((dα : ℝ) * (H : ℝ))) ^ 2 := by ring
    nlinarith [hcost, hmul]

end Qatlib.Papers.RepMultiplic24.MainResults
