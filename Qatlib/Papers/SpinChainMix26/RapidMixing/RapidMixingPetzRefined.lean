/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzRefinedDefs

/-!
# Block-length and cost-ledger identities

This module verifies the elementary consequences of the block-length choice `ellStar` in the
formalization of [Kim2026]. It proves positivity of the influence-based rate, unit periodic and
open-chain site update rates, and the defining logarithmic lower-bound constant.

The endpoint statements also collect Petz stationarity and scalar-reference marginal identities
under their positivity hypotheses, together with the arithmetic entries of `petzCostLedger`.

## Main statements

* `clause3_endpoint`: block-length inequalities, rate formulas, and unit periodic site rates.
* `clause4_endpoint`: the five cost-ledger entries.
* `clause5_endpoint` and `clause6_endpoint`: stationary-reference, marginal, and open-chain rate
  identities.

## References

* [Kim, 2026][Kim2026]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpinChainMix26.RapidMixing
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Qatlib.Papers.SpinChainMix26.RapidMixing.NEXT

namespace Qatlib.Papers.SpinChainMix26.RapidMixing
namespace NEXT

open Matrix Qatlib
open scoped BigOperators ComplexOrder

set_option autoImplicit false

/-- The influence constant of a nonnegative influence profile is nonnegative. -/
theorem aEta_nonneg (η : InfluenceProfile) : 0 ≤ aEta η := by
  classical
  unfold aEta
  exact mul_nonneg (by norm_num) (tsum_nonneg fun r => η.nonneg (r + 1))

/-- The chosen block length `ellStar η` strictly exceeds `aEta η`. -/
theorem ellStar_gt_aEta (η : InfluenceProfile) :
    (aEta η : ℝ) < (ellStar η : ℕ) := by
  have hceil : aEta η ≤ (Nat.ceil (aEta η) : ℝ) := Nat.le_ceil _
  have hone : (Nat.ceil (aEta η) : ℝ) < (Nat.ceil (aEta η) : ℝ) + 1 := by linarith
  rw [ellStar, Nat.cast_add, Nat.cast_one]
  linarith

/-- The chosen block length `ellStar η` is positive. -/
theorem ellStar_pos (η : InfluenceProfile) : 0 < ellStar η := by
  unfold ellStar
  omega

/-- The rate at the chosen block length `ellStar η` is positive. -/
theorem ellStar_gamma_pos (η : InfluenceProfile) : 0 < gammaOf η (ellStar η) :=
  gammaOf_pos (ellStar_pos η) (ellStar_gt_aEta η)

/-- The choice `ellStar η` exceeds `aEta η`, is positive, gives a positive rate with the
defining formulas, and yields unit site rates on every longer periodic chain. -/
theorem clause3_endpoint (η : InfluenceProfile) :
    (aEta η : ℝ) < (ellStar η : ℕ) ∧
      0 < ellStar η ∧
      0 < gammaOf η (ellStar η) ∧
      (gammaOf η (ellStar η) = 1 - aEta η / (ellStar η : ℝ)) ∧
      (aEta η = 2 * ∑' r : ℕ, η.eta (r + 1)) ∧
      (∀ n : ℕ, ellStar η < n → ∀ i : ℕ, i < n →
        siteUpdateRate n (ellStar η) i = 1) := by
  refine ⟨ellStar_gt_aEta η, ellStar_pos η, ellStar_gamma_pos η, gammaOf_eq η _, ?_⟩
  · refine ⟨aEta_eq_two_tsum η, ?_⟩
    intro n hn i hi
    exact clause29_rateOne_shape (ellStar_pos η) n hn i hi

/-- The cost ledger counts one update, preparation, and inverse preparation per block, and
multiplies the angle-gate and classical-bit costs by the number of blocks. -/
theorem clause4_endpoint (blocks angleGates classicalBits : ℕ) :
    (petzCostLedger blocks angleGates classicalBits).blockUpdates = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).statePreparations = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).inversePreparations = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).angleGates
        = blocks * angleGates ∧
      (petzCostLedger blocks angleGates classicalBits).classicalBits
        = blocks * classicalBits := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A positive semidefinite reference with positive definite complementary marginal is fixed by
its Petz update; for a positive scalar reference, site marginals are uniformized inside the
cut block and preserved outside it. -/
theorem clause5_endpoint {n ℓ d : ℕ} (c : PetzCut n ℓ) (_β : ℝ) (_chain : PeriodicChain n d)
    (σ : Operator (d ^ n)) (hd : 0 < d) (hσ : σ.PosSemidef)
    (hσA : (PartialTrace (Matrix.reindex (c.matrixEquiv (d := d)) (c.matrixEquiv (d := d)) σ)).PosDef)
    (k : ℝ) (hk : 0 < k) (i : Fin n) (out : Fin d) :
    petzHeatBath c σ σ = σ ∧
      siteMarginalMass (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) σ) i out
        = if (∃ j : Fin ℓ, c.siteSplit i = Sum.inr j) then
            (1 / (d : ℝ)) * (Matrix.trace σ).re
          else siteMarginalMass σ i out := by
  refine ⟨petzHeatBath_stationary c σ hσ hσA, ?_⟩
  exact siteMarginalMass_petzHeatBath_smul_one c k hk hd σ i out

/-- At `ellStar η`, all valid open-chain site rates equal one, the contraction rate is positive,
and the defining influence and rate formulas hold. -/
theorem clause6_endpoint (η : InfluenceProfile) (n : ℕ) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n → openSiteUpdateRate n (ellStar η) i = 1) ∧
      (0 < gammaOf η (ellStar η)) ∧
      (gammaOf η (ellStar η) = 1 - aEta η / (ellStar η : ℝ)) ∧
      (aEta η = 2 * ∑' r : ℕ, η.eta (r + 1)) := by
  have hstat := clause30_static_shape (n := n) (ellStar_pos η) (ellStar_gt_aEta η)
  exact ⟨hstat.1, hstat.2.2.2, hstat.2.2.1, hstat.2.1⟩

/-- The lower-bound constant at `ellStar η` has its defining logarithmic expression, the block
length is at least one, and the associated rate is positive. -/
theorem clause7_endpoint (η : InfluenceProfile) (d : ℕ) :
    lowerBoundConst (ellStar η) d
        = (1 / 2 : ℝ) * Real.log (16 * (ellStar η : ℝ) / (3 * (1 - 1 / (d : ℝ)) ^ 2)) ∧
      (1 ≤ ellStar η) ∧
      (0 < gammaOf η (ellStar η)) := by
  have h1 : 1 ≤ ellStar η := by
    unfold ellStar
    exact Nat.succ_le_of_lt (by omega)
  refine ⟨rfl, h1, ellStar_gamma_pos η⟩

end NEXT
end Qatlib.Papers.SpinChainMix26.RapidMixing
