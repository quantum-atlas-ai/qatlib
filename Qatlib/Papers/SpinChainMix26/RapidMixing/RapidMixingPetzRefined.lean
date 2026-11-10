/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzRefinedDefs
set_option warningAsError false
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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem aEta_nonneg (η : InfluenceProfile) : 0 ≤ aEta η := by
  classical
  unfold aEta
  exact mul_nonneg (by norm_num) (tsum_nonneg fun r => η.nonneg (r + 1))

theorem ellStar_gt_aEta (η : InfluenceProfile) :
    (aEta η : ℝ) < (ellStar η : ℕ) := by
  have hceil : aEta η ≤ (Nat.ceil (aEta η) : ℝ) := Nat.le_ceil _
  have hone : (Nat.ceil (aEta η) : ℝ) < (Nat.ceil (aEta η) : ℝ) + 1 := by linarith
  rw [ellStar, Nat.cast_add, Nat.cast_one]
  linarith

theorem ellStar_pos (η : InfluenceProfile) : 0 < ellStar η := by
  unfold ellStar
  omega

theorem ellStar_gamma_pos (η : InfluenceProfile) : 0 < gammaOf η (ellStar η) :=
  gammaOf_pos (ellStar_pos η) (ellStar_gt_aEta η)

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

theorem clause4_endpoint (blocks angleGates classicalBits : ℕ) :
    (petzCostLedger blocks angleGates classicalBits).blockUpdates = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).statePreparations = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).inversePreparations = blocks ∧
      (petzCostLedger blocks angleGates classicalBits).angleGates
        = blocks * angleGates ∧
      (petzCostLedger blocks angleGates classicalBits).classicalBits
        = blocks * classicalBits := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem clause5_endpoint {n ℓ d : ℕ} (c : PetzCut n ℓ) (β : ℝ) (chain : PeriodicChain n d)
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

theorem clause6_endpoint (η : InfluenceProfile) (n : ℕ) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n → openSiteUpdateRate n (ellStar η) i = 1) ∧
      (0 < gammaOf η (ellStar η)) ∧
      (gammaOf η (ellStar η) = 1 - aEta η / (ellStar η : ℝ)) ∧
      (aEta η = 2 * ∑' r : ℕ, η.eta (r + 1)) := by
  have hstat := clause30_static_shape (n := n) (ellStar_pos η) (ellStar_gt_aEta η)
  exact ⟨hstat.1, hstat.2.2.2, hstat.2.2.1, hstat.2.1⟩

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
