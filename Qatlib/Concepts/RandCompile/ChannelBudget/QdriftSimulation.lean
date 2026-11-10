/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.EffectiveInput.QdriftSimulationDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift
open Qatlib.Concepts.RandCompile.EffectiveInput

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

theorem clause27_endpoint : ∀ (L D : ℕ) (a : Fin L → ℚ) (b : ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t ε : ℝ) (tq eq : ℕ → ℚ) (fuel : ℕ),
    RelParamRead t tq → RelLowerParamRead ε eq →
    0 < weightTotal (simWeights b a) → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    (∃ k, k ≤ fuel ∧ epsCertified eq k = true) →
    ∃ (T s : ℕ),
      |t| ≤ T ∧
      (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
      finiteDiamondDistance
          (fairQdriftActualMap (simWeights b a) j0
            (fairQdriftSteps (weightTotal (simWeights b a)) T s)
            (fairQdriftFuel (fairQdriftSteps (weightTotal (simWeights b a)) T s) s) K t)
          (conjBranch (HamiltonianEvolution (∑ j, ((simWeights b a) j : ℂ) • K j) t))
        ≤ ENNReal.ofReal ε := by
  intro L D a b j0 K t ε tq eq fuel htq heq hW hK hex
  obtain ⟨T, s, h1, h2, h3⟩ :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.clause19_endpoint
      L D (simWeights b a) j0 K t ε tq eq fuel htq heq hW hK hex
  exact ⟨T, s, h1, h2, h3.1⟩

theorem clause27_bracket_endpoint : ∀ (L D : ℕ) (a : Fin L → ℚ) (b : ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t ε : ℝ) (tlo thi elo ehi : ℕ → ℚ) (fuel : ℕ),
    RelBracketStream t tlo thi → RelBracketStream ε elo ehi →
    0 < weightTotal (simWeights b a) → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    (∃ k, k ≤ fuel ∧ epsCertifiedBracket (elo k) (ehi k) k = true) →
    ∃ (T s : ℕ),
      |t| ≤ T ∧
      (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
      finiteDiamondDistance
          (fairQdriftActualMap (simWeights b a) j0
            (fairQdriftSteps (weightTotal (simWeights b a)) T s)
            (fairQdriftFuel (fairQdriftSteps (weightTotal (simWeights b a)) T s) s) K t)
          (conjBranch (HamiltonianEvolution (∑ j, ((simWeights b a) j : ℂ) • K j) t))
        ≤ ENNReal.ofReal ε := by
  intro L D a b j0 K t ε tlo thi elo ehi fuel ht heq hW hK hex
  obtain ⟨T, s, h1, h2, h3⟩ :=
    Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.clause19_bracket_endpoint
      L D (simWeights b a) j0 K t ε tlo thi elo ehi fuel ht heq hW hK hex
  exact ⟨T, s, h1, h2, h3⟩

theorem clause27_cost_digitReads (fuel b L : ℕ) (tq eq : ℕ → ℚ) :
    (simInputCost fuel b L tq eq).digitReads =
      (qdriftInputRun fuel L tq eq).cost.digitReads + simDigitReads L b := rfl

theorem clause27_cost_bitTime (fuel b L : ℕ) (tq eq : ℕ → ℚ) :
    (simInputCost fuel b L tq eq).bitTime =
      ((simInputCost fuel b L tq eq).ringOps + (simInputCost fuel b L tq eq).ceilOps
        + (simInputCost fuel b L tq eq).logOps) *
          ((simInputCost fuel b L tq eq).bitLength + 2)
          * ((simInputCost fuel b L tq eq).bitLength + 2) := by
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftRunCost.bitTime]

theorem clause27_cost_bitSpace (fuel b L : ℕ) (tq eq : ℕ → ℚ) :
    (simInputCost fuel b L tq eq).bitSpace =
      (simInputCost fuel b L tq eq).bitLength
        + (simInputCost fuel b L tq eq).digitReads * (simInputCost fuel b L tq eq).bitLength
        + 16 := by
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs.QdriftRunCost.bitSpace]

theorem clause27_cost (fuel b L : ℕ) (tq eq : ℕ → ℚ) :
    (simInputCost fuel b L tq eq).digitReads =
        (qdriftInputRun fuel L tq eq).cost.digitReads + simDigitReads L b ∧
    (simInputCost fuel b L tq eq).bitTime =
        ((simInputCost fuel b L tq eq).ringOps + (simInputCost fuel b L tq eq).ceilOps
          + (simInputCost fuel b L tq eq).logOps) *
            ((simInputCost fuel b L tq eq).bitLength + 2)
            * ((simInputCost fuel b L tq eq).bitLength + 2) ∧
    (simInputCost fuel b L tq eq).bitSpace =
        (simInputCost fuel b L tq eq).bitLength
          + (simInputCost fuel b L tq eq).digitReads * (simInputCost fuel b L tq eq).bitLength
          + 16 :=
  And.intro (clause27_cost_digitReads fuel b L tq eq)
    (And.intro (clause27_cost_bitTime fuel b L tq eq) (clause27_cost_bitSpace fuel b L tq eq))

theorem clause27_bitLength_bounds (fuel L : ℕ) (tq eq : ℕ → ℚ) (k s : ℕ)
    (hk : k ≤ scanPrecision fuel (epsCertified eq))
    (hs : s = successLevel (epsBudget eq (scanPrecision fuel (epsCertified eq)))) :
    ∀ k' ≤ k, qdRatBits (tq k') ≤ runBitLength k s L tq eq := by
  have _ := hk
  have _ := hs
  intro k' hk'
  have h1 := Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.runBitLength_bounds
    k s L tq eq k' hk'
  exact h1.1

theorem clause28_post_select_tight_count (L D : ℕ) (w : Fin L → ℕ)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) (hT : 0 < T) (he : 0 < eQ) :
    ∃ n : ℕ, 0 < n ∧
      finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
        (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        ≤ ENNReal.ofReal eQ := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.postSelected_source_tight_count_achievable
    w K t T eQ hW ht hK hT he

theorem clause28_endpoint : ∀ (W T : ℕ) (eQ : ℚ) (R n : ℕ),
    0 < eQ → tightCountCertified W T eQ R n = true →
    sourceTightCount W T eQ ≤ n ∧
    (∃ R' n', tightCountCertified W T eQ R' n' = true ∧
      sourceTightCount W T eQ ≤ n' ∧
      n' ≤ max 1 (Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ))) ∧
    (∀ (L D : ℕ) (w : Fin L → ℕ) (K : Fin L → Operator D) (t : ℝ) (T' : ℕ) (eQ' : ℝ)
      (hW : 0 < weightTotal w) (ht : |t| ≤ T')
      (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) (hT : 0 < T') (he : 0 < eQ'),
      ∃ n' : ℕ, 0 < n' ∧
        finiteDiamondDistance (postSelectedQdriftMap w hW n' K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
          ≤ ENNReal.ofReal eQ') := by
  intro W T eQ R n he h
  refine ⟨Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.tightCount_lower_bound
      W T eQ R n he h, ?_⟩
  refine ⟨Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.tightCount_achievable
      W T eQ he, ?_⟩
  intro L D w K t T' eQ' hW ht hK hT he
  exact clause28_post_select_tight_count L D w K t T' eQ' hW ht hK hT he

theorem clause28_synthesis (D : ℕ) (K : Operator D) (θ : ℝ) (hK : K.IsHermitian) :
    ∃ ts : List (TwoLevelInstruction (Fin D)),
      (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card (Fin D) * (Fintype.card (Fin D) + 1) / 2 ∧
      twoLevelProgram ts = HamiltonianEvolution K θ := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.nonPauli_exponential_two_level_synthesis
    D K θ hK

theorem clause29_no_free_lunch (L : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator 2) (n R : ℕ) (t : ℝ) :
    ctrlCrossBlock (ctrlBlockMapIdx (fairQdriftActualMap w j0 n R K t) coherentWitness) = 0 ∧
    ctrlCrossBlock coherentWitness ≠ 0 := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.no_free_lunch_endpoint
    (fairQdriftActualMap w j0 n R K t)

theorem clause29_table_minimal (lam t eps : ℝ) (n : ℕ) (hn : 0 < n) (heps : 0 < eps) :
    (2 * lam ^ 2 * t ^ 2 / (n : ℝ) ≤ eps) ↔
      Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps) ≤ n := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.tableQdriftCount_minimal
    lam t eps n hn heps

theorem clause29_pe_accuracy (lam deltaE pf : ℝ) (j : ℕ)
    (hshare : 0 < peErrorShare deltaE pf j) :
    2 * lam ^ 2 * (peTimes j) ^ 2
      ≤ peErrorShare deltaE pf j * (peQuerySteps lam deltaE pf j : ℝ) := by
  exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.pe_query_accuracy
    lam deltaE pf j hshare

theorem clause29_endpoint : ∀ (L : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator 2) (n R : ℕ) (t : ℝ),
    ctrlCrossBlock (ctrlBlockMapIdx (fairQdriftActualMap w j0 n R K t) coherentWitness) = 0 ∧
    ctrlCrossBlock coherentWitness ≠ 0 ∧
    (∀ (lam t eps : ℝ) (n : ℕ), 0 < n → 0 < eps →
      ((2 * lam ^ 2 * t ^ 2 / (n : ℝ) ≤ eps) ↔
        Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps) ≤ n)) ∧
    (∀ (lam deltaE pf : ℝ) (j : ℕ), 0 < peErrorShare deltaE pf j →
      2 * lam ^ 2 * (peTimes j) ^ 2
        ≤ peErrorShare deltaE pf j * (peQuerySteps lam deltaE pf j : ℝ)) ∧
    (∀ (pf : ℝ), 0 < pf →
      majorityFailure (2 / 5) (peRounds pf) ≤ pf / 2) ∧
    (∀ (L' D' : ℕ) (w' : Fin L' → ℕ) (j0' : Fin L') (n' R' : ℕ)
      (K' : Fin L' → Operator D') (t' : ℝ) (T' : ℕ) (eQ' : ℝ) (hW' : 0 < weightTotal w'),
      (1 ≤ R' → (1 / 2) ^ n' ≤ postSelectSuccessMass w' R' n' ∧
        postSelectSuccessMass w' R' n' ≤ 1) ∧
      (0 < n' → 1 ≤ R' → (∀ j, (K' j).IsHermitian ∧ ‖K' j‖ ≤ 1) →
        finiteDiamondDistance (postSelectedQdriftMap w' hW' n' K' t')
          (conjBranch (HamiltonianEvolution (∑ j, (w' j : ℂ) • K' j) t'))
          ≤ ENNReal.ofReal (postSelectDiamondBudget w' n' t')) ∧
      (0 < n' → 1 ≤ R' → (∀ j, (K' j).IsHermitian ∧ ‖K' j‖ ≤ 1) →
        finiteDiamondDistance (fairQdriftActualMap w' j0' n' R' K' t')
          (postSelectedQdriftMap w' hW' n' K' t')
          ≤ ENNReal.ofReal (n' * ((2 : ℝ)⁻¹)^R')) ∧
      (Nat.ceil (2 * (weightTotal w' : ℝ) ^ 2 * (T' : ℝ) ^ 2 / eQ') ≤ n' →
        0 < n' → 1 ≤ R' → |t'| ≤ T' → 0 < eQ' →
        (∀ j, (K' j).IsHermitian ∧ ‖K' j‖ ≤ 1) →
        finiteDiamondDistance (postSelectedQdriftMap w' hW' n' K' t')
          (conjBranch (HamiltonianEvolution (∑ j, (w' j : ℂ) • K' j) t'))
          ≤ ENNReal.ofReal eQ')) ∧
    (∀ (D : ℕ) (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D),
      Pᴴ = P → P * P = P →
        |selectiveMass Φ P X - selectiveMass Ψ P X| ≤ Matrix.traceNorm ((Φ - Ψ) X)) := by
  intro L w j0 K n R t
  have hnfl := clause29_no_free_lunch L w j0 K n R t
  refine ⟨hnfl.1, hnfl.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro lam t eps n hn heps
    exact clause29_table_minimal lam t eps n hn heps
  · intro lam deltaE pf j hshare
    exact clause29_pe_accuracy lam deltaE pf j hshare
  · intro pf hpf
    exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.majorityFailure_pe
      pf hpf
  · intro L' D' w' j0' n' R' K' t' T' eQ' hW'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hR'
      exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.postSelect_success_mass_bounds
        w' hW' R' n' hR'
    · intro hn' hR' hK'
      exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.postSelected_diamond_budget
        w' n' K' t' hW' hn' hK'
    · intro hn' hR' hK'
      exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.postSelect_vs_capped_sampling_bound
        w' j0' n' R' K' t' hW' hn' hK'
    · intro hceil hn' hR' ht' he' hK'
      exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.postSelected_source_tight_count
        w' K' t' T' eQ' n' hW' ht' hK' hn' he' hceil
  · intro D Φ Ψ P X hP hPP
    exact Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift.selectiveMass_diff_le
      Φ Ψ P X hP hPP

end Qatlib.Concepts.RandCompile.ChannelBudget.QdriftSimulation
