/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RationalLabelReadout

/-!
# Effective integer readouts for quantum counting

This module defines the rational amplitude decoder `effectiveLabelEstimate` and its rounded
integer count `effectiveIntegerCount`. The rational estimate lies in `[0, 1]` and approximates
the ideal label estimate within `2⁻ᵏ`, yielding count error at most `N * 2⁻ᵏ + 1/2`.

The module records rounding behavior, bit and space budget inequalities, and transfers counting
guarantees associated with [BrassardEtAl2002] to effective readouts through
`effectiveIntegerReadoutTransportsSpec`.

## Main statements

* `effectiveIntegerCount_error`: the combined decoder and rounding error bound.
* `effectiveIntegerCount_tie`: rounding at a half-integer.
* `effectiveIntegerCount_near_dev_nearest`: comparison with the ideal nearest count.
* `effectiveIntegerReadout_transports`: the combined effective counting guarantees.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
set_option warningAsError false

/-- The rational amplitude estimate obtained by applying `nativeAEDecode` to label `z` at
precision `k`. -/
def effectiveLabelEstimate (M k : ℕ) (z : Fin M) : ℚ :=
  nativeAEDecode M k z

/-- The integer count obtained by applying `aeEffRound` to the rational estimate `N *
effectiveLabelEstimate M k z`. -/
def effectiveIntegerCount (N M k : ℕ) (z : Fin M) : ℤ :=
  aeEffRound ((N : ℚ) * effectiveLabelEstimate M k z)

/-- The effective label estimate equals the native rational amplitude decoder on the same
record. -/
theorem effectiveLabelEstimate_eq_native (M k : ℕ) (z : Fin M) :
    effectiveLabelEstimate M k z = nativeAEDecode M k z := rfl

/-- The effective rational label estimate lies in the interval `[0, 1]`. -/
theorem effectiveLabelEstimate_mem (M k : ℕ) (z : Fin M) :
    0 ≤ effectiveLabelEstimate M k z ∧ effectiveLabelEstimate M k z ≤ 1 := by
  have h := native_ae_computed_scalar_precision M k z
  exact ⟨h.1, h.2.1⟩

/-- The effective rational label estimate differs from `aeEstimate M z` by at most `2⁻ᵏ`. -/
theorem effectiveLabelEstimate_error (M k : ℕ) (z : Fin M) :
    |(effectiveLabelEstimate M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := by
  have h := native_ae_computed_scalar_precision M k z
  exact h.2.2

/-- The effective integer count equals `aeEffCount` on the same parameters and label. -/
theorem effectiveIntegerCount_eq_frozen (N M k : ℕ) (z : Fin M) :
    effectiveIntegerCount N M k z = aeEffCount N M k z := rfl

/-- The effective integer count differs from the ideal scaled amplitude estimate `N * aeEstimate
M z` by at most `N * 2⁻ᵏ + 1/2`. -/
theorem effectiveIntegerCount_error (N M k : ℕ) (z : Fin M) :
    |(effectiveIntegerCount N M k z : ℝ) - (N : ℝ) * aeEstimate M z| ≤
      (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 :=
  aeEffCount_error N M k z

/-- For a rational input in `[0, n]`, `aeEffRound` produces an integer in `[0, n]`. -/
private theorem effRound_valid (x : ℚ) (n : ℕ) (hx0 : (0:ℚ) ≤ x) (hx1 : x ≤ (n:ℚ)) :
    0 ≤ aeEffRound x ∧ aeEffRound x ≤ n := by
  rw [aeEffRound_eq_intFloor]
  constructor
  · have hnonneg : (0:ℝ) ≤ (x : ℝ) + 1 / 2 := by
      have hx : (0:ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
      linarith
    exact Int.floor_nonneg.2 hnonneg
  · have hfloor : (Int.floor ((x : ℝ) + 1 / 2) : ℝ) ≤ (x : ℝ) + 1 / 2 := Int.floor_le _
    have hx : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx1
    have hlt : (Int.floor ((x : ℝ) + 1 / 2) : ℝ) < (n : ℝ) + 1 := by linarith
    have hlt' : (Int.floor ((x : ℝ) + 1 / 2) : ℤ) < n + 1 := by exact_mod_cast hlt
    omega

/-- The effective integer count lies between zero and `N`. -/
theorem effectiveIntegerCount_valid (N M k : ℕ) (z : Fin M) :
    0 ≤ effectiveIntegerCount N M k z ∧ effectiveIntegerCount N M k z ≤ N := by
  have h := native_ae_computed_scalar_precision M k z
  have hq0 : (0:ℚ) ≤ effectiveLabelEstimate M k z := h.1
  have hq1 : effectiveLabelEstimate M k z ≤ 1 := h.2.1
  exact effRound_valid ((N : ℚ) * effectiveLabelEstimate M k z) N
    (mul_nonneg (Nat.cast_nonneg N) hq0)
    (by simpa using! mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg N))

/-- If the scaled rational estimate is the half-integer `n + 1/2`, the effective integer count
is `n + 1`. -/
theorem effectiveIntegerCount_tie (N M k : ℕ) (z : Fin M) (n : ℤ)
    (h : (N : ℚ) * effectiveLabelEstimate M k z = (n : ℚ) + 1 / 2) :
    effectiveIntegerCount N M k z = n + 1 := by
  rw [effectiveIntegerCount, h]
  exact aeEffRound_half_up n

/-- Every positive-radius neighborhood of a half-integer contains rational inputs whose
effective rounded outputs are the two adjacent integers. -/
theorem effectiveIntegerReadout_boundary_density (n : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x y : ℚ,
      |(x : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound x = n ∧
        |(y : ℝ) - ((n : ℝ) + 1 / 2)| < ε ∧ aeEffRound y = n + 1 :=
  aeEffRound_boundary_dense n ε hε

/-- The effective integer count differs from `countLabelReadoutNearest N M z` by at most
`effRoundSlack N k`. -/
theorem effectiveIntegerCount_near_dev_nearest (N M k : ℕ) (z : Fin M) :
    |(effectiveIntegerCount N M k z : ℝ) - (countLabelReadoutNearest N M z : ℝ)| ≤
      effRoundSlack N k := by
  have h := aeEffCount_near_floor N M k z
  have hm := aeEstimate_mem M z
  have h0 : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z := mul_nonneg (Nat.cast_nonneg N) hm.1
  have hx0 : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := by linarith
  have hfl : (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℤ)
      = (countLabelReadoutNearest N M z : ℤ) := by
    have h1 : (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℤ)
        = ((Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2)).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (Int.floor_nonneg.2 hx0)]
    have h2 : ((Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2)).toNat : ℤ)
        = (Nat.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℤ) := by
      rw [Int.floor_toNat]
    rw [h1, h2, countLabelReadoutNearest]
  rw [hfl] at h
  rw [effectiveIntegerCount_eq_frozen]
  exact h

/-- The effective count bit budget is at least `Nat.clog 2 (N + 1) + k`, and the space budget is
at least twice the bit budget. -/
theorem effectiveIntegerReadout_budgets (N k : ℕ) :
    Nat.clog 2 (N + 1) + k ≤ effCountBitBudget N k ∧
      2 * effCountBitBudget N k ≤ effCountSpaceBudget N k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hb⟩ := clause90
  exact hb N k

/-- The conjunction of the effective-readout guarantees for Corollary 14, the singleton case,
basic approximate counting, and exact counting. These include their stated success
probabilities and the exact-counting cost bound [BrassardEtAl2002]. -/
def effectiveIntegerReadoutTransportsSpec : Prop :=

    (∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N), 2 ≤ N →
      ∀ (k : ℕ) (hM : 2 ≤ approxCountCor14Grid N),
        let t : ℝ := (S.card : ℝ)
        (8 : ℝ) / Real.pi ^ 2 ≤
          ∑ z ∈ Finset.univ.filter (fun z : Fin (approxCountCor14Grid N) =>
            |(effectiveIntegerCount N (approxCountCor14Grid N) k z : ℝ) - t| <
              cor14EffWidth N k t),
            (aeLaw (approxCountCor14Grid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
              (qftMatrix_unitary hN) hM).prob z) ∧

    (∀ S : Finset (Fin 1),
      cor14N1Output S = (S.card : ℤ) ∧
        |(cor14N1Output S : ℝ) - (S.card : ℝ)| < cor14Width 1 (S.card : ℝ) ∧
        (8 : ℝ) / Real.pi ^ 2 ≤ 1) ∧

    (∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) (k : ℕ),
        (S.card = 0 →
          (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
            basicApproxCountPrefixWeight hN S ω *
              basicApproxCountEffZero hN S ε ω (hω ω) k) = 1) ∧
        (0 < S.card →
          (2 : ℝ) / 3 ≤
            ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
              basicApproxCountPrefixWeight hN S ω *
                basicApproxCountEffGood hN S ε ω (hω ω) k)) ∧

    (∀ (N : ℕ) (hN : 0 < N) (S : Finset (Fin N))
        (hM₀ : 2 ≤ BHMTTh17.exactCountM₀ N)
        (hM : ∀ z₁ z₂ : Fin (BHMTTh17.exactCountM₀ N),
          2 ≤ BHMTTh17.exactCountGrid N
            ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₁)
            ((N : ℝ) * aeEstimate (BHMTTh17.exactCountM₀ N) z₂)) (k : ℕ),
      (2 : ℝ) / 3 ≤ exactCountEffSuccessMass hN S hM₀ hM k ∧
        BHMTTh17.exactCountCostMass hN S hM₀ hM ≤
          1000 * Real.sqrt (((S.card : ℝ) + 1) * ((N : ℝ) - (S.card : ℝ) + 1)))

/-- The effective integer readout satisfies all guarantees in
`effectiveIntegerReadoutTransportsSpec`. -/
theorem effectiveIntegerReadout_transports : effectiveIntegerReadoutTransportsSpec := by
  obtain ⟨_, _, _, _, _, _, _, _, h9, h10, h11, _⟩ := clause90
  exact ⟨h9.2.1, h9.2.2, h10, h11⟩
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
