/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutExt
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadoutConsumers
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostQuan
import Qatlib.Concepts.EstimatorLaws.MergedEstimator.MontanaroLemma18RestrictedSubgoalMont
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountRelDefs

/-!
# Refined amplitude readout, counting, and search

This module collects finite-precision count readouts, relative and exact counting consumers,
adaptive search estimates, and explicit query, gate, and workspace budgets. Its
amplitude-estimation windows, endpoint guarantees, and counting constructions develop the
framework of [BrassardEtAl2002]; the signed-mean estimates also connect to the mean-estimation
approach of [Montanaro2015].

The native readout layer exposes rational phase inputs, counted sine and arctangent sums,
decoder precision, and combined sampling and numerical error bounds. The final search results
connect rounded amplitude-amplification iterations to workspace circuits and transport query
guarantees through clean ancillas and oracle simulations.

## Main statements

* `nextCountReadout_error` bounds finite-precision integer count readout error.
* `nextRelative_success` and `nextCor4_success` provide relative and exact counting success
  bounds.
* `cor4_expected_cost_le` bounds the expected counting cost.
* `nextMontanaro_success_le` records a signed-mean success guarantee under its stated
  preparation and variance hypotheses.
* `nextApproxCount_final_layer` packages the unified final counting layer and its endpoint and
  rounding properties.
* `nextNativeOutput_precision` and `nextNative_same_record_success` combine native decoder
  precision with measured-label success.
* `nextMultiSearch_actual_upper` gives success and resource bounds for the workspace search
  circuit.

## References

* [Brassard et al., 2002][BrassardEtAl2002], Quantum amplitude amplification and estimation.
* [Montanaro, 2015][Montanaro2015], Quantum speedup of Monte Carlo methods.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeSearch.NativeMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
namespace AmplitudeReadoutRefined

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The rational amplitude readout `nativeAEDecode M k z` for phase label `z` and precision
parameter `k`. -/
def nextLabelRecord (M k : ℕ) (z : Fin M) : ℚ := nativeAEDecode M k z

/-- Rounds a real number to the integer `Int.floor (x + 1 / 2)`, so half-integer ties round
upward. -/
noncomputable def nextRound (x : ℝ) : ℤ := Int.floor (x + 1 / 2)

/-- The integer count obtained by multiplying `nextLabelRecord M k z` by the population size `N`
and applying `nextRound`. -/
noncomputable def nextCountReadout (N M k : ℕ) (z : Fin M) : ℤ :=
  nextRound ((N : ℝ) * (nextLabelRecord M k z : ℝ))

/-- For a nonnegative real number, its integer floor equals its natural-number floor cast to the
integers. -/
private theorem intFloor_eq_natFloor {y : ℝ} (hy : 0 ≤ y) :
    Int.floor y = (Nat.floor y : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor
  · exact_mod_cast (Nat.floor_le hy)
  · exact_mod_cast (show y < (Nat.floor y : ℝ) + 1 from
      Nat.lt_floor_add_one y)

/-- The refined count readout `nextCountReadout N M k z` agrees exactly with the existing engine
readout `aeEffCount N M k z`. -/
theorem nextCountReadout_eq_engine (N M k : ℕ) (z : Fin M) :
    nextCountReadout N M k z = aeEffCount N M k z := by
  unfold nextCountReadout nextRound aeEffCount aeEffEstimate nextLabelRecord
  rw [aeEffRound_eq_intFloor]
  congr 1
  push_cast
  ring

/-- The absolute error of `nextRound` is at most `1 / 2` for every real input. -/
theorem nextRound_error (x : ℝ) : |(nextRound x : ℝ) - x| ≤ 1 / 2 := by
  have hle : (Int.floor (x + 1 / 2) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have hlt : x + 1 / 2 < (Int.floor (x + 1 / 2) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [nextRound, abs_le]
  constructor <;> linarith

/-- A half-integer `n + 1 / 2` with natural `n` rounds upward to `n + 1` under `nextRound`. -/
theorem nextRound_tie (n : ℕ) : nextRound ((n : ℝ) + 1 / 2) = (n : ℤ) + 1 := by
  rw [nextRound, Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- Applying `nextRound` to a natural number cast to the reals returns that same number as an
integer. -/
theorem nextRound_exact (n : ℕ) : nextRound (n : ℝ) = (n : ℤ) := by
  rw [nextRound, Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- For `0 < e` and `e ≤ 1 / 2`, the value `n + 1 / 2 - e` rounds to the natural number `n`
under `nextRound`. -/
theorem nextRound_below_tie (n : ℕ) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 2) :
    nextRound ((n : ℝ) + 1 / 2 - e) = (n : ℤ) := by
  rw [nextRound, Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- Every `nextCountReadout N M k z` is an integer between `0` and the population size `N`,
inclusive. -/
theorem nextCountReadout_valid (N M k : ℕ) (z : Fin M) :
    0 ≤ nextCountReadout N M k z ∧ nextCountReadout N M k z ≤ N := by
  have hrec := native_ae_computed_scalar_precision M k z
  have hrec0 : (0:ℝ) ≤ (nativeAEDecode M k z : ℝ) := by exact_mod_cast hrec.1
  have hrec1 : (nativeAEDecode M k z : ℝ) ≤ 1 := by exact_mod_cast hrec.2.1
  have hN' : (0:ℝ) ≤ (N : ℝ) := by positivity
  have h0 : (0:ℝ) ≤ (N : ℝ) * (nextLabelRecord M k z : ℝ) := by
    rw [nextLabelRecord]
    exact mul_nonneg hN' hrec0
  have h1 : (N : ℝ) * (nextLabelRecord M k z : ℝ) ≤ (N : ℝ) := by
    rw [nextLabelRecord]
    simpa using! mul_le_mul_of_nonneg_left hrec1 hN'
  have hfl0 : (0:ℤ) ≤ Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) := by
    have hlt : (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
        < (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have h2 : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) > -1 := by
      linarith
    have h3 : (-1:ℤ) < Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) := by
      exact_mod_cast h2
    omega
  have hfl1 : Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) ≤ (N : ℤ) := by
    have hle : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
        ≤ (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2 := Int.floor_le _
    have hlt : (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
        < (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have h2 : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
        < (N : ℝ) + 1 := by linarith
    have h3 : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
        < ((N + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using! h2
    have h4 : Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) < (N + 1 : ℕ) := by
      exact_mod_cast h3
    omega
  unfold nextCountReadout
  exact ⟨hfl0, hfl1⟩

/-- The refined integer readout differs from `N * aeEstimate M z` by at most `N * ((2 : ℝ)⁻¹) ^
k + 1 / 2`, combining scalar decoding error with rounding error. -/
theorem nextCountReadout_error (N M k : ℕ) (z : Fin M) :
    |(nextCountReadout N M k z : ℝ) - (N : ℝ) * aeEstimate M z|
      ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 := by
  have hrec := native_ae_computed_scalar_precision M k z
  have hrec' : |((nativeAEDecode M k z : ℝ)) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := hrec.2.2
  have hround : |(nextRound ((N : ℝ) * (nextLabelRecord M k z : ℝ)) : ℝ)
      - (N : ℝ) * (nextLabelRecord M k z : ℝ)| ≤ 1 / 2 := by
    apply nextRound_error
  have hscaled : |(N : ℝ) * (nextLabelRecord M k z : ℝ)
      - (N : ℝ) * aeEstimate M z| ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := by
    have hfac : (N : ℝ) * (nextLabelRecord M k z : ℝ) - (N : ℝ) * aeEstimate M z
        = (N : ℝ) * ((nextLabelRecord M k z : ℝ) - aeEstimate M z) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N : ℝ))]
    have hrec'' : |(nextLabelRecord M k z : ℝ) - aeEstimate M z|
        ≤ ((2 : ℝ)⁻¹) ^ k := by
      rw [nextLabelRecord]
      exact hrec'
    exact mul_le_mul_of_nonneg_left hrec'' (by positivity)
  calc
    |(nextCountReadout N M k z : ℝ) - (N : ℝ) * aeEstimate M z|
        ≤ |((nextCountReadout N M k z : ℝ)
              - (N : ℝ) * (nextLabelRecord M k z : ℝ))|
          + |(N : ℝ) * (nextLabelRecord M k z : ℝ)
              - (N : ℝ) * aeEstimate M z| := abs_sub_le _ _ _
    _ ≤ 1 / 2 + (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := add_le_add hround hscaled
    _ = (N : ℝ) * ((2 : ℝ)⁻¹) ^ k + 1 / 2 := by ring

/-- If `N * ((2 : ℝ)⁻¹) ^ k ≤ 1`, the refined count readout and `countLabelReadoutNearest N M z`
differ by at most one. -/
theorem nextCountReadout_one_flip (N M k : ℕ) (z : Fin M)
    (hprec : (N : ℝ) * ((2 : ℝ)⁻¹) ^ k ≤ 1) :
    |(nextCountReadout N M k z : ℝ) - (countLabelReadoutNearest N M z : ℝ)| ≤ 1 := by
  have hrec := native_ae_computed_scalar_precision M k z
  have hrec' : |((nativeAEDecode M k z : ℝ)) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := hrec.2.2
  have hN' : (0:ℝ) ≤ (N : ℝ) := by positivity
  have hrec0 : (0:ℝ) ≤ (nativeAEDecode M k z : ℝ) := by exact_mod_cast hrec.1

  have hxy : |(N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
      - ((N : ℝ) * aeEstimate M z + 1 / 2)| ≤ 1 := by
    have hfac : (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
        - ((N : ℝ) * aeEstimate M z + 1 / 2)
        = (N : ℝ) * (nextLabelRecord M k z : ℝ) - (N : ℝ) * aeEstimate M z := by ring
    rw [hfac, nextLabelRecord]
    have hrec'' : |(nativeAEDecode M k z : ℝ) - aeEstimate M z|
        ≤ ((2 : ℝ)⁻¹) ^ k := hrec'
    have hfac' : (N : ℝ) * ((nativeAEDecode M k z : ℚ) : ℝ) - (N : ℝ) * aeEstimate M z
        = (N : ℝ) * (((nativeAEDecode M k z : ℚ) : ℝ) - aeEstimate M z) := by ring
    rw [hfac', abs_mul, abs_of_nonneg hN']
    calc
      (N : ℝ) * |((nativeAEDecode M k z : ℚ) : ℝ) - aeEstimate M z|
          ≤ (N : ℝ) * ((2 : ℝ)⁻¹) ^ k := mul_le_mul_of_nonneg_left hrec'' hN'
      _ ≤ 1 := hprec
  have hx0 : 0 ≤ (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2 := by
    rw [nextLabelRecord]
    have hmul : (0:ℝ) ≤ (N : ℝ) * (nativeAEDecode M k z : ℝ) := mul_nonneg hN' hrec0
    linarith
  have hy0 : 0 ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := by
    have hmul : (0:ℝ) ≤ (N : ℝ) * aeEstimate M z :=
      mul_nonneg hN' (by exact_mod_cast (aeEstimate_mem M z).1)
    linarith
  have hI1 : Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2)
      ≤ Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) + 1 := by
    have hfl : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
        ≤ (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2 := Int.floor_le _
    have hfl' : (N : ℝ) * aeEstimate M z + 1 / 2
        < (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hbound : (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
        ≤ (N : ℝ) * aeEstimate M z + 1 / 2 + 1 := by
      rw [abs_le] at hxy
      linarith
    have h2 : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
        < (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) + 2 := by linarith
    have h3 : Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2)
        < Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) + 2 := by
      exact_mod_cast h2
    omega
  have hI2 : Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2)
      ≤ Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) + 1 := by
    have hfl : (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
        ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := Int.floor_le _
    have hfl' : (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2
        < (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hbound : (N : ℝ) * aeEstimate M z + 1 / 2
        ≤ (N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2 + 1 := by
      rw [abs_le] at hxy
      linarith
    have h2 : (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
        < (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) + 2 := by linarith
    have h3 : Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2)
        < Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) + 2 := by
      exact_mod_cast h2
    omega
  have hI1r : (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
      ≤ (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) + 1 := by
    exact_mod_cast hI1
  have hI2r : (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)
      ≤ (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) + 1 := by
    exact_mod_cast hI2
  have hd : |(Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ)
      - (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hnear : (countLabelReadoutNearest N M z : ℝ)
      = (Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) : ℝ) := by
    rw [countLabelReadoutNearest]
    have hb := intFloor_eq_natFloor hy0
    rw [hb, Int.cast_natCast]
  have hfloor : (nextCountReadout N M k z : ℝ)
      = (Int.floor ((N : ℝ) * (nextLabelRecord M k z : ℝ) + 1 / 2) : ℝ) := by
    unfold nextCountReadout
    rfl
  rw [hfloor, hnear]
  exact hd

/-- For a positive population size `N`, the initial exact-counting grid `exactCountM₀ N` has
size at least two. -/
theorem exactCountM₀_ge_two {N : ℕ} (hN : 0 < N) : 2 ≤ exactCountM₀ N := by
  have hpi : (2:ℝ) < Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hsqrt : (1:ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N by omega)
  have hval : (1:ℝ) < 14 * Real.pi * Real.sqrt (N : ℝ) := by
    nlinarith
  have hceil : 1 < exactCountM₀ N := by
    rw [exactCountM₀]
    exact (Nat.lt_ceil (n := 1) (a := 14 * Real.pi * Real.sqrt (N : ℝ))).2 (by simpa using! hval)
  omega

/-- The adaptive grid `exactCountGrid N t'₁ t'₂` has size at least two whenever both rough
estimates lie in `[0, N]`. -/
theorem exactCountGrid_ge_two {N : ℕ} (t'₁ t'₂ : ℝ)
    (h1 : 0 ≤ t'₁) (h1' : t'₁ ≤ (N : ℝ))
    (h2 : 0 ≤ t'₂) (h2' : t'₂ ≤ (N : ℝ)) :
    2 ≤ exactCountGrid N t'₁ t'₂ := by
  have hr1 : 1 ≤ exactCountRough N t'₁ := by
    rw [exactCountRough, Real.one_le_sqrt]
    have ha : (1:ℝ) ≤ t'₁ + 1 := by linarith
    have hb : (1:ℝ) ≤ (N : ℝ) - t'₁ + 1 := by linarith
    have hc : (0:ℝ) ≤ (t'₁ + 1) * ((N : ℝ) - t'₁ + 1) := by positivity
    nlinarith
  have hr2 : 1 ≤ exactCountRough N t'₂ := by
    rw [exactCountRough, Real.one_le_sqrt]
    have ha : (1:ℝ) ≤ t'₂ + 1 := by linarith
    have hb : (1:ℝ) ≤ (N : ℝ) - t'₂ + 1 := by linarith
    have hc : (0:ℝ) ≤ (t'₂ + 1) * ((N : ℝ) - t'₂ + 1) := by positivity
    nlinarith
  have hmin : 1 ≤ min (exactCountRough N t'₁) (exactCountRough N t'₂) :=
    le_min hr1 hr2
  have hval : (1:ℝ) < 30 * min (exactCountRough N t'₁) (exactCountRough N t'₂) := by
    nlinarith
  have hceil : 1 < exactCountGrid N t'₁ t'₂ := by
    rw [exactCountGrid]
    exact (Nat.lt_ceil (n := 1)
      (a := 30 * min (exactCountRough N t'₁) (exactCountRough N t'₂))).2 (by simpa using! hval)
  omega

/-- For positive `N`, feeding any two scaled amplitude estimates from `exactCountM₀ N` into
`exactCountGrid` produces a grid of size at least two. -/
theorem exactCountGrid_ge_two_on_estimates {N : ℕ} (hN : 0 < N)
    (z₁ z₂ : Fin (exactCountM₀ N)) :
    2 ≤ exactCountGrid N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁)
      ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) := by
  have he₁ := aeEstimate_mem (exactCountM₀ N) z₁
  have he₂ := aeEstimate_mem (exactCountM₀ N) z₂
  have hN' : (0:ℝ) ≤ (N : ℝ) := by positivity
  apply exactCountGrid_ge_two
  · have hmul : (0:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ :=
      mul_nonneg hN' (by exact_mod_cast he₁.1)
    exact hmul
  · have hle : aeEstimate (exactCountM₀ N) z₁ ≤ 1 := he₁.2
    simpa using! mul_le_mul_of_nonneg_left hle hN'
  · have hmul : (0:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ :=
      mul_nonneg hN' (by exact_mod_cast he₂.1)
    exact hmul
  · have hle : aeEstimate (exactCountM₀ N) z₂ ≤ 1 := he₂.2
    simpa using! mul_le_mul_of_nonneg_left hle hN'

/-- For positive `N`, the adaptive exact-counting grid built from any two scaled amplitude
estimates on `exactCountM₀ N` has size at least thirty. -/
theorem exactCountGrid_ge_thirty {N : ℕ} (hN : 0 < N)
    (z₁ z₂ : Fin (exactCountM₀ N)) :
    30 ≤ exactCountGrid N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁)
      ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) := by
  have he₁ := aeEstimate_mem (exactCountM₀ N) z₁
  have he₂ := aeEstimate_mem (exactCountM₀ N) z₂
  have hN' : (0:ℝ) ≤ (N : ℝ) := by positivity
  have hr1 : 1 ≤ exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁) := by
    rw [exactCountRough, Real.one_le_sqrt]
    have ha : (1:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ + 1 := by
      have : (0:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ :=
        mul_nonneg hN' (by exact_mod_cast he₁.1)
      linarith
    have hb : (1:ℝ) ≤ (N : ℝ) - (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ + 1 := by
      have hle : aeEstimate (exactCountM₀ N) z₁ ≤ 1 := he₁.2
      have hmul : (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hle hN'
      linarith
    have hc : (0:ℝ) ≤ ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁ + 1)
        * ((N : ℝ) - (N : ℝ) * aeEstimate (exactCountM₀ N) z₁ + 1) := by positivity
    nlinarith
  have hr2 : 1 ≤ exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) := by
    rw [exactCountRough, Real.one_le_sqrt]
    have ha : (1:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ + 1 := by
      have : (0:ℝ) ≤ (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ :=
        mul_nonneg hN' (by exact_mod_cast he₂.1)
      linarith
    have hb : (1:ℝ) ≤ (N : ℝ) - (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ + 1 := by
      have hle : aeEstimate (exactCountM₀ N) z₂ ≤ 1 := he₂.2
      have hmul : (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hle hN'
      linarith
    have hc : (0:ℝ) ≤ ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂ + 1)
        * ((N : ℝ) - (N : ℝ) * aeEstimate (exactCountM₀ N) z₂ + 1) := by positivity
    nlinarith
  have hmin : 1 ≤ min (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁))
      (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂)) := le_min hr1 hr2
  have hval : (29:ℝ) < 30 * min (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁))
      (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂)) := by nlinarith
  have hceil : 29 < exactCountGrid N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁)
      ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂) := by
    rw [exactCountGrid]
    exact (Nat.lt_ceil (n := 29)
      (a := 30 * min (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₁))
        (exactCountRough N ((N : ℝ) * aeEstimate (exactCountM₀ N) z₂)))).2 (by simpa using! hval)
  omega

/-- For a bounded observable, positive `N` and `eps`, and `0 < nu ≤ 1 / 4`, the access ledger at
each pilot-selected precision is bounded by the ledger at `unknownSigmaWorstPrecision eps`.
The finite precision bound `hk` supplies the pilot execution's precision cap. -/
theorem unknownSigma_worst_path_accesses
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (ωp : Fin N → I) :
    unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp)
      ≤ unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps) := by
  have h := unknownSigma_budget_worst_path_pilot A j hA f nu eps N h K r hk
      hN hf hnu hnu1 heps ωp
  unfold unknownSigmaLedgerAccesses unknownSigmaAccesses
  exact Nat.add_le_add (Nat.add_le_add h.1 h.2.2.2.1) h.2.2.2.2.1

/-- The two-dimensional rotation `smallRotation (Real.pi / 4)`, used to prepare a uniform source
on `Fin 2` from basis state zero. -/
noncomputable def nextUniformSource : Matrix (Fin 2) (Fin 2) ℂ :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation (Real.pi / 4)

/-- The uniform-source preparation matrix `nextUniformSource` is unitary. -/
theorem nextUniformSource_unitary :
    nextUniformSource ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation_unitary _

/-- Preparing basis state zero with `nextUniformSource` gives each outcome in `Fin 2`
probability `1 / 2` under `signedMeanSource`. -/
theorem nextUniformSource_prob (i : Fin 2) :
    (signedMeanSource nextUniformSource (0 : Fin 2) nextUniformSource_unitary).prob i
      = 1 / 2 := by
  have hone : (signedMeanSource nextUniformSource (0 : Fin 2)
      nextUniformSource_unitary).prob 1 = 1 / 2 := by
    show BornProb
        (ApplyGate nextUniformSource (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) 1 = 1 / 2
    have h1 : BornProb (ApplyGate nextUniformSource (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) 1
        = MeasureProb (ApplyGate nextUniformSource (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) {1} := by
      symm
      simp [MeasureProb]
    have h := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation_success (Real.pi / 4)
    rw [h1]
    simp only [nextUniformSource]
    rw [h]
    have hsin : (Real.sin (Real.pi / 4)) ^ 2 = 1 / 2 := by
      rw [Real.sin_pi_div_four]
      have hsq : (Real.sqrt 2 / 2 : ℝ)^2 = (Real.sqrt 2 : ℝ)^2 / 4 := by ring
      rw [hsq, Real.sq_sqrt (by norm_num)]
      norm_num
    exact hsin
  have hsum : (∑ j : Fin 2, (signedMeanSource nextUniformSource (0 : Fin 2)
      nextUniformSource_unitary).prob j) = 1 :=
    (signedMeanSource nextUniformSource (0 : Fin 2) nextUniformSource_unitary).sum_one
  rw [Fin.sum_univ_two] at hsum
  by_cases hi : i = 1
  · subst hi
    exact hone
  · have h0 : (signedMeanSource nextUniformSource (0 : Fin 2)
        nextUniformSource_unitary).prob 0 = 1 / 2 := by
      rw [hone] at hsum
      linarith
    have hi' : i.val ≠ 1 := by
      intro hv
      apply hi
      exact Fin.ext hv
    have hival : i.val = 0 := by
      have := i.isLt
      omega
    have hieq : i = 0 := Fin.ext hival
    subst hieq
    exact h0

/-- The pilot event that either the empirical first moment or the empirical second moment of `f`
differs from its source expectation by more than `nu`. -/
abbrev nextPilotBadMoment (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (N : ℕ) (nu : ℝ) : (Fin N → I) → Prop :=
  fun ωp =>
    (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) ωp
        - (signedMeanSource A j hA).expect (fun i => (f i : ℝ))| ∨
      (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) ωp
        - (signedMeanSource A j hA).expect (fun i => (f i : ℝ)^2)|

/-- For `N > 0` and `nu > 0`, the probability of `nextPilotBadMoment` is at most the sum of the
source's second and fourth moments of `f`, divided by `N * nu ^ 2`. -/
theorem nextPilotBadMoment_mass
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ)
    (N : ℕ) (nu : ℝ) (hN : 0 < N) (hnu : 0 < nu) :
    (signedMeanSource A j hA).probEvent (L := N) (nextPilotBadMoment A j hA f N nu)
      ≤ (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
          / ((N : ℝ)*(nu : ℝ)^2) := by
  unfold nextPilotBadMoment
  exact unknownSigma_pilot_moment_failure_mass A j hA f N nu hN hnu

/-- If `N > 0`, `nu > 0`, `(8 / 9) ^ r < δ`, and the second-plus-fourth moment sum is at most `N
* nu ^ 2 * (δ - (8 / 9) ^ r)`, then the pilot bad-moment probability is at most `δ - (8 / 9)
^ r`. -/
theorem nextPilotBadMoment_mass_le_reserve
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ)
    (N : ℕ) (nu : ℝ) (r : ℕ) (hN : 0 < N) (hnu : 0 < nu)
    (δ : ℝ) (hδ : (8/9 : ℝ)^r < δ)
    (hreserve : unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        ≤ (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) :
    (signedMeanSource A j hA).probEvent (L := N) (nextPilotBadMoment A j hA f N nu)
      ≤ δ - (8/9 : ℝ)^r := by
  have hN' : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnu' : (0:ℝ) < nu := by exact_mod_cast hnu
  have hpos : (0:ℝ) < (N : ℝ) * (nu : ℝ)^2 := by positivity
  have hbound := nextPilotBadMoment_mass A j hA f N nu hN hnu
  have hdiv : (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
      / ((N : ℝ)*(nu : ℝ)^2)
      ≤ ((N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) / ((N : ℝ)*(nu : ℝ)^2) :=
    div_le_div_of_nonneg_right hreserve (by positivity)
  have hres : ((N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) / ((N : ℝ)*(nu : ℝ)^2)
      = δ - (8/9 : ℝ)^r := by
    rw [div_eq_iff (by positivity : (N : ℝ) * (nu : ℝ)^2 ≠ 0)]
    ring
  linarith

/-- For any `N`, positive `nu`, and `δ > (8 / 9) ^ r`, there is a unitary two-point source and a
rational observable with positive second moment whose second-plus-fourth moment sum exceeds
`N * nu ^ 2 * (δ - (8 / 9) ^ r)`. Thus this moment reserve does not hold uniformly over all
rational observables. -/
theorem unknownSigma_tail_promise_necessary
    (N : ℕ) (nu : ℝ) (hnu : 0 < nu) (δ : ℝ) (r : ℕ) (hδ : (8/9 : ℝ)^r < δ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2)
      (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (f : Fin 2 → ℚ),
      unknownSigmaSecondMoment A j hA f > 0 ∧
      unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
        > (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r) := by
  have hnu' : (0:ℝ) < nu := by exact_mod_cast hnu

  have hD : (0:ℝ) < δ - (8/9 : ℝ)^r := by linarith [hδ]
  have hres : (0:ℝ) ≤ (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r) := by positivity

  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r))
  have hn' : 4 * (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r) < (n : ℝ) := hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith

  have hx : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hx2 : ((n + 1 : ℕ) : ℝ)^2 ≥ ((n + 1 : ℕ) : ℝ) := by
    nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ) - 1)]
  have hx2one : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ)^2 := by linarith
  have hx4 : ((n + 1 : ℕ) : ℝ)^4 ≥ ((n + 1 : ℕ) : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hx2one (sq_nonneg (((n + 1 : ℕ) : ℝ)))
    nlinarith [hmul]
  have hx1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h4 : 4 * (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)
      < ((n + 1 : ℕ) : ℝ)^4 := by linarith
  refine ⟨nextUniformSource, (0 : Fin 2), nextUniformSource_unitary,
    fun i => if i = 1 then (n + 1 : ℕ) else 0, ?_, ?_⟩
  · have hprob0 := nextUniformSource_prob (0 : Fin 2)
    have hprob1 := nextUniformSource_prob (1 : Fin 2)
    have hmom : unknownSigmaSecondMoment nextUniformSource (0 : Fin 2)
        nextUniformSource_unitary (fun i => if i = 1 then (n + 1 : ℕ) else 0)
        = ((n + 1 : ℕ) : ℝ)^2 / 2 := by
      unfold unknownSigmaSecondMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
      rw [Fin.sum_univ_two]
      simp only [show (0 : Fin 2) ≠ 1 by decide]
      rw [hprob0, hprob1]
      push_cast
      ring
    rw [hmom]
    have hxpos : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith [sq_pos_of_pos hxpos]
  · have hprob0 := nextUniformSource_prob (0 : Fin 2)
    have hprob1 := nextUniformSource_prob (1 : Fin 2)
    have h2mom : unknownSigmaSecondMoment nextUniformSource (0 : Fin 2)
        nextUniformSource_unitary (fun i => if i = 1 then (n + 1 : ℕ) else 0)
        = ((n + 1 : ℕ) : ℝ)^2 / 2 := by
      unfold unknownSigmaSecondMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
      rw [Fin.sum_univ_two]
      simp only [show (0 : Fin 2) ≠ 1 by decide]
      rw [hprob0, hprob1]
      push_cast
      ring
    have h4mom : unknownSigmaFourthMoment nextUniformSource (0 : Fin 2)
        nextUniformSource_unitary (fun i => if i = 1 then (n + 1 : ℕ) else 0)
        = ((n + 1 : ℕ) : ℝ)^4 / 2 := by
      unfold unknownSigmaFourthMoment Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
      rw [Fin.sum_univ_two]
      simp only [show (0 : Fin 2) ≠ 1 by decide]
      rw [hprob0, hprob1]
      push_cast
      ring
    rw [h2mom, h4mom]

    have hhalf : (2:ℝ) * ((n + 1 : ℕ) : ℝ)^4 / 2 = ((n + 1 : ℕ) : ℝ)^4 := by ring
    nlinarith [h4, hhalf]

/-- The per-trial query parameter `(k + 2) * (2 * layerRepetitions k + 1)` for precision `k`. -/
noncomputable def nextTrialQueries (k : ℕ) : ℕ :=
  (k + 2) * (2 * layerRepetitions k + 1)

/-- The value of `nextTrialQueries` at the worst-case precision `unknownSigmaWorstPrecision
eps`. -/
noncomputable def nextWorstTrialQueries (eps : ℚ) : ℕ :=
  nextTrialQueries (unknownSigmaWorstPrecision eps)

/-- The layer grid size `layerGrid (unknownSigmaWorstPrecision eps)` associated with the
worst-case precision. -/
noncomputable def nextWorstLayerGrid (eps : ℚ) : ℕ :=
  layerGrid (unknownSigmaWorstPrecision eps)

/-- The inverse-layer grid count `layerGrid (unknownSigmaWorstPrecision eps) - 1`, using
natural-number subtraction. -/
noncomputable def nextWorstLayerGridInv (eps : ℚ) : ℕ :=
  layerGrid (unknownSigmaWorstPrecision eps) - 1

/-- Expands all seven fields of `unknownSigmaLedger N r k` into explicit formulas in `N`, `2 * r
+ 1`, `nextTrialQueries k`, and `layerGrid k`. In particular, inverse-layer accesses and
queries have the same count. -/
theorem unknownSigmaLedger_expand (N r k : ℕ) :
    (unknownSigmaLedger N r k).sourcePreparations = N + (2*r+1) ∧
    (unknownSigmaLedger N r k).layerCopies
      = (2*r+1) * (2 * nextTrialQueries k) ∧
    (unknownSigmaLedger N r k).measurements
      = N + (2*r+1) * (1 + 2*nextTrialQueries k) ∧
    (unknownSigmaLedger N r k).layerForward
      = (2*r+1) * (2 * nextTrialQueries k * layerGrid k) ∧
    (unknownSigmaLedger N r k).layerInverse
      = (2*r+1) * (2 * nextTrialQueries k * (layerGrid k - 1)) ∧
    (unknownSigmaLedger N r k).queries
      = (2*r+1) * (2 * nextTrialQueries k * (layerGrid k - 1)) ∧
    (unknownSigmaLedger N r k).gates
      = N + (2*r+1) * (1
          + 2*nextTrialQueries k * (5*(layerGrid k - 1)+3)) := by
  unfold unknownSigmaLedger
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Under the bounded-observable and positive-parameter hypotheses, every pilot-selected ledger
is componentwise bounded by the ledger at `unknownSigmaWorstPrecision eps`. It also gives
the explicit formulas for all seven fields of that worst-case ledger. -/
theorem unknownSigma_worst_path_components
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (heps : 0 < eps) (ωp : Fin N → I) :
    unknownSigmaLedgerLe
        (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp))
        (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).sourcePreparations
        = N + (2*r+1) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).layerCopies
        = (2*r+1) * (2 * nextTrialQueries (unknownSigmaWorstPrecision eps)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).measurements
        = N + (2*r+1) * (1 + 2*nextTrialQueries (unknownSigmaWorstPrecision eps)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).layerForward
        = (2*r+1) * (2 * nextTrialQueries (unknownSigmaWorstPrecision eps)
            * layerGrid (unknownSigmaWorstPrecision eps)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).layerInverse
        = (2*r+1) * (2 * nextTrialQueries (unknownSigmaWorstPrecision eps)
            * (layerGrid (unknownSigmaWorstPrecision eps) - 1)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).queries
        = (2*r+1) * (2 * nextTrialQueries (unknownSigmaWorstPrecision eps)
            * (layerGrid (unknownSigmaWorstPrecision eps) - 1)) ∧
    (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).gates
        = N + (2*r+1) * (1 + 2*nextTrialQueries (unknownSigmaWorstPrecision eps)
            * (5*(layerGrid (unknownSigmaWorstPrecision eps) - 1)+3)) := by
  have h := unknownSigma_budget_worst_path_pilot A j hA f nu eps N h K r hk
      hN hf hnu hnu1 heps ωp
  have he := unknownSigmaLedger_expand N r (unknownSigmaWorstPrecision eps)
  exact ⟨h, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩

/-- For the full record assembled from pilot sample `ωp` and trial record `ωt`,
`unknownSigmaResources` equals the ledger at the pilot-selected precision. The remaining
conclusions expand all seven resource fields into explicit formulas at that precision. -/
theorem unknownSigma_component_budget
    (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (f : I → ℚ) (nu eps : ℚ) (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (ωp : Fin N → I) (ωt : unknownSigmaTrialRecord I r (pilotPrecision N h f nu eps ωp)) :
    unknownSigmaResources A j hA f nu eps N h K r hk
        (⟨unknownSigmaPilotIndex N h f nu eps K hk ωp, (ωp, ωt)⟩ :
          unknownSigmaFullRecord I N K r)
      = unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).sourcePreparations
        = N + (2*r+1) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).layerCopies
        = (2*r+1) * (2 * nextTrialQueries (pilotPrecision N h f nu eps ωp)) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).measurements
        = N + (2*r+1) * (1 + 2*nextTrialQueries (pilotPrecision N h f nu eps ωp)) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).layerForward
        = (2*r+1) * (2 * nextTrialQueries (pilotPrecision N h f nu eps ωp)
            * layerGrid (pilotPrecision N h f nu eps ωp)) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).layerInverse
        = (2*r+1) * (2 * nextTrialQueries (pilotPrecision N h f nu eps ωp)
            * (layerGrid (pilotPrecision N h f nu eps ωp) - 1)) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).queries
        = (2*r+1) * (2 * nextTrialQueries (pilotPrecision N h f nu eps ωp)
            * (layerGrid (pilotPrecision N h f nu eps ωp) - 1)) ∧
    (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).gates
        = N + (2*r+1) * (1 + 2*nextTrialQueries (pilotPrecision N h f nu eps ωp)
            * (5*(layerGrid (pilotPrecision N h f nu eps ωp) - 1)+3)) := by
  have hres := unknownSigma_resources_eq A j hA f nu eps N h K r hk
    (⟨unknownSigmaPilotIndex N h f nu eps K hk ωp, (ωp, ωt)⟩ : unknownSigmaFullRecord I N K r)
  have he := unknownSigmaLedger_expand N r (pilotPrecision N h f nu eps ωp)
  exact ⟨hres, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩

/-- The amplitude-estimation error window `2 * Real.pi * Real.sqrt (a * (1 - a)) / M + Real.pi ^
2 / M ^ 2` from the BHMT bound [BrassardEtAl2002]. -/
noncomputable def nextAeWindow (M : ℕ) (a : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2

/-- The simplified amplitude-estimation window `2 * Real.pi * Real.sqrt a / M + Real.pi ^ 2 / M
^ 2`. -/
noncomputable def nextWindowBound (M : ℕ) (a : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt a / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2

/-- The natural ceiling of `16 * Real.pi / (eps * Real.sqrt a₀)`, used as the
amplitude-estimation grid for a positive amplitude lower bound `a₀`. -/
noncomputable def nextRelativeGrid (a₀ eps : ℝ) : ℕ :=
  ⌈16 * Real.pi / (eps * Real.sqrt a₀)⌉₊

/-- For `0 ≤ a ≤ 1`, the BHMT window `nextAeWindow M a` is bounded by the simpler window
`nextWindowBound M a`. -/
theorem nextAeWindow_le_bound (M : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    nextAeWindow M a ≤ nextWindowBound M a := by
  have hprod : a * (1 - a) ≤ a := by nlinarith
  have hsqrt : Real.sqrt (a * (1 - a)) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hmul : 2 * Real.pi * Real.sqrt (a * (1 - a)) ≤ 2 * Real.pi * Real.sqrt a :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hdiv : (2 * Real.pi * Real.sqrt (a * (1 - a))) / (M : ℝ)
      ≤ (2 * Real.pi * Real.sqrt a) / (M : ℝ) :=
    div_le_div_of_nonneg_right hmul (by positivity)
  unfold nextAeWindow nextWindowBound
  linarith

/-- If `0 < a₀ ≤ a ≤ 1`, `0 < eps ≤ 1`, and `0 ≤ u ≤ eps * Real.sqrt a₀ / (16 * Real.pi)`, then
`2 * Real.pi * Real.sqrt (a * (1 - a)) * u + Real.pi ^ 2 * u ^ 2 ≤ eps * a`. -/
private theorem nextAeWindow_poly {a₀ a eps u : ℝ}
    (ha0 : 0 < a₀) (ha0a : a₀ ≤ a) (ha1 : a ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ eps * Real.sqrt a₀ / (16 * Real.pi)) :
    2 * Real.pi * Real.sqrt (a * (1 - a)) * u + Real.pi ^ 2 * u ^ 2 ≤ eps * a := by
  have ha : 0 ≤ a := le_trans (le_of_lt ha0) ha0a
  have hsqrt1 : Real.sqrt (a * (1 - a)) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrt2 : Real.sqrt (a * a₀) ≤ Real.sqrt (a * a) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrt3 : Real.sqrt (a * a) = a := Real.sqrt_mul_self ha
  have hprod : Real.sqrt a * Real.sqrt a₀ = Real.sqrt (a * a₀) :=
    (Real.sqrt_mul ha a₀).symm

  have hA : 2 * Real.pi * Real.sqrt (a * (1 - a)) * u
      ≤ 2 * Real.pi * Real.sqrt a * u := by
    gcongr
  have hB : 2 * Real.pi * Real.sqrt a * u
      ≤ 2 * Real.pi * Real.sqrt a * (eps * Real.sqrt a₀ / (16 * Real.pi)) := by
    gcongr
  have hC : 2 * Real.pi * Real.sqrt a * (eps * Real.sqrt a₀ / (16 * Real.pi))
      ≤ (eps / 8) * a := by
    have h3 : (eps / 8) * Real.sqrt (a * a₀) ≤ (eps / 8) * a := by
      rw [hsqrt3] at hsqrt2
      exact mul_le_mul_of_nonneg_left hsqrt2 (by positivity : (0:ℝ) ≤ eps / 8)
    calc 2 * Real.pi * Real.sqrt a * (eps * Real.sqrt a₀ / (16 * Real.pi))
        = (eps / 8) * (Real.sqrt a * Real.sqrt a₀) := by field_simp; ring
      _ = (eps / 8) * Real.sqrt (a * a₀) := by rw [hprod]
      _ ≤ (eps / 8) * a := h3

  have hu2 : u ^ 2 ≤ (eps * Real.sqrt a₀ / (16 * Real.pi)) ^ 2 := by
    have hnonneg : 0 ≤ eps * Real.sqrt a₀ / (16 * Real.pi) := by positivity
    exact (sq_le_sq₀ hu0 hnonneg).2 hu1
  have hD : Real.pi ^ 2 * u ^ 2 ≤ eps ^ 2 * a / 256 := by
    have heq : Real.pi ^ 2 * (eps * Real.sqrt a₀ / (16 * Real.pi)) ^ 2
        = eps ^ 2 * a₀ / 256 := by
      field_simp
      rw [Real.sq_sqrt (le_of_lt ha0)]
      ring
    calc Real.pi ^ 2 * u ^ 2
        ≤ Real.pi ^ 2 * (eps * Real.sqrt a₀ / (16 * Real.pi)) ^ 2 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
      _ = eps ^ 2 * a₀ / 256 := heq
      _ ≤ eps ^ 2 * a / 256 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha0a (by positivity))
          (by positivity)

  have hsum : 2 * Real.pi * Real.sqrt (a * (1 - a)) * u + Real.pi ^ 2 * u ^ 2
      ≤ (eps / 8) * a + eps ^ 2 * a / 256 := by linarith
  have hfin : (eps / 8) * a + eps ^ 2 * a / 256 ≤ eps * a := by
    have h1 : eps ^ 2 * a ≤ eps * a := by
      have heps2 : eps ^ 2 ≤ eps := by nlinarith
      exact mul_le_mul_of_nonneg_right heps2 ha
    have h2 : (eps / 8) * a = eps * a / 8 := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
    have h3 : eps ^ 2 * a / 256 ≤ eps * a / 256 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : eps * a / 8 + eps * a / 256 ≤ eps * a := by
      have hpos : 0 ≤ eps * a := by positivity
      have h5 : eps * a * (1/8 + 1/256) ≤ eps * a := by
        have h5' : ((1/8:ℝ) + (1/256:ℝ)) ≤ 1 := by norm_num
        have := mul_le_mul_of_nonneg_left h5' hpos
        simpa using! this
      have h6 : eps * a / 8 + eps * a / 256 = eps * a * ((1/8:ℝ) + (1/256:ℝ)) := by ring
      rw [h6]
      exact h5
    calc (eps / 8) * a + eps ^ 2 * a / 256
        = eps * a / 8 + eps ^ 2 * a / 256 := by rw [h2]
      _ ≤ eps * a / 8 + eps * a / 256 := add_le_add_right h3 (eps * a / 8)
      _ ≤ eps * a := h4
  linarith

/-- For positive `M`, `0 < a₀ ≤ a ≤ 1`, and `0 < eps ≤ 1`, the grid condition `16 * Real.pi /
(eps * Real.sqrt a₀) ≤ M` makes `nextAeWindow M a` at most `eps * a`. -/
theorem nextAeWindow_le_relative {M : ℕ} {a₀ a eps : ℝ}
    (hM : 0 < M) (ha0 : 0 < a₀) (ha0a : a₀ ≤ a) (ha1 : a ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hgrid : 16 * Real.pi / (eps * Real.sqrt a₀) ≤ (M : ℝ)) :
    nextAeWindow M a ≤ eps * a := by
  have hM' : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hden : 0 < eps * Real.sqrt a₀ := by positivity
  have hmul : 16 * Real.pi ≤ (eps * Real.sqrt a₀) * (M : ℝ) := by
    calc 16 * Real.pi = (eps * Real.sqrt a₀) * (16 * Real.pi / (eps * Real.sqrt a₀)) := by
          field_simp
      _ ≤ (eps * Real.sqrt a₀) * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hgrid (le_of_lt hden)
  have hu : 1 / (M : ℝ) ≤ eps * Real.sqrt a₀ / (16 * Real.pi) := by
    rw [div_le_iff₀ hM']
    have h2 : (1:ℝ) ≤ (eps * Real.sqrt a₀ / (16 * Real.pi)) * (M : ℝ) := by
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * Real.pi)]
      linarith
    exact h2
  have hu' : 1 / (M : ℝ) ≤ eps * Real.sqrt a₀ / (16 * Real.pi) := by
    have h3 := mul_le_mul_of_nonneg_right hu (by positivity : (0:ℝ) ≤ 16 * Real.pi)
    have h4 : (1 / (M : ℝ)) * (16 * Real.pi) ≤ eps * Real.sqrt a₀ := by
      calc (1 / (M : ℝ)) * (16 * Real.pi)
          ≤ (eps * Real.sqrt a₀ / (16 * Real.pi)) * (16 * Real.pi) := h3
        _ = eps * Real.sqrt a₀ := by field_simp
    exact (le_div_iff₀ (by positivity : (0:ℝ) < 16 * Real.pi)).mpr h4
  have hpoly := nextAeWindow_poly ha0 ha0a ha1 heps heps1
    (by positivity) hu'
  have hinv : (M : ℝ)⁻¹ = 1 / (M : ℝ) := (one_div _).symm
  have h2 : 2 * Real.pi * Real.sqrt (a * (1 - a)) * (1 / (M : ℝ))
      + Real.pi ^ 2 * (1 / (M : ℝ)) ^ 2
      = 2 * Real.pi * Real.sqrt (a * (1 - a)) * (M : ℝ)⁻¹
        + Real.pi ^ 2 * (M : ℝ)⁻¹ ^ 2 := by
    rw [hinv]
  have h3 : nextAeWindow M a
      = 2 * Real.pi * Real.sqrt (a * (1 - a)) * (M : ℝ)⁻¹
        + Real.pi ^ 2 * (M : ℝ)⁻¹ ^ 2 := by
    unfold nextAeWindow
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  rw [h3, ← h2]
  exact hpoly

/-- For positive `a₀` and `eps`, `nextRelativeGrid a₀ eps` is at least `16 * Real.pi / (eps *
Real.sqrt a₀)` when cast to the reals. -/
theorem nextRelativeGrid_lower {a₀ eps : ℝ} (ha0 : 0 < a₀) (heps : 0 < eps) :
    16 * Real.pi / (eps * Real.sqrt a₀) ≤ (nextRelativeGrid a₀ eps : ℝ) := by
  exact Nat.le_ceil _

/-- For `0 < a₀ ≤ 1` and `0 < eps ≤ 1`, the relative-estimation grid `nextRelativeGrid a₀ eps`
has size at least two. -/
theorem nextRelativeGrid_two {a₀ eps : ℝ} (ha0 : 0 < a₀) (ha0' : a₀ ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) : 2 ≤ nextRelativeGrid a₀ eps := by
  have hlow : 16 * Real.pi / (eps * Real.sqrt a₀) ≤ (nextRelativeGrid a₀ eps : ℝ) :=
    nextRelativeGrid_lower ha0 heps
  have hden : 0 < eps * Real.sqrt a₀ := by positivity
  have hbig : 2 ≤ 16 * Real.pi / (eps * Real.sqrt a₀) := by
    rw [le_div_iff₀ hden]
    have hone : eps * Real.sqrt a₀ ≤ 1 := by
      have h1 : eps * Real.sqrt a₀ ≤ 1 * 1 := by
        apply mul_le_mul
        · linarith
        · exact Real.sqrt_le_one.mpr ha0'
        · exact Real.sqrt_nonneg _
        · linarith
      simpa using! h1
    have hpi : 2 ≤ 16 * Real.pi := by
      have := Real.pi_gt_three
      linarith
    linarith
  exact_mod_cast (le_trans hbig hlow)

/-- For `0 < a₀ ≤ a ≤ 1` and `0 < eps ≤ 1`, the chosen grid `nextRelativeGrid a₀ eps` gives an
amplitude-estimation window at most `eps * a`. -/
theorem nextRelativeWindow {a₀ a eps : ℝ} (ha0 : 0 < a₀) (ha0a : a₀ ≤ a) (ha1 : a ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    nextAeWindow (nextRelativeGrid a₀ eps) a ≤ eps * a := by
  have hM2 : 2 ≤ nextRelativeGrid a₀ eps :=
    nextRelativeGrid_two ha0 (le_trans ha0a ha1) heps heps1
  refine nextAeWindow_le_relative (M := nextRelativeGrid a₀ eps)
    (by omega) ha0 ha0a ha1 heps heps1 (nextRelativeGrid_lower ha0 heps)

/-- The BHMT success constant `8 / Real.pi ^ 2` is strictly greater than `2 / 3`
[BrassardEtAl2002]. -/
theorem nextBhmtConstant_gt_two_thirds : 8 / Real.pi ^ 2 > 2 / 3 := by
  have hpi : Real.pi ^ 2 < 12 := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.pi_pos.le
    nlinarith
  have hpos : 0 < Real.pi ^ 2 := by positivity
  have h1 : 2 / 3 < 8 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ hpos]
    nlinarith
  exact h1

/-- If the prepared marked probability `a` satisfies `0 < a₀ ≤ a ≤ 1` and `0 < eps ≤ 1`,
amplitude estimation on `nextRelativeGrid a₀ eps` yields absolute error at most `eps * a`
with probability at least `8 / Real.pi ^ 2`. This specializes the BHMT success bound to
relative error [BrassardEtAl2002]. -/
theorem nextRelative_success
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a₀ eps : ℝ) (ha0 : 0 < a₀) (ha0a : a₀ ≤ MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (∑ z ∈ Finset.univ.filter (fun z : Fin (nextRelativeGrid a₀ eps) =>
        |aeEstimate (nextRelativeGrid a₀ eps) z - MeasureProb (preparedAAState A j) S|
          ≤ eps * MeasureProb (preparedAAState A j) S),
      (aeLaw (nextRelativeGrid a₀ eps) A j S hA
        (nextRelativeGrid_two ha0 (le_trans ha0a ha1) heps heps1)).prob z)
      ≥ 8 / Real.pi ^ 2 := by
  have hM2 : 2 ≤ nextRelativeGrid a₀ eps :=
    nextRelativeGrid_two ha0 (le_trans ha0a ha1) heps heps1
  have hwin : nextAeWindow (nextRelativeGrid a₀ eps) (MeasureProb (preparedAAState A j) S)
      ≤ eps * MeasureProb (preparedAAState A j) S :=
    nextRelativeWindow ha0 ha0a ha1 heps heps1
  have hfrozen : (∑ z ∈ Finset.univ.filter (fun z : Fin (nextRelativeGrid a₀ eps) =>
        |aeEstimate (nextRelativeGrid a₀ eps) z - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (nextRelativeGrid a₀ eps) (MeasureProb (preparedAAState A j) S)),
      (aeLaw (nextRelativeGrid a₀ eps) A j S hA hM2).prob z) ≥ 8 / Real.pi ^ 2 := by
    simpa only [nextAeWindow] using!
      (prepared_ae_bhmt_error_and_endpoints (nextRelativeGrid a₀ eps) hM2 A j S hA).1
  have hsub : Finset.univ.filter (fun z : Fin (nextRelativeGrid a₀ eps) =>
        |aeEstimate (nextRelativeGrid a₀ eps) z - MeasureProb (preparedAAState A j) S|
          ≤ nextAeWindow (nextRelativeGrid a₀ eps) (MeasureProb (preparedAAState A j) S))
      ⊆ Finset.univ.filter (fun z : Fin (nextRelativeGrid a₀ eps) =>
        |aeEstimate (nextRelativeGrid a₀ eps) z - MeasureProb (preparedAAState A j) S|
          ≤ eps * MeasureProb (preparedAAState A j) S) := by
    intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_trans hz.2 hwin⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw (nextRelativeGrid a₀ eps) A j S hA hM2).nonneg z)
  linarith

/-- When the prepared marked probability is zero and `M ≥ 2`, the zero phase label has
probability one, decodes to amplitude zero, and satisfies the relative-error inequality for
any `eps`. -/
theorem nextRelative_zero
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (M : ℕ) (hM : 2 ≤ M) (eps : ℝ)
    (ha : MeasureProb (preparedAAState A j) S = 0) :
    ∀ z : Fin M, z.val = 0 →
      (aeLaw M A j S hA hM).prob z = 1 ∧
      aeEstimate M z = 0 ∧
      |aeEstimate M z - 0| ≤ eps * 0 := by
  intro z hzval
  have hz : z = ⟨0, by omega⟩ := Fin.ext hzval
  rw [hz]
  have hk := (offgrid_phase_geometric_and_periodic M 0 (⟨0, by omega⟩ : Fin M)
    (by omega)).2.2 (⟨0, by omega⟩ : Fin M)
  have hk' : qpeKernel M 0 (⟨0, by omega⟩ : Fin M) = 1 := by
    simpa [Qatlib.Foundations.PureStateMath.Ket] using! hk
  refine ⟨?_, ?_, ?_⟩
  · rw [aeLaw_zero_mass M hM A j S hA ha (⟨0, by omega⟩ : Fin M), hk']
    norm_num
  · simp [aeEstimate]
  · simp [aeEstimate]

/-- The amplitude-estimation window `nextAeWindow M a` is at least its quadratic term `Real.pi ^
2 / M ^ 2` for every `M` and `a`. -/
theorem nextAeWindow_ge_second (M : ℕ) (a : ℝ) :
    Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ nextAeWindow M a := by
  unfold nextAeWindow
  have hsq : 0 ≤ Real.sqrt (a * (1 - a)) := Real.sqrt_nonneg _
  have hmul : 0 ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) := by positivity
  have hdiv : 0 ≤ (2 * Real.pi * Real.sqrt (a * (1 - a))) / (M : ℝ) :=
    div_nonneg hmul (by positivity)
  linarith

/-- For every fixed grid size `M ≥ 2` and `0 < eps ≤ 1`, some amplitude `0 < a ≤ 1` has
`nextAeWindow M a > eps * a`. Thus this error window cannot certify relative accuracy
uniformly down to arbitrarily small positive amplitudes on a fixed grid. -/
theorem nextFixedGrid_insufficient (M : ℕ) (hM : 2 ≤ M) (eps : ℝ) (heps : 0 < eps)
    (heps1 : eps ≤ 1) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ nextAeWindow M a > eps * a := by
  have hMpos : (0:ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  refine ⟨Real.pi ^ 2 / (4 * (M : ℝ) ^ 2), ?_, ?_, ?_⟩
  · positivity
  · have hpi : Real.pi ≤ 2 * (M : ℝ) := by
      have h1 := Real.pi_lt_four
      have h2 : (2:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hsq : Real.pi ^ 2 ≤ (2 * (M : ℝ)) ^ 2 :=
      (sq_le_sq₀ Real.pi_pos.le (by positivity)).mpr hpi
    have h3 : (2 * (M : ℝ)) ^ 2 = 4 * (M : ℝ) ^ 2 := by ring
    have h4 : Real.pi ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by nlinarith
    have h5 : 0 < 4 * (M : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ h5]
    simpa using! h4
  · have hX : 0 ≤ Real.pi ^ 2 / (4 * (M : ℝ) ^ 2) := by positivity
    have h2 : eps * (Real.pi ^ 2 / (4 * (M : ℝ) ^ 2))
        ≤ 1 * (Real.pi ^ 2 / (4 * (M : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right heps1 hX
    have h2' : eps * (Real.pi ^ 2 / (4 * (M : ℝ) ^ 2))
        ≤ Real.pi ^ 2 / (4 * (M : ℝ) ^ 2) := by simpa using! h2
    have h3 : Real.pi ^ 2 / (4 * (M : ℝ) ^ 2) < Real.pi ^ 2 / (M : ℝ) ^ 2 := by
      have hX' : 0 < Real.pi ^ 2 / (4 * (M : ℝ) ^ 2) := by positivity
      have heq : Real.pi ^ 2 / (M : ℝ) ^ 2
          = 4 * (Real.pi ^ 2 / (4 * (M : ℝ) ^ 2)) := by field_simp
      rw [heq]
      nlinarith
    have h4 : Real.pi ^ 2 / (M : ℝ) ^ 2
        ≤ nextAeWindow M (Real.pi ^ 2 / (4 * (M : ℝ) ^ 2)) :=
      nextAeWindow_ge_second M _
    linarith

/-- If `0 < a₀ ≤ a`, `0 < eps ≤ 1`, and a real budget `M` is at least `16 * Real.pi / (eps *
Real.sqrt a₀)`, then it is also at least `16 * Real.pi / (eps * Real.sqrt a)`. -/
theorem nextRelativeGrid_forced {a₀ a eps M : ℝ} (ha0 : 0 < a₀) (ha0a : a₀ ≤ a)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hM : 16 * Real.pi / (eps * Real.sqrt a₀) ≤ M) :
    16 * Real.pi / (eps * Real.sqrt a) ≤ M := by
  have hsqrt : Real.sqrt a₀ ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
  have ha : 0 < a := lt_of_lt_of_le ha0 ha0a
  have hsqrtpos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtpos0 : 0 < Real.sqrt a₀ := Real.sqrt_pos.2 ha0
  have h2 : eps * Real.sqrt a₀ ≤ eps * Real.sqrt a :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hX : 0 ≤ 16 * Real.pi := by positivity
  have h0 : 0 < eps * Real.sqrt a := mul_pos (by positivity) hsqrtpos
  have h0' : 0 < eps * Real.sqrt a₀ := mul_pos (by positivity) hsqrtpos0
  have hone : 1 / (eps * Real.sqrt a) ≤ 1 / (eps * Real.sqrt a₀) :=
    one_div_le_one_div_of_le h0' h2
  have hone' : (eps * Real.sqrt a)⁻¹ ≤ (eps * Real.sqrt a₀)⁻¹ := by
    have h := hone
    rwa [one_div, one_div] at h
  have h3 : 16 * Real.pi / (eps * Real.sqrt a) ≤ 16 * Real.pi / (eps * Real.sqrt a₀) := by
    calc 16 * Real.pi / (eps * Real.sqrt a)
        = 16 * Real.pi * ((eps * Real.sqrt a)⁻¹) :=
          div_eq_mul_inv (16 * Real.pi) (eps * Real.sqrt a)
      _ ≤ 16 * Real.pi * ((eps * Real.sqrt a₀)⁻¹) :=
          mul_le_mul_of_nonneg_left hone' hX
      _ = 16 * Real.pi / (eps * Real.sqrt a₀) :=
          (div_eq_mul_inv (16 * Real.pi) (eps * Real.sqrt a₀)).symm
  linarith

/-- For `M ≥ 2`, prepared amplitude estimation uses `M` forward accesses, `M - 1` backward
accesses and queries, and `5 * (M - 1) + 3` gates. Its flag and Fourier access words contain
`2 * (M - 1)` and `2` fixed macros, respectively. -/
theorem nextRelative_access_counts (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    aeForwardAccesses (aeAccessWord (I := I) M) = M ∧
    aeBackwardAccesses (aeAccessWord (I := I) M) = M - 1 ∧
    QueryCount (countedAECircuit M A j) = M - 1 ∧
    GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
    aeFixedMacros (aeFlagAccessWord (I := I) M) = 2 * (M - 1) ∧
    aeFixedMacros (aeFourierAccessWord (I := I) M) = 2 := by
  have h := prepared_ae_separate_access_counts (I := I) M (by omega)
  have h2 := prepared_ae_expanded_access_and_output M hM A j S hA
  exact ⟨h.1, h.2.1, h2.1, h2.2.1, h.2.2.1, h.2.2.2⟩

/-- For `0 < a₀ ≤ 1` and `0 < eps ≤ 1`, the relative grid is at most `16 * Real.pi / (eps *
Real.sqrt a₀) + 1`, while its real-valued size minus one is at most `16 * Real.pi / (eps *
Real.sqrt a₀)`. -/
theorem nextRelative_budget {a₀ eps : ℝ} (ha0 : 0 < a₀) (ha0' : a₀ ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (nextRelativeGrid a₀ eps : ℝ) ≤ 16 * Real.pi / (eps * Real.sqrt a₀) + 1 ∧
    (nextRelativeGrid a₀ eps : ℝ) - 1 ≤ 16 * Real.pi / (eps * Real.sqrt a₀) := by
  have hpos : 0 ≤ 16 * Real.pi / (eps * Real.sqrt a₀) := by positivity
  have hceil : (nextRelativeGrid a₀ eps : ℝ)
      < 16 * Real.pi / (eps * Real.sqrt a₀) + 1 := by
    exact Nat.ceil_lt_add_one hpos
  have hlow : 16 * Real.pi / (eps * Real.sqrt a₀) ≤ (nextRelativeGrid a₀ eps : ℝ) :=
    nextRelativeGrid_lower ha0 heps
  constructor
  · linarith
  · linarith

/-- The finite set of seeds `r` for which the heuristic output `G F r` satisfies `F (G F r) =
true`. -/
def nextGoodSeeds {I : Type} [Fintype I]
    (F : I → Bool) (G : (I → Bool) → I → I) : Finset I :=
  Finset.univ.filter fun r => F (G F r) = true

/-- The Boolean validation test deciding whether the heuristic output `G F r` satisfies `F`. -/
def nextGoodSeedValid {I : Type} (F : I → Bool) (G : (I → Bool) → I → I)
    (r : I) : Bool :=
  decide (F (G F r) = true)

/-- The seed-validation test `nextGoodSeedValid F G r` returns true exactly when `r` belongs to
`nextGoodSeeds F G`. -/
theorem nextGoodSeedValid_iff {I : Type} [Fintype I]
    (F : I → Bool) (G : (I → Bool) → I → I) (r : I) :
    nextGoodSeedValid F G r = true ↔ r ∈ nextGoodSeeds F G := by
  simp [nextGoodSeedValid, nextGoodSeeds]

/-- Natural-number weights for macro gates, bits, phase queries, preparation calls, validation
calls, and forward and backward heuristic calls in the heuristic-search cost. -/
structure NextHeuristicWeights where
  gate : ℕ
  bit : ℕ
  phase : ℕ
  prepare : ℕ
  validation : ℕ
  gForward : ℕ
  gBackward : ℕ

/-- A capped seed-search trace together with its optional heuristic output and counters for
forward heuristic calls, backward heuristic calls, and predicate validations. -/
structure NextHeuristicTrace (I : Type) where
  seedTrace : CappedSearchTrace I
  output : Option I
  gForward : ℕ
  gBackward : ℕ
  fValidation : ℕ

/-- Converts a capped seed-search trace into a heuristic trace by mapping its result through `G
F`. Each of the three added call counters equals the seed trace's validation-query count. -/
def nextHeuristicRecord {I : Type} (F : I → Bool) (G : (I → Bool) → I → I)
    (tr : CappedSearchTrace I) : NextHeuristicTrace I :=
  { seedTrace := tr
  , output := tr.result.map (G F)
  , gForward := tr.validationQueries
  , gBackward := tr.validationQueries
  , fValidation := tr.validationQueries }

/-- The probability mass function obtained by geometrically scheduled search for `nextGoodSeeds
F G`, followed by `nextHeuristicRecord F G` to produce the heuristic output and resource
counters. -/
noncomputable def nextHeuristicConsumer {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ) :
    PMF (NextHeuristicTrace I) :=
  (searchForSchedule A hA j₀ (nextGoodSeeds F G) (nextGoodSeedValid F G)
    (geometricSearchSchedule M T)).map (nextHeuristicRecord F G)

/-- The weighted sum in `ℝ≥0∞` of a heuristic trace's macro gates, bits, phase queries,
preparation calls, predicate validations, and forward and backward heuristic calls. -/
noncomputable def nextHeuristicCost {I : Type} (w : NextHeuristicWeights)
    (tr : NextHeuristicTrace I) : ℝ≥0∞ :=
  (w.gate : ℝ≥0∞) * (tr.seedTrace.macroGates : ℝ≥0∞)
    + (w.bit : ℝ≥0∞) * (tr.seedTrace.bits : ℝ≥0∞)
    + (w.phase : ℝ≥0∞) * (tr.seedTrace.phaseQueries : ℝ≥0∞)
    + (w.prepare : ℝ≥0∞) * (tr.seedTrace.prepareCalls : ℝ≥0∞)
    + (w.validation : ℝ≥0∞) * (tr.fValidation : ℝ≥0∞)
    + (w.gForward : ℝ≥0∞) * (tr.gForward : ℝ≥0∞)
    + (w.gBackward : ℝ≥0∞) * (tr.gBackward : ℝ≥0∞)

/-- The natural-number weighted total of the seven resource counters charged by
`nextHeuristicCost`. -/
def nextHeuristicTotalCost {I : Type} (w : NextHeuristicWeights)
    (tr : NextHeuristicTrace I) : ℕ :=
  w.gate * tr.seedTrace.macroGates
    + w.bit * tr.seedTrace.bits
    + w.phase * tr.seedTrace.phaseQueries
    + w.prepare * tr.seedTrace.prepareCalls
    + w.validation * tr.fValidation
    + w.gForward * tr.gForward
    + w.gBackward * tr.gBackward

/-- Casting `nextHeuristicTotalCost w tr` to `ℝ≥0∞` gives exactly `nextHeuristicCost w tr`. -/
theorem nextHeuristicTotalCost_cast {I : Type} (w : NextHeuristicWeights)
    (tr : NextHeuristicTrace I) :
    (nextHeuristicTotalCost w tr : ℝ≥0∞) = nextHeuristicCost w tr := by
  simp only [nextHeuristicTotalCost, nextHeuristicCost, Nat.cast_add, Nat.cast_mul]

/-- The real constant combining the seven resource weights with coefficients `400`, `300`,
`100`, `300`, `100`, `100`, and `100` in the heuristic-search expectation bound. -/
def nextHeuristicCostConstant (w : NextHeuristicWeights) : ℝ :=
  400 * (w.gate : ℝ) + 300 * (w.bit : ℝ) + 100 * (w.phase : ℝ)
    + 300 * (w.prepare : ℝ)
    + 100 * (w.validation : ℝ) + 100 * (w.gForward : ℝ) + 100 * (w.gBackward : ℝ)

/-- The fraction of all seeds that belong to `nextGoodSeeds F G`, expressed as the real ratio of
their cardinality to `Fintype.card I`. -/
noncomputable def nextHeuristicDensity {I : Type} [Fintype I]
    (F : I → Bool) (G : (I → Bool) → I → I) : ℝ :=
  ((nextGoodSeeds F G).card : ℝ) / (Fintype.card I : ℝ)

/-- The sum of the window sizes in `geometricSearchSchedule M T`, used as the deterministic cap
on phase queries. -/
def nextHeuristicSigmaP (M T : ℕ) : ℕ := (geometricSearchSchedule M T).sum

/-- The amplitude-amplification angle `Real.arcsin (Real.sqrt hF)` associated with density `hF`. -/
noncomputable def nextHeuristicAngle (hF : ℝ) : ℝ := Real.arcsin (Real.sqrt hF)

/-- For a density `hF` in `[0, 1]`, the sine of `nextHeuristicAngle hF` equals `Real.sqrt hF`. -/
theorem nextHeuristicAngle_sin {hF : ℝ} (h0 : 0 ≤ hF) (h1 : hF ≤ 1) :
    Real.sin (nextHeuristicAngle hF) = Real.sqrt hF := by
  have hsq : (Real.sqrt hF) ^ 2 = hF := Real.sq_sqrt h0
  have hle : Real.sqrt hF ≤ 1 := by nlinarith [Real.sqrt_nonneg hF]
  unfold nextHeuristicAngle
  exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg hF]) hle

/-- For `0 ≤ hF ≤ 1`, the squared sine of `nextHeuristicAngle hF` is exactly `hF`. -/
theorem nextHeuristicAngle_sq {hF : ℝ} (h0 : 0 ≤ hF) (h1 : hF ≤ 1) :
    (Real.sin (nextHeuristicAngle hF)) ^ 2 = hF := by
  rw [nextHeuristicAngle_sin h0 h1, Real.sq_sqrt h0]

/-- A density strictly between zero and one has a heuristic angle strictly between zero and
`Real.pi / 2`. -/
theorem nextHeuristicAngle_range {hF : ℝ} (h0 : 0 < hF) (h1 : hF < 1) :
    0 < nextHeuristicAngle hF ∧ nextHeuristicAngle hF < Real.pi / 2 := by
  constructor
  · have hnonneg : 0 ≤ nextHeuristicAngle hF :=
      (Real.arcsin_nonneg).2 (Real.sqrt_nonneg hF)
    have hsin : Real.sin (nextHeuristicAngle hF) = Real.sqrt hF :=
      nextHeuristicAngle_sin (le_of_lt h0) (le_of_lt h1)
    have hpos : 0 < Real.sqrt hF := Real.sqrt_pos.2 h0
    by_contra hc
    have hz : nextHeuristicAngle hF = 0 := le_antisymm (le_of_not_gt hc) hnonneg
    rw [hz, Real.sin_zero] at hsin
    exact absurd hsin (Ne.symm (ne_of_gt hpos))
  · have hlt : Real.arcsin (Real.sqrt hF) < Real.pi / 2 :=
      (Real.arcsin_lt_pi_div_two).2 (by
        have hsq : (Real.sqrt hF) ^ 2 = hF := Real.sq_sqrt (le_of_lt h0)
        nlinarith [Real.sqrt_nonneg hF])
    exact hlt

/-- For `0 ≤ hF ≤ 1`, `Real.sin (2 * nextHeuristicAngle hF)` equals `2 * Real.sqrt (hF * (1 -
hF))`. -/
theorem nextHeuristicAngle_sin_two {hF : ℝ} (h0 : 0 ≤ hF) (h1 : hF ≤ 1) :
    Real.sin (2 * nextHeuristicAngle hF) = 2 * Real.sqrt (hF * (1 - hF)) := by
  have hsq : (Real.sqrt hF) ^ 2 = hF := Real.sq_sqrt h0
  have hle : Real.sqrt hF ≤ 1 := by nlinarith [Real.sqrt_nonneg hF]
  rw [nextHeuristicAngle, Real.sin_two_mul, Real.cos_arcsin, hsq,
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg hF]) hle,
    Real.sqrt_mul h0 (1 - hF)]
  ring

/-- Every trace in the support of `nextHeuristicConsumer` has all three added call counters
equal to its seed-validation count, and its output equals its seed result mapped through `G
F`. -/
theorem nextHeuristic_ledger_identities {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (tr : NextHeuristicTrace I)
    (htr : tr ∈ (nextHeuristicConsumer F G A hA j₀ M T).support) :
    tr.gForward = tr.seedTrace.validationQueries ∧
    tr.gBackward = tr.seedTrace.validationQueries ∧
    tr.fValidation = tr.seedTrace.validationQueries ∧
    tr.output = tr.seedTrace.result.map (G F) := by
  obtain ⟨tr', htr', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
  obtain ⟨rfl⟩ := heq
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Every output returned by a supported execution of `nextHeuristicConsumer F G` satisfies the
predicate `F`. -/
theorem nextHeuristic_output_sound {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (tr : NextHeuristicTrace I)
    (htr : tr ∈ (nextHeuristicConsumer F G A hA j₀ M T).support) :
    ∀ x, tr.output = some x → F x = true := by
  obtain ⟨tr', htr', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
  obtain ⟨rfl⟩ := heq
  intro x hx
  have hmap : tr'.result.map (G F) = some x := hx
  cases hr : tr'.result with
  | none => simp [hr] at hmap
  | some r =>
      rw [hr] at hmap
      have hgx : G F r = x := by simpa using! hmap
      have hgood := (geometric_search_actual_support_soundness_and_metadata A hA j₀
        (nextGoodSeeds F G) (nextGoodSeedValid F G) M T
        (fun y => nextGoodSeedValid_iff F G y) tr' htr').1 r hr
      have hF : F (G F r) = true := (Finset.mem_filter.mp hgood).2
      rw [← hgx]
      exact hF

/-- Every supported heuristic-search trace uses at most `T` seed validations, forward heuristic
calls, backward heuristic calls, and predicate validations. Its phase-query count is at most
`nextHeuristicSigmaP M T`. -/
theorem nextHeuristic_termination {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (tr : NextHeuristicTrace I)
    (htr : tr ∈ (nextHeuristicConsumer F G A hA j₀ M T).support) :
    tr.seedTrace.validationQueries ≤ T ∧
    tr.seedTrace.phaseQueries ≤ nextHeuristicSigmaP M T ∧
    tr.gForward ≤ T ∧ tr.gBackward ≤ T ∧ tr.fValidation ≤ T := by
  obtain ⟨tr', htr', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
  obtain ⟨rfl⟩ := heq
  have hcaps := (geometric_search_zero_one_endpoints_and_path_caps A hA j₀
    (nextGoodSeeds F G) (nextGoodSeedValid F G) M T
    (fun y => nextGoodSeedValid_iff F G y)).2.2 tr' htr'
  obtain ⟨hid, hval, -⟩ := hcaps
  exact ⟨hval, hid, hval, hval, hval⟩

/-- The probability that `nextHeuristicConsumer` returns no output equals the probability that
its underlying geometrically scheduled seed search returns no seed. -/
theorem nextHeuristic_failure_event_eq {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nextHeuristicConsumer F G A hA j₀ M T) (fun tr => tr.output = none)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ (nextGoodSeeds F G) (nextGoodSeedValid F G)
          (geometricSearchSchedule M T)) (fun tr => tr.result = none) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  unfold nextHeuristicConsumer
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro out
  cases hout : out.result with
  | none => simp [hout, nextHeuristicRecord]
  | some r => simp [hout, nextHeuristicRecord]

/-- If the prepared good-seed mass is `Real.sin θ ^ 2` with `0 < θ < Real.pi / 2`, and window
`j` satisfies `1 ≤ geometricWindow M j * Real.sin (2 * θ)`, the real-valued failure
probability is at most `(25 / 32) ^ (T - j)`. -/
theorem nextHeuristic_total_failure {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (j : ℕ)
    (hmass : MeasureProb (preparedAAState A j₀) (nextGoodSeeds F G) = (Real.sin θ)^2)
    (hMature : 1 ≤ (geometricWindow M j : ℝ) * Real.sin (2 * θ)) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nextHeuristicConsumer F G A hA j₀ M T)
        (fun tr => tr.output = none)).toReal ≤ (25/32 : ℝ)^(T - j) := by
  rw [nextHeuristic_failure_event_eq]
  exact geometric_search_actual_cutoff_failure_probability A hA j₀
    (nextGoodSeeds F G) (nextGoodSeedValid F G) M T j θ
    (fun y => nextGoodSeedValid_iff F G y) hθ0 hθ1 hmass hMature

/-- If the prepared state assigns zero probability to `nextGoodSeeds F G`, the heuristic
consumer returns no output with probability one. -/
theorem nextHeuristic_zero_density_fails {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (hmass : MeasureProb (preparedAAState A j₀) (nextGoodSeeds F G) = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (nextHeuristicConsumer F G A hA j₀ M T) (fun tr => tr.output = none) = 1 := by
  rw [nextHeuristic_failure_event_eq]
  exact (geometric_search_zero_one_endpoints_and_path_caps A hA j₀
    (nextGoodSeeds F G) (nextGoodSeedValid F G) M T
    (fun y => nextGoodSeedValid_iff F G y)).1 hmass

/-- When `Real.sin (2 * θ) > 0`, the seven component bounds with coefficients `400`, `300`,
`100`, `300`, `100`, `100`, and `100` combine into a weighted bound of `ENNReal.ofReal
(nextHeuristicCostConstant w / Real.sin (2 * θ))`. -/
private theorem nextHeuristic_cost_sum_le (w : NextHeuristicWeights) (θ : ℝ)
    (hsin : 0 < Real.sin (2 * θ))
    (E1 E2 E3 E4 E5 E6 E7 : ℝ≥0∞)
    (h1 : E1 ≤ ENNReal.ofReal (400 / Real.sin (2 * θ)))
    (h2 : E2 ≤ ENNReal.ofReal (300 / Real.sin (2 * θ)))
    (h3 : E3 ≤ ENNReal.ofReal (100 / Real.sin (2 * θ)))
    (h4 : E4 ≤ ENNReal.ofReal (300 / Real.sin (2 * θ)))
    (h5 : E5 ≤ ENNReal.ofReal (100 / Real.sin (2 * θ)))
    (h6 : E6 ≤ ENNReal.ofReal (100 / Real.sin (2 * θ)))
    (h7 : E7 ≤ ENNReal.ofReal (100 / Real.sin (2 * θ))) :
    (w.gate : ℝ≥0∞) * E1 + (w.bit : ℝ≥0∞) * E2 + (w.phase : ℝ≥0∞) * E3
      + (w.prepare : ℝ≥0∞) * E4 + (w.validation : ℝ≥0∞) * E5
      + (w.gForward : ℝ≥0∞) * E6 + (w.gBackward : ℝ≥0∞) * E7
      ≤ ENNReal.ofReal (nextHeuristicCostConstant w / Real.sin (2 * θ)) := by
  have hle : (w.gate : ℝ≥0∞) * E1 + (w.bit : ℝ≥0∞) * E2 + (w.phase : ℝ≥0∞) * E3
      + (w.prepare : ℝ≥0∞) * E4 + (w.validation : ℝ≥0∞) * E5
      + (w.gForward : ℝ≥0∞) * E6 + (w.gBackward : ℝ≥0∞) * E7
      ≤ (w.gate : ℝ≥0∞) * ENNReal.ofReal (400 / Real.sin (2 * θ))
        + (w.bit : ℝ≥0∞) * ENNReal.ofReal (300 / Real.sin (2 * θ))
        + (w.phase : ℝ≥0∞) * ENNReal.ofReal (100 / Real.sin (2 * θ))
        + (w.prepare : ℝ≥0∞) * ENNReal.ofReal (300 / Real.sin (2 * θ))
        + (w.validation : ℝ≥0∞) * ENNReal.ofReal (100 / Real.sin (2 * θ))
        + (w.gForward : ℝ≥0∞) * ENNReal.ofReal (100 / Real.sin (2 * θ))
        + (w.gBackward : ℝ≥0∞) * ENNReal.ofReal (100 / Real.sin (2 * θ)) :=
    add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul' le_rfl h1) (mul_le_mul' le_rfl h2)) (mul_le_mul' le_rfl h3))
      (mul_le_mul' le_rfl h4)) (mul_le_mul' le_rfl h5)) (mul_le_mul' le_rfl h6))
      (mul_le_mul' le_rfl h7)
  have hrw : ∀ (c : ℕ) (K : ℝ) (hK : 0 ≤ K),
      (c : ℝ≥0∞) * ENNReal.ofReal (K / Real.sin (2 * θ))
        = ENNReal.ofReal ((c : ℝ) * (K / Real.sin (2 * θ))) := by
    intro c K hK
    rw [← ENNReal.ofReal_natCast c, ← ENNReal.ofReal_mul (by positivity)]
  rw [hrw w.gate 400 (by norm_num), hrw w.bit 300 (by norm_num),
      hrw w.phase 100 (by norm_num), hrw w.prepare 300 (by norm_num),
      hrw w.validation 100 (by norm_num), hrw w.gForward 100 (by norm_num),
      hrw w.gBackward 100 (by norm_num)] at hle
  have hpos : ∀ (c : ℕ) (K : ℝ) (hK : 0 ≤ K),
      0 ≤ (c : ℝ) * (K / Real.sin (2 * θ)) := by
    intro c K hK
    have h1 : 0 ≤ (c : ℝ) := by positivity
    have h2 : 0 ≤ K / Real.sin (2 * θ) := div_nonneg hK (le_of_lt hsin)
    exact mul_nonneg h1 h2
  refine hle.trans ?_
  rw [← ENNReal.ofReal_add (hpos w.gate 400 (by norm_num)) (hpos w.bit 300 (by norm_num)),
    ← ENNReal.ofReal_add (by
      have hs : 0 < Real.sin (2 * θ) := hsin
      have h1 : 0 ≤ (w.gate : ℝ) * (400 / Real.sin (2 * θ)) := hpos w.gate 400 (by norm_num)
      have h2 : 0 ≤ (w.bit : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.bit 300 (by norm_num)
      linarith) (hpos w.phase 100 (by norm_num)),
    ← ENNReal.ofReal_add (by
      have hs : 0 < Real.sin (2 * θ) := hsin
      have h1 : 0 ≤ (w.gate : ℝ) * (400 / Real.sin (2 * θ)) := hpos w.gate 400 (by norm_num)
      have h2 : 0 ≤ (w.bit : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.bit 300 (by norm_num)
      have h3 : 0 ≤ (w.phase : ℝ) * (100 / Real.sin (2 * θ)) := hpos w.phase 100 (by norm_num)
      linarith) (hpos w.prepare 300 (by norm_num)),
    ← ENNReal.ofReal_add (by
      have hs : 0 < Real.sin (2 * θ) := hsin
      have h1 : 0 ≤ (w.gate : ℝ) * (400 / Real.sin (2 * θ)) := hpos w.gate 400 (by norm_num)
      have h2 : 0 ≤ (w.bit : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.bit 300 (by norm_num)
      have h3 : 0 ≤ (w.phase : ℝ) * (100 / Real.sin (2 * θ)) := hpos w.phase 100 (by norm_num)
      have h4 : 0 ≤ (w.prepare : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.prepare 300 (by norm_num)
      linarith) (hpos w.validation 100 (by norm_num)),
    ← ENNReal.ofReal_add (by
      have hs : 0 < Real.sin (2 * θ) := hsin
      have h1 : 0 ≤ (w.gate : ℝ) * (400 / Real.sin (2 * θ)) := hpos w.gate 400 (by norm_num)
      have h2 : 0 ≤ (w.bit : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.bit 300 (by norm_num)
      have h3 : 0 ≤ (w.phase : ℝ) * (100 / Real.sin (2 * θ)) := hpos w.phase 100 (by norm_num)
      have h4 : 0 ≤ (w.prepare : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.prepare 300 (by norm_num)
      have h5 : 0 ≤ (w.validation : ℝ) * (100 / Real.sin (2 * θ)) :=
          hpos w.validation 100 (by norm_num)
      linarith) (hpos w.gForward 100 (by norm_num)),
    ← ENNReal.ofReal_add (by
      have hs : 0 < Real.sin (2 * θ) := hsin
      have h1 : 0 ≤ (w.gate : ℝ) * (400 / Real.sin (2 * θ)) := hpos w.gate 400 (by norm_num)
      have h2 : 0 ≤ (w.bit : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.bit 300 (by norm_num)
      have h3 : 0 ≤ (w.phase : ℝ) * (100 / Real.sin (2 * θ)) := hpos w.phase 100 (by norm_num)
      have h4 : 0 ≤ (w.prepare : ℝ) * (300 / Real.sin (2 * θ)) := hpos w.prepare 300 (by norm_num)
      have h5 : 0 ≤ (w.validation : ℝ) * (100 / Real.sin (2 * θ)) :=
          hpos w.validation 100 (by norm_num)
      have h6 : 0 ≤ (w.gForward : ℝ) * (100 / Real.sin (2 * θ)) := hpos w.gForward 100 (by norm_num)
      linarith) (hpos w.gBackward 100 (by norm_num))]
  have heq : (nextHeuristicCostConstant w / Real.sin (2 * θ))
      = (w.gate : ℝ) * (400 / Real.sin (2 * θ))
        + (w.bit : ℝ) * (300 / Real.sin (2 * θ))
        + (w.phase : ℝ) * (100 / Real.sin (2 * θ))
        + (w.prepare : ℝ) * (300 / Real.sin (2 * θ))
        + (w.validation : ℝ) * (100 / Real.sin (2 * θ))
        + (w.gForward : ℝ) * (100 / Real.sin (2 * θ))
        + (w.gBackward : ℝ) * (100 / Real.sin (2 * θ)) := by
    have hne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
    unfold nextHeuristicCostConstant
    field_simp <;> ring
  exact ENNReal.ofReal_le_ofReal (by rw [heq])

/-- If the prepared good-seed mass is `Real.sin θ ^ 2`, `0 < θ < Real.pi / 2`, and `1 ≤ M *
Real.sin (2 * θ)`, then the expected heuristic cost is at most `ENNReal.ofReal
(nextHeuristicCostConstant w / Real.sin (2 * θ))`. -/
theorem nextHeuristic_expected_cost {I : Type} [Fintype I] [DecidableEq I]
    (F : I → Bool) (G : (I → Bool) → I → I)
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (M T : ℕ)
    (w : NextHeuristicWeights) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : MeasureProb (preparedAAState A j₀) (nextGoodSeeds F G) = (Real.sin θ)^2)
    (hMature : 1 ≤ (M : ℝ) * Real.sin (2 * θ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (nextHeuristicConsumer F G A hA j₀ M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal (nextHeuristicCostConstant w / Real.sin (2 * θ)) := by
  have hvalid : ∀ y, nextGoodSeedValid F G y = true ↔ y ∈ nextGoodSeeds F G :=
    fun y => nextGoodSeedValid_iff F G y
  obtain ⟨hphase, hbits, hval, hprep, hgate⟩ :=
    geometric_search_intrinsic_expected_resource_budget A hA j₀ (nextGoodSeeds F G)
      (nextGoodSeedValid F G) M T θ hvalid hθ0 hθ1 hmass hMature
  have hsin : 0 < Real.sin (2 * θ) := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0 < 2 * θ by linarith)
      (show 2 * θ < Real.pi by linarith)
    linarith [h]
  have hcongr : ∀ a : CappedSearchTrace I,
      nextHeuristicCost w (nextHeuristicRecord F G a)
        = (w.gate : ℝ≥0∞) * (a.macroGates : ℝ≥0∞)
          + (w.bit : ℝ≥0∞) * (a.bits : ℝ≥0∞)
          + (w.phase : ℝ≥0∞) * (a.phaseQueries : ℝ≥0∞)
          + (w.prepare : ℝ≥0∞) * (a.prepareCalls : ℝ≥0∞)
          + (w.validation : ℝ≥0∞) * (a.validationQueries : ℝ≥0∞)
          + (w.gForward : ℝ≥0∞) * (a.validationQueries : ℝ≥0∞)
          + (w.gBackward : ℝ≥0∞) * (a.validationQueries : ℝ≥0∞) := by
    intro a
    rfl
  unfold nextHeuristicConsumer
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hcongr]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  exact nextHeuristic_cost_sum_le w θ hsin
    _ _ _ _ _ _ _ hgate hbits hphase hprep hval hval hval

/-- For positive `n`, specializes the heuristic expectation bound to preparation by `QFTMatrix
n` from basis state zero. If the good-seed mass is `Real.sin θ ^ 2`, `0 < θ < Real.pi / 2`,
and `1 ≤ M * Real.sin (2 * θ)`, the expected cost is at most `ENNReal.ofReal
(nextHeuristicCostConstant w / Real.sin (2 * θ))`. -/
theorem nextHeuristic_qft_expected_cost {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n)
    (M T : ℕ) (w : NextHeuristicWeights) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n))
        (nextGoodSeeds F G) = (Real.sin θ)^2)
    (hMature : 1 ≤ (M : ℝ) * Real.sin (2 * θ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal (nextHeuristicCostConstant w / Real.sin (2 * θ)) := by
  exact nextHeuristic_expected_cost F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
    M T w θ hθ0 hθ1 hmass hMature

/-- For seeds in `Fin n`, the heuristic density equals `(nextGoodSeeds F G).card / n` as a real
ratio. -/
theorem nextHeuristic_qft_density {n : ℕ}
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n) :
    nextHeuristicDensity F G = ((nextGoodSeeds F G).card : ℝ) / (n : ℝ) := by
  unfold nextHeuristicDensity
  rw [Fintype.card_fin]

/-- For positive `n`, a nonempty good-seed set of density at most `1 / 2`, and `1 ≤ M * Real.sin
(2 * nextHeuristicAngle (nextHeuristicDensity F G))`, the QFT-prepared heuristic consumer
has expected cost at most `ENNReal.ofReal (nextHeuristicCostConstant w / Real.sqrt (2 *
nextHeuristicDensity F G))`. -/
theorem nextHeuristic_qft_rate_bound {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n)
    (M T : ℕ) (w : NextHeuristicWeights)
    (hcard : 0 < (nextGoodSeeds F G).card)
    (hdensity : nextHeuristicDensity F G ≤ 1 / 2)
    (hMature : 1 ≤ (M : ℝ)
      * Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal (nextHeuristicCostConstant w
          / Real.sqrt (2 * nextHeuristicDensity F G)) := by
  have hdense : 0 < nextHeuristicDensity F G := by
    rw [nextHeuristic_qft_density]
    have hcard' : (0:ℝ) < (nextGoodSeeds F G).card := by exact_mod_cast hcard
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hrange := nextHeuristicAngle_range hdense (by linarith)
  have hmass : MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n))
      (nextGoodSeeds F G)
      = (Real.sin (nextHeuristicAngle (nextHeuristicDensity F G))) ^ 2 := by
    have hqft : MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n))
        (nextGoodSeeds F G) = ((nextGoodSeeds F G).card : ℝ) / (n : ℝ) :=
      prepared_qft_mark_mass n hn (nextGoodSeeds F G)
    have hang : (Real.sin (nextHeuristicAngle (nextHeuristicDensity F G))) ^ 2
        = nextHeuristicDensity F G := nextHeuristicAngle_sq (le_of_lt hdense) (by linarith)
    rw [hqft, hang, nextHeuristic_qft_density]
  have hbound := nextHeuristic_qft_expected_cost hn F G M T w
    (nextHeuristicAngle (nextHeuristicDensity F G)) hrange.1 hrange.2 hmass hMature
  have hsin2 : Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))
      = 2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) :=
    nextHeuristicAngle_sin_two (le_of_lt hdense) (by linarith)
  have h4 : Real.sqrt (4 * (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)))
      = 2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) := by
    rw [Real.sqrt_mul (x := 4) (by norm_num) (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G))]
    norm_num
  have hsq : Real.sqrt (2 * nextHeuristicDensity F G)
      ≤ 2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) := by
    have h1 : 2 * nextHeuristicDensity F G
        ≤ 4 * (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) := by
      nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rw [h4] at h2
    exact h2
  have hdiv : nextHeuristicCostConstant w
        / Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))
      ≤ nextHeuristicCostConstant w / Real.sqrt (2 * nextHeuristicDensity F G) := by
    rw [hsin2]
    have hpos1 : 0
        < 2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) := by
      have h1 : 0 < nextHeuristicDensity F G * (1 - nextHeuristicDensity F G) := by
        have h2 : 1 / 2 ≤ 1 - nextHeuristicDensity F G := by linarith
        nlinarith
      have h1' : 0 < Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)) :=
        Real.sqrt_pos.2 h1
      linarith
    have hpos2 : 0 < Real.sqrt (2 * nextHeuristicDensity F G) := by
      have h1 : 0 < 2 * nextHeuristicDensity F G := by nlinarith
      exact Real.sqrt_pos.2 h1
    have hCw : 0 ≤ nextHeuristicCostConstant w := by
      unfold nextHeuristicCostConstant
      positivity
    have hmul : nextHeuristicCostConstant w * Real.sqrt (2 * nextHeuristicDensity F G)
        ≤ nextHeuristicCostConstant w
          * (2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G))) :=
      mul_le_mul_of_nonneg_left hsq hCw
    have hiff := (div_le_div_iff₀ hpos1 hpos2 :
        nextHeuristicCostConstant w
            / (2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G)))
          ≤ nextHeuristicCostConstant w / Real.sqrt (2 * nextHeuristicDensity F G)
          ↔ nextHeuristicCostConstant w * Real.sqrt (2 * nextHeuristicDensity F G)
            ≤ nextHeuristicCostConstant w
              * (2 * Real.sqrt (nextHeuristicDensity F G * (1 - nextHeuristicDensity F G))))
    exact hiff.mpr hmul
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  exact hdiv

/-- For positive `n`, `T ≥ 1`, a nonempty good-seed set of density at most `1 / 2`, and a mature
initial window, the QFT-prepared expected cost is at most `ENNReal.ofReal
((nextHeuristicCostConstant w / Real.sqrt 2) * Real.sqrt (nextHeuristicSigmaP M T * n))`.
Maturity means `1 ≤ M * Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))`. -/
theorem nextHeuristic_qft_spec_shape_bound {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n)
    (M T : ℕ) (w : NextHeuristicWeights)
    (hT : 1 ≤ T)
    (hcard : 0 < (nextGoodSeeds F G).card)
    (hdensity : nextHeuristicDensity F G ≤ 1 / 2)
    (hMature : 1 ≤ (M : ℝ)
      * Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal ((nextHeuristicCostConstant w / Real.sqrt 2)
          * Real.sqrt ((nextHeuristicSigmaP M T : ℝ) * (n : ℝ))) := by
  have hrate := nextHeuristic_qft_rate_bound hn F G M T w hcard hdensity hMature
  have hdense : 0 < nextHeuristicDensity F G := by
    rw [nextHeuristic_qft_density]
    have hcard' : (0:ℝ) < (nextGoodSeeds F G).card := by exact_mod_cast hcard
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hsigma : 1 ≤ nextHeuristicSigmaP M T := by
    unfold nextHeuristicSigmaP
    have hT' : 0 < T := by omega
    have hmem : 1 ∈ geometricSearchSchedule M T := by
      rw [geometricSearchSchedule, List.mem_ofFn]
      refine ⟨⟨0, hT'⟩, ?_⟩
      show geometricWindow M 0 = 1
      show max 1 (min M ((6^(0:ℕ)+5^(0:ℕ)-1)/5^(0:ℕ))) = 1
      norm_num
    have hle := List.le_sum_of_mem hmem
    simpa using! hle
  have hinv : (1:ℝ) / nextHeuristicDensity F G
      = (n : ℝ) / ((nextGoodSeeds F G).card : ℝ) := by
    rw [nextHeuristic_qft_density]
    have hne : (nextGoodSeeds F G).card ≠ 0 := ne_of_gt hcard
    have hnR : (n : ℝ) ≠ 0 := by
      have h1 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact ne_of_gt h1
    field_simp
  have h1 : (1:ℝ) ≤ (nextHeuristicSigmaP M T : ℝ) * ((nextGoodSeeds F G).card : ℝ) := by
    have hsigmaR : (1:ℝ) ≤ (nextHeuristicSigmaP M T : ℝ) := by
      exact_mod_cast hsigma
    have hcardR : (1:ℝ) ≤ ((nextGoodSeeds F G).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hcard)
    nlinarith
  have h2 : (n : ℝ) / ((nextGoodSeeds F G).card : ℝ)
      ≤ (nextHeuristicSigmaP M T : ℝ) * (n : ℝ) := by
    have hposcard : (0:ℝ) < ((nextGoodSeeds F G).card : ℝ) := by exact_mod_cast hcard
    have hle : (1:ℝ) / ((nextGoodSeeds F G).card : ℝ)
        ≤ (nextHeuristicSigmaP M T : ℝ) := by
      rw [div_le_iff₀ hposcard]
      have hh : (1:ℝ) ≤ (nextHeuristicSigmaP M T : ℝ) * ((nextGoodSeeds F G).card : ℝ) := h1
      nlinarith
    have hmul : (n : ℝ) * ((1:ℝ) / (nextGoodSeeds F G).card)
        ≤ (n : ℝ) * (nextHeuristicSigmaP M T : ℝ) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have heq : (n : ℝ) / ((nextGoodSeeds F G).card : ℝ)
        = (n : ℝ) * ((1:ℝ) / (nextGoodSeeds F G).card) := by
      field_simp
    rw [heq]
    simpa [mul_comm] using! hmul
  have h3 : (1:ℝ) / nextHeuristicDensity F G
      ≤ (nextHeuristicSigmaP M T : ℝ) * (n : ℝ) := by
    rw [hinv]
    exact h2
  have h4 : Real.sqrt (1 / nextHeuristicDensity F G)
      ≤ Real.sqrt ((nextHeuristicSigmaP M T : ℝ) * (n : ℝ)) := Real.sqrt_le_sqrt h3
  have h5 : nextHeuristicCostConstant w / Real.sqrt (2 * nextHeuristicDensity F G)
      = (nextHeuristicCostConstant w / Real.sqrt 2)
        * Real.sqrt (1 / nextHeuristicDensity F G) := by
    have hne : nextHeuristicDensity F G ≠ 0 := ne_of_gt hdense
    have hpos : 0 < Real.sqrt (nextHeuristicDensity F G) := Real.sqrt_pos.2 hdense
    have hne2 : Real.sqrt 2 ≠ 0 := by positivity
    rw [Real.sqrt_mul (x := 2) (by norm_num) (nextHeuristicDensity F G)]
    have hsqrtinv : Real.sqrt (1 / nextHeuristicDensity F G)
        = 1 / Real.sqrt (nextHeuristicDensity F G) := by
      rw [show (1 / nextHeuristicDensity F G) = (nextHeuristicDensity F G)⁻¹ by
          rw [one_div], Real.sqrt_inv]
      field_simp
    rw [hsqrtinv]
    field_simp <;> ring
  refine hrate.trans (ENNReal.ofReal_le_ofReal ?_)
  calc nextHeuristicCostConstant w / Real.sqrt (2 * nextHeuristicDensity F G)
      = (nextHeuristicCostConstant w / Real.sqrt 2)
        * Real.sqrt (1 / nextHeuristicDensity F G) := h5
    _ ≤ (nextHeuristicCostConstant w / Real.sqrt 2)
        * Real.sqrt ((nextHeuristicSigmaP M T : ℝ) * (n : ℝ)) := by
      have hCw : 0 ≤ nextHeuristicCostConstant w := by
        unfold nextHeuristicCostConstant
        positivity
      have hsqrt2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      exact mul_le_mul_of_nonneg_left h4 (div_nonneg hCw (le_of_lt hsqrt2))

/-- For positive `n`, QFT preparation from basis state zero gives the good-seed set probability
equal to the squared sine of `nextHeuristicAngle (nextHeuristicDensity F G)`. -/
theorem nextHeuristic_qft_mass {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n) :
    MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n)) (nextGoodSeeds F G)
      = (Real.sin (nextHeuristicAngle (nextHeuristicDensity F G))) ^ 2 := by
  have hqft : MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n))
      (nextGoodSeeds F G) = ((nextGoodSeeds F G).card : ℝ) / (n : ℝ) :=
    prepared_qft_mark_mass n hn (nextGoodSeeds F G)
  have hcardR : (0:ℝ) ≤ ((nextGoodSeeds F G).card : ℝ) := Nat.cast_nonneg _
  have hnR : (0:ℝ) < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hn
  have hle : ((nextGoodSeeds F G).card : ℝ) ≤ (Fintype.card (Fin n) : ℝ) :=
    Nat.cast_le.2 (Finset.card_le_univ (s := (nextGoodSeeds F G)))
  have hang : (Real.sin (nextHeuristicAngle (nextHeuristicDensity F G))) ^ 2
      = nextHeuristicDensity F G :=
    nextHeuristicAngle_sq (div_nonneg hcardR (le_of_lt hnR))
      (by
        unfold nextHeuristicDensity
        refine (div_le_iff₀ hnR).2 ?_
        rw [one_mul]
        exact hle)
  rw [hqft, hang, nextHeuristic_qft_density]

/-- For positive `n`, a nonempty good-seed set with density at most `1 / 2` has heuristic angle
strictly between zero and `Real.pi / 2`. -/
theorem nextHeuristic_qft_angle_range {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n)
    (hcard : 0 < (nextGoodSeeds F G).card)
    (hdensity : nextHeuristicDensity F G ≤ 1 / 2) :
    0 < nextHeuristicAngle (nextHeuristicDensity F G) ∧
    nextHeuristicAngle (nextHeuristicDensity F G) < Real.pi / 2 := by
  have hcardR : (0:ℝ) < ((nextGoodSeeds F G).card : ℝ) := by
    have : (0:ℝ) < ((nextGoodSeeds F G).card : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hcard)
    exact this
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdense : 0 < nextHeuristicDensity F G := by
    rw [nextHeuristic_qft_density]
    exact div_pos hcardR hnR
  exact nextHeuristicAngle_range hdense (lt_of_le_of_lt hdensity (by norm_num))

/-- The preliminary counting grid size `Nat.ceil (80 * Real.pi * Real.sqrt N)`. -/
noncomputable def nextCor4RoughGrid (N : ℕ) : ℕ :=
  Nat.ceil (80 * Real.pi * Real.sqrt (N : ℝ))

/-- The adaptive final counting grid size `Nat.ceil (48 * Real.sqrt ((v + 1) * (N - v + 1)))`,
where `v = min t'₁ t'₂` is the smaller rough estimate. -/
noncomputable def nextCor4Grid (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  Nat.ceil (48 * Real.sqrt ((min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1)))

/-- The counting error window `2 * Real.pi * k * Real.sqrt (t * (N - t)) / M + Real.pi ^ 2 * k ^
2 * N / M ^ 2` associated with the BHMT amplitude-estimation bound [BrassardEtAl2002]. -/
noncomputable def nextCor4Window (M k : ℕ) (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) +
    Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M : ℝ) ^ 2

/-- The preliminary counting window `nextCor4Window (nextCor4RoughGrid N) 17 N t`, using tail
parameter `17`. -/
noncomputable def nextCor4RoughWindow (N : ℕ) (t : ℝ) : ℝ :=
  nextCor4Window (nextCor4RoughGrid N) 17 N t

/-- For positive `N`, the preliminary counting grid `nextCor4RoughGrid N` has size at least two. -/
theorem nextCor4_rough_grid_two {N : ℕ} (hN : 0 < N) : 2 ≤ nextCor4RoughGrid N := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ N by omega)
  have hval : (1 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by nlinarith
  have hceil : 1 < nextCor4RoughGrid N := by
    rw [nextCor4RoughGrid]
    exact (Nat.lt_ceil (n := 1) (a := 80 * Real.pi * Real.sqrt (N : ℝ))).2 (by simpa using! hval)
  omega

/-- For positive `N` and `1 ≤ t ≤ N`, the preliminary counting error window `nextCor4RoughWindow
N t` is at most `t / 2`. -/
theorem nextCor4_rough_window_le {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht1 : 1 ≤ t) (htN : t ≤ (N : ℝ)) :
    nextCor4RoughWindow N t ≤ t / 2 := by
  have hMge : 80 * Real.pi * Real.sqrt (N : ℝ) ≤ (nextCor4RoughGrid N : ℝ) := by
    rw [nextCor4RoughGrid]
    exact Nat.le_ceil _
  have hMpos : (0 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht1
  have hgap : 0 ≤ (N : ℝ) - t := by linarith
  have hsqrtD : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt (t * (N : ℝ)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtNt : Real.sqrt (t * (N : ℝ)) = Real.sqrt t * Real.sqrt (N : ℝ) :=
    Real.sqrt_mul ht0 _

  have hA : 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
      (nextCor4RoughGrid N : ℝ) ≤ (17 : ℝ) / 40 * Real.sqrt t := by
    have hrecip : 1 / (nextCor4RoughGrid N : ℝ) ≤ 1 / (80 * Real.pi * Real.sqrt (N : ℝ)) :=
      one_div_le_one_div_of_le hMpos hMge
    have hnum : (0 : ℝ) ≤ 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * (N : ℝ)) := by
      have : (0 : ℝ) ≤ Real.sqrt (t * (N : ℝ)) := Real.sqrt_nonneg _
      positivity
    have hstep : 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
          (nextCor4RoughGrid N : ℝ)
        ≤ 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * (N : ℝ)) / (nextCor4RoughGrid N : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ ?_
      · exact mul_le_mul_of_nonneg_left hsqrtD (by positivity)
      · exact le_of_lt (lt_of_lt_of_le hMpos hMge)
    calc 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
          (nextCor4RoughGrid N : ℝ)
        ≤ 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * (N : ℝ)) / (nextCor4RoughGrid N : ℝ) := hstep
      _ = 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * (N : ℝ)) *
          (1 / (nextCor4RoughGrid N : ℝ)) := by field_simp
      _ ≤ 2 * Real.pi * (17 : ℝ) * Real.sqrt (t * (N : ℝ)) *
          (1 / (80 * Real.pi * Real.sqrt (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hrecip hnum
      _ = (17 : ℝ) / 40 * Real.sqrt t := by
        rw [hsqrtNt]
        field_simp
        ring

  have hB : Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) / (nextCor4RoughGrid N : ℝ) ^ 2
      ≤ 289 / 6400 := by
    have hsq : (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 ≤ (nextCor4RoughGrid N : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ 80 * Real.pi * Real.sqrt (N : ℝ) := by positivity
      nlinarith [sq_nonneg (nextCor4RoughGrid N : ℝ)]
    have hMpos2 : (0 : ℝ) < (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 := sq_pos_of_pos hMpos
    have hrecip2 : 1 / (nextCor4RoughGrid N : ℝ) ^ 2
        ≤ 1 / (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le hMpos2 hsq
    have hnum : (0 : ℝ) ≤ Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) := by positivity
    calc Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) / (nextCor4RoughGrid N : ℝ) ^ 2
        = Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) * (1 / (nextCor4RoughGrid N : ℝ) ^ 2) := by
          field_simp
      _ ≤ Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) *
          (1 / (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hrecip2 hnum
      _ = 289 / 6400 := by
        have hsq2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
        rw [show (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2
            = 6400 * Real.pi ^ 2 * (N : ℝ) by
          rw [mul_pow, mul_pow, hsq2]; ring]
        field_simp [hNne, hpine]
        ring

  have hsqrtle : Real.sqrt t ≤ t := by
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hnonneg : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    by_cases h : Real.sqrt t ≤ 1
    · have hmul : Real.sqrt t * Real.sqrt t ≤ 1 * Real.sqrt t := by
        have := mul_le_mul_of_nonneg_right h hnonneg
        simpa using! this
      nlinarith [hmul]
    · have h1 : 1 ≤ Real.sqrt t := le_of_not_ge h
      have hmul : 1 * Real.sqrt t ≤ Real.sqrt t * Real.sqrt t := by
        have := mul_le_mul_of_nonneg_left h1 hnonneg
        simpa using! this
      nlinarith [hmul]
  have hcomb : (17 : ℝ) / 40 * Real.sqrt t + 289 / 6400 ≤ t / 2 := by
    have hmul : (17 : ℝ) / 40 * Real.sqrt t ≤ (17 : ℝ) / 40 * t := by
      exact mul_le_mul_of_nonneg_left hsqrtle (by norm_num)
    have hfin : (17 : ℝ) / 40 * t + 289 / 6400 ≤ t / 2 := by
      nlinarith [ht1]
    linarith
  unfold nextCor4RoughWindow nextCor4Window
  linarith

/-- The preliminary phase labels whose scaled amplitude estimates differ from the target count
`t` by at most `nextCor4RoughWindow N t`. -/
noncomputable def nextCor4Good (N : ℕ) (t : ℝ) : Finset (Fin (nextCor4RoughGrid N)) :=
  Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
    |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - t| ≤ nextCor4RoughWindow N t)

/-- The probability that amplitude estimation with QFT preparation on grid `M` yields a label
whose `exactCountOutput N` equals the marked-set cardinality `S.card`. -/
noncomputable def nextCor4FinalMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (M : ℕ)
    (hM : 2 ≤ M) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = ((S.card : ℕ) : ℤ)),
    (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y

/-- The total exact-counting success probability obtained from two independent preliminary
amplitude-estimation labels and a final grid chosen by `nextCor4Grid`. It averages the final
success mass over the product of the two preliminary label laws. -/
noncomputable def nextCor4SuccessMass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂)) : ℝ :=
  ∑ z₁ : Fin (nextCor4RoughGrid N), ∑ z₂ : Fin (nextCor4RoughGrid N),
    ((aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₁) *
    ((aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).prob z₂) *
    (nextCor4FinalMass hN S
      (nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
      (hM z₁ z₂))

/-- For positive `N`, the preliminary QFT-prepared counting law assigns `nextCor4Good N S.card`
probability at least `1 - 1 / (2 * (17 - 1)) = 31 / 32`, by the BHMT tail bound
[BrassardEtAl2002]. -/
theorem nextCor4_rough_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    1 - 1 / (2 * ((17 : ℝ) - 1)) ≤
      ∑ z ∈ nextCor4Good N (S.card : ℝ),
        (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z := by
  have h := bhmt_counting_k2_window N (nextCor4RoughGrid N) S hN
    (nextCor4_rough_grid_two hN) 17 (by norm_num)
  have hsub : nextCor4Good N (S.card : ℝ)
      = Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
          |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
            2 * Real.pi * (17 : ℝ) * Real.sqrt ((S.card : ℝ) * ((N : ℝ) - S.card)) /
                (nextCor4RoughGrid N : ℝ) +
              Real.pi ^ 2 * (17 : ℝ) ^ 2 * (N : ℝ) / (nextCor4RoughGrid N : ℝ) ^ 2) := by
    ext z
    simp only [nextCor4Good, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold nextCor4RoughWindow nextCor4Window
    rfl
  rw [hsub]
  exact h

/-- For positive `N` and a marked-set cardinality at least one, each good preliminary label
yields a scaled amplitude estimate between `S.card / 2` and `3 * S.card / 2`. -/
theorem nextCor4_rough_range {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    {z : Fin (nextCor4RoughGrid N)} (hz : z ∈ nextCor4Good N (S.card : ℝ))
    (ht1 : 1 ≤ (S.card : ℝ)) :
    (S.card : ℝ) / 2 ≤ (N : ℝ) * aeEstimate (nextCor4RoughGrid N) z ∧
      (N : ℝ) * aeEstimate (nextCor4RoughGrid N) z ≤ 3 * (S.card : ℝ) / 2 := by
  have hcard : (S.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
  have hwin := nextCor4_rough_window_le hN ht1 hcard
  have hhz := hz
  simp only [nextCor4Good, Finset.mem_filter, Finset.mem_univ, true_and] at hhz
  rcases abs_le.mp hhz with ⟨hl, hu⟩
  constructor
  · linarith
  · linarith

/-- If both preliminary estimates lie in `[0, N]`, the adaptive final counting grid
`nextCor4Grid N t'₁ t'₂` has size at least two. -/
theorem nextCor4_grid_two {N : ℕ} {t'₁ t'₂ : ℝ}
    (h1 : 0 ≤ t'₁) (h1' : t'₁ ≤ (N : ℝ)) (h2 : 0 ≤ t'₂) (h2' : t'₂ ≤ (N : ℝ)) :
    2 ≤ nextCor4Grid N t'₁ t'₂ := by
  have hvmin : 0 ≤ min t'₁ t'₂ := le_min h1 h2
  have hvmin' : min t'₁ t'₂ ≤ (N : ℝ) := le_trans (min_le_left _ _) h1'
  have hA0 : (0 : ℝ) ≤ min t'₁ t'₂ + 1 := by linarith
  have hB0 : (0 : ℝ) ≤ (N : ℝ) - min t'₁ t'₂ + 1 := by linarith
  have hA1 : (1 : ℝ) ≤ min t'₁ t'₂ + 1 := by linarith
  have hB1 : (1 : ℝ) ≤ (N : ℝ) - min t'₁ t'₂ + 1 := by linarith
  have hsq : (1 : ℝ) ≤ (min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1) := by
    nlinarith [mul_nonneg hA0 hB0]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1)) :=
    (Real.one_le_sqrt).2 hsq
  unfold nextCor4Grid
  have hval : (1 : ℝ) < 48 * Real.sqrt ((min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1)) := by
    nlinarith
  have hceil : 1 < Nat.ceil (48 * Real.sqrt ((min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1))) := by
    exact (Nat.lt_ceil (n := 1)
      (a := 48 * Real.sqrt ((min t'₁ t'₂ + 1) * ((N : ℝ) - min t'₁ t'₂ + 1)))).2 (by simpa using! hval)
  omega

/-- For positive `N`, `1 ≤ t ≤ N / 2`, and `t / 2 ≤ v ≤ 3 * t / 2`, any grid satisfying `48 *
Real.sqrt ((v + 1) * (N - v + 1)) ≤ M` has `nextCor4Window M 1 N t < 1 / 2`. -/
theorem nextCor4_final_window_lt_half {N : ℕ} (hN : 0 < N) {t v : ℝ} {M : ℕ}
    (ht0 : 1 ≤ t) (htN : t ≤ (N : ℝ) / 2)
    (hv1 : t / 2 ≤ v) (hv2 : v ≤ 3 * t / 2)
    (hM : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) ≤ (M : ℝ)) :
    nextCor4Window M 1 N t < 1 / 2 := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ht0' : 0 ≤ t := le_trans (by norm_num) ht0
  have hgap : 0 ≤ (N : ℝ) - t := by linarith
  have hD : 0 ≤ t * ((N : ℝ) - t) := mul_nonneg ht0' hgap

  have hv0 : 0 ≤ v := by linarith
  have hvgap : (N : ℝ) / 4 ≤ (N : ℝ) - v := by linarith
  have hvN : (0 : ℝ) ≤ (N : ℝ) - v := by linarith
  have hstep1 : (t / 2) * ((N : ℝ) - v) ≤ v * ((N : ℝ) - v) := by
    simpa [mul_comm] using! mul_le_mul_of_nonneg_left hv1 hvN
  have hstep2 : (t / 2) * ((N : ℝ) / 4) ≤ (t / 2) * ((N : ℝ) - v) := by
    simpa [mul_comm] using!
      (mul_le_mul_of_nonneg_right hvgap (by linarith : (0 : ℝ) ≤ t / 2))
  have hprod : t * (N : ℝ) / 8 ≤ v * ((N : ℝ) - v) := by linarith
  have hD2 : t * (N : ℝ) / 8 ≤ (v + 1) * ((N : ℝ) - v + 1) := by
    have hsq : (v + 1) * ((N : ℝ) - v + 1) - v * ((N : ℝ) - v) = (N : ℝ) + 1 := by
      ring
    have hnonneg : (0 : ℝ) ≤ (N : ℝ) + 1 := by linarith
    linarith

  have hsqrtD : Real.sqrt (t * (N : ℝ) / 8) ≤ Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcmp : 16 * Real.sqrt (t * (N : ℝ)) ≤ 48 * Real.sqrt (t * (N : ℝ) / 8) := by
    have hsq : (16 * Real.sqrt (t * (N : ℝ))) ^ 2
        ≤ (48 * Real.sqrt (t * (N : ℝ) / 8)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith
    have hsqnonneg : 0 ≤ 16 * Real.sqrt (t * (N : ℝ)) := by positivity
    have hsqnonneg2 : 0 ≤ 48 * Real.sqrt (t * (N : ℝ) / 8) := by positivity
    nlinarith [sq_nonneg (16 * Real.sqrt (t * (N : ℝ)) - 48 * Real.sqrt (t * (N : ℝ) / 8))]
  have hMlow : 16 * Real.sqrt (t * (N : ℝ)) ≤ (M : ℝ) := by
    have h1 : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) ≤ (M : ℝ) := hM
    have h2 : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1))
        ≥ 48 * Real.sqrt (t * (N : ℝ) / 8) := by
      have : (0:ℝ) ≤ 48 := by norm_num
      exact mul_le_mul_of_nonneg_left hsqrtD this
    linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : (0 : ℝ) < 16 * Real.sqrt (t * (N : ℝ)) := by positivity
    linarith

  have hT1 : 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) ≤ Real.pi / 8 := by
    have hsqrtD2 : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt (t * (N : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hnum : (0 : ℝ) ≤ 2 * Real.pi * Real.sqrt (t * (N : ℝ)) := by positivity
    have hrecip : (M : ℝ)⁻¹ ≤ (16 * Real.sqrt (t * (N : ℝ)))⁻¹ := by
      have h := one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < 16 * Real.sqrt (t * (N : ℝ))) hMlow
      simpa [one_div] using! h
    have hstep : 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (M : ℝ)
        ≤ 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (16 * Real.sqrt (t * (N : ℝ))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrecip hnum
    have heq : 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (16 * Real.sqrt (t * (N : ℝ)))
        = Real.pi / 8 := by field_simp; ring
    have hstep2 : 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ)
        ≤ 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (M : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ ?_
      · exact mul_le_mul_of_nonneg_left hsqrtD2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      · exact le_of_lt hMpos
    calc _ ≤ 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (M : ℝ) := hstep2
      _ ≤ 2 * Real.pi * Real.sqrt (t * (N : ℝ)) / (16 * Real.sqrt (t * (N : ℝ))) := hstep
      _ = Real.pi / 8 := heq
  have hT2 : Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 ≤ Real.pi ^ 2 / 256 := by
    have hsq : (16 * Real.sqrt (t * (N : ℝ))) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ 16 * Real.sqrt (t * (N : ℝ)) := by positivity
      nlinarith [sq_nonneg (M : ℝ)]
    have hrecip : ((M : ℝ) ^ 2)⁻¹ ≤ ((16 * Real.sqrt (t * (N : ℝ))) ^ 2)⁻¹ := by
      have h := one_div_le_one_div_of_le
        (sq_pos_of_pos (by positivity : (0:ℝ) < 16 * Real.sqrt (t * (N:ℝ)))) hsq
      simpa [one_div] using! h
    have hnum : (0 : ℝ) ≤ Real.pi ^ 2 * (N : ℝ) := by positivity
    have hstep : Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2
        ≤ Real.pi ^ 2 * (N : ℝ) * ((16 * Real.sqrt (t * (N : ℝ))) ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrecip hnum
    have heq : Real.pi ^ 2 * (N : ℝ) * ((16 * Real.sqrt (t * (N : ℝ))) ^ 2)⁻¹
        = Real.pi ^ 2 / (256 * t) := by
      have hsq2 : Real.sqrt (t * (N : ℝ)) ^ 2 = t * (N : ℝ) := Real.sq_sqrt (by positivity)
      have hsq3 : (16 * Real.sqrt (t * (N : ℝ))) ^ 2 = 256 * (t * (N : ℝ)) := by
        rw [mul_pow, hsq2]; ring
      rw [hsq3]
      have htne : t ≠ 0 := by linarith
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      have hne : (256 : ℝ) * (t * (N : ℝ)) ≠ 0 := by positivity
      field_simp [hne, htne, hNne]
    rw [heq] at hstep
    have hlast : Real.pi ^ 2 / (256 * t) ≤ Real.pi ^ 2 / 256 := by
      have hden : (0 : ℝ) < 256 * t := by positivity
      rw [div_le_iff₀ hden]
      nlinarith [ht0, Real.pi_pos]
    exact hstep.trans hlast

  have hpi : Real.pi < 22 / 7 := lt_trans Real.pi_lt_d6 (by norm_num)
  have hsum : Real.pi / 8 + Real.pi ^ 2 / 256 < 1 / 2 := by
    have h1 : Real.pi / 8 < 22 / 56 := by
      have h8 : (0 : ℝ) < 8 := by norm_num
      exact (div_lt_iff₀ h8).2 (by linarith)
    have h2 : Real.pi ^ 2 / 256 < 484 / (49 * 256) := by
      have hpisq : Real.pi ^ 2 < ((22 : ℝ) / 7) ^ 2 := by nlinarith [Real.pi_pos, hpi]
      have h4 : (0 : ℝ) < 256 := by norm_num
      exact (div_lt_iff₀ h4).2 (by nlinarith)
    linarith
  have hwin : nextCor4Window M 1 N t
      = 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ)
        + Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := by
    unfold nextCor4Window
    simp only [Nat.cast_one, one_pow]
    ring
  calc nextCor4Window M 1 N t
      = 2 * Real.pi * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ)
        + Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := hwin
    _ ≤ Real.pi / 8 + Real.pi ^ 2 / 256 := add_le_add hT1 hT2
    _ < 1 / 2 := hsum

/-- For positive `N` and `M ≥ 2`, if the final counting window at `S.card` is strictly less than
`1 / 2`, the probability of exact integer output is at least `8 / Real.pi ^ 2`. The
conclusion follows by rounding the BHMT error event [BrassardEtAl2002]. -/
theorem nextCor4_final_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (M : ℕ)
    (hM : 2 ≤ M) (hwin : nextCor4Window M 1 N (S.card : ℝ) < 1 / 2) :
    8 / Real.pi ^ 2 ≤ nextCor4FinalMass hN S M hM := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha : (S.card : ℝ) / (N : ℝ)
      = MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S := by
    rw [prepared_qft_mark_mass N hN S]
  have hbhmt := (prepared_ae_bhmt_error_and_endpoints M hM (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
    (qftMatrix_unitary hN)).1
  rw [← ha] at hbhmt

  have hD : 0 ≤ (S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)) := by
    have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hgap : (0 : ℝ) ≤ (N : ℝ) - (S.card : ℝ) := by
      have hle : (S.card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
      linarith
    exact mul_nonneg hcard hgap
  have hnonnegA : (0 : ℝ) ≤ ((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)) := by
    have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hle : (S.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
    have hfrac : (0 : ℝ) ≤ (S.card : ℝ) / (N : ℝ) := div_nonneg hcard (le_of_lt hN')
    have hone : (0 : ℝ) ≤ 1 - (S.card : ℝ) / (N : ℝ) := by
      have : (S.card : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hN']
        exact hle
      linarith
    exact mul_nonneg hfrac hone
  have hsqrtid : (N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
      (1 - (S.card : ℝ) / (N : ℝ))) = Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ))) := by
    have hsq1 : ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
        (1 - (S.card : ℝ) / (N : ℝ)))) ^ 2
        = (S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)) := by
      rw [mul_pow]
      have h2 : Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ))) ^ 2
          = ((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)) :=
        Real.sq_sqrt hnonnegA
      rw [h2]
      field_simp [hN'.ne']
    have hsq2 : (Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)))) ^ 2
        = (S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)) := Real.sq_sqrt hD
    have hL : (0 : ℝ) ≤ (N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
        (1 - (S.card : ℝ) / (N : ℝ))) := by positivity
    have hR : (0 : ℝ) ≤ Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ))) := Real.sqrt_nonneg _
    have hprod : ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
        (1 - (S.card : ℝ) / (N : ℝ))) - Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)))) *
        ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
        (1 - (S.card : ℝ) / (N : ℝ))) + Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)))) = 0 := by
      have he : ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ)))) ^ 2
          - (Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)))) ^ 2 = 0 := by
        rw [hsq1, hsq2]
        ring
      nlinarith [he]
    have hsum : 0 ≤ (N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
        (1 - (S.card : ℝ) / (N : ℝ))) + Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ))) := by
      linarith
    nlinarith [hprod]
  have hmain : ∀ y : Fin M,
      |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ)) →
      |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ) := by
    intro y hy
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    have hid : (N : ℝ) * aeEstimate M y - (S.card : ℝ)
        = (N : ℝ) * (aeEstimate M y - (S.card : ℝ) / (N : ℝ)) := by
      field_simp [hN'.ne']
    have hmulW : (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ))
        = nextCor4Window M 1 N (S.card : ℝ) := by
      unfold nextAeWindow nextCor4Window
      have hspread : (N : ℝ) * (2 * Real.pi * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ))) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2)
        = 2 * Real.pi * ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ)))) / (M : ℝ) + Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := by
        ring
      rw [hspread, hsqrtid]
      ring
    have h1 : (N : ℝ) * |aeEstimate M y - (S.card : ℝ) / (N : ℝ)|
        ≤ (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hy hN0
    calc |(N : ℝ) * aeEstimate M y - (S.card : ℝ)|
        = (N : ℝ) * |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| := by
          rw [hid, abs_mul, abs_of_nonneg hN0]
      _ ≤ (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ)) := h1
      _ = nextCor4Window M 1 N (S.card : ℝ) := hmulW
  have hsub1 : Finset.univ.filter (fun y : Fin M =>
      |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ)))
      ⊆ Finset.univ.filter (fun y : Fin M =>
        |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hmain y hy

  have hsub2 : Finset.univ.filter (fun y : Fin M =>
      |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ))
      ⊆ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = ((S.card : ℕ) : ℤ)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hlt : |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| < 1 / 2 :=
      lt_of_le_of_lt hy hwin
    unfold exactCountOutput
    apply Int.floor_eq_iff.mpr
    obtain ⟨hl, hu⟩ := abs_lt.mp hlt
    push_cast
    constructor <;> linarith

  have hmono1 := Finset.sum_le_sum_of_subset_of_nonneg hsub1
    (fun y _ _ => (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).nonneg y)
  have hmono2 := Finset.sum_le_sum_of_subset_of_nonneg hsub2
    (fun y _ _ => (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).nonneg y)
  calc 8 / Real.pi ^ 2
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ))),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y := hbhmt
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y := hmono1
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          exactCountOutput N y = ((S.card : ℕ) : ℤ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y := hmono2
    _ = nextCor4FinalMass hN S M hM := rfl

/-- The product of two preliminary success lower bounds `31 / 32` and the final lower bound `8 /
Real.pi ^ 2` is at least `3 / 4`. -/
theorem nextCor4_success_constant : 3 / 4 ≤ (31 / 32) * (31 / 32) * (8 / Real.pi ^ 2) := by
  have hpi : Real.pi ≤ 22 / 7 := (lt_trans Real.pi_lt_d6 (by norm_num)).le
  have hpisq : Real.pi ^ 2 ≤ ((22 : ℝ) / 7) ^ 2 := by nlinarith [Real.pi_pos, hpi]
  have hstep : (3 : ℝ) / 4 * Real.pi ^ 2 ≤ ((961 : ℝ) / 1024) * 8 := by
    calc (3 : ℝ) / 4 * Real.pi ^ 2 ≤ (3 : ℝ) / 4 * ((22 : ℝ) / 7) ^ 2 :=
          mul_le_mul_of_nonneg_left hpisq (by norm_num : (0 : ℝ) ≤ 3 / 4)
      _ = 363 / 49 := by ring
      _ ≤ (961 : ℝ) / 1024 * 8 := by norm_num
  refine ?_
  rw [show ((31 : ℝ) / 32) * ((31 : ℝ) / 32) = ((961 : ℝ) / 1024) from by norm_num,
    show ((961 : ℝ) / 1024) * (8 / Real.pi ^ 2) =
        (((961 : ℝ) / 1024) * 8) / Real.pi ^ 2 from by ring,
    le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
  exact hstep

/-- If a good-label set has mass at least `31 / 32` under a nonnegative normalized law `p`, and
nonnegative `q` is at least `8 / Real.pi ^ 2` on each good-label pair, then its product-law
average is at least `(31 / 32) * (31 / 32) * (8 / Real.pi ^ 2)`. -/
private theorem nextCor4_joint_assembly {M : ℕ} (p : Fin M → ℝ) (hp0 : ∀ z, 0 ≤ p z)
    (_hp1 : ∑ z, p z = 1) (G : Finset (Fin M))
    (mG : 31 / 32 ≤ ∑ z ∈ G, p z) (q : Fin M → Fin M → ℝ) (hq0 : ∀ z₁ z₂, 0 ≤ q z₁ z₂)
    (hqG : ∀ z₁ ∈ G, ∀ z₂ ∈ G, 8 / Real.pi ^ 2 ≤ q z₁ z₂) :
    (31 / 32) * (31 / 32) * (8 / Real.pi ^ 2) ≤ ∑ z₁, ∑ z₂, p z₁ * p z₂ * q z₁ z₂ := by
  have hstep1 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂
      ≤ ∑ z₁ : Fin M, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      (fun z₁ _ _ => Finset.sum_nonneg (fun z₂ _ =>
        mul_nonneg (mul_nonneg (hp0 z₁) (hp0 z₂)) (hq0 z₁ z₂)))
  have h1 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂
      ≤ ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁ * p z₂ * q z₁ z₂ :=
    hstep1.trans (Finset.sum_le_sum (fun z₁ _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        (fun z₂ _ _ => mul_nonneg (mul_nonneg (hp0 z₁) (hp0 z₂)) (hq0 z₁ z₂))))
  have hpt : ∀ z₁ ∈ G, ∀ z₂ ∈ G,
      (8 / Real.pi ^ 2) * (p z₁ * p z₂) ≤ p z₁ * p z₂ * q z₁ z₂ := by
    intro z₁ hz₁ z₂ hz₂
    have h := mul_le_mul_of_nonneg_right (hqG z₁ hz₁ z₂ hz₂)
      (mul_nonneg (hp0 z₁) (hp0 z₂))
    rwa [mul_comm (q z₁ z₂) (p z₁ * p z₂)] at h
  have h2 : (8 / Real.pi ^ 2) * (∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂)
      ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ := by
    calc (8 / Real.pi ^ 2) * (∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂)
        = ∑ z₁ ∈ G, ∑ z₂ ∈ G, (8 / Real.pi ^ 2) * (p z₁ * p z₂) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z₁ _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ :=
          Finset.sum_le_sum (fun z₁ hz₁ => Finset.sum_le_sum (fun z₂ hz₂ => hpt z₁ hz₁ z₂ hz₂))
  have h3 : ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ = (∑ z ∈ G, p z) * (∑ z ∈ G, p z) := by
    rw [Finset.sum_mul_sum]
  have hGG : (31 / 32) * (31 / 32) ≤ (∑ z ∈ G, p z) * (∑ z ∈ G, p z) :=
    mul_le_mul mG mG (show (0 : ℝ) ≤ 31 / 32 by norm_num)
      (Finset.sum_nonneg (fun z _ => hp0 z))
  have hfin : (31 / 32) * (31 / 32) * (8 / Real.pi ^ 2)
      ≤ (8 / Real.pi ^ 2) * ((∑ z ∈ G, p z) * (∑ z ∈ G, p z)) := by
    calc (31 / 32) * (31 / 32) * (8 / Real.pi ^ 2)
        = (8 / Real.pi ^ 2) * ((31 / 32) * (31 / 32)) := by ring
      _ ≤ (8 / Real.pi ^ 2) * ((∑ z ∈ G, p z) * (∑ z ∈ G, p z)) :=
          mul_le_mul_of_nonneg_left hGG (by positivity)
  calc (31 / 32) * (31 / 32) * (8 / Real.pi ^ 2)
      ≤ (8 / Real.pi ^ 2) * (∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂) := hfin.trans_eq (by rw [h3])
    _ ≤ ∑ z₁ ∈ G, ∑ z₂ ∈ G, p z₁ * p z₂ * q z₁ z₂ := h2
    _ ≤ ∑ z₁ : Fin M, ∑ z₂ : Fin M, p z₁ * p z₂ * q z₁ z₂ := h1

/-- For positive `N` and `1 ≤ S.card ≤ N / 2`, the two-preliminary-sample adaptive counting
construction has `nextCor4SuccessMass` at least `3 / 4`, provided its preliminary and final
grids all have size at least two. -/
theorem nextCor4_success {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2)
    (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂)) :
    3 / 4 ≤ nextCor4SuccessMass hN S hM₀ hM := by
  have hcardle : (S.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN

  have hp0 : ∀ z : Fin (nextCor4RoughGrid N),
      (0 : ℝ) ≤ (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z := fun z =>
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).nonneg z

  have hqG : ∀ z₁ ∈ nextCor4Good N (S.card : ℝ), ∀ z₂ ∈ nextCor4Good N (S.card : ℝ),
      8 / Real.pi ^ 2 ≤
        nextCor4FinalMass hN S
          (nextCor4Grid N
            ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
            ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
          (hM z₁ z₂) := by
    intro z₁ hz₁ z₂ hz₂
    have hr₁ := nextCor4_rough_range hN S hz₁ hcard
    have hr₂ := nextCor4_rough_range hN S hz₂ hcard
    have hmin1 : (S.card : ℝ) / 2 ≤ min ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) := le_min hr₁.1 hr₂.1
    have hmin2 : min ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) ≤ 3 * (S.card : ℝ) / 2 :=
      le_trans (min_le_left _ _) hr₁.2
    have hgrid : 48 * Real.sqrt ((min ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) + 1) *
        ((N : ℝ) - min ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) + 1))
        ≤ (nextCor4Grid N
          ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
          ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) : ℝ) := by
      rw [nextCor4Grid]
      exact Nat.le_ceil _
    have hwin := nextCor4_final_window_lt_half hN hcard hcardN hmin1 hmin2 hgrid
    exact nextCor4_final_mass hN S
      (nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
      (hM z₁ z₂) hwin
  have hq0 : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N), (0 : ℝ) ≤
      nextCor4FinalMass hN S
        (nextCor4Grid N
          ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
          ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
        (hM z₁ z₂) := by
    intro z₁ z₂
    exact Finset.sum_nonneg (fun y _ =>
      (aeLaw (nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
        (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) (hM z₁ z₂)).nonneg y)
  have hmass := nextCor4_joint_assembly
    (fun z : Fin (nextCor4RoughGrid N) =>
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) hM₀).prob z)
    hp0 (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM₀).sum_one
    (nextCor4Good N (S.card : ℝ))
    (by
      have h := nextCor4_rough_mass hN S
      have hnum : (1 : ℝ) - 1 / (2 * ((17 : ℝ) - 1)) = 31 / 32 := by norm_num
      rw [hnum] at h
      exact h)
    (fun z₁ z₂ => nextCor4FinalMass hN S
      (nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
      (hM z₁ z₂))
    hq0 hqG
  have hconst := nextCor4_success_constant
  unfold nextCor4SuccessMass
  exact hconst.trans hmass

/-- For positive `N`, `M ≥ 2`, and an empty marked set, the zero phase label has probability one
and its exact count output is zero. -/
theorem nextCor4_zero_branch {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (M : ℕ) (hM : 2 ≤ M)
    (hzero : S.card = 0) :
    ∀ y : Fin M, y.val = 0 →
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y = 1 ∧
      exactCountOutput N y = 0 := by
  intro y hy
  have hmass : MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S = 0 := by
    rw [prepared_qft_mark_mass N hN S]
    simp [hzero]
  have hz := nextRelative_zero (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN)
    M hM 1 hmass y hy
  refine ⟨hz.1, ?_⟩
  unfold exactCountOutput
  rw [hz.2.1]
  norm_num

/-- The output-bit budget `3 * Nat.clog 2 (N + 1) + 16` for the adaptive exact-counting
construction. -/
noncomputable def nextCor4OutputBits (N : ℕ) : ℕ := 3 * Nat.clog 2 (N + 1) + 16

/-- The space budget `2 * nextCor4OutputBits N + 4` for the adaptive exact-counting
construction. -/
noncomputable def nextCor4SpaceBudget (N : ℕ) : ℕ := 2 * nextCor4OutputBits N + 4

/-- The Corollary 4 and efficient-counting output budgets each cover `Nat.clog 2 (N + 1)`, and
their space budgets each cover twice the corresponding output budget. -/
theorem nextCor4_space (N : ℕ) :
    Nat.clog 2 (N + 1) ≤ nextCor4OutputBits N ∧
    2 * nextCor4OutputBits N ≤ nextCor4SpaceBudget N ∧
    Nat.clog 2 (N + 1) ≤ Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0 ∧
    2 * Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0 ≤ Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountSpaceBudget N 0 := by
  have h1 : Nat.clog 2 (N + 1) ≤ nextCor4OutputBits N := by
    unfold nextCor4OutputBits
    omega
  have h2 : 2 * nextCor4OutputBits N ≤ nextCor4SpaceBudget N := by
    unfold nextCor4SpaceBudget
    omega
  have h3 : Nat.clog 2 (N + 1) ≤ Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0 := by
    unfold Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget
    omega
  have h4 : 2 * Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0
      ≤ Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountSpaceBudget N 0 := by
    unfold Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountSpaceBudget
    omega
  exact ⟨h1, h2, h3, h4⟩

/-- For `0 < r < 1`, every finite sum of the powers `r ^ (i + 1)` is bounded by the
geometric-series value `r / (1 - r)`. -/
theorem sum_pow_succ_le (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (L : ℕ) :
    (∑ i ∈ Finset.range L, r ^ (i + 1)) ≤ r / (1 - r) := by
  have hne : r ≠ 1 := by linarith
  have key : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, r ^ (i + 1)) ≤ r * (1 - r ^ n) / (1 - r) := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hpow : (0:ℝ) ≤ r ^ n := by positivity
        calc (∑ i ∈ Finset.range (n + 1), r ^ (i + 1))
            = r ^ (n + 1) + ∑ i ∈ Finset.range n, r ^ (i + 1) := by
              rw [Finset.sum_range_succ]; ring
          _ ≤ r ^ (n + 1) + r * (1 - r ^ n) / (1 - r) := by
            simpa [add_comm] using! add_le_add_left ih (r ^ (n + 1))
          _ = r * (1 - r ^ (n + 1)) / (1 - r) := by field_simp; ring
  have h := key L
  have hpow : (0:ℝ) ≤ r ^ L := by positivity
  have hden : (0:ℝ) < 1 - r := by linarith
  refine h.trans ?_
  have hle : (1:ℝ) - r ^ L ≤ 1 := by linarith
  have hm : (0:ℝ) ≤ r := hr0.le
  have hmul : r * (1 - r ^ L) ≤ r * 1 := mul_le_mul_of_nonneg_left hle hm
  exact div_le_div_of_nonneg_right (by simpa using! hmul) hden.le

/-- Every natural-number power `4 ^ (j + 1)` is at least two. -/
theorem two_le_four_pow (j : ℕ) : 2 ≤ 4 ^ (j + 1) := by
  have h1 : ∀ n : ℕ, 1 ≤ 4 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; nlinarith
  have h2 : 4 * 1 ≤ 4 * 4 ^ j := Nat.mul_le_mul_left 4 (h1 j)
  have h3 : 4 ^ j * 4 = 4 ^ (j + 1) := by rw [pow_succ]
  have h4 : 4 * 4 ^ j = 4 ^ j * 4 := Nat.mul_comm _ _
  omega

/-- The level-`j` counting window on `nextCor4RoughGrid N`, using the tail parameter `4 ^ (j +
1)` in `nextCor4Window`. -/
noncomputable def ladderWindow (N : ℕ) (j : ℕ) (t : ℝ) : ℝ :=
  nextCor4Window (nextCor4RoughGrid N) (4 ^ (j + 1)) N t

/-- The cost function `Real.sqrt ((v + 1) * ((N : ℝ) + 1))` used to bound the refinement ledger
at an estimated count `v`. -/
noncomputable def ladderCost (v : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt ((v + 1) * ((N : ℝ) + 1))

/-- For fixed `N`, `ladderCost` is monotone in its real-valued estimate. -/
theorem ladderCost_mono {N : ℕ} {v w : ℝ} (hvw : v ≤ w) :
    ladderCost v N ≤ ladderCost w N := by
  have hN : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
  have h1 : (v + 1) * ((N : ℝ) + 1) ≤ (w + 1) * ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  exact Real.sqrt_le_sqrt h1

/-- For `N > 0` and `0 ≤ t ≤ N`, the rough-grid window is at most `k * Real.sqrt t / 40 + k ^ 2
/ 6400`. -/
theorem nextCor4Window_le {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ))
    (k : ℕ) :
    nextCor4Window (nextCor4RoughGrid N) k N t
      ≤ (k : ℝ) * Real.sqrt t / 40 + (k : ℝ) ^ 2 / 6400 := by
  have hMge : 80 * Real.pi * Real.sqrt (N : ℝ) ≤ (nextCor4RoughGrid N : ℝ) := by
    rw [nextCor4RoughGrid]
    exact Nat.le_ceil _
  have hMpos : (0 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hgap : 0 ≤ (N : ℝ) - t := by linarith
  have hsqrtD : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt (t * (N : ℝ)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtNt : Real.sqrt (t * (N : ℝ)) = Real.sqrt t * Real.sqrt (N : ℝ) :=
    Real.sqrt_mul ht0 _
  have hA : 2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
      (nextCor4RoughGrid N : ℝ) ≤ (k : ℝ) / 40 * Real.sqrt t := by
    have hrecip : 1 / (nextCor4RoughGrid N : ℝ) ≤ 1 / (80 * Real.pi * Real.sqrt (N : ℝ)) :=
      one_div_le_one_div_of_le hMpos hMge
    have hnum : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt (t * (N : ℝ)) := by
      have : (0:ℝ) ≤ Real.sqrt (t * (N : ℝ)) := Real.sqrt_nonneg _
      positivity
    have hstep : 2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
          (nextCor4RoughGrid N : ℝ)
        ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt (t * (N : ℝ)) / (nextCor4RoughGrid N : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ ?_
      · exact mul_le_mul_of_nonneg_left hsqrtD (by positivity)
      · exact le_of_lt (lt_of_lt_of_le hMpos hMge)
    calc 2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
          (nextCor4RoughGrid N : ℝ)
        ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt (t * (N : ℝ)) / (nextCor4RoughGrid N : ℝ) := hstep
      _ = 2 * Real.pi * (k : ℝ) * Real.sqrt (t * (N : ℝ)) *
          (1 / (nextCor4RoughGrid N : ℝ)) := by field_simp
      _ ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt (t * (N : ℝ)) *
          (1 / (80 * Real.pi * Real.sqrt (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hrecip hnum
      _ = (k : ℝ) / 40 * Real.sqrt t := by
        rw [hsqrtNt]
        field_simp
        ring
  have hB : Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (nextCor4RoughGrid N : ℝ) ^ 2
      ≤ (k : ℝ) ^ 2 / 6400 := by
    have hsq : (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 ≤ (nextCor4RoughGrid N : ℝ) ^ 2 := by
      have hnonneg : 0 ≤ 80 * Real.pi * Real.sqrt (N : ℝ) := by positivity
      nlinarith [sq_nonneg (nextCor4RoughGrid N : ℝ)]
    have hMpos2 : (0 : ℝ) < (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 := sq_pos_of_pos hMpos
    have hrecip2 : 1 / (nextCor4RoughGrid N : ℝ) ^ 2
        ≤ 1 / (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2 :=
      one_div_le_one_div_of_le hMpos2 hsq
    have hnum : (0 : ℝ) ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) := by positivity
    calc Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (nextCor4RoughGrid N : ℝ) ^ 2
        = Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) * (1 / (nextCor4RoughGrid N : ℝ) ^ 2) := by
          field_simp
      _ ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) *
          (1 / (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hrecip2 hnum
      _ = (k : ℝ) ^ 2 / 6400 := by
        have hsq2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
        rw [show (80 * Real.pi * Real.sqrt (N : ℝ)) ^ 2
            = 6400 * Real.pi ^ 2 * (N : ℝ) by
          rw [mul_pow, mul_pow, hsq2]; ring]
        field_simp [hNne, hpine]
  unfold nextCor4Window
  linarith

/-- For `N > 0` and `0 ≤ t ≤ N`, `ladderWindow N j t` is at most `4 ^ (j + 1) * Real.sqrt t / 40
+ 16 ^ (j + 1) / 6400`, with the natural powers cast to the reals. -/
theorem ladderWindow_le {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ))
    (j : ℕ) :
    ladderWindow N j t ≤ ((4 ^ (j + 1) : ℕ) : ℝ) * Real.sqrt t / 40 +
      ((16 ^ (j + 1) : ℕ) : ℝ) / 6400 := by
  have hk : ((4 ^ (j + 1) : ℕ) : ℝ) ^ 2 = ((16 ^ (j + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    calc ((4 : ℝ) ^ (j + 1)) ^ 2 = (4:ℝ) ^ ((j + 1) * 2) := (pow_mul _ _ _).symm
      _ = ((4:ℝ)^2) ^ (j + 1) := by
          rw [show (j + 1) * 2 = 2 * (j + 1) by omega, pow_mul]
      _ = (16:ℝ) ^ (j + 1) := by rw [show (4:ℝ)^2 = (16:ℝ) by norm_num]
  have h := nextCor4Window_le hN ht0 htN (4 ^ (j + 1))
  unfold ladderWindow at h
  rw [hk] at h
  exact h

/-- The probability of rough-grid label `z` under `aeLaw` for the marked set `S`, using the QFT
preparation of the zero basis state on `Fin N`. -/
noncomputable def firstProb {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (z : Fin (nextCor4RoughGrid N)) : ℝ :=
  (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
    (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z

/-- The real count estimate `N * aeEstimate (nextCor4RoughGrid N) z` associated with a
rough-grid label. -/
noncomputable def firstReadout {N : ℕ} (z : Fin (nextCor4RoughGrid N)) : ℝ :=
  (N : ℝ) * aeEstimate (nextCor4RoughGrid N) z

/-- The rough-grid labels whose `firstReadout` strictly exceeds `S.card` plus the level-`j`
ladder window. -/
noncomputable def overSet {N : ℕ} (S : Finset (Fin N)) (j : ℕ) :
    Finset (Fin (nextCor4RoughGrid N)) :=
  Finset.univ.filter (fun z =>
    (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < firstReadout z)

/-- For `N > 0`, the `firstProb` mass of `overSet S j` is at most `1 / (2 * (4 ^ (j + 1) - 1))`,
with the power interpreted in the reals. -/
theorem over_mass_le {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (j : ℕ) :
    (∑ z ∈ overSet S j, firstProb hN S z)
      ≤ 1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)) := by
  have hp := two_le_four_pow j
  have hw := bhmt_counting_k2_window N (nextCor4RoughGrid N) S hN
    (nextCor4_rough_grid_two hN) (4 ^ (j + 1)) hp
  have hg : (∑ z ∈ Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
      |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
        ladderWindow N j (S.card : ℝ)),
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z)
      ≥ 1 - 1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)) := by
    simpa [ladderWindow, nextCor4Window] using! hw
  set G := Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
      |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
        ladderWindow N j (S.card : ℝ)) with hGdef
  have hpart : (∑ z ∈ G, (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z)
      + (∑ z ∈ Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
          ¬ |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
            ladderWindow N j (S.card : ℝ)),
        (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z)
      = 1 := by
    have h1 := (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).sum_one
    rw [← h1]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun z : Fin (nextCor4RoughGrid N) =>
        |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
          ladderWindow N j (S.card : ℝ))
      (fun z : Fin (nextCor4RoughGrid N) =>
        (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z)
  have hbad : (∑ z ∈ Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
      ¬ |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
        ladderWindow N j (S.card : ℝ)),
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z)
      ≤ 1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)) := by
    have h1 := hg
    rw [hGdef] at h1
    linarith [hpart, h1]
  have hsub : overSet S j ⊆ Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
      ¬ |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
        ladderWindow N j (S.card : ℝ)) := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hgood
    have habs := abs_le.mp hgood
    simp only [firstReadout] at hz'
    linarith [habs.1, habs.2]
  have hnonneg : ∀ z ∈ Finset.univ.filter (fun z : Fin (nextCor4RoughGrid N) =>
      ¬ |(N : ℝ) * aeEstimate (nextCor4RoughGrid N) z - (S.card : ℝ)| ≤
        ladderWindow N j (S.card : ℝ)), z ∉ overSet S j → (0:ℝ) ≤
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z := by
    intro z _ _
    exact (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).nonneg z
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  exact hmono.trans hbad

/-- The product-law probability that two independent rough labels both lie in `overSet S j` is
bounded by the square of `1 / (2 * (4 ^ (j + 1) - 1))`. -/
theorem pair_over_mass_le {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (j : ℕ) :
    (∑ z ∈ (overSet S j) ×ˢ (overSet S j),
        (firstProb hN S z.1) * (firstProb hN S z.2))
      ≤ (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
        (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) := by
  have hone := over_mass_le hN S j
  have hp := two_le_four_pow j
  have h1 : (∑ z ∈ (overSet S j) ×ˢ (overSet S j),
        (firstProb hN S z.1) * (firstProb hN S z.2))
      = (∑ z ∈ overSet S j, firstProb hN S z) * (∑ z ∈ overSet S j, firstProb hN S z) := by
    rw [Finset.sum_product]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  rw [h1]
  have hden : 0 < 2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1) := by
    have h1' : (2:ℝ) ≤ ((4 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hp
    linarith
  have hX : 0 ≤ ∑ z ∈ overSet S j, firstProb hN S z := by
    apply Finset.sum_nonneg
    intro z _
    exact (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).nonneg z
  exact mul_le_mul hone hone hX (div_nonneg (by norm_num) (le_of_lt hden))

/-- The ladder window is nonnegative whenever `N > 0` and `0 ≤ t ≤ N`. -/
theorem ladderWindow_nonneg {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t)
    (htN : t ≤ (N : ℝ)) (j : ℕ) :
    0 ≤ ladderWindow N j t := by
  have hD : 0 ≤ t * ((N : ℝ) - t) := mul_nonneg ht0 (sub_nonneg.mpr htN)
  have hM : (0 : ℝ) < (nextCor4RoughGrid N : ℝ) := by
    have hMge : 80 * Real.pi * Real.sqrt (N : ℝ) ≤ (nextCor4RoughGrid N : ℝ) := by
      rw [nextCor4RoughGrid]
      exact Nat.le_ceil _
    have hMpos : (0 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by
      have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      positivity
    exact lt_of_lt_of_le hMpos hMge
  unfold ladderWindow nextCor4Window
  have h1 : 0 ≤ 2 * Real.pi * ((4 ^ (j + 1) : ℕ) : ℝ) *
      Real.sqrt (t * ((N : ℝ) - t)) / (nextCor4RoughGrid N : ℝ) := by
    have : (0:ℝ) ≤ Real.sqrt (t * ((N : ℝ) - t)) := Real.sqrt_nonneg _
    positivity
  have h2 : 0 ≤ Real.pi ^ 2 * ((4 ^ (j + 1) : ℕ) : ℝ) ^ 2 * (N : ℝ) /
      (nextCor4RoughGrid N : ℝ) ^ 2 := by
    have hN' : (0 : ℝ) ≤ (N : ℝ) := by positivity
    positivity
  linarith

/-- If `t < v ≤ t + ladderWindow N L t` with `L > 0` and `0 ≤ t ≤ N`, then `ladderCost v N` is
bounded by the base ladder cost plus the next-level costs for all crossed levels below `L`. -/
theorem ladder_pointwise_gt {N : ℕ} (hN : 0 < N) {t v : ℝ} (ht0 : 0 ≤ t)
    (htN : t ≤ (N : ℝ)) (L : ℕ) (hL : 0 < L) (htv : t < v)
    (hcross : v ≤ t + ladderWindow N L t) :
    ladderCost v N
      ≤ ladderCost (t + ladderWindow N 0 t) N
        + ∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0) := by
  classical
  have hlevel : ∀ j : ℕ, 0 ≤ ladderCost (t + ladderWindow N j t) N := by
    intro j
    have hw := ladderWindow_nonneg hN ht0 htN j
    unfold ladderCost
    have h1 : 0 ≤ (t + ladderWindow N j t + 1) * ((N : ℝ) + 1) := by positivity
    exact Real.sqrt_nonneg _
  have hex : ∃ j : ℕ, v ≤ t + ladderWindow N j t := ⟨L, hcross⟩
  have hjs : v ≤ t + ladderWindow N (Nat.find hex) t := Nat.find_spec hex
  have hjsle : Nat.find hex ≤ L := by
    by_contra hcon
    have hlt : L < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    exact hmin hcross
  by_cases hz : Nat.find hex = 0
  · have hvcross : v ≤ t + ladderWindow N 0 t := by
      rw [hz] at hjs
      exact hjs
    calc ladderCost v N ≤ ladderCost (t + ladderWindow N 0 t) N :=
        ladderCost_mono hvcross
      _ ≤ ladderCost (t + ladderWindow N 0 t) N +
          (∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0)) := by
        have hn : 0 ≤ ∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0) :=
          Finset.sum_nonneg (fun j _ => by
            by_cases hc : t + ladderWindow N j t < v
            · rw [if_pos hc]; exact hlevel (j + 1)
            · rw [if_neg hc])
        linarith
      _ = _ := rfl
  · have hpos : 0 < Nat.find hex := by omega
    have hmin := Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex)
    have hnotprev : ¬ (v ≤ t + ladderWindow N (Nat.find hex - 1) t) := hmin
    have hcond : t + ladderWindow N (Nat.find hex - 1) t < v := by linarith
    have hprevlt : Nat.find hex - 1 < L := by omega
    have hsum : (∑ j ∈ Finset.range L,
        (if t + ladderWindow N j t < v
         then ladderCost (t + ladderWindow N (j + 1) t) N else 0))
        ≥ ladderCost v N := by
      have hmem : Nat.find hex - 1 ∈ Finset.range L := Finset.mem_range.mpr hprevlt
      have hnonneg : ∀ b ∈ Finset.range L, 0 ≤
          (if t + ladderWindow N b t < v
           then ladderCost (t + ladderWindow N (b + 1) t) N else 0) := by
        intro b _
        by_cases hc : t + ladderWindow N b t < v
        · rw [if_pos hc]; exact hlevel (b + 1)
        · rw [if_neg hc]
      have hsingle := Finset.single_le_sum
        (f := fun b =>
          (if t + ladderWindow N b t < v
           then ladderCost (t + ladderWindow N (b + 1) t) N else 0))
        (fun b hb => hnonneg b hb) hmem
      have hval : (if t + ladderWindow N (Nat.find hex - 1) t < v
          then ladderCost (t + ladderWindow N ((Nat.find hex - 1) + 1) t) N else 0)
          ≥ ladderCost v N := by
        rw [if_pos hcond]
        have hstep : (Nat.find hex - 1) + 1 = Nat.find hex := by omega
        rw [hstep]
        exact ladderCost_mono hjs
      exact hval.trans hsingle
    calc ladderCost v N
        ≤ (∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0)) := hsum
      _ ≤ ladderCost (t + ladderWindow N 0 t) N +
          (∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0)) := by
        have hn : 0 ≤ ladderCost (t + ladderWindow N 0 t) N := hlevel 0
        linarith
      _ = _ := rfl

/-- The smaller of the two `firstReadout` values associated with a pair of rough-grid labels. -/
noncomputable def pairMin {N : ℕ} (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) : ℝ :=
  min (firstReadout z.1) (firstReadout z.2)

/-- Pairs whose `pairMin` strictly exceeds the level-`j` threshold are exactly the Cartesian
product `overSet S j ×ˢ overSet S j`. -/
theorem filter_overshoot_eq {N : ℕ} (S : Finset (Fin N)) (j : ℕ) :
    ((Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
        (Finset.univ : Finset (Fin (nextCor4RoughGrid N)))).filter
      (fun z => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z)
      = overSet S j ×ˢ overSet S j := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  have hmin : (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
      ↔ (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < firstReadout z.1 ∧
        (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < firstReadout z.2 := by
    simp only [pairMin]
    constructor
    · intro h
      have h1 : min (firstReadout z.1) (firstReadout z.2) ≤ firstReadout z.1 :=
        min_le_left _ _
      have h2 : min (firstReadout z.1) (firstReadout z.2) ≤ firstReadout z.2 :=
        min_le_right _ _
      exact ⟨lt_of_lt_of_le h h1, lt_of_lt_of_le h h2⟩
    · intro h
      exact lt_min h.1 h.2
  rw [hmin]
  simp only [overSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The product-law mass of pairs whose `pairMin` exceeds `S.card + ladderWindow N j S.card` is
bounded by the square of the single-label tail bound. -/
theorem sum_pair_overshoot_le {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (j : ℕ) :
    (∑ z ∈ ((Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
        (Finset.univ : Finset (Fin (nextCor4RoughGrid N)))).filter
      (fun z => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z),
        (firstProb hN S z.1) * (firstProb hN S z.2))
      ≤ (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
        (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) := by
  rw [filter_overshoot_eq]
  exact pair_over_mass_le hN S j

/-- For `N > 0` and `0 ≤ t ≤ N / 2`, the linear term `2 * Real.pi * 4 ^ (j + 1) * Real.sqrt (t *
(N - t)) / nextCor4RoughGrid N` is bounded by `ladderWindow N j t`. -/
theorem ladderWindow_ge {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t)
    (htN : t ≤ (N : ℝ) / 2) (j : ℕ) :
    2 * Real.pi * ((4 ^ (j + 1) : ℕ) : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) /
        (nextCor4RoughGrid N : ℝ)
      ≤ ladderWindow N j t := by
  have hMge : 80 * Real.pi * Real.sqrt (N : ℝ) ≤ (nextCor4RoughGrid N : ℝ) := by
    rw [nextCor4RoughGrid]
    exact Nat.le_ceil _
  have hMpos : (0 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hMpos' : (0 : ℝ) < (nextCor4RoughGrid N : ℝ) := lt_of_lt_of_le hMpos hMge
  have hgap : 0 ≤ (N : ℝ) - t := by linarith
  have hD : 0 ≤ t * ((N : ℝ) - t) := mul_nonneg ht0 hgap
  have hsqrtD : Real.sqrt (t * ((N : ℝ) - t)) ≤ Real.sqrt (t * (N : ℝ)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtNt : Real.sqrt (t * (N : ℝ)) = Real.sqrt t * Real.sqrt (N : ℝ) :=
    Real.sqrt_mul ht0 _
  unfold ladderWindow nextCor4Window
  have h1 : 0 ≤ 2 * Real.pi * ((4 ^ (j + 1) : ℕ) : ℝ) *
      Real.sqrt (t * ((N : ℝ) - t)) / (nextCor4RoughGrid N : ℝ) := by
    have : (0:ℝ) ≤ Real.sqrt (t * ((N : ℝ) - t)) := Real.sqrt_nonneg _
    positivity
  have h2 : 0 ≤ Real.pi ^ 2 * ((4 ^ (j + 1) : ℕ) : ℝ) ^ 2 * (N : ℝ) /
      (nextCor4RoughGrid N : ℝ) ^ 2 := by
    have hN' : (0 : ℝ) ≤ (N : ℝ) := by positivity
    positivity
  linarith

/-- For `v` below the top of a positive finite ladder, `ladderCost v N` is bounded by
indicator-weighted costs for `v ≤ t`, `t < v`, and each crossed ladder level, assuming `N >
0` and `0 ≤ t ≤ N`. -/
theorem ladder_pointwise_all {N : ℕ} (hN : 0 < N) {t v : ℝ} (ht0 : 0 ≤ t)
    (htN : t ≤ (N : ℝ)) (L : ℕ) (hL : 0 < L) (hcross : v ≤ t + ladderWindow N L t) :
    ladderCost v N
      ≤ ladderCost t N * (if v ≤ t then 1 else 0)
        + ladderCost (t + ladderWindow N 0 t) N * (if t < v then 1 else 0)
        + ∑ j ∈ Finset.range L,
            (if t + ladderWindow N j t < v
             then ladderCost (t + ladderWindow N (j + 1) t) N else 0) := by
  by_cases htv : t < v
  · have h1 := ladder_pointwise_gt hN ht0 htN L hL htv hcross
    have hbase : ladderCost (t + ladderWindow N 0 t) N * (if t < v then 1 else 0)
        = ladderCost (t + ladderWindow N 0 t) N := by rw [if_pos htv, mul_one]
    rw [if_pos htv, if_neg (by linarith : ¬ (v ≤ t))]
    have hn : 0 ≤ ∑ j ∈ Finset.range L,
        (if t + ladderWindow N j t < v
         then ladderCost (t + ladderWindow N (j + 1) t) N else 0) := by
      apply Finset.sum_nonneg
      intro j _
      by_cases hc : t + ladderWindow N j t < v
      · rw [if_pos hc]
        have hw := ladderWindow_nonneg hN ht0 htN (j + 1)
        unfold ladderCost
        have h1 : 0 ≤ (t + ladderWindow N (j + 1) t + 1) * ((N : ℝ) + 1) := by positivity
        exact Real.sqrt_nonneg _
      · rw [if_neg hc]
    linarith
  · have hvle : v ≤ t := by linarith
    rw [if_pos hvle, if_neg htv]
    have hmono : ladderCost v N ≤ ladderCost t N := ladderCost_mono hvle
    have hn : 0 ≤ ∑ j ∈ Finset.range L,
        (if t + ladderWindow N j t < v
         then ladderCost (t + ladderWindow N (j + 1) t) N else 0) := by
      apply Finset.sum_nonneg
      intro j _
      by_cases hc : t + ladderWindow N j t < v
      · rw [if_pos hc]
        have hw := ladderWindow_nonneg hN ht0 htN (j + 1)
        unfold ladderCost
        have h1 : 0 ≤ (t + ladderWindow N (j + 1) t + 1) * ((N : ℝ) + 1) := by positivity
        exact Real.sqrt_nonneg _
      · rw [if_neg hc]
    linarith

/-- For `N > 0` and `1 ≤ t ≤ N / 2`, the level `N + 3` ladder window is at least `N`. -/
theorem ladder_top_ge {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 1 ≤ t)
    (htN : t ≤ (N : ℝ) / 2) :
    (N : ℝ) ≤ ladderWindow N (N + 3) t := by
  have hN' : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMge : 80 * Real.pi * Real.sqrt (N : ℝ) ≤ (nextCor4RoughGrid N : ℝ) := by
    rw [nextCor4RoughGrid]
    exact Nat.le_ceil _
  have hMpos : (0 : ℝ) < 80 * Real.pi * Real.sqrt (N : ℝ) := by positivity
  have hMle : (nextCor4RoughGrid N : ℝ) ≤ 81 * Real.pi * Real.sqrt (N : ℝ) := by
    have hceil : (nextCor4RoughGrid N : ℝ) ≤ 80 * Real.pi * Real.sqrt (N : ℝ) + 1 := by
      rw [nextCor4RoughGrid]
      have hc := Nat.ceil_lt_add_one (a := 80 * Real.pi * Real.sqrt (N : ℝ)) (by positivity)
      exact le_of_lt hc
    have hN2 : (1:ℝ) ≤ (N : ℝ) := by
      have hn : (1:ℕ) ≤ N := Nat.succ_le_of_lt hN
      exact_mod_cast hn
    have hpi : (1:ℝ) ≤ Real.pi := by
      have := Real.pi_gt_three
      linarith
    have hsqrt : (1:ℝ) ≤ Real.sqrt (N : ℝ) := (Real.one_le_sqrt).2 hN2
    nlinarith
  have hgap : (0:ℝ) ≤ (N : ℝ) - t := by linarith
  have hhalf : (N : ℝ) / 2 ≤ (N : ℝ) - t := by linarith
  have hpow : ∀ n : ℕ, n + 1 ≤ 4 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hrec := ih
        nlinarith
  have hbig : 256 * (N : ℕ) ≤ 4 ^ (N + 4) := by
    have h1 : (N : ℕ) + 1 ≤ 4 ^ N := hpow N
    have h2 : 4 ^ N * 256 = 4 ^ (N + 4) := by rw [Nat.pow_add]
    omega
  have hsqrtD : Real.sqrt (t * ((N : ℝ) - t)) ≥ Real.sqrt (N : ℝ) / 2 := by
    have h2 : (N : ℝ) / 4 ≤ t * ((N : ℝ) - t) := by
      have hm := mul_le_mul (show (1:ℝ) ≤ t by linarith) hhalf
        (by positivity : (0:ℝ) ≤ (N : ℝ) / 2) (by linarith : (0:ℝ) ≤ t)
      linarith
    have h4 : Real.sqrt ((N : ℝ) / 4) = Real.sqrt (N : ℝ) / 2 := by
      rw [Real.sqrt_div (by positivity), show Real.sqrt 4 = 2 by norm_num]
    have h5 : Real.sqrt ((N : ℝ) / 4) ≤ Real.sqrt (t * ((N : ℝ) - t)) :=
      Real.sqrt_le_sqrt h2
    linarith
  have hlow := ladderWindow_ge hN (by linarith) htN (N + 3)
  have hk : (4 ^ ((N + 3) + 1) : ℕ) = 4 ^ (N + 4) := by congr 1
  rw [hk] at hlow
  have hA' : (256 : ℝ) * (N : ℝ) ≤ ((4 ^ (N + 4) : ℕ) : ℝ) := by
    exact_mod_cast hbig
  have hC1 : (256 : ℝ) * (N : ℝ) * (2 * Real.pi)
      ≤ ((4 ^ (N + 4) : ℕ) : ℝ) * (2 * Real.pi) :=
    mul_le_mul hA' (le_refl _) (by positivity) (by positivity)
  have hC1' : (256 : ℝ) * (N : ℝ) * (2 * Real.pi) * (Real.sqrt (N : ℝ) / 2)
      ≤ ((4 ^ (N + 4) : ℕ) : ℝ) * (2 * Real.pi) * (Real.sqrt (N : ℝ) / 2) :=
    mul_le_mul hC1 (le_refl _) (by positivity) (by positivity)
  have hC2 : ((4 ^ (N + 4) : ℕ) : ℝ) * (2 * Real.pi) * (Real.sqrt (N : ℝ) / 2)
      ≤ ((4 ^ (N + 4) : ℕ) : ℝ) * (2 * Real.pi) * Real.sqrt (t * ((N : ℝ) - t)) :=
    mul_le_mul (le_refl _) hsqrtD (by positivity) (by positivity)
  have hkey : 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
      ≤ 2 * Real.pi * ((4 ^ (N + 4) : ℕ) : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) := by
    have e1 : 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
        = (256 : ℝ) * (N : ℝ) * (2 * Real.pi) * (Real.sqrt (N : ℝ) / 2) := by ring
    have e2 : 2 * Real.pi * ((4 ^ (N + 4) : ℕ) : ℝ) * Real.sqrt (t * ((N : ℝ) - t))
        = ((4 ^ (N + 4) : ℕ) : ℝ) * (2 * Real.pi) * Real.sqrt (t * ((N : ℝ) - t)) := by ring
    rw [e1, e2]
    exact hC1'.trans hC2
  have heq : 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
      / (81 * Real.pi * Real.sqrt (N : ℝ)) = (256 : ℝ) * (N : ℝ) / 81 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hsqrtN : Real.sqrt (N : ℝ) ≠ 0 := by positivity
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
  have hstep : 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
      / (nextCor4RoughGrid N : ℝ)
      ≥ 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
        / (81 * Real.pi * Real.sqrt (N : ℝ)) := by
    have hrecip : (81 * Real.pi * Real.sqrt (N : ℝ))⁻¹ ≤ (nextCor4RoughGrid N : ℝ)⁻¹ := by
      have h := one_div_le_one_div_of_le
        (show (0:ℝ) < (nextCor4RoughGrid N : ℝ) by exact lt_of_lt_of_le hMpos hMge) hMle
      simpa only [one_div] using! h
    have hnum : (0:ℝ) ≤ 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2) := by
      positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrecip hnum
  calc (N : ℝ)
      ≤ 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
          / (81 * Real.pi * Real.sqrt (N : ℝ)) := by
            rw [heq]
            have h81 : (256 : ℝ) / 81 ≥ 1 := by norm_num
            linarith
    _ ≤ 2 * Real.pi * (256 : ℝ) * (N : ℝ) * (Real.sqrt (N : ℝ) / 2)
          / (nextCor4RoughGrid N : ℝ) := hstep
    _ ≤ 2 * Real.pi * ((4 ^ (N + 4) : ℕ) : ℝ) * Real.sqrt (t * ((N : ℝ) - t))
          / (nextCor4RoughGrid N : ℝ) := by
            exact div_le_div_of_nonneg_right hkey (by positivity)
    _ ≤ ladderWindow N (N + 3) t := hlow

/-- Every rough-grid count readout is at most `N`. -/
theorem firstReadout_le {N : ℕ} (z : Fin (nextCor4RoughGrid N)) :
    firstReadout z ≤ (N : ℝ) := by
  have h := aeEstimate_mem (nextCor4RoughGrid N) z
  simp only [firstReadout]
  have h1 := mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg N)
  simpa using! h1

/-- The minimum readout of every pair of rough-grid labels is at most `N`. -/
theorem pairMin_le {N : ℕ} (z : Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :
    pairMin z ≤ (N : ℝ) := by
  simp only [pairMin]
  exact (min_le_left _ _).trans (firstReadout_le z.1)

/-- The squared tail bound `(1 / (2 * (4 ^ (j + 1) - 1))) ^ 2` for the minimum of two
independent rough readouts. -/
noncomputable def dyadWeight (j : ℕ) : ℝ :=
  (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
    (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)))

/-- Every dyadic tail weight `dyadWeight j` is nonnegative. -/
theorem dyadWeight_nonneg (j : ℕ) : 0 ≤ dyadWeight j := by
  have hden : 0 < 2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1) := by
    have h1 : (2:ℝ) ≤ ((4 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast two_le_four_pow j
    linarith
  unfold dyadWeight
  exact mul_nonneg (div_nonneg (by norm_num) hden.le) (div_nonneg (by norm_num) hden.le)

/-- The level-`j` squared tail weight is at most `(4 / 9) * (1 / 16) ^ (j + 1)`. -/
theorem dyadWeight_le {j : ℕ} :
    dyadWeight j ≤ (4/9) * (((1/16 : ℝ))^(j+1)) := by
  have h4 : (4:ℕ) ≤ 4 ^ (j + 1) := by
    have h1 : (1:ℕ) ≤ 4 ^ j := by
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ]; nlinarith
    rw [show 4 ^ (j + 1) = 4 * 4 ^ j by rw [pow_succ]; ring]
    omega
  have hden : 0 < 2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1) := by
    have h1 : (2:ℝ) ≤ ((4 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast two_le_four_pow j
    linarith
  have hkey : 2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)
      ≥ (3/2) * (((4 ^ (j + 1) : ℕ) : ℝ)) := by
    have h4' : (4:ℝ) ≤ ((4 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hcast : (((4 ^ (j + 1) : ℕ) : ℝ)) = ((4:ℝ)^(j+1)) := by
    rw [Nat.cast_pow]
    congr 1
  have hone : 1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))
      ≤ (2/3) * (((1/4 : ℝ))^(j+1)) := by
    refine (one_div_le_one_div_of_le
      (show 0 < (3/2) * (((4 ^ (j + 1) : ℕ) : ℝ)) by positivity) hkey).trans ?_
    rw [hcast]
    have e1 : 1 / ((3/2) * ((4:ℝ)^(j+1))) = (2/3) / ((4:ℝ)^(j+1)) := by
      ring
    have e2 : (2/3) / ((4:ℝ)^(j+1)) = (2/3) * (((1/4 : ℝ))^(j+1)) := by
      rw [div_pow, one_pow]
      ring
    rw [e1, e2]
  have hsq : (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
        (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)))
      ≤ ((2/3) * (((1/4 : ℝ))^(j+1))) * ((2/3) * (((1/4 : ℝ))^(j+1))) := by
    have h := mul_self_le_mul_self (by positivity) hone
    exact h
  have hsq2 : (((1/4 : ℝ))^(j+1)) * (((1/4 : ℝ))^(j+1)) = (((1/16 : ℝ))^(j+1)) := by
    calc (((1/4 : ℝ))^(j+1)) * (((1/4 : ℝ))^(j+1))
        = (((1/4 : ℝ)) * ((1/4 : ℝ)))^(j+1) := (mul_pow (1/4) (1/4) (j+1)).symm
      _ = ((1/16 : ℝ))^(j+1) := by norm_num
  unfold dyadWeight
  calc (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
        (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)))
      ≤ ((2/3) * (((1/4 : ℝ))^(j+1))) * ((2/3) * (((1/4 : ℝ))^(j+1))) := hsq
    _ = (4/9) * ((((1/4 : ℝ))^(j+1)) * (((1/4 : ℝ))^(j+1))) := by ring
    _ = (4/9) * (((1/16 : ℝ))^(j+1)) := by rw [hsq2]

/-- Multiplying `(1 / 16) ^ (j + 1)` by `2 ^ (j + 2)` gives `(1 / 4) * (1 / 8) ^ j` over the
reals. -/
theorem dyad_mix_two (j : ℕ) :
    ((1/16 : ℝ))^(j+1) * ((2:ℝ)^(j+2)) = (1/4) * (((1/8 : ℝ))^j) := by
  calc ((1/16 : ℝ))^(j+1) * ((2:ℝ)^(j+2))
      = ((1/16 : ℝ))^j * ((1/16 : ℝ)) * ((2:ℝ)^j) * (4:ℝ) := by
        rw [pow_succ, pow_succ]
        ring
    _ = (1/4) * (((1/16 : ℝ) * (2:ℝ))^j) := by
        rw [mul_pow]
        ring
    _ = (1/4) * (((1/8 : ℝ))^j) := by norm_num

/-- Multiplying `(1 / 16) ^ (j + 1)` by `4 ^ (j + 2)` gives `(1 / 4) ^ j` over the reals. -/
theorem dyad_mix_four (j : ℕ) :
    ((1/16 : ℝ))^(j+1) * ((4:ℝ)^(j+2)) = (((1/4 : ℝ))^j) := by
  calc ((1/16 : ℝ))^(j+1) * ((4:ℝ)^(j+2))
      = ((1/16 : ℝ))^j * ((1/16 : ℝ)) * ((4:ℝ)^j) * (16:ℝ) := by
        rw [pow_succ, pow_succ]
        ring
    _ = (((1/16 : ℝ) * (4:ℝ))^j) * ((1/16 : ℝ)) * (16:ℝ) := by
        rw [mul_pow]
        ring
    _ = ((1/4 : ℝ))^j := by ring

/-- Every finite initial sum of `dyadWeight` is at most `4 / 135`. -/
theorem dyadWeight_sum_le (L : ℕ) :
    (∑ j ∈ Finset.range L, dyadWeight j) ≤ 4 / 135 := by
  have h := sum_pow_succ_le (1/16 : ℝ) (by norm_num) (by norm_num) L
  have h15 : (1/16 : ℝ) / (1 - 1/16) = 1/15 := by norm_num
  have hge : (1/16 : ℝ) / (1 - 1/16) ≤ 1/15 := by rw [h15]
  calc (∑ j ∈ Finset.range L, dyadWeight j)
      ≤ ∑ j ∈ Finset.range L, (4/9) * (((1/16 : ℝ))^(j+1)) := by
        apply Finset.sum_le_sum
        intro j _
        exact dyadWeight_le (j := j)
    _ = (4/9) * (∑ j ∈ Finset.range L, ((1/16 : ℝ))^(j+1)) := by
        rw [Finset.mul_sum]
    _ ≤ (4/9) * (1/15) := by
      have h' : (∑ j ∈ Finset.range L, ((1/16 : ℝ))^(j+1)) ≤ 1/15 := h.trans hge
      exact mul_le_mul_of_nonneg_left h' (by norm_num)
    _ = 4/135 := by norm_num

/-- Every finite initial sum of `dyadWeight j * 2 ^ (j + 2)` is at most `8 / 63`. -/
theorem dyadWeight_two_sum_le (L : ℕ) :
    (∑ j ∈ Finset.range L, dyadWeight j * ((2:ℝ)^(j+2))) ≤ 8 / 63 := by
  have h := sum_pow_succ_le (1/8 : ℝ) (by norm_num) (by norm_num) L
  have h7 : (1/8 : ℝ) / (1 - 1/8) = 1/7 := by norm_num
  have hge : (1/8 : ℝ) / (1 - 1/8) ≤ 1/7 := by rw [h7]
  have hsum8 : (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j) ≤ 8 / 7 := by
    have h8 : ∀ j ∈ Finset.range L, ((1/8 : ℝ))^j = 8 * ((1/8 : ℝ))^(j+1) := by
      intro j _
      have e : ((1/8 : ℝ))^(j+1) * 8 = ((1/8 : ℝ))^j := by
        rw [pow_succ]
        field_simp
      have e2 : ((1/8 : ℝ))^j = 8 * ((1/8 : ℝ))^(j+1) := by
        rw [← e]
        ring
      exact e2
    calc (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j)
        = ∑ j ∈ Finset.range L, (8 * ((1/8 : ℝ))^(j+1)) :=
          Finset.sum_congr rfl h8
      _ = 8 * (∑ j ∈ Finset.range L, ((1/8 : ℝ))^(j+1)) := by rw [Finset.mul_sum]
      _ ≤ 8 * (1/7) := by
        have h' : (∑ j ∈ Finset.range L, ((1/8 : ℝ))^(j+1)) ≤ 1/7 := h.trans hge
        exact mul_le_mul_of_nonneg_left h' (by norm_num)
      _ = 8/7 := by norm_num
  calc (∑ j ∈ Finset.range L, dyadWeight j * ((2:ℝ)^(j+2)))
      ≤ ∑ j ∈ Finset.range L, (4/9) * (((1/16 : ℝ))^(j+1) * ((2:ℝ)^(j+2))) := by
        apply Finset.sum_le_sum
        intro j _
        have hmul : (0:ℝ) ≤ ((2:ℝ)^(j+2)) := by
          have h2 : (0:ℝ) ≤ (2:ℝ) := by norm_num
          exact pow_nonneg h2 _
        have h := mul_le_mul_of_nonneg_right (dyadWeight_le (j := j)) hmul
        calc dyadWeight j * ((2:ℝ)^(j+2))
            ≤ ((4/9) * ((1/16 : ℝ))^(j+1)) * ((2:ℝ)^(j+2)) := h
          _ = (4/9) * (((1/16 : ℝ))^(j+1) * ((2:ℝ)^(j+2))) := by ring
    _ = ∑ j ∈ Finset.range L, (4/9) * ((1/4) * (((1/8 : ℝ))^j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [dyad_mix_two]
    _ = (4/9) * (1/4) * (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ (4/9) * (1/4) * (8/7) := by
        have h1 : (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j) ≤ 8/7 := hsum8
        have h2 : (0:ℝ) ≤ (4/9) * (1/4) := by norm_num
        calc (4/9) * (1/4) * (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j)
            = (∑ j ∈ Finset.range L, ((1/8 : ℝ))^j) * ((4/9) * (1/4)) := by ring
          _ ≤ (8/7) * ((4/9) * (1/4)) := mul_le_mul_of_nonneg_right h1 h2
          _ = (4/9) * (1/4) * (8/7) := by ring
    _ = 8/63 := by norm_num

/-- Every finite initial sum of `dyadWeight j * 4 ^ (j + 2)` is at most `16 / 27`. -/
theorem dyadWeight_four_sum_le (L : ℕ) :
    (∑ j ∈ Finset.range L, dyadWeight j * ((4:ℝ)^(j+2))) ≤ 16 / 27 := by
  have h := sum_pow_succ_le (1/4 : ℝ) (by norm_num) (by norm_num) L
  have h3 : (1/4 : ℝ) / (1 - 1/4) = 1/3 := by norm_num
  have hge : (1/4 : ℝ) / (1 - 1/4) ≤ 1/3 := by rw [h3]
  have hsum4 : (∑ j ∈ Finset.range L, ((1/4 : ℝ))^j) ≤ 4 / 3 := by
    have h4 : ∀ j ∈ Finset.range L, ((1/4 : ℝ))^j = 4 * ((1/4 : ℝ))^(j+1) := by
      intro j _
      have e : ((1/4 : ℝ))^(j+1) * 4 = ((1/4 : ℝ))^j := by
        rw [pow_succ]
        field_simp
      have e2 : ((1/4 : ℝ))^j = 4 * ((1/4 : ℝ))^(j+1) := by
        rw [← e]
        ring
      exact e2
    calc (∑ j ∈ Finset.range L, ((1/4 : ℝ))^j)
        = ∑ j ∈ Finset.range L, (4 * ((1/4 : ℝ))^(j+1)) :=
          Finset.sum_congr rfl h4
      _ = 4 * (∑ j ∈ Finset.range L, ((1/4 : ℝ))^(j+1)) := by rw [Finset.mul_sum]
      _ ≤ 4 * (1/3) := by
        have h' : (∑ j ∈ Finset.range L, ((1/4 : ℝ))^(j+1)) ≤ 1/3 := h.trans hge
        exact mul_le_mul_of_nonneg_left h' (by norm_num)
      _ = 4/3 := by norm_num
  calc (∑ j ∈ Finset.range L, dyadWeight j * ((4:ℝ)^(j+2)))
      ≤ ∑ j ∈ Finset.range L, (4/9) * (((1/16 : ℝ))^(j+1) * ((4:ℝ)^(j+2))) := by
        apply Finset.sum_le_sum
        intro j _
        have hmul : (0:ℝ) ≤ ((4:ℝ)^(j+2)) := by
          have h2 : (0:ℝ) ≤ (4:ℝ) := by norm_num
          exact pow_nonneg h2 _
        have h := mul_le_mul_of_nonneg_right (dyadWeight_le (j := j)) hmul
        calc dyadWeight j * ((4:ℝ)^(j+2))
            ≤ ((4/9) * ((1/16 : ℝ))^(j+1)) * ((4:ℝ)^(j+2)) := h
          _ = (4/9) * (((1/16 : ℝ))^(j+1) * ((4:ℝ)^(j+2))) := by ring
    _ = ∑ j ∈ Finset.range L, (4/9) * (((1/4 : ℝ))^j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [dyad_mix_four]
    _ = (4/9) * (∑ j ∈ Finset.range L, ((1/4 : ℝ))^j) := by rw [Finset.mul_sum]
    _ ≤ (4/9) * (4/3) := by exact mul_le_mul_of_nonneg_left hsum4 (by norm_num)
    _ = 16/27 := by norm_num

/-- If `y` is nonnegative and `x ≤ y ^ 2`, then `Real.sqrt x ≤ y`. -/
theorem sqrt_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := (Real.sqrt_le_iff).2 ⟨hy, h⟩

/-- The square root of the sum of two nonnegative reals is at most the sum of their square
roots. -/
theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 : 0 ≤ Real.sqrt a * Real.sqrt b :=
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  nlinarith

/-- The square root of the sum of three nonnegative reals is at most the sum of their square
roots. -/
theorem sqrt_add3_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have h1 := sqrt_add_le (show 0 ≤ a + b by linarith) hc
  have h2 := sqrt_add_le ha hb
  calc Real.sqrt (a + b + c) = Real.sqrt ((a + b) + c) := by ring
    _ ≤ Real.sqrt (a + b) + Real.sqrt c := h1
    _ ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by linarith

/-- The real cast of `4 ^ (j + 2)` equals the square of the real power `2 ^ (j + 2)`. -/
theorem four_pow_cast_sq (j : ℕ) :
    ((4 ^ (j + 2) : ℕ) : ℝ) = (((2 : ℝ)^(j + 2)))^2 := by
  have e : 2 * (j + 2) = (j + 2) + (j + 2) := by omega
  rw [Nat.cast_pow, show ((4:ℕ):ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul]
  rw [e, pow_add]
  ring

/-- The real cast of `16 ^ (j + 2)` equals the square of the real power `4 ^ (j + 2)`. -/
theorem sixteen_pow_cast_sq (j : ℕ) :
    ((16 ^ (j + 2) : ℕ) : ℝ) = (((4 : ℝ)^(j + 2)))^2 := by
  have e : 2 * (j + 2) = (j + 2) + (j + 2) := by omega
  rw [Nat.cast_pow, show ((16:ℕ):ℝ) = (4:ℝ)^2 by norm_num, ← pow_mul]
  rw [e, pow_add]
  ring

/-- The square root of the real cast of `4 ^ (j + 2)` is `2 ^ (j + 2)`. -/
theorem sqrt_four_cast (j : ℕ) :
    Real.sqrt (((4 ^ (j + 2) : ℕ) : ℝ)) = ((2 : ℝ)^(j + 2)) := by
  rw [four_pow_cast_sq, Real.sqrt_sq]
  positivity

/-- The square root of the real cast of `16 ^ (j + 2)` is `4 ^ (j + 2)`. -/
theorem sqrt_sixteen_cast (j : ℕ) :
    Real.sqrt (((16 ^ (j + 2) : ℕ) : ℝ)) = ((4 : ℝ)^(j + 2)) := by
  rw [sixteen_pow_cast_sq, Real.sqrt_sq]
  positivity

/-- The real square root of `6400` is `80`. -/
theorem sqrt_6400 : Real.sqrt 6400 = 80 := by
  rw [show (6400:ℝ) = (80:ℝ)^2 by norm_num, Real.sqrt_sq]
  norm_num

/-- The ratio `Real.sqrt 2 / Real.sqrt 40` is at most `1 / 4`. -/
theorem sqrt_two_over_sqrt_forty : Real.sqrt 2 / Real.sqrt 40 ≤ 1/4 := by
  have h1 : Real.sqrt 2 / Real.sqrt 40 = Real.sqrt (2 / 40) := by
    have h := Real.sqrt_div (x := (2:ℝ)) (by norm_num) (40:ℝ)
    rw [h]
  rw [h1]
  apply (Real.sqrt_le_iff).2
  refine ⟨by norm_num, ?_⟩
  norm_num

/-- The real square root of two is at most `3 / 2`. -/
theorem sqrt_two_le : Real.sqrt 2 ≤ 3/2 := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by norm_num, ?_⟩
  norm_num

/-- For `N > 0` and `1 ≤ t ≤ N`, the cost at ladder level `j + 1` is at most `Real.sqrt (t * N)`
times `2 + 2 ^ (j + 2) / 4 + 4 ^ (j + 2) * (3 / 2) / 80`. -/
theorem cor4_level_cost_le {N : ℕ} (hN : 0 < N) {t : ℝ} (ht1 : 1 ≤ t)
    (htN : t ≤ (N : ℝ)) (j : ℕ) :
    ladderCost (t + ladderWindow N (j + 1) t) N
      ≤ Real.sqrt (t * (N : ℝ)) *
          (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := by
  have ht0 : 0 ≤ t := by linarith
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have htN' : 0 ≤ t * (N : ℝ) := by positivity
  have hsqrtle : Real.sqrt t ≤ t := by
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hnonneg : (0:ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
    by_cases h : Real.sqrt t ≤ 1
    · have hmul : Real.sqrt t * Real.sqrt t ≤ 1 * Real.sqrt t := by
        have := mul_le_mul_of_nonneg_right h hnonneg
        simpa using! this
      nlinarith [hmul]
    · have h1 : 1 ≤ Real.sqrt t := le_of_not_ge h
      have hmul : 1 * Real.sqrt t ≤ Real.sqrt t * Real.sqrt t := by
        have := mul_le_mul_of_nonneg_left h1 hnonneg
        simpa using! this
      nlinarith [hmul]
  have hw := ladderWindow_le hN ht0 htN (j + 1)
  have hdom : t + ladderWindow N (j + 1) t + 1
      ≤ 2 * t + (((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40
          + (((16 ^ (j + 2) : ℕ) : ℝ)) / 6400 := by
    have h1 : (((4 ^ (j + 2) : ℕ) : ℝ)) * Real.sqrt t
        ≤ (((4 ^ (j + 2) : ℕ) : ℝ)) * t :=
      mul_le_mul_of_nonneg_left hsqrtle (by positivity)
    have h1' : (((4 ^ (j + 2) : ℕ) : ℝ)) * Real.sqrt t / 40
        ≤ (((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40 :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    linarith
  have hA : Real.sqrt (t + ladderWindow N (j + 1) t + 1)
      ≤ Real.sqrt (2 * t) + Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
          + Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400) := by
    have h1 : 0 ≤ t + ladderWindow N (j + 1) t + 1 := by
      have hw0 := ladderWindow_nonneg hN ht0 htN (j + 1)
      positivity
    have h3 : 0 ≤ 2 * t := by linarith
    have h4 : 0 ≤ (((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40 := by positivity
    have h5 : 0 ≤ (((16 ^ (j + 2) : ℕ) : ℝ)) / 6400 := by positivity
    calc Real.sqrt (t + ladderWindow N (j + 1) t + 1)
        ≤ Real.sqrt (2 * t + (((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40
            + (((16 ^ (j + 2) : ℕ) : ℝ)) / 6400) := Real.sqrt_le_sqrt hdom
      _ ≤ Real.sqrt (2 * t) + Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
          + Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400) := sqrt_add3_le h3 h4 h5
  have hB : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt (N : ℝ) := by
    have h1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have h2 : Real.sqrt (2 * (N : ℝ)) = Real.sqrt 2 * Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_mul (x := (2:ℝ)) (by norm_num) ((N : ℝ))]
    exact (Real.sqrt_le_sqrt h1).trans_eq h2
  have hsplit : ladderCost (t + ladderWindow N (j + 1) t) N
      ≤ (Real.sqrt (2 * t) + Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
          + Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400))
          * (Real.sqrt 2 * Real.sqrt (N : ℝ)) := by
    unfold ladderCost
    have h1 : 0 ≤ t + ladderWindow N (j + 1) t + 1 := by
      have hw0 := ladderWindow_nonneg hN ht0 htN (j + 1)
      positivity
    have h2 : 0 ≤ ((N : ℝ) + 1) := by linarith
    have h3 : Real.sqrt ((t + ladderWindow N (j + 1) t + 1) * ((N : ℝ) + 1))
        = Real.sqrt (t + ladderWindow N (j + 1) t + 1) * Real.sqrt ((N : ℝ) + 1) := by
      rw [Real.sqrt_mul (x := t + ladderWindow N (j + 1) t + 1) h1 ((N : ℝ) + 1)]
    rw [h3]
    exact mul_le_mul hA hB (by positivity) (by positivity)
  have hsqrt2t : Real.sqrt (2 * t) = Real.sqrt 2 * Real.sqrt t := by
    rw [Real.sqrt_mul (x := (2:ℝ)) (by norm_num) t]
  have hsqrtAj : Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
      = ((2 : ℝ)^(j + 2)) * (Real.sqrt t / Real.sqrt 40) := by
    have h1 : 0 ≤ (((4 ^ (j + 2) : ℕ) : ℝ)) := by positivity
    have h2 : 0 ≤ t / 40 := by positivity
    have h3 : ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
        = (((4 ^ (j + 2) : ℕ) : ℝ)) * (t / 40) := by ring
    rw [h3, Real.sqrt_mul (x := (((4 ^ (j + 2) : ℕ) : ℝ))) h1 (t / 40), sqrt_four_cast]
    rw [Real.sqrt_div (x := t) ht0 (40:ℝ)]
  have hsqrtCj : Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400)
      = ((4 : ℝ)^(j + 2)) / 80 := by
    have h1 : 0 ≤ (((16 ^ (j + 2) : ℕ) : ℝ)) := by positivity
    rw [Real.sqrt_div (x := (((16 ^ (j + 2) : ℕ) : ℝ))) h1 (6400:ℝ), sqrt_sixteen_cast,
      sqrt_6400]
  have hsqrtprod : Real.sqrt t * Real.sqrt (N : ℝ) = Real.sqrt (t * (N : ℝ)) := by
    rw [Real.sqrt_mul (x := t) ht0 ((N : ℝ))]
  have hNle : Real.sqrt (N : ℝ) ≤ Real.sqrt (t * (N : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hlt : (0:ℝ) ≤ t := by linarith
    nlinarith [mul_nonneg (le_of_lt hNpos) hlt]
  have hfinal : (Real.sqrt (2 * t) + Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
          + Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400))
          * (Real.sqrt 2 * Real.sqrt (N : ℝ))
      ≤ Real.sqrt (t * (N : ℝ)) *
          (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := by
    have h1 : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
    have h2 : Real.sqrt 2 / Real.sqrt 40 ≤ 1/4 := sqrt_two_over_sqrt_forty
    have h3 : Real.sqrt 2 ≤ 3/2 := sqrt_two_le
    rw [hsqrt2t, hsqrtAj, hsqrtCj]
    have h4 : (Real.sqrt 2 * Real.sqrt t) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
        = 2 * Real.sqrt (t * (N : ℝ)) := by
      calc (Real.sqrt 2 * Real.sqrt t) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          = Real.sqrt 2 * Real.sqrt 2 * (Real.sqrt t * Real.sqrt (N : ℝ)) := by ring
        _ = 2 * (Real.sqrt t * Real.sqrt (N : ℝ)) := by rw [h1]
        _ = 2 * Real.sqrt (t * (N : ℝ)) := by rw [hsqrtprod]
    have h5 : (((2 : ℝ)^(j + 2)) * (Real.sqrt t / Real.sqrt 40))
          * (Real.sqrt 2 * Real.sqrt (N : ℝ))
        ≤ ((2 : ℝ)^(j + 2)) * Real.sqrt (t * (N : ℝ)) / 4 := by
      have hA1 : 0 ≤ (Real.sqrt t / Real.sqrt 40) * (Real.sqrt 2 * Real.sqrt (N : ℝ)) := by
        positivity
      have hA2 : (Real.sqrt t / Real.sqrt 40) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          ≤ Real.sqrt (t * (N : ℝ)) / 4 := by
        have hh : (Real.sqrt 2 / Real.sqrt 40) * Real.sqrt (t * (N : ℝ))
            ≤ (1/4) * Real.sqrt (t * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
        calc (Real.sqrt t / Real.sqrt 40) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
            = (Real.sqrt 2 / Real.sqrt 40) * (Real.sqrt t * Real.sqrt (N : ℝ)) := by ring
          _ = (Real.sqrt 2 / Real.sqrt 40) * Real.sqrt (t * (N : ℝ)) := by rw [hsqrtprod]
          _ ≤ (1/4) * Real.sqrt (t * (N : ℝ)) := hh
          _ = Real.sqrt (t * (N : ℝ)) / 4 := by ring
      have hA1 : (0:ℝ) ≤ ((2 : ℝ)^(j + 2)) := by positivity
      calc ((2 : ℝ)^(j + 2)) * (Real.sqrt t / Real.sqrt 40)
              * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          = ((2 : ℝ)^(j + 2))
              * ((Real.sqrt t / Real.sqrt 40) * (Real.sqrt 2 * Real.sqrt (N : ℝ))) := by
              ring
        _ ≤ ((2 : ℝ)^(j + 2)) * (Real.sqrt (t * (N : ℝ)) / 4) :=
              mul_le_mul_of_nonneg_left hA2 hA1
        _ = ((2 : ℝ)^(j + 2)) * Real.sqrt (t * (N : ℝ)) / 4 := by ring
    have h6 : (((4 : ℝ)^(j + 2)) / 80) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
        ≤ ((4 : ℝ)^(j + 2)) * (3/2) * Real.sqrt (t * (N : ℝ)) / 80 := by
      have hA1 : (0:ℝ) ≤ (Real.sqrt 2 * Real.sqrt (N : ℝ)) / 80 := by positivity
      have hA2 : (Real.sqrt 2 * Real.sqrt (N : ℝ)) / 80
          ≤ (3/2) * Real.sqrt (t * (N : ℝ)) / 80 := by
        have h31 : Real.sqrt 2 * Real.sqrt (N : ℝ)
            ≤ (3/2) * Real.sqrt (t * (N : ℝ)) := by
          have h32 : Real.sqrt 2 * Real.sqrt (N : ℝ)
              ≤ (3/2) * Real.sqrt (N : ℝ) := by
            have hh := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (N : ℝ))
            simpa [mul_comm] using! hh
          calc Real.sqrt 2 * Real.sqrt (N : ℝ)
              ≤ (3/2) * Real.sqrt (N : ℝ) := h32
            _ ≤ (3/2) * Real.sqrt (t * (N : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hNle (by norm_num)
        linarith
      have hz : (Real.sqrt 2 * Real.sqrt (N : ℝ)) / 80 * ((4 : ℝ)^(j + 2))
            ≤ (3/2) * Real.sqrt (t * (N : ℝ)) / 80 * ((4 : ℝ)^(j + 2)) :=
            mul_le_mul_of_nonneg_right hA2 (by positivity)
      calc ((4 : ℝ)^(j + 2)) / 80 * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          = ((4 : ℝ)^(j + 2)) * ((Real.sqrt 2 * Real.sqrt (N : ℝ)) / 80) := by ring
        _ = (Real.sqrt 2 * Real.sqrt (N : ℝ)) / 80 * ((4 : ℝ)^(j + 2)) := by ring
        _ ≤ (3/2) * Real.sqrt (t * (N : ℝ)) / 80 * ((4 : ℝ)^(j + 2)) := hz
        _ = ((4 : ℝ)^(j + 2)) * ((3/2) * Real.sqrt (t * (N : ℝ)) / 80) := by ring
        _ = ((4 : ℝ)^(j + 2)) * (3/2) * Real.sqrt (t * (N : ℝ)) / 80 := by ring
    calc (Real.sqrt 2 * Real.sqrt t + ((2 : ℝ)^(j + 2)) * (Real.sqrt t / Real.sqrt 40)
            + ((4 : ℝ)^(j + 2)) / 80) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
        = (Real.sqrt 2 * Real.sqrt t) * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          + (((2 : ℝ)^(j + 2)) * (Real.sqrt t / Real.sqrt 40))
            * (Real.sqrt 2 * Real.sqrt (N : ℝ))
          + (((4 : ℝ)^(j + 2)) / 80) * (Real.sqrt 2 * Real.sqrt (N : ℝ)) := by ring
      _ ≤ 2 * Real.sqrt (t * (N : ℝ))
          + ((2 : ℝ)^(j + 2)) * Real.sqrt (t * (N : ℝ)) / 4
          + ((4 : ℝ)^(j + 2)) * (3/2) * Real.sqrt (t * (N : ℝ)) / 80 :=
        add_le_add (add_le_add h4.le h5) h6
      _ = Real.sqrt (t * (N : ℝ)) *
          (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := by ring
  calc ladderCost (t + ladderWindow N (j + 1) t) N
      ≤ (Real.sqrt (2 * t) + Real.sqrt ((((4 ^ (j + 2) : ℕ) : ℝ)) * t / 40)
          + Real.sqrt ((((16 ^ (j + 2) : ℕ) : ℝ)) / 6400))
          * (Real.sqrt 2 * Real.sqrt (N : ℝ)) := hsplit
    _ ≤ Real.sqrt (t * (N : ℝ)) *
          (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := hfinal

/-- Distributes a finite weighted sum across two indicator terms and a finite ladder sum,
pulling out the constant coefficients and exchanging the two finite sums. -/
theorem sum_ladder_rearrange {ι κ μ : Type*} (P : Finset (ι × κ)) (w : ι × κ → ℝ)
    (L : Finset μ) (A0 A1 : ℝ) (c1 c2 : ι × κ → Prop) (B : μ → ℝ)
    (c3 : ι × κ → μ → Prop) :
    (∑ z ∈ P, w z * (A0 * (if c1 z then 1 else 0)
        + A1 * (if c2 z then 1 else 0)
        + ∑ j ∈ L, (if c3 z j then B j else 0)))
      = A0 * (∑ z ∈ P, w z * (if c1 z then 1 else 0))
        + A1 * (∑ z ∈ P, w z * (if c2 z then 1 else 0))
        + ∑ j ∈ L, (∑ z ∈ P, w z * (if c3 z j then B j else 0)) := by
  have h1 : (∑ z ∈ P, w z * (A0 * (if c1 z then 1 else 0)
        + A1 * (if c2 z then 1 else 0)
        + ∑ j ∈ L, (if c3 z j then B j else 0)))
      = ∑ z ∈ P, (w z * (A0 * (if c1 z then 1 else 0))
        + w z * (A1 * (if c2 z then 1 else 0))
        + w z * ∑ j ∈ L, (if c3 z j then B j else 0)) := by
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [h1]
  simp only [Finset.sum_add_distrib]
  have h2 : (∑ z ∈ P, w z * (A0 * (if c1 z then 1 else 0)))
      = A0 * (∑ z ∈ P, w z * (if c1 z then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have h3 : (∑ z ∈ P, w z * (A1 * (if c2 z then 1 else 0)))
      = A1 * (∑ z ∈ P, w z * (if c2 z then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  have h4 : (∑ z ∈ P, w z * ∑ j ∈ L, (if c3 z j then B j else 0))
      = ∑ j ∈ L, (∑ z ∈ P, w z * (if c3 z j then B j else 0)) := by
    have hz : ∀ z ∈ P, w z * ∑ j ∈ L, (if c3 z j then B j else 0)
        = ∑ j ∈ L, w z * (if c3 z j then B j else 0) := by
      intro z _
      exact Finset.mul_sum L (fun j => if c3 z j then B j else 0) (w z)
    rw [Finset.sum_congr rfl hz, Finset.sum_comm]
  rw [h2, h3, h4]

/-- For `N > 0` and `1 ≤ S.card ≤ N / 2`, the expected `ladderCost` of the minimum of two
independent rough readouts is at most `6 * Real.sqrt (S.card * N)`. -/
theorem cor4_expected_cost_le {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2) :
    (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
        (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N)
      ≤ 6 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
  have ht1 : 1 ≤ (S.card : ℝ) := hcard
  have ht0 : 0 ≤ (S.card : ℝ) := by linarith
  have htN : (S.card : ℝ) ≤ (N : ℝ) := by linarith
  have hae : FinDist (Fin (nextCor4RoughGrid N)) :=
    aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)
  have hnonneg : ∀ z : Fin (nextCor4RoughGrid N), 0 ≤ firstProb hN S z := by
    intro z
    show 0 ≤ (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z
    exact (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).nonneg z
  have hsum1 : (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      firstProb hN S z) = 1 := by
    show (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
        (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).prob z) = 1
    exact (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) (nextCor4_rough_grid_two hN)).sum_one
  set P : Finset (Fin (nextCor4RoughGrid N) × Fin (nextCor4RoughGrid N)) :=
    (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
      (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) with hP
  have hpair : (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2)) = 1 := by
    rw [hP, Finset.sum_product]
    rw [← Finset.sum_mul_sum]
    rw [hsum1]
    ring

  have hpoint : ∀ z ∈ P, ladderCost (pairMin z) N
      ≤ ladderCost (S.card : ℝ) N * (if pairMin z ≤ (S.card : ℝ) then 1 else 0)
        + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
            * (if (S.card : ℝ) < pairMin z then 1 else 0)
        + ∑ j ∈ Finset.range (N + 3),
            (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
             then ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N
             else 0) := by
    intro z _
    have hcross : pairMin z ≤ (S.card : ℝ) + ladderWindow N (N + 3) (S.card : ℝ) := by
      have htop := ladder_top_ge hN ht1 hcardN
      have hpm : pairMin z ≤ (N : ℝ) := pairMin_le z
      have hw0 : 0 ≤ ladderWindow N (N + 3) (S.card : ℝ) :=
        ladderWindow_nonneg hN ht0 htN (N + 3)
      linarith
    exact ladder_pointwise_all hN ht0 htN (N + 3) (by omega) hcross

  have hbase : ∀ c : (Fin (nextCor4RoughGrid N) × (Fin (nextCor4RoughGrid N))) → Prop,
      (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) * (if c z then 1 else 0)) ≤ 1 := by
    intro c
    have hle : ∀ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) * (if c z then 1 else 0)
        ≤ (firstProb hN S z.1) * (firstProb hN S z.2) := by
      intro z _
      have hz : 0 ≤ (firstProb hN S z.1) * (firstProb hN S z.2) :=
        mul_nonneg (hnonneg z.1) (hnonneg z.2)
      have h1 : (if c z then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : (firstProb hN S z.1) * (firstProb hN S z.2) * (if c z then 1 else 0)
          ≤ (firstProb hN S z.1) * (firstProb hN S z.2) * 1 :=
        mul_le_mul_of_nonneg_left h1 hz
      calc (firstProb hN S z.1) * (firstProb hN S z.2) * (if c z then 1 else 0)
          ≤ (firstProb hN S z.1) * (firstProb hN S z.2) * 1 := h2
        _ = (firstProb hN S z.1) * (firstProb hN S z.2) := by ring
    calc (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) * (if c z then 1 else 0))
        ≤ ∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) := Finset.sum_le_sum hle
      _ = 1 := hpair

  have hlevel : ∀ j ∈ Finset.range (N + 3),
      (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
          (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
           then ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N
           else 0))
        ≤ ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N *
            dyadWeight j := by
    intro j _
    set B : ℝ := ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N with hB
    have hB0 : 0 ≤ B := by
      unfold B
      have hw := ladderWindow_nonneg hN ht0 htN (j + 1)
      have h1 : 0 ≤ ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ) + 1)
          * ((N : ℝ) + 1) := by positivity
      exact Real.sqrt_nonneg _
    have hfil : (∑ z ∈ P.filter
            (fun z => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z),
          (firstProb hN S z.1) * (firstProb hN S z.2)) ≤ dyadWeight j := by
      have h := sum_pair_overshoot_le hN S j
      unfold dyadWeight at h
      exact h
    calc (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
          (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
           then B else 0))
        = ∑ z ∈ P, (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
           then (firstProb hN S z.1) * (firstProb hN S z.2) * B else 0) := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hc : (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
          · rw [if_pos hc, if_pos hc]
          · rw [if_neg hc, if_neg hc]
            ring
        _ = ∑ z ∈ P.filter
            (fun z => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z),
            (firstProb hN S z.1) * (firstProb hN S z.2) * B := by
          rw [← Finset.sum_filter]
        _ = B * (∑ z ∈ P.filter
            (fun z => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z),
            (firstProb hN S z.1) * (firstProb hN S z.2)) := by
          rw [← Finset.sum_mul]
          ring
        _ ≤ B * dyadWeight j := mul_le_mul_of_nonneg_left hfil hB0

  have hA0 : ladderCost (S.card : ℝ) N ≤ 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
    unfold ladderCost
    have e1 : (S.card : ℝ) + 1 ≤ 2 * (S.card : ℝ) := by linarith
    have e2 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have hm : ((S.card : ℝ) + 1) * ((N : ℝ) + 1)
        ≤ (2 * (S.card : ℝ)) * (2 * (N : ℝ)) := mul_le_mul e1 e2 (by linarith) (by linarith)
    have h3 : ((S.card : ℝ) + 1) * ((N : ℝ) + 1) ≤ 4 * ((S.card : ℝ) * (N : ℝ)) := by
      nlinarith
    have h4 : Real.sqrt (4 * ((S.card : ℝ) * (N : ℝ)))
        = 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
      rw [Real.sqrt_mul (x := (4:ℝ)) (by norm_num) ((S.card : ℝ) * (N : ℝ))]
      have hs4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.sqrt_sq]
        norm_num
      rw [hs4]
    exact (Real.sqrt_le_sqrt h3).trans_eq h4

  have hA1 : ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
      ≤ (5/2) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
    unfold ladderCost
    have hsq : Real.sqrt (S.card : ℝ) ≤ (S.card : ℝ) := by
      have hq : Real.sqrt (S.card : ℝ) ^ 2 = (S.card : ℝ) := Real.sq_sqrt ht0
      have hn : (0:ℝ) ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
      by_cases h : Real.sqrt (S.card : ℝ) ≤ 1
      · have hmul : Real.sqrt (S.card : ℝ) * Real.sqrt (S.card : ℝ)
            ≤ 1 * Real.sqrt (S.card : ℝ) := by
          have := mul_le_mul_of_nonneg_right h hn
          simpa using! this
        nlinarith [hmul]
      · have h1 : 1 ≤ Real.sqrt (S.card : ℝ) := le_of_not_ge h
        have hmul : 1 * Real.sqrt (S.card : ℝ)
            ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (S.card : ℝ) := by
          have := mul_le_mul_of_nonneg_left h1 hn
          simpa using! this
        nlinarith [hmul]
    have hw := ladderWindow_le hN ht0 htN 0
    have h1 : (S.card : ℝ) + ladderWindow N 0 (S.card : ℝ) + 1
        ≤ (841/400) * (S.card : ℝ) := by
      have h2 : (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * Real.sqrt (S.card : ℝ)
          ≤ (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have h2' : (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * Real.sqrt (S.card : ℝ) / 40
          ≤ (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * (S.card : ℝ) / 40 :=
        div_le_div_of_nonneg_right h2 (by norm_num)
      have h3 : (S.card : ℝ) + 1 + (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * Real.sqrt (S.card : ℝ) / 40
            + (((16 ^ (1 : ℕ) : ℕ) : ℝ)) / 6400
          ≤ (841/400) * (S.card : ℝ) := by
        have h2'' : (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * Real.sqrt (S.card : ℝ) / 40
            ≤ (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * (S.card : ℝ) / 40 := h2'
        norm_num at h2'' ⊢
        nlinarith [h2'']
      have h4 : ladderWindow N 0 (S.card : ℝ)
          ≤ (((4 ^ (1 : ℕ) : ℕ) : ℝ)) * Real.sqrt (S.card : ℝ) / 40
            + (((16 ^ (1 : ℕ) : ℕ) : ℝ)) / 6400 := by
        simpa using! hw
      linarith
    have e1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by linarith
    have hm : ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ) + 1) * ((N : ℝ) + 1)
        ≤ ((841/400) * (S.card : ℝ)) * (2 * (N : ℝ)) :=
      mul_le_mul h1 e1 (by linarith) (by positivity)
    have h5 : ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ) + 1) * ((N : ℝ) + 1)
        ≤ (841/200) * ((S.card : ℝ) * (N : ℝ)) := by nlinarith
    have h6 : Real.sqrt (841/200) ≤ 5/2 := by
      apply (Real.sqrt_le_iff).2
      refine ⟨by norm_num, ?_⟩
      norm_num
    have h7 : Real.sqrt ((841/200) * ((S.card : ℝ) * (N : ℝ)))
        = Real.sqrt (841/200) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
      rw [Real.sqrt_mul (x := (841/200:ℝ)) (by positivity) ((S.card : ℝ) * (N : ℝ))]
    have h8 : Real.sqrt (841/200) * Real.sqrt ((S.card : ℝ) * (N : ℝ))
        ≤ (5/2) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) :=
      mul_le_mul h6 (le_refl _) (Real.sqrt_nonneg _) (by norm_num)
    calc Real.sqrt (((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ) + 1) * ((N : ℝ) + 1))
        ≤ Real.sqrt ((841/200) * ((S.card : ℝ) * (N : ℝ))) := Real.sqrt_le_sqrt h5
      _ = Real.sqrt (841/200) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := h7
      _ ≤ (5/2) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := h8

  have hlev : (∑ j ∈ Finset.range (N + 3),
        ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N * dyadWeight j)
      ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
    have hstep : ∀ j ∈ Finset.range (N + 3),
        ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N * dyadWeight j
          ≤ dyadWeight j * Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
              (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := by
      intro j _
      have h := cor4_level_cost_le hN ht1 htN j
      have h0 : 0 ≤ dyadWeight j := dyadWeight_nonneg j
      calc ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N * dyadWeight j
          = dyadWeight j * ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N := by
              ring
        _ ≤ dyadWeight j * (Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
              (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80)) :=
            mul_le_mul_of_nonneg_left h h0
        _ = dyadWeight j * Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
              (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) := by ring
    have hA : (∑ j ∈ Finset.range (N + 3), dyadWeight j) ≤ 4 / 135 := dyadWeight_sum_le _
    have hB : (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2))) ≤ 8 / 63 :=
      dyadWeight_two_sum_le _
    have hC : (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2))) ≤ 16 / 27 :=
      dyadWeight_four_sum_le _
    have hexp : (∑ j ∈ Finset.range (N + 3),
          dyadWeight j * Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
            (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80))
        = Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
            (2 * (∑ j ∈ Finset.range (N + 3), dyadWeight j)
              + (1/4) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2)))
              + (3/160) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2)))) := by
      have h1 : (∑ j ∈ Finset.range (N + 3),
            dyadWeight j * Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
              (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80))
          = Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
              (∑ j ∈ Finset.range (N + 3),
                dyadWeight j * (2 + ((2 : ℝ)^(j + 2)) / 4
                  + ((4 : ℝ)^(j + 2)) * (3/2) / 80)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have e1 : (∑ j ∈ Finset.range (N + 3), dyadWeight j * 2)
          = 2 * (∑ j ∈ Finset.range (N + 3), dyadWeight j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have e2 : (∑ j ∈ Finset.range (N + 3), dyadWeight j * (((2:ℝ)^(j + 2)) / 4))
          = (1/4) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have e3 : (∑ j ∈ Finset.range (N + 3),
            dyadWeight j * (((4:ℝ)^(j + 2)) * (3/2) / 80))
          = (3/160) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hrest : (∑ j ∈ Finset.range (N + 3),
            dyadWeight j * (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80))
          = 2 * (∑ j ∈ Finset.range (N + 3), dyadWeight j)
            + (1/4) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2)))
            + (3/160) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2))) := by
        calc (∑ j ∈ Finset.range (N + 3),
              dyadWeight j * (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80))
            = ∑ j ∈ Finset.range (N + 3),
                (dyadWeight j * 2 + dyadWeight j * (((2:ℝ)^(j + 2)) / 4)
                  + dyadWeight j * (((4:ℝ)^(j + 2)) * (3/2) / 80)) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = (∑ j ∈ Finset.range (N + 3), dyadWeight j * 2)
              + (∑ j ∈ Finset.range (N + 3), dyadWeight j * (((2:ℝ)^(j + 2)) / 4))
              + (∑ j ∈ Finset.range (N + 3),
                  dyadWeight j * (((4:ℝ)^(j + 2)) * (3/2) / 80)) := by
              simp only [Finset.sum_add_distrib]
          _ = 2 * (∑ j ∈ Finset.range (N + 3), dyadWeight j)
              + (1/4) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2)))
              + (3/160) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2))) := by
              rw [e1, e2, e3]
      rw [h1, hrest]
    have hbr : (2:ℝ) * (4/135) + (1/4) * (8/63) + (3/160) * (16/27) ≤ 1 := by norm_num
    calc (∑ j ∈ Finset.range (N + 3),
          ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N * dyadWeight j)
        ≤ ∑ j ∈ Finset.range (N + 3), dyadWeight j * Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
            (2 + ((2 : ℝ)^(j + 2)) / 4 + ((4 : ℝ)^(j + 2)) * (3/2) / 80) :=
          Finset.sum_le_sum hstep
      _ = Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
            (2 * (∑ j ∈ Finset.range (N + 3), dyadWeight j)
              + (1/4) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((2:ℝ)^(j + 2)))
              + (3/160) * (∑ j ∈ Finset.range (N + 3), dyadWeight j * ((4:ℝ)^(j + 2)))) := hexp
      _ ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
            (2 * (4/135) + (1/4) * (8/63) + (3/160) * (16/27)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hA (by norm_num))
              (mul_le_mul_of_nonneg_left hB (by norm_num)))
              (mul_le_mul_of_nonneg_left hC (by norm_num)))
            (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
        have hs : (0:ℝ) ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) := Real.sqrt_nonneg _
        calc Real.sqrt ((S.card : ℝ) * (N : ℝ)) *
                (2 * (4/135) + (1/4) * (8/63) + (3/160) * (16/27))
            ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) * 1 := mul_le_mul_of_nonneg_left hbr hs
          _ = Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by ring

  have hmain : (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N)
      ≤ ladderCost (S.card : ℝ) N
        + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
        + ∑ j ∈ Finset.range (N + 3),
            ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N *
              dyadWeight j := by
    have hrearr := sum_ladder_rearrange (ι := Fin (nextCor4RoughGrid N))
      (κ := Fin (nextCor4RoughGrid N)) (μ := ℕ) P
      (fun z => (firstProb hN S z.1) * (firstProb hN S z.2))
      (Finset.range (N + 3))
      (ladderCost (S.card : ℝ) N)
      (ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N)
      (fun z => pairMin z ≤ (S.card : ℝ))
      (fun z => (S.card : ℝ) < pairMin z)
      (fun j => ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N)
      (fun z j => (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z)
    have hstep : ∀ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N
        ≤ (firstProb hN S z.1) * (firstProb hN S z.2) *
          (ladderCost (S.card : ℝ) N * (if pairMin z ≤ (S.card : ℝ) then 1 else 0)
            + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
                * (if (S.card : ℝ) < pairMin z then 1 else 0)
            + ∑ j ∈ Finset.range (N + 3),
                (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
                 then ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N
                 else 0)) := by
      intro z hz
      exact mul_le_mul_of_nonneg_left (hpoint z hz)
        (mul_nonneg (hnonneg z.1) (hnonneg z.2))
    calc (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
          ladderCost (pairMin z) N)
        ≤ ∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
          (ladderCost (S.card : ℝ) N * (if pairMin z ≤ (S.card : ℝ) then 1 else 0)
            + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
                * (if (S.card : ℝ) < pairMin z then 1 else 0)
            + ∑ j ∈ Finset.range (N + 3),
                (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
                 then ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N
                 else 0)) := Finset.sum_le_sum hstep
      _ = ladderCost (S.card : ℝ) N *
            (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
              (if pairMin z ≤ (S.card : ℝ) then 1 else 0))
          + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N *
            (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
              (if (S.card : ℝ) < pairMin z then 1 else 0))
          + ∑ j ∈ Finset.range (N + 3),
            (∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
              (if (S.card : ℝ) + ladderWindow N j (S.card : ℝ) < pairMin z
               then ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N
               else 0)) := hrearr
      _ ≤ ladderCost (S.card : ℝ) N * 1
          + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N * 1
          + ∑ j ∈ Finset.range (N + 3),
            ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N *
              dyadWeight j := by
        have hA0' : 0 ≤ ladderCost (S.card : ℝ) N := by
          unfold ladderCost
          exact Real.sqrt_nonneg _
        have hA1' : 0 ≤ ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N := by
          unfold ladderCost
          exact Real.sqrt_nonneg _
        refine add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hbase _) hA0')
          (mul_le_mul_of_nonneg_left (hbase _) hA1'))
          (Finset.sum_le_sum (fun j hj => hlevel j hj))
      _ = ladderCost (S.card : ℝ) N
        + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
        + ∑ j ∈ Finset.range (N + 3),
            ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N *
              dyadWeight j := by ring
  calc (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
        (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N)
      = ∑ z ∈ P, (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N := by rw [hP]
    _ ≤ ladderCost (S.card : ℝ) N
        + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
        + ∑ j ∈ Finset.range (N + 3),
            ladderCost ((S.card : ℝ) + ladderWindow N (j + 1) (S.card : ℝ)) N *
              dyadWeight j := hmain
    _ ≤ 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
        + (5/2) * Real.sqrt ((S.card : ℝ) * (N : ℝ))
        + Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
          gcongr
    _ ≤ 6 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
      have : (0:ℝ) ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) := Real.sqrt_nonneg _
      linarith

/-- For `N > 0` and `1 ≤ S.card ≤ N / 2`, the two rough-grid charges plus the expected
refinement cost `ladderCost (pairMin z) N` total at most `650 * Real.sqrt (S.card * N)`. -/
theorem cor4_total_ledger_le {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2) :
    2 * (nextCor4RoughGrid N : ℝ) +
        (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
          (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
          (firstProb hN S z.1) * (firstProb hN S z.2) * ladderCost (pairMin z) N)
      ≤ 650 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
  have hM0 : (nextCor4RoughGrid N : ℝ) ≤ 80 * Real.pi * Real.sqrt (N : ℝ) + 1 := by
    rw [nextCor4RoughGrid]
    have hc := Nat.ceil_lt_add_one (a := 80 * Real.pi * Real.sqrt (N : ℝ)) (by positivity)
    exact le_of_lt hc
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hsqrtN1 : (1:ℝ) ≤ Real.sqrt (N : ℝ) := (Real.one_le_sqrt).2 hN1
  have ht1 : (1:ℝ) ≤ (S.card : ℝ) := hcard
  have hprod : (0:ℝ) < (S.card : ℝ) * (N : ℝ) := by
    have hts : (0:ℝ) < (S.card : ℝ) := by linarith
    have hNs : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact mul_pos hts hNs
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul : (1:ℝ) * (N : ℝ) ≤ (S.card : ℝ) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right ht1 (le_of_lt hNpos)
  have hprod1 : (1:ℝ) ≤ (S.card : ℝ) * (N : ℝ) := by
    have h := mul_le_mul ht1 hN1 (by norm_num) (by linarith)
    simpa using! h
  have hsqrtprod1 : (1:ℝ) ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) :=
    (Real.one_le_sqrt).2 hprod1
  have hNle : Real.sqrt (N : ℝ) ≤ Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
    apply Real.sqrt_le_sqrt
    simpa using! hmul
  have hM0' : 2 * (nextCor4RoughGrid N : ℝ)
      ≤ 640 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
          + 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
    have h1 : 2 * (nextCor4RoughGrid N : ℝ)
        ≤ 2 * (80 * Real.pi * Real.sqrt (N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hM0 (by norm_num)
    have h2 : 2 * (80 * Real.pi * Real.sqrt (N : ℝ) + 1)
        ≤ 640 * Real.sqrt (N : ℝ) + 2 := by
      have h3 : 160 * Real.pi * Real.sqrt (N : ℝ) ≤ 640 * Real.sqrt (N : ℝ) := by
        have hsqrtN0 : (0:ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        have hpi : 160 * Real.pi ≤ 640 := by linarith
        exact mul_le_mul_of_nonneg_right hpi hsqrtN0
      nlinarith
    calc 2 * (nextCor4RoughGrid N : ℝ)
          ≤ 2 * (80 * Real.pi * Real.sqrt (N : ℝ) + 1) := h1
        _ ≤ 640 * Real.sqrt (N : ℝ) + 2 := h2
        _ ≤ 640 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
            + 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
          have h4 : (2:ℝ) ≤ 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by linarith
          linarith
  have hsec := cor4_expected_cost_le hN S hcard hcardN
  calc 2 * (nextCor4RoughGrid N : ℝ) +
        (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
          (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
          (firstProb hN S z.1) * (firstProb hN S z.2) * ladderCost (pairMin z) N)
      ≤ (640 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
            + 2 * Real.sqrt ((S.card : ℝ) * (N : ℝ)))
          + 6 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by linarith
    _ ≤ 650 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by linarith

/-- The real-valued precision parameter obtained by adding one to the integer floor of `ε * t`. -/
noncomputable def nextApproxCountPrecision (t ε : ℝ) : ℝ := (⌊ε * t⌋ : ℝ) + 1

/-- The counting scale `Real.sqrt (N / p) + Real.sqrt (t * (N - t)) / p`, where `p =
nextApproxCountPrecision t ε`. -/
noncomputable def nextApproxCountScale (N t ε : ℝ) : ℝ :=
  Real.sqrt (N / nextApproxCountPrecision t ε) +
    Real.sqrt (t * (N - t)) / nextApproxCountPrecision t ε

/-- If `ε * t` is nonnegative, then `nextApproxCountPrecision t ε` is at least one. -/
theorem nextApproxCountPrecision_ge_one {t ε : ℝ} (hε0 : 0 ≤ ε * t) :
    1 ≤ nextApproxCountPrecision t ε := by
  have hfl : (0 : ℝ) ≤ (⌊ε * t⌋ : ℝ) := by
    exact_mod_cast (Int.floor_nonneg.mpr hε0)
  unfold nextApproxCountPrecision
  linarith

/-- If `0 ≤ ε * t < 1`, then `nextApproxCountPrecision t ε = 1`. -/
theorem nextApproxCountPrecision_eq_one {t ε : ℝ} (h0 : 0 ≤ ε * t) (h1 : ε * t < 1) :
    nextApproxCountPrecision t ε = 1 := by
  have hz : ⌊ε * t⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  unfold nextApproxCountPrecision
  rw [hz]
  norm_num

/-- If `1 ≤ ε * t`, then `nextApproxCountPrecision t ε` lies between `2` and `2 * (ε * t)`. -/
theorem nextApproxCountPrecision_bounds {t ε : ℝ} (hge : 1 ≤ ε * t) :
    2 ≤ nextApproxCountPrecision t ε ∧
      nextApproxCountPrecision t ε ≤ 2 * (ε * t) := by
  constructor
  · have hfl : (0 : ℤ) < ⌊ε * t⌋ := Int.floor_pos.mpr hge
    have hfl1 : (1 : ℤ) ≤ ⌊ε * t⌋ := by omega
    have hflr : (1 : ℝ) ≤ (⌊ε * t⌋ : ℝ) := by exact_mod_cast hfl1
    unfold nextApproxCountPrecision
    linarith
  · have hfl : (⌊ε * t⌋ : ℝ) ≤ ε * t := by
      exact_mod_cast (Int.floor_le (ε * t))
    unfold nextApproxCountPrecision
    linarith

/-- For `N > 0`, `1 ≤ t ≤ N / 2`, `0 < ε ≤ 1`, and `1 ≤ ε * t`, the relative-counting scale `(1
/ ε) * Real.sqrt (N / t)` is at most three times `nextApproxCountScale N t ε`. -/
theorem nextApproxCountScale_rel_le {N t ε : ℝ} (hN : 0 < N) (ht1 : 1 ≤ t)
    (htN : t ≤ N / 2) (heps : 0 < ε) (heps1 : ε ≤ 1) (hge : 1 ≤ ε * t) :
    (1 / ε) * Real.sqrt (N / t) ≤ 3 * nextApproxCountScale N t ε := by
  have hk := nextApproxCountPrecision_bounds hge
  have hkpos : (0 : ℝ) < nextApproxCountPrecision t ε := by linarith
  have h2εtpos : (0 : ℝ) < 2 * (ε * t) := by positivity
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1

  have hsq : Real.sqrt (t * (N - t)) ≥ (2 / 3) * Real.sqrt (t * N) := by
    have h3 : (4 / 9) * (t * N) ≤ t * (N - t) := by
      have h5 : (4 / 9) * N ≤ N - t := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h5 (le_trans (by norm_num) ht1)]
    have h4 : Real.sqrt ((4 / 9) * (t * N)) = (2 / 3) * Real.sqrt (t * N) := by
      have hsq4 : Real.sqrt (4 / 9 : ℝ) = 2 / 3 := by
        rw [show (4/9:ℝ) = (2/3)^2 by ring,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (2:ℝ)/3)]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (4:ℝ)/9) (t * N), hsq4,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ t) N]
    calc Real.sqrt (t * (N - t)) ≥ Real.sqrt ((4 / 9) * (t * N)) :=
        Real.sqrt_le_sqrt h3
      _ = (2 / 3) * Real.sqrt (t * N) := h4

  have hB : Real.sqrt (t * (N - t)) / nextApproxCountPrecision t ε
      ≥ Real.sqrt (N / t) / (3 * ε) := by
    have h1 : Real.sqrt (t * (N - t)) / (2 * (ε * t))
        ≤ Real.sqrt (t * (N - t)) / nextApproxCountPrecision t ε := by
      rw [div_le_div_iff₀ h2εtpos hkpos]
      exact mul_le_mul_of_nonneg_left hk.2 (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (t * (N - t)) / (2 * (ε * t))
        ≥ (2 / 3) * Real.sqrt (t * N) / (2 * (ε * t)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have h3 : (2 / 3) * Real.sqrt (t * N) / (2 * (ε * t))
        = Real.sqrt (N / t) / (3 * ε) := by
      have h1 : Real.sqrt (t * N) = Real.sqrt t * Real.sqrt N :=
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ t) N
      have h2 : Real.sqrt (N / t) = Real.sqrt N / Real.sqrt t :=
        Real.sqrt_div (by positivity : (0:ℝ) ≤ N) t
      rw [h1, h2]
      field_simp
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ t)]
    have h3' : Real.sqrt (N / t) / (3 * ε)
        = (2 / 3) * Real.sqrt (t * N) / (2 * (ε * t)) := h3.symm
    rw [h3']
    exact h2.ge.trans h1
  have hS : nextApproxCountScale N t ε ≥ Real.sqrt (N / t) / (3 * ε) := by
    unfold nextApproxCountScale
    have h2 : Real.sqrt (t * (N - t)) / nextApproxCountPrecision t ε
        ≤ Real.sqrt (t * (N - t)) / nextApproxCountPrecision t ε
            + Real.sqrt (N / nextApproxCountPrecision t ε) := by
      linarith [Real.sqrt_nonneg (N / nextApproxCountPrecision t ε)]
    linarith
  have hkey : (1 / ε) * Real.sqrt (N / t)
      = 3 * (Real.sqrt (N / t) / (3 * ε)) := by field_simp
  rw [hkey]
  nlinarith [hS]

/-- For `N > 0`, `1 ≤ t ≤ N / 2`, `ε > 0`, and `ε * t < 1`, the exact-counting scale `Real.sqrt
(t * N)` is at most twice `nextApproxCountScale N t ε`. -/
theorem nextApproxCountScale_exact_le {N t ε : ℝ} (hN : 0 < N) (ht1 : 1 ≤ t)
    (htN : t ≤ N / 2) (heps : 0 < ε) (hlt : ε * t < 1) :
    Real.sqrt (t * N) ≤ 2 * nextApproxCountScale N t ε := by
  have hεt0 : (0 : ℝ) ≤ ε * t :=
    le_of_lt (mul_pos heps (lt_of_lt_of_le (by norm_num) ht1))
  have hk : nextApproxCountPrecision t ε = 1 :=
    nextApproxCountPrecision_eq_one hεt0 hlt
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
  have hsq : Real.sqrt (t * (N - t)) ≥ (2 / 3) * Real.sqrt (t * N) := by
    have h3 : (4 / 9) * (t * N) ≤ t * (N - t) := by
      have h5 : (4 / 9) * N ≤ N - t := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h5 (le_trans (by norm_num) ht1)]
    have h4 : Real.sqrt ((4 / 9) * (t * N)) = (2 / 3) * Real.sqrt (t * N) := by
      have hsq4 : Real.sqrt (4 / 9 : ℝ) = 2 / 3 := by
        rw [show (4/9:ℝ) = (2/3)^2 by ring,
          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (2:ℝ)/3)]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (4:ℝ)/9) (t * N), hsq4,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ t) N]
    calc Real.sqrt (t * (N - t)) ≥ Real.sqrt ((4 / 9) * (t * N)) :=
        Real.sqrt_le_sqrt h3
      _ = (2 / 3) * Real.sqrt (t * N) := h4
  have hs : nextApproxCountScale N t ε = Real.sqrt N + Real.sqrt (t * (N - t)) := by
    rw [nextApproxCountScale, hk]
    simp only [div_one]
  have hS : nextApproxCountScale N t ε ≥ Real.sqrt (t * N) * (2 / 3) := by
    rw [hs]
    nlinarith [hsq, Real.sqrt_nonneg (N : ℝ)]
  have hNpos : (0 : ℝ) < N := hN
  nlinarith [hS, Real.sqrt_nonneg (t * N)]

/-- For `N > 0`, `1 ≤ t ≤ N / 2`, `ε > 0`, and `ε * N ≤ 1 / 3`, the exact-counting scale
`Real.sqrt (t * N)` is at most twice `nextApproxCountScale N t ε`. -/
theorem nextApproxCountScale_fallback_le {N t ε : ℝ} (hN : 0 < N) (ht1 : 1 ≤ t)
    (htN : t ≤ N / 2) (heps : 0 < ε) (hfb : ε * N ≤ 1 / 3) :
    Real.sqrt (t * N) ≤ 2 * nextApproxCountScale N t ε := by
  have hlt : ε * t < 1 := by
    have h1 : ε * (N / 2) ≤ 1 / 6 := by
      have := mul_le_mul_of_nonneg_right hfb (by norm_num : (0:ℝ) ≤ 1 / 2)
      linarith
    have h2 : ε * t ≤ ε * (N / 2) :=
      mul_le_mul_of_nonneg_left htN (le_of_lt heps)
    linarith
  exact nextApproxCountScale_exact_le hN ht1 htN heps hlt

/-- The integer output of the relative-counting branch, obtained by rounding the final
amplitude-based count estimate via `basicApproxCountOutput` after prefix `ω`. -/
noncomputable def nextApproxCountRelOutput {N : ℕ} (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (y : Fin (basicApproxCountFinalM ε (basicApproxCountStop N ω))) : ℤ :=
  basicApproxCountOutput N ε ω y

/-- The conditional probability, after prefix `ω`, that the final integer readout differs from
`S.card` by at most `ε * S.card`. -/
noncomputable def nextApproxCountRelGood {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  basicApproxCountFinalGood hN S ε ω hω

/-- The conditional probability, after prefix `ω`, that the final integer count readout is zero. -/
noncomputable def nextApproxCountRelZero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hω : 2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) : ℝ :=
  basicApproxCountFinalZero hN S ε ω hω

/-- The relative-counting cost ledger for prefix `ω`, summing the visited doubling-grid sizes
and the final grid size through `basicApproxCountTotalCost`. -/
noncomputable def nextApproxCountRelCost {N : ℕ} (ε : ℝ)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : ℕ :=
  basicApproxCountTotalCost N ε ω

/-- For `0 < ε ≤ 1`, the final grid `basicApproxCountFinalM ε s` has size at least two at every
stopping level `s`. -/
theorem nextApproxCountRel_grid_two (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℕ) :
    2 ≤ basicApproxCountFinalM ε s := by
  have hpi : (2 : ℝ) ≤ 20 * Real.pi ^ 2 := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq : (0 : ℝ) ≤ (Real.pi - 3) ^ 2 := sq_nonneg _
    nlinarith [hsq]
  have h2s : (1 : ℝ) ≤ 2 ^ s := by
    exact_mod_cast Nat.one_le_two_pow
  have hbig : (1 : ℝ) < 20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ) := by
    have hform : 20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ)
        = (20 * Real.pi ^ 2 * (2 ^ s : ℝ)) / ε := by ring
    rw [hform, lt_div_iff₀ hε]
    have h1 : (2 : ℝ) ≤ 20 * Real.pi ^ 2 * (2 ^ s : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hpi (by positivity : (0:ℝ) ≤ 2 ^ s)
      nlinarith [hmul, h2s]
    nlinarith [h1, hε1]
  unfold basicApproxCountFinalM
  have hceil : (1 : ℝ) < (Nat.ceil (20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ)) : ℝ) :=
    lt_of_lt_of_le hbig (Nat.le_ceil _)
  have hceilN : (1 : ℕ) < Nat.ceil (20 * Real.pi ^ 2 / ε * (2 ^ s : ℝ)) := by
    exact_mod_cast hceil
  omega

/-- For a nonempty marked set, `N > 0`, and `0 < ε ≤ 1`, the relative-counting branch achieves
error at most `ε * S.card` with total probability at least `2 / 3`, assuming all final grids
have size at least two. -/
theorem nextApproxCountRel_accuracy {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hS : 0 < S.card)
    (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    (2 / 3 : ℝ) ≤
      ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          nextApproxCountRelGood hN S ε ω (hω ω) := by
  have h := bhmt_basic_approx_count_success N S hN ε hε hε1 hω
  simpa [nextApproxCountRelGood] using! h.2 hS

/-- For a nonempty marked set, `N > 0`, and `0 < ε ≤ 1`, the expected relative-counting ledger
is at most `2000 * (1 / ε) * Real.sqrt (N / S.card)`. -/
theorem nextApproxCountRel_cost {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hS : 0 < S.card) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω *
        ((nextApproxCountRelCost ε ω : ℕ) : ℝ))
      ≤ 2000 * (1 / ε) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) := by
  have h := bhmt_basic_approx_count_expected_cost N S hN ε hε hε1
  simpa [nextApproxCountRelCost] using! (h.2 hS).2

/-- For a nonempty marked set, `N > 0`, and `0 < ε ≤ 1`, the expected relative-counting ledger
is at least `(7 * Real.pi / 2) * (1 / ε) * Real.sqrt (N / S.card)`. -/
theorem nextApproxCountRel_cost_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hS : 0 < S.card) :
    7 * Real.pi / 2 * (1 / ε) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
      ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          ((nextApproxCountRelCost ε ω : ℕ) : ℝ) := by
  have h := bhmt_basic_approx_count_expected_cost N S hN ε hε hε1
  simpa [nextApproxCountRelCost] using! (h.2 hS).1

/-- For an empty marked set, `N > 0`, and `0 < ε ≤ 1`, the relative-counting branch outputs zero
with total probability one, assuming all final grids have size at least two. -/
theorem nextApproxCountRel_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hS : S.card = 0)
    (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω)) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω *
        nextApproxCountRelZero hN S ε ω (hω ω)) = 1 := by
  have h := bhmt_basic_approx_count_success N S hN ε hε hε1 hω
  simpa [nextApproxCountRelZero] using! h.1 hS

/-- For an empty marked set and `N > 0`, the expected relative-counting ledger equals `2 * 2 ^
basicApproxCountLoopCap N - 2` plus the final grid size at that cap. -/
theorem nextApproxCountRel_zero_cost {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hS : S.card = 0) :
    (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω *
        ((nextApproxCountRelCost ε ω : ℕ) : ℝ))
      = 2 * (2 : ℝ) ^ basicApproxCountLoopCap N - 2
        + (basicApproxCountFinalM ε (basicApproxCountLoopCap N) : ℝ) := by
  have h := bhmt_basic_approx_count_zero_cost hN S hS ε
  simpa [nextApproxCountRelCost] using! h

/-- For `N > 0`, `nextCor4Grid` has size at least two when its two count estimates come from
rough-grid amplitude labels. -/
theorem nextCor4_grid_two_on_estimates {N : ℕ} (hN : 0 < N)
    (z₁ z₂ : Fin (nextCor4RoughGrid N)) :
    2 ≤ nextCor4Grid N
      ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
      ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN.le
  apply nextCor4_grid_two
  · exact mul_nonneg hN0 (aeEstimate_mem (nextCor4RoughGrid N) z₁).1
  · have h1 := (aeEstimate_mem (nextCor4RoughGrid N) z₁).2
    have hmul : (N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁ ≤ (N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 hN0
    linarith
  · exact mul_nonneg hN0 (aeEstimate_mem (nextCor4RoughGrid N) z₂).1
  · have h1 := (aeEstimate_mem (nextCor4RoughGrid N) z₂).2
    have hmul : (N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂ ≤ (N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left h1 hN0
    linarith

/-- The exact-counting branch's total success probability, given by `nextCor4SuccessMass` after
two independent rough readouts and their selected final counting grid. -/
noncomputable def nextApproxCountExactSuccessMass {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N)) (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂)) : ℝ :=
  nextCor4SuccessMass hN S hM₀ hM

/-- The exact-counting branch's ledger: two rough-grid charges plus the expected `ladderCost`
evaluated at the smaller of two independent rough readouts. -/
noncomputable def nextApproxCountExactCost {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N)) : ℝ :=
  2 * (nextCor4RoughGrid N : ℝ) +
    (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
      (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      (firstProb hN S z.1) * (firstProb hN S z.2) * ladderCost (pairMin z) N)

/-- For `N > 0` and `1 ≤ S.card ≤ N / 2`, the exact-counting branch returns `S.card` with
probability at least `3 / 4`, assuming the rough and final grids have size at least two. -/
theorem nextApproxCountExact_accuracy {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2)
    (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂)) :
    3 / 4 ≤ nextApproxCountExactSuccessMass hN S hM₀ hM := by
  simpa [nextApproxCountExactSuccessMass] using! nextCor4_success hN S hcard hcardN hM₀ hM

/-- For `N > 0` and `1 ≤ S.card ≤ N / 2`, the exact-counting ledger is at most `650 * Real.sqrt
(S.card * N)`. -/
theorem nextApproxCountExact_cost {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2) :
    nextApproxCountExactCost hN S ≤ 650 * Real.sqrt ((S.card : ℝ) * (N : ℝ)) := by
  simpa [nextApproxCountExactCost] using! cor4_total_ledger_le hN S hcard hcardN

/-- The natural ceiling of `9 * Real.pi * 2 ^ basicApproxCountStop N ω`, used as the first scale
parameter after prefix `ω`. -/
noncomputable def nextApproxCountL1 {N : ℕ}
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)) : ℕ :=
  Nat.ceil (9 * Real.pi * (2 ^ basicApproxCountStop N ω : ℝ))

/-- Under the stated positive-angle and angle-size bounds, a zero prefix through level `n` and
the crossing `(1 / 5) < 2 ^ (n + 1) * θ` force `nextApproxCountL1 ω ≥ (18 / 5) * Real.sqrt
(N / S.card)` when `n + 1` is within the loop cap. -/
theorem nextApproxCountL1_lower {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hS : 0 < S.card) (θ : ℝ) (hθ0 : 0 < θ)
    (hangle : θ * Real.sqrt (N : ℝ) ≤ Real.pi / 2 * Real.sqrt (S.card : ℝ))
    (n : ℕ) (hn : n + 1 ≤ basicApproxCountLoopCap N)
    (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val))
    (hz : CountRelNext.countRelPrefixZero N n ω)
    (hcross : (1 / 5 : ℝ) < (2 : ℝ) ^ (n + 1) * θ) :
    (18 / 5) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) ≤ (nextApproxCountL1 ω : ℝ) := by
  have hscale := CountRelNext.countRel_exit_scale hN S hS θ hθ0 hangle n hn ω hz hcross
  have hpi : (0 : ℝ) < 9 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hscale hpi.le
  have hceil : (9 * Real.pi * (2 ^ basicApproxCountStop N ω : ℝ))
      ≤ (nextApproxCountL1 ω : ℝ) := by
    unfold nextApproxCountL1
    exact Nat.le_ceil _
  have hkey : (18 / 5) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
      ≤ 9 * Real.pi * (2 ^ basicApproxCountStop N ω : ℝ) := by
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    calc
      (18 / 5) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
          = 9 * Real.pi * ((2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / (S.card : ℝ))) := by
            field_simp
            ring
      _ ≤ 9 * Real.pi * (2 ^ basicApproxCountStop N ω : ℝ) := hmul
  linarith

/-- The complement-estimation grid size `Nat.ceil (40 / Real.sqrt ε)`. -/
noncomputable def nextApproxCountComplementGrid (ε : ℝ) : ℕ :=
  Nat.ceil (40 / Real.sqrt ε)

/-- The natural ceiling of one plus twice the smaller of `Real.sqrt (r₁ / (ε * N))` and
`Real.sqrt (r₂ / (ε * N))`. -/
noncomputable def nextApproxCountL2 (ε : ℝ) (N : ℕ) (r₁ r₂ : ℝ) : ℕ :=
  Nat.ceil (2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) + 1)

/-- The second scale parameter `nextApproxCountL2 ε N r₁ r₂` is always at least one. -/
theorem nextApproxCountL2_ge_one (ε : ℝ) (N : ℕ) (r₁ r₂ : ℝ) :
    1 ≤ nextApproxCountL2 ε N r₁ r₂ := by
  have hceil : (2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) + 1 : ℝ)
      ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ) := by
    unfold nextApproxCountL2
    exact Nat.le_ceil _
  have hnonneg : (0 : ℝ) ≤ 2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (r₁ / (ε * (N : ℝ))) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.sqrt (r₂ / (ε * (N : ℝ))) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) := le_min h1 h2
    linarith
  have h3 : (1 : ℝ) ≤ 2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) + 1 := by
    linarith
  exact_mod_cast h3.trans hceil

/-- If `ε > 0`, `N > 0`, and both readouts are at least the nonnegative value `v - w`, then
`nextApproxCountL2 ε N r₁ r₂ ≥ 2 * Real.sqrt ((v - w) / (ε * N)) + 1`. -/
theorem nextApproxCountL2_lower_window {ε : ℝ} {N : ℕ} {r₁ r₂ v w : ℝ}
    (hε : 0 < ε) (hN : 0 < N)
    (h1 : v - w ≤ r₁) (h2 : v - w ≤ r₂) (hwv : w ≤ v) :
    2 * Real.sqrt ((v - w) / (ε * (N : ℝ))) + 1
      ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ) := by
  have hεN : (0 : ℝ) < ε * (N : ℝ) :=
    mul_pos hε (by exact_mod_cast hN)
  have hv0 : 0 ≤ v - w := sub_nonneg.mpr hwv
  have hA : Real.sqrt ((v - w) / (ε * (N : ℝ)))
      ≤ Real.sqrt (r₁ / (ε * (N : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right h1 (le_of_lt hεN)
  have hB : Real.sqrt ((v - w) / (ε * (N : ℝ)))
      ≤ Real.sqrt (r₂ / (ε * (N : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right h2 (le_of_lt hεN)
  have hmin : Real.sqrt ((v - w) / (ε * (N : ℝ)))
      ≤ min (Real.sqrt (r₁ / (ε * (N : ℝ)))) (Real.sqrt (r₂ / (ε * (N : ℝ)))) := by
    exact le_min hA hB
  have hceil : (2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) + 1 : ℝ)
      ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ) := by
    unfold nextApproxCountL2
    exact Nat.le_ceil _
  linarith

/-- If `ε > 0`, `N > 0`, `v ≥ 0`, and both readouts are at least `v / 4`, then
`nextApproxCountL2 ε N r₁ r₂ ≥ Real.sqrt (v / (ε * N)) + 1`. -/
theorem nextApproxCountL2_lower_relative {ε : ℝ} {N : ℕ} {r₁ r₂ v : ℝ}
    (hε : 0 < ε) (hN : 0 < N) (hv0 : 0 ≤ v)
    (h1 : v / 4 ≤ r₁) (h2 : v / 4 ≤ r₂) :
    Real.sqrt (v / (ε * (N : ℝ))) + 1 ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ) := by
  have hεN : (0 : ℝ) < ε * (N : ℝ) :=
    mul_pos hε (by exact_mod_cast hN)
  have hvq : (0 : ℝ) ≤ v / 4 := by positivity
  have hA : Real.sqrt ((v / 4) / (ε * (N : ℝ)))
      ≤ Real.sqrt (r₁ / (ε * (N : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right h1 (le_of_lt hεN)
  have hB : Real.sqrt ((v / 4) / (ε * (N : ℝ)))
      ≤ Real.sqrt (r₂ / (ε * (N : ℝ))) := by
    refine Real.sqrt_le_sqrt ?_
    exact div_le_div_of_nonneg_right h2 (le_of_lt hεN)
  have hmin : Real.sqrt ((v / 4) / (ε * (N : ℝ)))
      ≤ min (Real.sqrt (r₁ / (ε * (N : ℝ)))) (Real.sqrt (r₂ / (ε * (N : ℝ)))) := by
    exact le_min hA hB
  have hceil : (2 * min (Real.sqrt (r₁ / (ε * (N : ℝ))))
                     (Real.sqrt (r₂ / (ε * (N : ℝ)))) + 1 : ℝ)
      ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ) := by
    unfold nextApproxCountL2
    exact Nat.le_ceil _

  have hsqrt : 2 * Real.sqrt ((v / 4) / (ε * (N : ℝ)))
      = Real.sqrt (v / (ε * (N : ℝ))) := by
    have h1' : Real.sqrt ((v / 4) / (ε * (N : ℝ)))
        = Real.sqrt (v / 4) / Real.sqrt (ε * (N : ℝ)) :=
      Real.sqrt_div hvq (ε * (N : ℝ))
    have h2' : Real.sqrt (v / 4) = Real.sqrt v / 2 := by
      rw [show v / 4 = v * (1 / 4 : ℝ) by ring, Real.sqrt_mul hv0 (1 / 4 : ℝ)]
      have hq : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by ring, Real.sqrt_sq (by norm_num)]
      rw [hq]
      ring
    have h3' : Real.sqrt (v / (ε * (N : ℝ)))
        = Real.sqrt v / Real.sqrt (ε * (N : ℝ)) :=
      Real.sqrt_div hv0 (ε * (N : ℝ))
    rw [h1', h2', h3']
    ring
  linarith

/-- The relative-accuracy grid parameter `Nat.ceil ((1 / Real.sqrt ε) * L₁ * (1 + L₂))`. -/
noncomputable def nextApproxCountM1 (ε : ℝ) (L₁ L₂ : ℕ) : ℕ :=
  Nat.ceil ((1 / Real.sqrt ε) * (L₁ : ℝ) * (1 + (L₂ : ℝ)))

/-- The exact-accuracy grid parameter obtained by applying `nextCor4Grid` to the two preliminary
count estimates. -/
noncomputable def nextApproxCountM2 (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  nextCor4Grid N t'₁ t'₂

/-- Selects the smaller of the relative-accuracy and exact-accuracy grid parameters `M₁` and
`M₂`. -/
noncomputable def nextApproxCountM (M₁ M₂ : ℕ) : ℕ := min M₁ M₂

/-- The final amplitude-estimation grid size `Nat.ceil (10 * Real.pi * M)` associated with a
selected parameter `M`. -/
noncomputable def nextApproxCountFinalGrid (M : ℕ) : ℕ :=
  Nat.ceil (10 * Real.pi * (M : ℝ))

/-- Under the stated positive square-root identities and lower bounds on `M` and `M'`, the
counting window `2 * Real.pi * st * sc / M' + Real.pi ^ 2 * N / M' ^ 2` is at most `ε * t /
3`. -/
theorem nextApproxCount_window_le {ε t N M M' se sN st sc : ℝ}
    (hse : se ^ 2 = ε) (hse0 : 0 < se)
    (hst : st ^ 2 = t) (hst0 : 0 < st)
    (hsc : sc ^ 2 = (N : ℝ) - t) (hsc0 : 0 < sc)
    (hsN : sN ^ 2 = (N : ℝ)) (hsN0 : 0 < sN)
    (hM : (1 / se) * (18 / 5) * (sN / st) * (1 + (1 / 6) * (sc / (se * sN))) ≤ M)
    (hM' : 10 * Real.pi * M ≤ M') :
    2 * Real.pi * (st * sc) / M' + Real.pi ^ 2 * (N : ℝ) / M' ^ 2 ≤ ε * t / 3 := by
  set D : ℝ := 6 * se * sN + sc with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    positivity
  set M0 : ℝ := (1 / se) * (18 / 5) * (sN / st) * (1 + (1 / 6) * (sc / (se * sN))) with hM0def
  have hM0pos : 0 < M0 := by
    rw [hM0def]
    positivity
  have hMge : M0 ≤ M := by simpa [hM0def] using! hM
  have hMpos : 0 < M := lt_of_lt_of_le hM0pos hMge
  have hM'pos : 0 < M' := by
    have h1 : 0 < 10 * Real.pi * M := by positivity
    linarith
  have hNnonneg : (0 : ℝ) ≤ N := by nlinarith [hsN, sq_nonneg sN]

  have hM0id : M0 = 3 * D / (5 * se ^ 2 * st) := by
    dsimp [M0, D]
    field_simp
    ring

  have hT1 : 2 * Real.pi * (st * sc) / M' ≤ (st * sc) / (5 * M) := by
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    have hrec : 1 / M' ≤ 1 / (10 * Real.pi * M) :=
      one_div_le_one_div_of_le (by positivity) hM'
    have hmul := mul_le_mul_of_nonneg_left hrec
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (st * sc))
    calc
      2 * Real.pi * (st * sc) / M' = 2 * Real.pi * (st * sc) * (1 / M') := by ring
      _ ≤ 2 * Real.pi * (st * sc) * (1 / (10 * Real.pi * M)) := hmul
      _ = (st * sc) / (5 * M) := by field_simp; ring
  have hT2 : Real.pi ^ 2 * (N : ℝ) / M' ^ 2 ≤ (N : ℝ) / (100 * M ^ 2) := by
    have hsq : (10 * Real.pi * M) ^ 2 ≤ M' ^ 2 := by
      have h1 : (10 * Real.pi * M) * (10 * Real.pi * M) ≤ M' * (10 * Real.pi * M) :=
        mul_le_mul_of_nonneg_right hM' (by positivity)
      have h2 : M' * (10 * Real.pi * M) ≤ M' * M' :=
        mul_le_mul_of_nonneg_left hM' (by positivity : (0 : ℝ) ≤ M')
      nlinarith [h1, h2]
    have hpi1 : (0 : ℝ) < Real.pi := Real.pi_pos
    have hrec : 1 / M' ^ 2 ≤ 1 / (10 * Real.pi * M) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hsq
    have hmul := mul_le_mul_of_nonneg_left hrec
      (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 * (N : ℝ))
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    calc
      Real.pi ^ 2 * (N : ℝ) / M' ^ 2 = Real.pi ^ 2 * (N : ℝ) * (1 / M' ^ 2) := by ring
      _ ≤ Real.pi ^ 2 * (N : ℝ) * (1 / (10 * Real.pi * M) ^ 2) := hmul
      _ = (N : ℝ) / (100 * M ^ 2) := by field_simp; ring

  have hS1 : (st * sc) / (5 * M) ≤ (st * sc) / (5 * M0) := by
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (le_of_lt hst0) (le_of_lt hsc0)
    · exact mul_pos (by norm_num : (0 : ℝ) < 5) hM0pos
    · exact mul_le_mul_of_nonneg_left hMge (by norm_num : (0 : ℝ) ≤ 5)
  have hS2 : (N : ℝ) / (100 * M ^ 2) ≤ (N : ℝ) / (100 * M0 ^ 2) := by
    have hsq : M0 * M0 ≤ M * M := by
      have h1 : M0 * M0 ≤ M * M0 := mul_le_mul_of_nonneg_right hMge (le_of_lt hM0pos)
      have h2 : M * M0 ≤ M * M := mul_le_mul_of_nonneg_left hMge (le_of_lt hMpos)
      linarith
    have h1 : 100 * (M0 * M0) ≤ 100 * (M * M) := by nlinarith [hsq]
    apply div_le_div_of_nonneg_left
    · exact hNnonneg
    · have hM0sq : (0 : ℝ) < M0 * M0 := mul_pos hM0pos hM0pos
      have hM0sq' : (0 : ℝ) < 100 * (M0 * M0) := by nlinarith [hM0sq]
      simpa [pow_two] using! hM0sq'
    · have h1' : 100 * (M0 ^ 2) ≤ 100 * (M ^ 2) := by nlinarith [h1]
      exact h1'

  have hk1 : se ^ 2 * st ^ 2 = ε * t := by
    rw [show se ^ 2 * st ^ 2 = (se ^ 2) * (st ^ 2) by ring, hse, hst]
  have hk2 : se ^ 4 * st ^ 2 = ε ^ 2 * t := by
    rw [show se ^ 4 * st ^ 2 = (se ^ 2) ^ 2 * (st ^ 2) by ring, hse, hst]
  have hA : (st * sc) / (5 * M0) = ε * t * sc / (3 * D) := by
    rw [hM0id]
    field_simp [ne_of_gt hse0, ne_of_gt hst0, ne_of_gt hDpos]
    nlinarith [hk1]
  have hB : (N : ℝ) / (100 * M0 ^ 2) = ε ^ 2 * t * (N : ℝ) / (36 * D ^ 2) := by
    rw [hM0id]
    field_simp [ne_of_gt hse0, ne_of_gt hst0, ne_of_gt hDpos]
    nlinarith [hk2]
  have hsum : (st * sc) / (5 * M0) + (N : ℝ) / (100 * M0 ^ 2)
      ≤ ε * t * sc / (3 * D) + ε ^ 2 * t * (N : ℝ) / (36 * D ^ 2) := by
    rw [hA, hB]

  have hgoal : ε * t * sc / (3 * D) + ε ^ 2 * t * (N : ℝ) / (36 * D ^ 2) ≤ ε * t / 3 := by
    have hεnonneg : (0 : ℝ) ≤ ε := by nlinarith [hse, hse0]
    have htnonneg : (0 : ℝ) ≤ t := by nlinarith [hst, hst0]
    have hεpos : 0 < ε := by nlinarith [hse, hse0]
    have htpos : 0 < t := by nlinarith [hst, hst0]
    have hεtpos : 0 < ε * t := mul_pos hεpos htpos
    have hpi1 : (0 : ℝ) < Real.pi := Real.pi_pos
    have hD2pos : 0 < 36 * D ^ 2 := by positivity
    have heq : ε * t * sc / (3 * D) + ε ^ 2 * t * (N : ℝ) / (36 * D ^ 2)
        = (12 * sc * D + ε * (N : ℝ)) * (ε * t) / (36 * D ^ 2) := by
      field_simp [ne_of_gt hDpos]
      ring
    rw [heq]
    have hkey : 12 * sc * D + ε * (N : ℝ) ≤ 12 * D ^ 2 := by
      have hDdef' : D = 6 * se * sN + sc := hDdef
      rw [hDdef']
      have hsq : (0 : ℝ) ≤ 6 * se * sN * sc := by
        have hpi1 : (0 : ℝ) < Real.pi := Real.pi_pos
        positivity
      have hscnonneg : (0 : ℝ) ≤ sc := le_of_lt hsc0
      nlinarith [hse, hsN, mul_nonneg hsq (le_of_lt hse0)]
    rw [div_le_iff₀ hD2pos]
    nlinarith [hkey]
  linarith [hT1, hT2, hS1, hS2, hsum, hgoal]

/-- For `ε > 0`, `N > 0`, and `0 < t ≤ N / 2`, the stated lower bounds on `L₁` and `L₂` make the
final grid from `nextApproxCountM1` yield a parameter-one counting window at most `ε * t /
3`. -/
theorem nextApproxCountM1_adequate {ε t : ℝ} {N : ℕ} {L₁ L₂ : ℕ}
    (hε : 0 < ε) (hN : 0 < N) (ht : 0 < t) (htN : t ≤ (N : ℝ) / 2)
    (hL1 : (18 / 5) * Real.sqrt ((N : ℝ) / t) ≤ (L₁ : ℝ))
    (hL2 : (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ))) ≤ (L₂ : ℝ)) :
    nextCor4Window (nextApproxCountFinalGrid (nextApproxCountM1 ε L₁ L₂)) 1 N t
      ≤ ε * t / 3 := by
  set M : ℕ := nextApproxCountM1 ε L₁ L₂ with hMdef
  set M' : ℕ := nextApproxCountFinalGrid M with hM'def
  have hceil : (1 / Real.sqrt ε) * (L₁ : ℝ) * (1 + (L₂ : ℝ)) ≤ (M : ℝ) := by
    unfold M nextApproxCountM1
    exact Nat.le_ceil _
  have h1 : (1 / Real.sqrt ε) * (18 / 5) * Real.sqrt ((N : ℝ) / t)
      ≤ (1 / Real.sqrt ε) * (L₁ : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt ε)
    simpa [mul_assoc] using! h
  have h2 : 1 + (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ)))
      ≤ 1 + (L₂ : ℝ) := by linarith [hL2]
  have h3 : (1 / Real.sqrt ε) * (18 / 5) * Real.sqrt ((N : ℝ) / t)
      * (1 + (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ))))
      ≤ (1 / Real.sqrt ε) * (L₁ : ℝ) * (1 + (L₂ : ℝ)) := by
    have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
    simpa [mul_assoc] using! hmul
  have hscale : (1 / Real.sqrt ε) * (18 / 5) * Real.sqrt ((N : ℝ) / t)
      * (1 + (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ)))) ≤ (M : ℝ) := by
    linarith
  have hconv1 : Real.sqrt ((N : ℝ) / t) = Real.sqrt (N : ℝ) / Real.sqrt t :=
    Real.sqrt_div (by positivity) t
  have hconv2 : Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ)))
      = Real.sqrt ((N : ℝ) - t) / (Real.sqrt ε * Real.sqrt (N : ℝ)) := by
    have h1 : Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ)))
        = Real.sqrt ((N : ℝ) - t) / Real.sqrt (ε * (N : ℝ)) :=
      Real.sqrt_div (by linarith) (ε * (N : ℝ))
    have h2 : Real.sqrt (ε * (N : ℝ)) = Real.sqrt ε * Real.sqrt (N : ℝ) :=
      Real.sqrt_mul (by positivity) (N : ℝ)
    rw [h1, h2]
  have hgrid : 10 * Real.pi * (M : ℝ) ≤ (M' : ℝ) := by
    unfold M' nextApproxCountFinalGrid
    exact Nat.le_ceil _
  have hwin := nextApproxCount_window_le (ε := ε) (t := t) (N := (N : ℝ))
    (M := (M : ℝ)) (M' := (M' : ℝ))
    (se := Real.sqrt ε) (sN := Real.sqrt (N : ℝ))
    (st := Real.sqrt t) (sc := Real.sqrt ((N : ℝ) - t))
    (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ε))
    (by positivity)
    (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ t))
    (by positivity)
    (Real.sq_sqrt (by linarith : (0 : ℝ) ≤ (N : ℝ) - t))
    (Real.sqrt_pos.2 (by linarith [htN, ht, hN]))
    (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ)))
    (by positivity)
    (by rw [hconv1, hconv2] at hscale; exact hscale)
    hgrid
  have hsqrt : Real.sqrt (t * ((N : ℝ) - t)) = Real.sqrt t * Real.sqrt ((N : ℝ) - t) :=
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ t) ((N : ℝ) - t)
  simpa [nextCor4Window, hsqrt] using! hwin

/-- For `0 ≤ t ≤ N`, enlarging a positive grid from `M` to `M'` can only decrease
`nextCor4Window` at a fixed tail parameter `k`. -/
theorem nextCor4Window_mono_grid {M M' k : ℕ} {N : ℕ} {t : ℝ}
    (hM : (M : ℝ) ≤ (M' : ℝ)) (hM0 : 0 < (M : ℝ))
    (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ)) :
    nextCor4Window M' k N t ≤ nextCor4Window M k N t := by
  have h1 : 2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) / (M' : ℝ)
      ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) := by
    have hbase : Real.sqrt (t * ((N : ℝ) - t)) / (M' : ℝ)
        ≤ Real.sqrt (t * ((N : ℝ) - t)) / (M : ℝ) := by
      have hrec : 1 / (M' : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hM0 hM
      have hrec' : (M' : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ := by simpa [one_div] using! hrec
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hrec' (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hbase (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ))
    convert! hmul using 1 <;> ring
  have h2 : Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M' : ℝ) ^ 2
      ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := by
    have hsq : (M : ℝ) ^ 2 ≤ (M' : ℝ) ^ 2 := by
      have h1' : (M : ℝ) * (M : ℝ) ≤ (M' : ℝ) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hM (le_of_lt hM0)
      have h2' : (M' : ℝ) * (M : ℝ) ≤ (M' : ℝ) * (M' : ℝ) :=
        mul_le_mul_of_nonneg_left hM (by linarith [hM, hM0])
      nlinarith [h1', h2']
    have hbase : (N : ℝ) / (M' : ℝ) ^ 2 ≤ (N : ℝ) / (M : ℝ) ^ 2 := by
      have hrec : 1 / (M' : ℝ) ^ 2 ≤ 1 / (M : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hsq
      have hmul := mul_le_mul_of_nonneg_left hrec (by positivity : (0 : ℝ) ≤ (N : ℝ))
      simpa [div_eq_mul_inv, one_div] using! hmul
    have hmul := mul_le_mul_of_nonneg_left hbase
      (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 * (k : ℝ) ^ 2)
    convert! hmul using 1 <;> ring
  unfold nextCor4Window
  linarith

/-- For `N > 0`, `1 ≤ t ≤ N / 2`, and `t / 2 ≤ v ≤ 3 * t / 2`, a parameter `M₂ ≥ 48 * Real.sqrt
((v + 1) * (N - v + 1))` makes the final parameter-one counting window strictly less than `1
/ 2`. -/
theorem nextApproxCountM2_adequate {N : ℕ} (hN : 0 < N) {t v : ℝ} {M₂ : ℕ}
    (ht1 : 1 ≤ t) (htN : t ≤ (N : ℝ) / 2)
    (hv1 : t / 2 ≤ v) (hv2 : v ≤ 3 * t / 2)
    (hM₂ : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) ≤ (M₂ : ℝ)) :
    nextCor4Window (nextApproxCountFinalGrid M₂) 1 N t < 1 / 2 := by
  have hM₂pos : 0 < (M₂ : ℝ) := by
    have h1 : 0 < 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) := by
      have hv1' : 0 < v + 1 := by linarith
      have hv2' : 0 < (N : ℝ) - v + 1 := by linarith
      have hmul : 0 < (v + 1) * ((N : ℝ) - v + 1) := mul_pos hv1' hv2'
      have hsq : 0 < Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) := Real.sqrt_pos.2 hmul
      nlinarith [hsq]
    linarith
  have hwin := nextCor4_final_window_lt_half hN ht1 htN hv1 hv2 hM₂
  have hgrid : (M₂ : ℝ) ≤ (nextApproxCountFinalGrid M₂ : ℝ) := by
    have hceil : (10 * Real.pi * (M₂ : ℝ)) ≤ (Nat.ceil (10 * Real.pi * (M₂ : ℝ)) : ℝ) :=
      Nat.le_ceil _
    have hpi1 : (0 : ℝ) < Real.pi := Real.pi_pos
    have hpi1' : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hM₂0 : (0 : ℝ) ≤ (M₂ : ℝ) := le_of_lt hM₂pos
    have hscale : (M₂ : ℝ) ≤ 10 * Real.pi * (M₂ : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hpi1' hM₂0
      nlinarith [hmul]
    unfold nextApproxCountFinalGrid
    exact hscale.trans hceil
  have hmono := nextCor4Window_mono_grid (M := M₂) (M' := nextApproxCountFinalGrid M₂)
    (k := 1) (N := N) (t := t) hgrid hM₂pos (by positivity) (by linarith)
  exact lt_of_le_of_lt hmono hwin

/-- Under the relative-grid and exact-grid adequacy hypotheses, choosing the smaller parameter
with `nextApproxCountM` gives a final parameter-one counting window either at most `ε * t /
3` or strictly less than `1 / 2`. -/
theorem nextApproxCountM_adequate {ε t : ℝ} {N : ℕ} {L₁ L₂ M₂ : ℕ} {v : ℝ}
    (hε : 0 < ε) (hN : 0 < N) (ht : 0 < t) (ht1 : 1 ≤ t) (htN : t ≤ (N : ℝ) / 2)
    (hL1 : (18 / 5) * Real.sqrt ((N : ℝ) / t) ≤ (L₁ : ℝ))
    (hL2 : (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ))) ≤ (L₂ : ℝ))
    (hv1 : t / 2 ≤ v) (hv2 : v ≤ 3 * t / 2)
    (hM₂ : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) ≤ (M₂ : ℝ)) :
    nextCor4Window
        (nextApproxCountFinalGrid
          (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂)) 1 N t
        ≤ ε * t / 3 ∨
      nextCor4Window
        (nextApproxCountFinalGrid
          (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂)) 1 N t < 1 / 2 := by
  by_cases hmin : nextApproxCountM1 ε L₁ L₂ ≤ M₂
  · left
    have hM : nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂ = nextApproxCountM1 ε L₁ L₂ := by
      simp [nextApproxCountM, min_eq_left hmin]
    rw [hM]
    exact nextApproxCountM1_adequate hε hN ht htN hL1 hL2
  · right
    have hM : nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂ = M₂ := by
      have hle : M₂ ≤ nextApproxCountM1 ε L₁ L₂ := by omega
      simp [nextApproxCountM, min_eq_right hle]
    rw [hM]
    exact nextApproxCountM2_adequate hN ht1 htN hv1 hv2 hM₂

open Qatlib.Concepts.AEMeanReadout.AELawStability
open Qatlib.Concepts.EstimatorLaws.MergedEstimator
open Qatlib.Concepts.EstimatorLaws.TvStability

/-- The access ledger `2 * (k + 2) * (2 * layerRepetitions k + 1) * layerGrid k` for the
positive and negative layered estimates in one signed trial. -/
def nextMontanaroTrialAccessCount (k : ℕ) : ℕ :=
  2 * (k + 2) * (2 * layerRepetitions k + 1) * layerGrid k

/-- The total access ledger for `2 * r + 1` signed trials, charging
`nextMontanaroTrialAccessCount k` and one additional center-sampling access per trial. -/
def nextMontanaroUAccessCount (k r : ℕ) : ℕ :=
  (2 * r + 1) * (nextMontanaroTrialAccessCount k + 1)

/-- For every real `x ≤ 1` and natural `r`, `(1 - x) ^ r * (1 + r * x) ≤ 1`. -/
theorem nextMontanaro_pow_mul_le_one (x : ℝ) (hx1 : x ≤ 1) (r : ℕ) :
    (1 - x) ^ r * (1 + (r : ℝ) * x) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hkey : (1 - x) * (1 + ((r + 1 : ℕ) : ℝ) * x) ≤ 1 + (r : ℝ) * x := by
        push_cast
        have hsq : 0 ≤ x ^ 2 := sq_nonneg x
        have hnn : 0 ≤ ((r + 1 : ℕ) : ℝ) * x ^ 2 := mul_nonneg (by positivity) hsq
        nlinarith [hsq, hnn]
      have hpow : 0 ≤ (1 - x) ^ r := pow_nonneg (by linarith) r
      calc
        (1 - x) ^ (r + 1) * (1 + ((r + 1 : ℕ) : ℝ) * x)
            = (1 - x) ^ r * ((1 - x) * (1 + ((r + 1 : ℕ) : ℝ) * x)) := by
              rw [pow_succ]; ring
        _ ≤ (1 - x) ^ r * (1 + (r : ℝ) * x) := mul_le_mul_of_nonneg_left hkey hpow
        _ ≤ 1 := ih

/-- For `r ≥ 336`, the intrinsic amplification term `(143 / 144) ^ r` is at most `3 / 10`. -/
theorem nextMontanaro_intrinsic_le (r : ℕ) (hr : 336 ≤ r) :
    (143 / 144 : ℝ) ^ r ≤ 3 / 10 := by
  have hkey := nextMontanaro_pow_mul_le_one (1 / 144 : ℝ) (by norm_num) r
  have hpow : (1 - (1 / 144 : ℝ)) ^ r = (143 / 144 : ℝ) ^ r := by
    congr 1
    norm_num
  rw [hpow] at hkey
  have hden : 1 + (r : ℝ) * (1 / 144 : ℝ) ≥ 10 / 3 := by
    have hr' : (336 : ℝ) ≤ r := by exact_mod_cast hr
    have hmul : (336 : ℝ) * (1 / 144 : ℝ) ≤ (r : ℝ) * (1 / 144 : ℝ) :=
      mul_le_mul_of_nonneg_right hr' (show (0 : ℝ) ≤ 1 / 144 by norm_num)
    have hval : (336 : ℝ) * (1 / 144 : ℝ) = 7 / 3 := by norm_num
    linarith [hval]
  have hp : 0 ≤ (143 / 144 : ℝ) ^ r := pow_nonneg (by norm_num) r
  have hmul : (143 / 144 : ℝ) ^ r * (10 / 3) ≤ 1 := by
    calc
      (143 / 144 : ℝ) ^ r * (10 / 3)
          ≤ (143 / 144 : ℝ) ^ r * (1 + (r : ℝ) * (1 / 144 : ℝ)) :=
        mul_le_mul_of_nonneg_left hden hp
      _ ≤ 1 := hkey
  nlinarith

/-- For `0 ≤ γ ≤ 1`, the center-sampling term `(2 * r + 1) * γ` is at most `(Real.pi ^ 2 /
Real.sqrt 6) * (2 * r + 1) * Real.sqrt γ`. -/
theorem nextMontanaro_center_charged (r : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (2 * r + 1) * γ ≤ (Real.pi ^ 2 / Real.sqrt 6) *
      ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ := by
  by_cases hγ : γ = 0
  · simp [hγ]
  · have hγpos : 0 < γ := lt_of_le_of_ne hγ0 (Ne.symm hγ)
    have hsqrt : Real.sqrt γ ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using! hγ1⟩
    have hratio : 1 ≤ Real.pi ^ 2 / Real.sqrt 6 := by
      have hs6 : Real.sqrt 6 ≤ 3 := by
        have h6 : 0 ≤ (6 : ℝ) := by norm_num
        nlinarith [Real.sq_sqrt h6]
      have hpi2 : 9 ≤ Real.pi ^ 2 := by
        have h3 := Real.pi_gt_three
        nlinarith [sq_nonneg (Real.pi - 3)]
      rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
      linarith
    have hn : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) := by positivity
    have hsq : Real.sqrt γ ^ 2 = γ := Real.sq_sqrt (le_of_lt hγpos)
    have hX : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg γ)
    have hle : Real.sqrt γ * Real.sqrt γ ≤ Real.sqrt γ := by
      nlinarith [hsqrt, Real.sqrt_nonneg γ]
    calc
      (2 * r + 1) * γ = ((2 * r + 1 : ℕ) : ℝ) * γ := by push_cast; ring
      _ = ((2 * r + 1 : ℕ) : ℝ) * (Real.sqrt γ * Real.sqrt γ) := by
        rw [Real.mul_self_sqrt (le_of_lt hγpos)]
      _ ≤ ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ :=
        mul_le_mul_of_nonneg_left hle hn
      _ ≤ (Real.pi ^ 2 / Real.sqrt 6) * ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ := by
        have h1 := mul_le_mul_of_nonneg_right hratio hX
        calc
          ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ
              = 1 * (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ) := by ring
          _ ≤ (Real.pi ^ 2 / Real.sqrt 6) * (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ) := h1
          _ = _ := by ring

/-- For unitary preparations with payoff-value L1 distance at most `2 * γ`, target variance at
most `σ ^ 2`, `σ > 0`, `k ≥ 4`, `r ≥ 336`, and `0 ≤ γ ≤ 1`, the median's probability of
error exceeding `9 * σ * (1 / 2) ^ k` is at most `3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) *
nextMontanaroUAccessCount k r * Real.sqrt γ`. This charges the preparation perturbation to
the full access ledger in the setting of Lemma 18 of [Montanaro2015]. -/
theorem nextMontanaro_failure_le {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ) (γ : ℝ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (hk : 4 ≤ k) (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ)
    (hr : 336 ≤ r)
    (hvar : (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * ((f i : ℝ)
        - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))) ^ 2) ≤ (σ : ℝ) ^ 2) :
    (nativeSignedLaw A₁ j f σ k hA₁
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))).probEvent
      (fun ξ : Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k) =>
        9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k
          < |(nativeSignedOutputMedian f σ k r ξ : ℝ)
            - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))|)
      ≤ 3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (nextMontanaroUAccessCount k r : ℝ)
          * Real.sqrt γ := by
  have hrest := montanaroLemma18RestrictedSubgoal I A₁ A₂ j f σ k r γ hA₁ hA₂ hk hσ hγ0 hd
  (try dsimp only at hrest)
  have hbound := hrest hvar
  have h1 := nextMontanaro_intrinsic_le r hr
  have h2 := nextMontanaro_center_charged r γ hγ0 hγ1
  have hT : (nextMontanaroUAccessCount k r : ℝ)
      = (2 * r + 1 : ℕ) * (2 * (k + 2) * (2 * layerRepetitions k + 1) * layerGrid k + 1) := by
    simp [nextMontanaroUAccessCount, nextMontanaroTrialAccessCount]
  have hXY : (Real.pi ^ 2 / Real.sqrt 6)
        * ((2 * r + 1) * 2 * (k + 2) * (2 * layerRepetitions k + 1) * (layerGrid k : ℕ)) * Real.sqrt γ
      + (Real.pi ^ 2 / Real.sqrt 6) * ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt γ
      = (Real.pi ^ 2 / Real.sqrt 6) * (nextMontanaroUAccessCount k r : ℝ) * Real.sqrt γ := by
    rw [hT]
    push_cast
    ring
  exact hbound.trans (by linarith [h1, h2, hXY])

/-- Under the unitary, variance, depth, repetition, and payoff-distance hypotheses of
`nextMontanaro_failure_le`, setting `γ = 0` makes the complement of the error event have
probability at least `2 / 3`. -/
theorem nextMontanaro_success_le {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ) (γ : ℝ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (hk : 4 ≤ k) (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ)
    (hr : 336 ≤ r)
    (hvar : (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * ((f i : ℝ)
        - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))) ^ 2) ≤ (σ : ℝ) ^ 2)
    (hγ : γ = 0) :
    2 / 3 ≤ 1 - (nativeSignedLaw A₁ j f σ k hA₁
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))).probEvent
      (fun ξ : Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k) =>
        9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k
          < |(nativeSignedOutputMedian f σ k r ξ : ℝ)
            - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))|) := by
  have hbound := nextMontanaro_failure_le A₁ A₂ j f σ k r γ hA₁ hA₂ hk hσ hγ0 hγ1 hd hr hvar
  rw [hγ, Real.sqrt_zero] at hbound
  have hone : (nativeSignedLaw A₁ j f σ k hA₁
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))
        (fun x l => nativeLayerPrepare_unitary A₁
          (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA₁ (fun _ => le_max_left _ _))).probEvent
      (fun ξ : Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k) =>
        9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k
          < |(nativeSignedOutputMedian f σ k r ξ : ℝ)
            - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))|) ≤ 3 / 10 := by
    simpa using! hbound
  linarith

/-- Expands `nextMontanaroUAccessCount k r` to `(2 * r + 1) * (2 ^ (k + 7) * (k + 2) ^ 2 * (16 *
k + 33) + 1)`. -/
theorem nextMontanaro_resource_closed_form (k r : ℕ) :
    nextMontanaroUAccessCount k r
      = (2 * r + 1) * (2 ^ (k + 7) * (k + 2) ^ 2 * (16 * k + 33) + 1) := by
  have hsched : 2 * (k + 2) * (2 * layerRepetitions k + 1) * layerGrid k
      = 2 ^ (k + 7) * (k + 2) ^ 2 * (16 * k + 33) := by
    have h7 : 2 ^ (k + 7) = 2 ^ (k + 6) * 2 := by
      have h := Nat.pow_succ 2 (k + 6)
      rw [show (k + 6).succ = k + 7 by omega] at h
      exact h
    simp [layerGrid, layerRepetitions]
    rw [h7]
    ring
  simp [nextMontanaroUAccessCount, nextMontanaroTrialAccessCount, hsched]

/-- Rewrites the signed estimator's accuracy window `9 * σ * (1 / 2) ^ k` as `9 * σ * (2 ^ k)⁻¹`
over the reals. -/
theorem nextMontanaro_accuracy_window (σ : ℚ) (k : ℕ) :
    9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k = 9 * (σ : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  have hinv : (1 / 2 : ℝ) = ((2 : ℝ))⁻¹ := by norm_num
  rw [hinv, inv_pow]

/-- Every real `X ≥ 1` lies below some real power `2 ^ k` that is strictly less than `2 * X`. -/
theorem nextMontanaro_depth_exists (X : ℝ) (hX : 1 ≤ X) :
    ∃ k : ℕ, X ≤ 2 ^ k ∧ 2 ^ k < 2 * X := by
  have htwo : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.pow_succ]
      calc
        m + 2 = (m + 1) + 1 := by omega
        _ ≤ 2 ^ m + 1 := by omega
        _ ≤ 2 ^ m * 2 := by omega
  have hex : ∃ k : ℕ, X ≤ 2 ^ k := by
    refine ⟨Nat.ceil X, ?_⟩
    have hm : (Nat.ceil X : ℝ) ≥ X := Nat.le_ceil X
    have hceil : (1 : ℕ) ≤ Nat.ceil X := by
      have h1 : (1 : ℝ) ≤ X := hX
      have h2 : (1 : ℝ) ≤ (Nat.ceil X : ℝ) := le_trans h1 (Nat.le_ceil X)
      exact_mod_cast h2
    calc
      X ≤ (Nat.ceil X : ℝ) := Nat.le_ceil X
      _ ≤ (Nat.ceil X : ℝ) + 1 := by linarith
      _ ≤ 2 ^ Nat.ceil X := by exact_mod_cast htwo (Nat.ceil X)
  set k := Nat.find hex with hkdef
  have hk : X ≤ 2 ^ k := by
    rw [hkdef]
    exact Nat.find_spec hex
  refine ⟨k, hk, ?_⟩
  by_cases hk0 : k = 0
  · have hX1 : X ≤ 1 := by simpa [hk0] using! hk
    simp [hk0]
    linarith [hX]
  · have hmin : ¬ (X ≤ 2 ^ (k - 1)) := by
      intro hc
      exact Nat.find_min hex (by rw [hkdef]; omega) hc
    have hlt : (2 : ℝ) ^ (k - 1) < X := by
      by_contra hc
      exact hmin (le_of_not_gt hc)
    have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      have h := Nat.pow_succ 2 (k - 1)
      rw [show (k - 1).succ = k by omega] at h
      exact_mod_cast h
    rw [hpow]
    nlinarith

/-- If `2 ^ k ≤ C`, then the signed estimator's total access ledger is at most `(2 * r + 1) * (C
* 128 * (k + 2) ^ 2 * (16 * k + 33) + 1)`. -/
theorem nextMontanaro_resource_rate_nat (k r C : ℕ) (hk2 : 2 ^ k ≤ C) :
    nextMontanaroUAccessCount k r
      ≤ (2 * r + 1) * (C * 128 * (k + 2) ^ 2 * (16 * k + 33) + 1) := by
  have hclosed := nextMontanaro_resource_closed_form k r
  have h7 : 2 ^ (k + 7) ≤ C * 2 ^ 7 := by
    have h : 2 ^ (k + 7) = 2 ^ k * 2 ^ 7 := Nat.pow_add 2 k 7
    rw [h]
    exact Nat.mul_le_mul_right (2 ^ 7) hk2
  rw [hclosed]
  calc
    (2 * r + 1) * (2 ^ (k + 7) * (k + 2) ^ 2 * (16 * k + 33) + 1)
        ≤ (2 * r + 1) * (C * 2 ^ 7 * (k + 2) ^ 2 * (16 * k + 33) + 1) := by
          have hmul := Nat.mul_le_mul_right ((k + 2) ^ 2 * (16 * k + 33)) h7
          nlinarith
    _ = (2 * r + 1) * (C * 128 * (k + 2) ^ 2 * (16 * k + 33) + 1) := by
          norm_num [Nat.pow_succ]

/-- The single-trial signed-estimator law consisting of a center sample and positive and
negative layered records, with the required preparation-unitarity proofs supplied
automatically. -/
noncomputable def nextMontanaroSignedLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    FinDist (I × (LayerRecord k × LayerRecord k)) :=
  nativeSignedLaw A j f σ k hA
    (fun x l => nativeLayerPrepare_unitary A
      (fun i => max 0 ((f i - f x) / (4 * σ))) k l hA (fun _ => le_max_left _ _))
    (fun x l => nativeLayerPrepare_unitary A
      (fun i => max 0 ((f x - f i) / (4 * σ))) k l hA (fun _ => le_max_left _ _))

/-- The Born-probability expectation of payoff `f` in the state obtained by applying `A` to
basis state `j`. -/
noncomputable def nextMontanaroTargetMean {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) : ℝ :=
  ∑ i, BornProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ)

/-- The event that the median of `2 * r + 1` signed trial outputs differs from `μ` by strictly
more than `9 * σ * (1 / 2) ^ k`. -/
def nextMontanaroFailureEvent {I : Type} [Fintype I] [DecidableEq I]
    (f : I → ℚ) (σ : ℚ) (k r : ℕ) (μ : ℝ) :
    (Fin (2 * r + 1) → I × (LayerRecord k × LayerRecord k)) → Prop :=
  fun ξ => 9 * (σ : ℝ) * (1 / 2 : ℝ) ^ k
    < |(nativeSignedOutputMedian f σ k r ξ : ℝ) - μ|

/-- Under the unitary, payoff-distance, target-variance, depth, and repetition hypotheses of
`nextMontanaro_failure_le`, the named event `nextMontanaroFailureEvent` under
`nextMontanaroSignedLaw` has probability at most `3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) *
nextMontanaroUAccessCount k r * Real.sqrt γ`. -/
theorem nextMontanaro_failure_le' {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ) (γ : ℝ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (hk : 4 ≤ k) (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ)
    (hr : 336 ≤ r)
    (hvar : (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * ((f i : ℝ)
        - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))) ^ 2) ≤ (σ : ℝ) ^ 2) :
    (nextMontanaroSignedLaw A₁ j f σ k hA₁).probEvent
      (nextMontanaroFailureEvent f σ k r (nextMontanaroTargetMean A₂ j f))
      ≤ 3 / 10 + (Real.pi ^ 2 / Real.sqrt 6) * (nextMontanaroUAccessCount k r : ℝ)
          * Real.sqrt γ := by
  exact nextMontanaro_failure_le A₁ A₂ j f σ k r γ hA₁ hA₂ hk hσ hγ0 hγ1 hd hr hvar

/-- Under the hypotheses of `nextMontanaro_success_le`, including `γ = 0`, the complement of
`nextMontanaroFailureEvent` under `nextMontanaroSignedLaw` has probability at least `2 / 3`. -/
theorem nextMontanaro_success_le' {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) (σ : ℚ) (k r : ℕ) (γ : ℝ)
    (hA₁ : A₁ ∈ Matrix.unitaryGroup I ℂ) (hA₂ : A₂ ∈ Matrix.unitaryGroup I ℂ)
    (hk : 4 ≤ k) (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hd : payoffValueL1Dist A₁ A₂ j f ≤ 2 * γ)
    (hr : 336 ≤ r)
    (hvar : (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * ((f i : ℝ)
        - (∑ i, BornProb (ApplyGate A₂ (Qatlib.Foundations.PureStateMath.Ket j)) i * (f i : ℝ))) ^ 2) ≤ (σ : ℝ) ^ 2)
    (hγ : γ = 0) :
    2 / 3 ≤ 1 - (nextMontanaroSignedLaw A₁ j f σ k hA₁).probEvent
      (nextMontanaroFailureEvent f σ k r (nextMontanaroTargetMean A₂ j f)) := by
  exact nextMontanaro_success_le A₁ A₂ j f σ k r γ hA₁ hA₂ hk hσ hγ0 hγ1 hd hr hvar hγ

/-- The payoff-value L1 distance between a preparation matrix and itself is zero. -/
theorem nextMontanaro_value_dist_self {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℚ) :
    payoffValueL1Dist A A j f = 0 := by
  unfold payoffValueL1Dist
  apply Finset.sum_eq_zero
  intro v _
  simp

/-- Defines the even final counting grid as twice the natural ceiling of `5 * Real.pi * M`. -/
noncomputable def nextApproxCountFinalGridEven (M : ℕ) : ℕ :=
  2 * Nat.ceil (5 * Real.pi * (M : ℝ))

/-- The even final counting grid is at least `10 * Real.pi * M` after coercion to the reals. -/
theorem nextApproxCountFinalGridEven_ge (M : ℕ) :
    10 * Real.pi * (M : ℝ) ≤ (nextApproxCountFinalGridEven M : ℝ) := by
  have hceil : 5 * Real.pi * (M : ℝ) ≤ (Nat.ceil (5 * Real.pi * (M : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hcast : ((2 * Nat.ceil (5 * Real.pi * (M : ℝ)) : ℕ) : ℝ)
      = 2 * (Nat.ceil (5 * Real.pi * (M : ℝ)) : ℝ) := by
    push_cast
    ring
  rw [nextApproxCountFinalGridEven, hcast]
  linarith

/-- The original final counting grid is no larger than the even final counting grid. -/
theorem nextApproxCountFinalGrid_le_even (M : ℕ) :
    (nextApproxCountFinalGrid M : ℝ) ≤ (nextApproxCountFinalGridEven M : ℝ) := by
  have hceil : 5 * Real.pi * (M : ℝ) ≤ (Nat.ceil (5 * Real.pi * (M : ℝ)) : ℝ) :=
    Nat.le_ceil _
  have hcast : ((2 * Nat.ceil (5 * Real.pi * (M : ℝ)) : ℕ) : ℝ)
      = 2 * (Nat.ceil (5 * Real.pi * (M : ℝ)) : ℝ) := by
    push_cast
    ring
  have htwo : 10 * Real.pi * (M : ℝ) ≤ 2 * (Nat.ceil (5 * Real.pi * (M : ℝ)) : ℝ) := by
    linarith
  have hnat : Nat.ceil (10 * Real.pi * (M : ℝ))
      ≤ 2 * Nat.ceil (5 * Real.pi * (M : ℝ)) := by
    rw [Nat.ceil_le]
    linarith [htwo, hcast]
  rw [nextApproxCountFinalGrid, nextApproxCountFinalGridEven, hcast]
  exact_mod_cast hnat

/-- The real value of `nextApproxCountFinalGrid M` is positive whenever `M` is at least one. -/
theorem nextApproxCountFinalGrid_pos {M : ℕ} (hM : 1 ≤ M) :
    0 < (nextApproxCountFinalGrid M : ℝ) := by
  unfold nextApproxCountFinalGrid
  have h : 0 < Nat.ceil (10 * Real.pi * (M : ℝ)) := by
    apply (Nat.ceil_pos).2
    have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    nlinarith [Real.pi_pos]
  exact_mod_cast h

/-- The grid `nextApproxCountFinalGridEven M` is divisible by two. -/
theorem nextApproxCountFinalGridEven_even (M : ℕ) : 2 ∣ nextApproxCountFinalGridEven M := by
  refine ⟨Nat.ceil (5 * Real.pi * (M : ℝ)), ?_⟩
  simp [nextApproxCountFinalGridEven]

/-- The even final counting grid is at least two whenever its input `M` is at least one. -/
theorem nextApproxCountFinalGridEven_two {M : ℕ} (hM : 1 ≤ M) :
    2 ≤ nextApproxCountFinalGridEven M := by
  have hpos : (0 : ℝ) < 5 * Real.pi * (M : ℝ) := by positivity
  have hceil : 0 < Nat.ceil (5 * Real.pi * (M : ℝ)) := (Nat.ceil_pos).2 hpos
  unfold nextApproxCountFinalGridEven
  omega

/-- Builds the final counting grid by applying `nextApproxCountFinalGridEven` to the minimum of
`nextApproxCountM1` and `M₂`. -/
noncomputable def nextApproxCountUnifiedGrid (ε : ℝ) (L₁ L₂ M₂ : ℕ) : ℕ :=
  nextApproxCountFinalGridEven (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂)

/-- For a nonempty domain and a grid of size at least two, the QFT-prepared amplitude-estimation
law assigns mass at least `8 / Real.pi ^ 2` to labels whose scaled estimate lies within
`nextCor4Window M 1 N S.card` of the marked count. -/
theorem nextCountingWindow_mass {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (M : ℕ) (hM : 2 ≤ M) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          |(N : ℝ) * aeEstimate M z - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha : (S.card : ℝ) / (N : ℝ)
      = MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S := by
    rw [prepared_qft_mark_mass N hN S]
  have hbhmt := (prepared_ae_bhmt_error_and_endpoints M hM (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
    (qftMatrix_unitary hN)).1
  rw [← ha] at hbhmt

  have hsqrtid : (N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
      (1 - (S.card : ℝ) / (N : ℝ))) = Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ))) := by
    have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hle : (S.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show S.card ≤ N by simpa using! S.card_le_univ)
    have hnonnegA : (0 : ℝ) ≤ ((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)) := by
      have hfrac : (0 : ℝ) ≤ (S.card : ℝ) / (N : ℝ) := div_nonneg hcard (le_of_lt hN')
      have hone : (0 : ℝ) ≤ 1 - (S.card : ℝ) / (N : ℝ) := by
        have hdiv : (S.card : ℝ) / (N : ℝ) ≤ 1 := by
          rw [div_le_one hN']
          exact hle
        linarith
      exact mul_nonneg hfrac hone
    have he : (N : ℝ) ^ 2 * (((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)))
        = (S.card : ℝ) * ((N : ℝ) - (S.card : ℝ)) := by field_simp [hN'.ne']
    calc (N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)))
        = Real.sqrt ((N : ℝ) ^ 2 *
            (((S.card : ℝ) / (N : ℝ)) * (1 - (S.card : ℝ) / (N : ℝ)))) := by
          rw [Real.sqrt_mul (sq_nonneg (N : ℝ))]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      _ = Real.sqrt ((S.card : ℝ) * ((N : ℝ) - (S.card : ℝ))) := by rw [he]
  have hmain : ∀ y : Fin M,
      |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ)) →
      |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ) := by
    intro y hy
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    have hid : (N : ℝ) * aeEstimate M y - (S.card : ℝ)
        = (N : ℝ) * (aeEstimate M y - (S.card : ℝ) / (N : ℝ)) := by
      field_simp [hN'.ne']
    have hmulW : (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ))
        = nextCor4Window M 1 N (S.card : ℝ) := by
      unfold nextAeWindow nextCor4Window
      have hspread : (N : ℝ) * (2 * Real.pi * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ))) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2)
        = 2 * Real.pi * ((N : ℝ) * Real.sqrt (((S.card : ℝ) / (N : ℝ)) *
          (1 - (S.card : ℝ) / (N : ℝ)))) / (M : ℝ) + Real.pi ^ 2 * (N : ℝ) / (M : ℝ) ^ 2 := by
        ring
      rw [hspread, hsqrtid]
      ring
    have h1 : (N : ℝ) * |aeEstimate M y - (S.card : ℝ) / (N : ℝ)|
        ≤ (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hy hN0
    calc |(N : ℝ) * aeEstimate M y - (S.card : ℝ)|
        = (N : ℝ) * |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| := by
          rw [hid, abs_mul, abs_of_nonneg hN0]
      _ ≤ (N : ℝ) * nextAeWindow M ((S.card : ℝ) / (N : ℝ)) := h1
      _ = nextCor4Window M 1 N (S.card : ℝ) := hmulW
  have hsub1 : Finset.univ.filter (fun y : Fin M =>
      |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ)))
      ⊆ Finset.univ.filter (fun y : Fin M =>
        |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hmain y hy
  have hmono1 := Finset.sum_le_sum_of_subset_of_nonneg hsub1
    (fun y _ _ => (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).nonneg y)
  calc 8 / Real.pi ^ 2
      ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          |aeEstimate M y - (S.card : ℝ) / (N : ℝ)| ≤ nextAeWindow M ((S.card : ℝ) / (N : ℝ))),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y := hbhmt
    _ ≤ ∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          |(N : ℝ) * aeEstimate M y - (S.card : ℝ)| ≤ nextCor4Window M 1 N (S.card : ℝ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y := hmono1

/-- When every input is marked and the grid is even and at least two, the QFT-prepared counting
law returns `N` through `exactCountOutput` with probability one. This is the full-marked
endpoint used in approximate counting in [Brassard et al., Theorem 18][BrassardEtAl2002]. -/
theorem nextApproxCount_final_one {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (M : ℕ) (hM : 2 ≤ M) (hdiv : 2 ∣ M) (hcard : S.card = N) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = (N : ℤ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) = 1 := by
  have ha : MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S = 1 := by
    rw [prepared_qft_mark_mass N hN S, hcard]
    field_simp
  have hfreezeAll := (prepared_ae_bhmt_error_and_endpoints M hM (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
    (qftMatrix_unitary hN))
  (try dsimp only at hfreezeAll)
  have hone : (∑ z ∈ Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z) = 1 := by
    exact hfreezeAll.2.2 ha hdiv

  have hsub : Finset.univ.filter (fun z : Fin M => aeEstimate M z = 1)
      ⊆ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = (N : ℤ)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    unfold exactCountOutput
    have h1 : (N : ℝ) * aeEstimate M z = (N : ℝ) := by rw [hz]; ring
    rw [h1]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hnonneg : ∀ i : Fin M, 0 ≤ (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).prob i := fun i =>
    (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).nonneg i

  have hmono : (∑ y ∈ Finset.univ.filter (fun y : Fin M => aeEstimate M y = 1),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y)
      ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = (N : ℤ)),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)

  have hle : (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        exactCountOutput N y = (N : ℤ)),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) ≤ 1 := by
    have h1 := (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).sum_one
    have hsub' : Finset.univ.filter (fun y : Fin M =>
        exactCountOutput N y = (N : ℤ)) ⊆ Finset.univ := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact Finset.mem_univ y
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun i _ _ => hnonneg i)
    rw [h1] at h2
    exact h2
  have hge : (1 : ℝ) ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        exactCountOutput N y = (N : ℤ)),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) :=
    le_trans (le_of_eq hone.symm) hmono
  exact le_antisymm hle hge

/-- When no input is marked and the grid is at least two, the QFT-prepared counting law returns
zero through `exactCountOutput` with probability one. This is the empty-set endpoint used in
approximate counting in [Brassard et al., Theorem 18][BrassardEtAl2002]. -/
theorem nextApproxCount_final_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (M : ℕ) (hM : 2 ≤ M) (hcard : S.card = 0) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) = 1 := by
  have ha : MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S = 0 := by
    rw [prepared_qft_mark_mass N hN S, hcard]
    simp
  have hfreezeAll := (prepared_ae_bhmt_error_and_endpoints M hM (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
    (qftMatrix_unitary hN))
  (try dsimp only at hfreezeAll)

  have hfreeze' : (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).prob (⟨0, by omega⟩ : Fin M) = 1 := by
    exact hfreezeAll.2.1 ha

  have hz0 : exactCountOutput N (⟨0, by omega⟩ : Fin M) = 0 := by
    unfold exactCountOutput
    have hrec : aeEstimate M (⟨0, by omega⟩ : Fin M) = 0 := by
      have hzval : (⟨0, by omega⟩ : Fin M).val = 0 := rfl
      unfold aeEstimate
      rw [hzval]
      simp [Real.sin_zero]
    rw [hrec]
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hnonneg : ∀ i : Fin M, 0 ≤ (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).prob i := fun i =>
    (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).nonneg i
  have hsub : insert (⟨0, by omega⟩ : Fin M) (∅ : Finset (Fin M))
      ⊆ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0) := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with hz | hz
    · subst z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz0
    · exact absurd hz (by simp)
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
  have hmono' : (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).prob (⟨0, by omega⟩ : Fin M)
      ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) := by
    simpa using! hmono
  have hle : (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) ≤ 1 := by
    have h1 := (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN) hM).sum_one
    have hsub' : Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0)
        ⊆ Finset.univ := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact Finset.mem_univ y
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun i _ _ => hnonneg i)
    rw [h1] at h2
    exact h2
  have hge : (1 : ℝ) ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) := by
    calc (1 : ℝ)
        ≤ (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob
            (⟨0, by omega⟩ : Fin M) := le_of_eq hfreeze'.symm
      _ ≤ (∑ y ∈ Finset.univ.filter (fun y : Fin M => exactCountOutput N y = 0),
        (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob y) := hmono'
  exact le_antisymm hle hge

/-- If `ε * S.card` is at least one and the unrounded scaled estimate has error at most one
third of that tolerance, `exactCountOutput` has error at most `ε * S.card`. -/
theorem nextApproxCount_output_accuracy {N : ℕ} (S : Finset (Fin N)) {M : ℕ}
    (ε : ℝ) (hεt : 1 ≤ ε * (S.card : ℝ)) {z : Fin M}
    (hz : |(N : ℝ) * aeEstimate M z - (S.card : ℝ)| ≤ ε * (S.card : ℝ) / 3) :
    |((exactCountOutput N z : ℝ)) - (S.card : ℝ)| ≤ ε * (S.card : ℝ) := by
  have hfloor : |((exactCountOutput N z : ℝ)) - (N : ℝ) * aeEstimate M z| ≤ 1 / 2 := by
    unfold exactCountOutput
    have hfl : Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2)
        ≤ (N : ℝ) * aeEstimate M z + 1 / 2 := Int.floor_le _
    have hfl2 : (N : ℝ) * aeEstimate M z + 1 / 2
        < Int.floor ((N : ℝ) * aeEstimate M z + 1 / 2) + 1 := Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have h1 := abs_le.mp hfloor
  have h2 := abs_le.mp hz
  rw [abs_le]
  constructor <;> linarith

/-- Given positive square-root witnesses for `ε`, `t`, `N - t`, and `N` and the stated lower
bound on `m`, bounds the two-term counting error at `nextApproxCountFinalGridEven m` by `ε *
t / 3`. -/
theorem nextApproxCount_even_window_le {ε t N : ℝ} {m : ℕ} {se sN st sc : ℝ}
    (hse : se ^ 2 = ε) (hse0 : 0 < se)
    (hst : st ^ 2 = t) (hst0 : 0 < st)
    (hsc : sc ^ 2 = (N : ℝ) - t) (hsc0 : 0 < sc)
    (hsN : sN ^ 2 = (N : ℝ)) (hsN0 : 0 < sN)
    (hM : (1 / se) * (18 / 5) * (sN / st) * (1 + (1 / 6) * (sc / (se * sN))) ≤ (m : ℝ)) :
    2 * Real.pi * (st * sc) / (nextApproxCountFinalGridEven m : ℝ)
      + Real.pi ^ 2 * (N : ℝ) / (nextApproxCountFinalGridEven m : ℝ) ^ 2 ≤ ε * t / 3 := by
  refine nextApproxCount_window_le hse hse0 hst hst0 hsc hsc0 hsN hsN0 hM ?_
  exact nextApproxCountFinalGridEven_ge m

/-- Restates the even-grid counting-window bound: the positive square-root witnesses and lower
bound on `m` imply an error window of at most `ε * t / 3` at `nextApproxCountFinalGridEven
m`. -/
theorem nextApproxCount_unified_window_le {ε t N : ℝ} {m : ℕ} {se sN st sc : ℝ}
    (hse : se ^ 2 = ε) (hse0 : 0 < se)
    (hst : st ^ 2 = t) (hst0 : 0 < st)
    (hsc : sc ^ 2 = (N : ℝ) - t) (hsc0 : 0 < sc)
    (hsN : sN ^ 2 = (N : ℝ)) (hsN0 : 0 < sN)
    (hM : (1 / se) * (18 / 5) * (sN / st) * (1 + (1 / 6) * (sc / (se * sN))) ≤ (m : ℝ)) :
    2 * Real.pi * (st * sc) / (nextApproxCountFinalGridEven m : ℝ)
      + Real.pi ^ 2 * (N : ℝ) / (nextApproxCountFinalGridEven m : ℝ) ^ 2 ≤ ε * t / 3 :=
  nextApproxCount_even_window_le hse hse0 hst hst0 hsc hsc0 hsN hsN0 hM

/-- The candidate grid parameter `nextApproxCountM1 ε L₁ L₂` is at least one when `ε` and `L₁`
are positive. -/
theorem nextApproxCountM1_one {ε : ℝ} (hε : 0 < ε) {L₁ L₂ : ℕ} (hL1 : 0 < (L₁ : ℝ)) :
    1 ≤ nextApproxCountM1 ε L₁ L₂ := by
  have hpos : (0 : ℝ) < (1 / Real.sqrt ε) * (L₁ : ℝ) * (1 + (L₂ : ℝ)) := by positivity
  have hceil : 0 < Nat.ceil ((1 / Real.sqrt ε) * (L₁ : ℝ) * (1 + (L₂ : ℝ))) :=
    (Nat.ceil_pos).2 hpos
  unfold nextApproxCountM1
  omega

/-- For a positive tolerance, a count between one and `N / 2`, and a coarse estimate between `t
/ 2` and `3 * t / 2`, the stated lower bounds on `L₁`, `L₂`, and `M₂` make the unified
counting window either at most `ε * t / 3` or strictly below one half. -/
theorem nextApproxCountM_adequate_even {ε t : ℝ} {N : ℕ} {L₁ L₂ M₂ : ℕ} {v : ℝ}
    (hε : 0 < ε) (hN : 0 < N) (ht : 0 < t) (ht1 : 1 ≤ t) (htN : t ≤ (N : ℝ) / 2)
    (hL1 : (18 / 5) * Real.sqrt ((N : ℝ) / t) ≤ (L₁ : ℝ))
    (hL2 : (1 / 6) * Real.sqrt (((N : ℝ) - t) / (ε * (N : ℝ))) ≤ (L₂ : ℝ))
    (hv1 : t / 2 ≤ v) (hv2 : v ≤ 3 * t / 2)
    (hM₂ : 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) ≤ (M₂ : ℝ)) :
    nextCor4Window
        (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) 1 N t ≤ ε * t / 3 ∨
      nextCor4Window
        (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) 1 N t < 1 / 2 := by
  have hbase := nextApproxCountM_adequate hε hN ht ht1 htN hL1 hL2 hv1 hv2 hM₂
  have hle : (nextApproxCountFinalGrid
        (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂) : ℝ)
      ≤ (nextApproxCountUnifiedGrid ε L₁ L₂ M₂ : ℝ) := by
    unfold nextApproxCountUnifiedGrid
    exact nextApproxCountFinalGrid_le_even _
  have hM1 : 1 ≤ nextApproxCountM1 ε L₁ L₂ := by
    refine nextApproxCountM1_one hε ?_
    have hsqrt : (0 : ℝ) < Real.sqrt ((N : ℝ) / t) := by
      apply Real.sqrt_pos.2
      apply div_pos
      · exact_mod_cast hN
      · exact_mod_cast ht
    linarith
  have hM2pos : 0 < M₂ := by
    have hpos : (0 : ℝ) < 48 * Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) := by
      have hmul : (0 : ℝ) < (v + 1) * ((N : ℝ) - v + 1) :=
        mul_pos (by linarith) (by linarith)
      have hsqrt : (0 : ℝ) < Real.sqrt ((v + 1) * ((N : ℝ) - v + 1)) :=
        Real.sqrt_pos.2 hmul
      exact mul_pos (by norm_num) hsqrt
    have hlt : (0 : ℝ) < (M₂ : ℝ) := lt_of_lt_of_le hpos hM₂
    exact_mod_cast hlt
  have hM2 : 1 ≤ M₂ := by omega
  have hmin : 1 ≤ nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂ := by
    unfold nextApproxCountM
    omega
  have hpos : 0 < (nextApproxCountFinalGrid
        (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂) : ℝ) :=
    nextApproxCountFinalGrid_pos hmin
  have hgt : (0 : ℝ) ≤ t := by linarith
  have hmono := nextCor4Window_mono_grid (M := nextApproxCountFinalGrid
      (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂))
    (M' := nextApproxCountUnifiedGrid ε L₁ L₂ M₂) (k := 1) (N := N) (t := t)
    hle hpos hgt (by linarith)
  exact hbase.elim (fun h => Or.inl (hmono.trans h)) (fun h => Or.inr (hmono.trans_lt h))

/-- The rounded count `exactCountOutput N y` differs from the scaled amplitude estimate `N *
aeEstimate M y` by at most one half. -/
theorem nextApproxCount_output_round {N : ℕ} {M : ℕ} {y : Fin M} :
    |((exactCountOutput N y : ℝ)) - (N : ℝ) * aeEstimate M y| ≤ 1 / 2 := by
  unfold exactCountOutput
  have hfl : Int.floor ((N : ℝ) * aeEstimate M y + 1 / 2)
      ≤ (N : ℝ) * aeEstimate M y + 1 / 2 := Int.floor_le _
  have hfl2 : (N : ℝ) * aeEstimate M y + 1 / 2
      < Int.floor ((N : ℝ) * aeEstimate M y + 1 / 2) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- The unified counting grid has size at least two when `ε`, `L₁`, and `M₂` are positive. -/
theorem nextApproxCountUnifiedGrid_two {ε : ℝ} (hε : 0 < ε) {L₁ L₂ M₂ : ℕ}
    (hL1 : 0 < (L₁ : ℝ)) (hM₂ : 0 < (M₂ : ℝ)) :
    2 ≤ nextApproxCountUnifiedGrid ε L₁ L₂ M₂ := by
  have hM1 : 1 ≤ nextApproxCountM1 ε L₁ L₂ := nextApproxCountM1_one hε hL1
  have hM2 : 1 ≤ M₂ := by
    have hpos : 0 < M₂ := by
      have : (0 : ℝ) < (M₂ : ℝ) := hM₂
      exact_mod_cast this
    omega
  have hmin : 1 ≤ nextApproxCountM (nextApproxCountM1 ε L₁ L₂) M₂ := by
    unfold nextApproxCountM
    omega
  exact nextApproxCountFinalGridEven_two hmin

/-- For positive tolerance and positive grid inputs, packages the unified grid's counting-window
mass bound, probability-one empty and full endpoints, and rounding error bound. It also
transfers unrounded error at most `ε * S.card / 3` to rounded error at most `ε * S.card`
when that tolerance is at least one. -/
theorem nextApproxCount_final_layer {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε) (L₁ L₂ M₂ : ℕ) (hL1 : 0 < (L₁ : ℝ)) (hM₂ : 0 < (M₂ : ℝ)) :
    (8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) =>
          |(N : ℝ) * aeEstimate (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) z
              - (S.card : ℝ)| ≤
            nextCor4Window (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) 1 N (S.card : ℝ)),
        (aeLaw (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN)
          (nextApproxCountUnifiedGrid_two hε hL1 hM₂)).prob z) ∧
    (S.card = N →
      (∑ y ∈ Finset.univ.filter (fun y : Fin (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) =>
          exactCountOutput N y = (N : ℤ)),
        (aeLaw (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN)
          (nextApproxCountUnifiedGrid_two hε hL1 hM₂)).prob y) = 1) ∧
    (S.card = 0 →
      (∑ y ∈ Finset.univ.filter (fun y : Fin (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) =>
          exactCountOutput N y = 0),
        (aeLaw (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN)
          (nextApproxCountUnifiedGrid_two hε hL1 hM₂)).prob y) = 1) ∧
    (∀ y : Fin (nextApproxCountUnifiedGrid ε L₁ L₂ M₂),
      |((exactCountOutput N y : ℝ))
          - (N : ℝ) * aeEstimate (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) y| ≤ 1 / 2) ∧
    (1 ≤ ε * (S.card : ℝ) →
      ∀ y : Fin (nextApproxCountUnifiedGrid ε L₁ L₂ M₂),
        |(N : ℝ) * aeEstimate (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) y
            - (S.card : ℝ)| ≤ ε * (S.card : ℝ) / 3 →
        |((exactCountOutput N y : ℝ)) - (S.card : ℝ)| ≤ ε * (S.card : ℝ)) := by
  have hM : 2 ≤ nextApproxCountUnifiedGrid ε L₁ L₂ M₂ :=
    nextApproxCountUnifiedGrid_two hε hL1 hM₂
  have hdiv : 2 ∣ nextApproxCountUnifiedGrid ε L₁ L₂ M₂ :=
    nextApproxCountFinalGridEven_even _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact nextCountingWindow_mass hN S (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) hM
  · intro hcard
    exact nextApproxCount_final_one hN S (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) hM hdiv hcard
  · intro hcard
    exact nextApproxCount_final_zero hN S (nextApproxCountUnifiedGrid ε L₁ L₂ M₂) hM hcard
  · intro y
    exact nextApproxCount_output_round
  · intro hεt y hy
    exact nextApproxCount_output_accuracy S ε hεt hy

/-- Forms the rational phase input `piRatApprox (k + 8) * z.val / M` for the native amplitude
decoder. -/
def nextNativeInput (M k : ℕ) (z : Fin M) : ℚ :=
  piRatApprox (k + 8) * z.val / M

/-- Runs `nativeAESinCounted` on `nextNativeInput M k z`, returning the rational sine
approximation together with its term count. -/
def nextNativePhaseInversion (M k : ℕ) (z : Fin M) : ℚ × ℕ :=
  nativeAESinCounted (nextNativeInput M k z) k

/-- The value returned by `nextNativePhaseInversion` equals `nativeAESin` evaluated on the same
native phase input. -/
theorem nextNativePhaseInversion_value (M k : ℕ) (z : Fin M) :
    (nextNativePhaseInversion M k z).1 = nativeAESin (nextNativeInput M k z) k := by
  have h := congrArg Prod.fst (nativeAESin_value_and_terms (nextNativeInput M k z) k)
  simpa [nextNativePhaseInversion] using! h

/-- The native phase-inversion computation records exactly `8 * (k + 8)` sine-series terms. -/
theorem nextNativePhaseInversion_terms (M k : ℕ) (z : Fin M) :
    (nextNativePhaseInversion M k z).2 = 8 * (k + 8) := by
  have h := congrArg Prod.snd (nativeAESin_value_and_terms (nextNativeInput M k z) k)
  simpa [nextNativePhaseInversion] using! h

/-- Expresses the real value of the native sine approximation as the alternating sine Taylor sum
with `8 * (k + 8)` terms at `nextNativeInput M k z`. -/
theorem nextNative_phaseInversion_term_structure (M k : ℕ) (z : Fin M) :
    (nativeAESin (nextNativeInput M k z) k : ℝ) =
      ∑ j ∈ Finset.range (8 * (k + 8)),
        (-1 : ℝ) ^ j * (nextNativeInput M k z : ℝ) ^ (2 * j + 1) /
          ((2 * j + 1).factorial : ℝ) :=
  nativeAESin_cast (nextNativeInput M k z) k

/-- Squares the rational value produced by `nextNativePhaseInversion` and clamps the result to
the interval from zero to one. -/
def nextNativeOutput (M k : ℕ) (z : Fin M) : ℚ :=
  let p := (nextNativePhaseInversion M k z).1
  max 0 (min 1 (p ^ 2))

/-- The refined native output agrees exactly with the established decoder `nativeAEDecode`. -/
theorem nextNativeOutput_eq_frozen (M k : ℕ) (z : Fin M) :
    nextNativeOutput M k z = nativeAEDecode M k z := by
  have h := nextNativePhaseInversion_value M k z
  unfold nextNativeOutput nativeAEDecode
  rw [h]
  rfl

/-- The rational native output lies between zero and one and differs from `aeEstimate M z` by at
most `((2 : ℝ)⁻¹) ^ k`. -/
theorem nextNativeOutput_precision (M k : ℕ) (z : Fin M) :
    0 ≤ nextNativeOutput M k z ∧ nextNativeOutput M k z ≤ 1 ∧
      |(nextNativeOutput M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k := by
  have h := native_ae_computed_scalar_precision M k z
  rw [← nextNativeOutput_eq_frozen] at h
  exact h

/-- Selects the native counting layer using `nextCor4Grid N t'₁ t'₂`. -/
noncomputable def nextNativeLayerSelect (N : ℕ) (t'₁ t'₂ : ℝ) : ℕ :=
  nextCor4Grid N t'₁ t'₂

/-- The native layer selector agrees with `nextCor4Grid` on every input. -/
theorem nextNativeLayerSelect_eq (N : ℕ) (t'₁ t'₂ : ℝ) :
    nextNativeLayerSelect N t'₁ t'₂ = nextCor4Grid N t'₁ t'₂ := rfl

/-- If both preliminary count estimates lie between zero and `N`, the native layer selector
returns a grid of size at least two. -/
theorem nextNativeLayerSelect_legal {N : ℕ} {t'₁ t'₂ : ℝ}
    (h1 : 0 ≤ t'₁) (h1' : t'₁ ≤ (N : ℝ)) (h2 : 0 ≤ t'₂) (h2' : t'₂ ≤ (N : ℝ)) :
    2 ≤ nextNativeLayerSelect N t'₁ t'₂ :=
  nextCor4_grid_two h1 h1' h2 h2'

/-- For `N = 8`, the native layer selector returns `144` on estimates `(0, 0)` and `240` on
estimates `(4, 4)`. -/
theorem nextNativeLayerSelect_result_dependent :
    nextNativeLayerSelect 8 0 0 = 144 ∧ nextNativeLayerSelect 8 4 4 = 240 := by
  constructor
  · have hmin : min (0 : ℝ) 0 = 0 := min_self 0
    have hsqrt : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have hsq : ((0 + 1 : ℝ) * (((8 : ℕ) : ℝ) - 0 + 1)) = 9 := by norm_num
    have hval : (48 * 3 : ℝ) = (144 : ℤ) := by norm_num
    unfold nextNativeLayerSelect nextCor4Grid
    rw [hmin, hsq, hsqrt, hval, Nat.ceil_intCast]
    simp
  · have hmin : min (4 : ℝ) 4 = 4 := min_self 4
    have hsqrt : Real.sqrt 25 = 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have hsq : ((4 + 1 : ℝ) * (((8 : ℕ) : ℝ) - 4 + 1)) = 25 := by norm_num
    have hval : (48 * 5 : ℝ) = (240 : ℤ) := by norm_num
    unfold nextNativeLayerSelect nextCor4Grid
    rw [hmin, hsq, hsqrt, hval, Nat.ceil_intCast]
    simp

/-- Defines the amplitude-estimation input error as `2 * Real.pi * Real.sqrt (a * (1 - a)) / M +
Real.pi ^ 2 / M ^ 2`. -/
noncomputable def nextNativeInputError (M : ℕ) (a : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2

/-- Defines the native decoder error allowance as `((2 : ℝ)⁻¹) ^ k`. -/
noncomputable def nextNativeDecoderError (k : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ k

/-- Expands the sum of `nextNativeInputError` and `nextNativeDecoderError` into its
amplitude-estimation and finite-precision terms. -/
theorem nextNative_error_split (M : ℕ) (k : ℕ) (a : ℝ) :
    nextNativeInputError M a + nextNativeDecoderError k =
      2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
        Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k := by
  simp [nextNativeInputError, nextNativeDecoderError]

/-- Under the QFT-prepared amplitude-estimation law, the same measured label yields a native
scaled output within `N` times the sum of the amplitude-estimation window and decoder error
of `N * a` with mass at least `8 / Real.pi ^ 2`, where `a` is the prepared marked
probability. -/
theorem nextNative_same_record_success {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (S : Finset (Fin N)) :
    let a := MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |((N : ℚ) * nextNativeOutput M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) *
        (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
          Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k)),
      (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z) ≥ 8 / Real.pi ^ 2 := by
  (try dsimp only)
  have h := native_ae_counting_relative_output_consumer (Fin N) M k N hM
    (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN)
  simpa only [nextNativeOutput_eq_frozen] using! h.1

/-- For a unitary preparation and a grid of size at least two, records `M` forward accesses, `M
- 1` backward accesses and queries, and `5 * (M - 1) + 3` circuit gates. The native
phase-inversion term count is `8 * (k + 8)`. -/
theorem nextNative_access_ledger (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (z : Fin M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    aeForwardAccesses (aeAccessWord (I := I) M) = M ∧
    aeBackwardAccesses (aeAccessWord (I := I) M) = M - 1 ∧
    QueryCount (countedAECircuit M A j) = M - 1 ∧
    GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
    (nextNativePhaseInversion M k z).2 = 8 * (k + 8) := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ :=
    nextRelative_access_counts M hM A j S hA
  exact ⟨h1, h2, h3, h4, nextNativePhaseInversion_terms M k z⟩

/-- Recursively accumulates the first `L` rational terms of the alternating arctangent series
and counts one term at each step. -/
def nextNativeAtanCounted (x : ℚ) : ℕ → ℚ × ℕ
  | 0 => (0, 0)
  | L + 1 =>
      ((nextNativeAtanCounted x L).1 + (-1 : ℚ) ^ L * x ^ (2 * L + 1) / (2 * L + 1),
        (nextNativeAtanCounted x L).2 + 1)

/-- The value component of `nextNativeAtanCounted x L` equals `atanRatSeries x L`. -/
theorem nextNativeAtanCounted_value (x : ℚ) (L : ℕ) :
    (nextNativeAtanCounted x L).1 = atanRatSeries x L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      show (nextNativeAtanCounted x (L + 1)).1 = atanRatSeries x (L + 1)
      rw [nextNativeAtanCounted, atanRatSeries]
      rw [ih]

/-- The term-count component of `nextNativeAtanCounted x L` is exactly `L`. -/
theorem nextNativeAtanCounted_terms (x : ℚ) (L : ℕ) :
    (nextNativeAtanCounted x L).2 = L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      show (nextNativeAtanCounted x (L + 1)).2 = L + 1
      rw [nextNativeAtanCounted]
      rw [ih]

/-- Combines the counted arctangent sums at `1 / 5` and `1 / 239` with coefficients `16` and
`-4`, using `k + 3` terms in each sum and adding their term counts. -/
def nextNativePiCounted (k : ℕ) : ℚ × ℕ :=
  ((nextNativeAtanCounted ((1 / 5 : ℚ)) (k + 3)).1 * 16 -
      (nextNativeAtanCounted ((1 / 239 : ℚ)) (k + 3)).1 * 4,
    (nextNativeAtanCounted ((1 / 5 : ℚ)) (k + 3)).2 +
      (nextNativeAtanCounted ((1 / 239 : ℚ)) (k + 3)).2)

/-- The value component of the counted pi computation is `piRatApprox k`. -/
theorem nextNativePiCounted_value (k : ℕ) :
    (nextNativePiCounted k).1 = piRatApprox k := by
  unfold nextNativePiCounted piRatApprox
  rw [nextNativeAtanCounted_value, nextNativeAtanCounted_value]
  ring

/-- The counted pi computation uses exactly `2 * (k + 3)` arctangent-series terms. -/
theorem nextNativePiCounted_terms (k : ℕ) :
    (nextNativePiCounted k).2 = 2 * (k + 3) := by
  unfold nextNativePiCounted
  rw [nextNativeAtanCounted_terms, nextNativeAtanCounted_terms]
  omega

/-- Defines the native GCD-operation ledger as the term count of `nextNativePiCounted (k + 8)`,
plus one and the `8 * (k + 8)` sine-series terms. -/
def nextNativeGcdCount (k : ℕ) : ℕ :=
  (nextNativePiCounted (k + 8)).2 + 1 + 8 * (k + 8)

/-- Expands the native GCD-operation ledger to `2 * (k + 11) + 1 + 8 * (k + 8)`. -/
theorem nextNativeGcdCount_eq (k : ℕ) :
    nextNativeGcdCount k = 2 * (k + 11) + 1 + 8 * (k + 8) := by
  rw [nextNativeGcdCount, nextNativePiCounted_terms]

/-- Sets the native decoder's persistent cell budget to two. -/
def nextNativePersistentCells : ℕ := 2

/-- Sets the native decoder's peak cell budget to one more than `nextNativePersistentCells`. -/
def nextNativePeakCells : ℕ := nextNativePersistentCells + 1

/-- The native persistent cell budget is no larger than its peak cell budget. -/
theorem nextNativePersistent_le_peak :
    nextNativePersistentCells ≤ nextNativePeakCells := by
  unfold nextNativePeakCells
  omega

/-- Defines the native classical macro count as three times each of the sine-series and
pi-series term counts, totaling `3 * (8 * (k + 8)) + 3 * (2 * (k + 11))`. -/
noncomputable def nextNativeClassicalMacros (k : ℕ) : ℕ :=
  3 * (8 * (k + 8)) + 3 * (2 * (k + 11))

/-- For a unitary preparation and a grid of size at least two, gives the amplitude-estimation
circuit gate count `5 * (M - 1) + 3` together with the explicit native classical macro
count. -/
theorem nextNativeGateLedger (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
      nextNativeClassicalMacros k = 3 * (8 * (k + 8)) + 3 * (2 * (k + 11)) := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ :=
    nextRelative_access_counts M hM A j S hA
  refine ⟨h4, rfl⟩

/-- Packages the native sine value and term count, agreement with `nativeAEDecode`, output
bounds between zero and one, and error at most `((2 : ℝ)⁻¹) ^ k` relative to `aeEstimate`. -/
def nextNativeOutputSpec (M k : ℕ) (z : Fin M) : Prop :=
  (nextNativePhaseInversion M k z).1 = nativeAESin (nextNativeInput M k z) k ∧
  (nextNativePhaseInversion M k z).2 = 8 * (k + 8) ∧
  nextNativeOutput M k z = nativeAEDecode M k z ∧
  0 ≤ nextNativeOutput M k z ∧ nextNativeOutput M k z ≤ 1 ∧
    |(nextNativeOutput M k z : ℝ) - aeEstimate M z| ≤ ((2 : ℝ)⁻¹) ^ k

/-- Every native output satisfies `nextNativeOutputSpec`, including its value, term count,
range, and precision requirements. -/
theorem nextNativeOutputSpec_holds (M k : ℕ) (z : Fin M) : nextNativeOutputSpec M k z :=
  ⟨nextNativePhaseInversion_value M k z, nextNativePhaseInversion_terms M k z,
    nextNativeOutput_eq_frozen M k z, nextNativeOutput_precision M k z⟩

/-- Packages the native layer selector's agreement with `nextCor4Grid` and lower bound of two at
`(8, 0, 0)`, together with the explicit values `144` at `(8, 0, 0)` and `240` at `(8, 4,
4)`. -/
def nextNativeLayerSpec : Prop :=
  nextNativeLayerSelect 8 0 0 = nextCor4Grid 8 0 0 ∧
  2 ≤ nextNativeLayerSelect 8 0 0 ∧
  nextNativeLayerSelect 8 0 0 = 144 ∧ nextNativeLayerSelect 8 4 4 = 240

/-- The native layer selector satisfies all concrete equalities and the size bound collected in
`nextNativeLayerSpec`. -/
theorem nextNativeLayerSpec_holds : nextNativeLayerSpec :=
  ⟨nextNativeLayerSelect_eq 8 0 0,
    nextNativeLayerSelect_legal (N := 8) (t'₁ := 0) (t'₂ := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    nextNativeLayerSelect_result_dependent.1, nextNativeLayerSelect_result_dependent.2⟩

/-- Packages the decomposition of the native error allowance and the `8 / Real.pi ^ 2` lower
bound on the mass of labels whose scaled native output is within the combined error window
of the prepared marked count. -/
def nextNativeRecordSpec {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (S : Finset (Fin N)) : Prop :=
  nextNativeInputError M (MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S) +
      nextNativeDecoderError k =
    2 * Real.pi * Real.sqrt (MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S *
      (1 - MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S)) / (M : ℝ) +
      Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k ∧
  (let a := MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S
   (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
     |((N : ℚ) * nextNativeOutput M k z : ℝ) - (N : ℝ) * a| ≤ (N : ℝ) *
       (2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) +
         Real.pi ^ 2 / (M : ℝ) ^ 2 + ((2 : ℝ)⁻¹) ^ k)),
     (aeLaw M (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z)
     ≥ 8 / Real.pi ^ 2)

/-- The native readout satisfies `nextNativeRecordSpec` for every positive domain size and
amplitude-estimation grid of size at least two. -/
theorem nextNativeRecordSpec_holds {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (S : Finset (Fin N)) : nextNativeRecordSpec hN M k hM S :=
  ⟨nextNative_error_split M k
      (MeasureProb (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)) S),
    nextNative_same_record_success hN M k hM S⟩

/-- Packages the QFT-prepared readout's forward and backward access counts, query and circuit
gate counts, and native sine-series term count. -/
def nextNativeAccessSpec {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M) (z : Fin M)
    (S : Finset (Fin N)) : Prop :=
  aeForwardAccesses (aeAccessWord (I := Fin N) M) = M ∧
  aeBackwardAccesses (aeAccessWord (I := Fin N) M) = M - 1 ∧
  QueryCount (countedAECircuit M (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = M - 1 ∧
  GateCount (countedAECircuit M (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 5 * (M - 1) + 3 ∧
  (nextNativePhaseInversion M k z).2 = 8 * (k + 8)

/-- The QFT-prepared native readout satisfies the access, query, gate, and sine-term identities
in `nextNativeAccessSpec`. -/
theorem nextNativeAccessSpec_holds {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (z : Fin M) (S : Finset (Fin N)) : nextNativeAccessSpec hN M k hM z S :=
  nextNative_access_ledger M hM k z (QFTMatrix N) (⟨0, hN⟩ : Fin N) S (qftMatrix_unitary hN)

/-- Packages the native GCD ledger, the comparison of persistent and peak cell budgets, the
QFT-prepared circuit gate count, and the classical macro count. -/
def nextNativeResourceSpec {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (S : Finset (Fin N)) : Prop :=
  nextNativeGcdCount k = 2 * (k + 11) + 1 + 8 * (k + 8) ∧
  nextNativePersistentCells ≤ nextNativePeakCells ∧
  GateCount (countedAECircuit M (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 5 * (M - 1) + 3 ∧
  nextNativeClassicalMacros k = 3 * (8 * (k + 8)) + 3 * (2 * (k + 11))

/-- The QFT-prepared native readout satisfies every resource identity and cell-budget comparison
in `nextNativeResourceSpec`. -/
theorem nextNativeResourceSpec_holds {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M)
    (S : Finset (Fin N)) : nextNativeResourceSpec hN M k hM S :=
  ⟨nextNativeGcdCount_eq k, nextNativePersistent_le_peak,
    (nextNativeGateLedger M hM k (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN)).1,
    (nextNativeGateLedger M hM k (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      (qftMatrix_unitary hN)).2⟩

/-- Defines the search angle as `Real.arcsin (Real.sqrt (t / N))`. -/
noncomputable def nextMultiSearchAngle (t N : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (t / N))

/-- Chooses the search iteration count as the natural floor of `Real.pi / (4 *
nextMultiSearchAngle t N)`. -/
noncomputable def nextMultiSearchIterations (t N : ℝ) : ℕ :=
  Nat.floor (Real.pi / (4 * nextMultiSearchAngle t N))

/-- For `0 < t ≤ N / 2` and `N ≥ 2`, gives the search angle's range and sine-square identity,
bounds the rounded amplified angle's distance from `Real.pi / 2` by the original angle, and
bounds the iteration count by `Real.pi * Real.sqrt (N / t) / 4`. The amplified sine-square
success is at least `1 - t / N`. -/
theorem nextMultiSearch_angle_and_rounding {t N : ℝ} (ht0 : 0 < t) (htN : t ≤ N / 2)
    (hN : (2 : ℝ) ≤ N) :
    let θ := nextMultiSearchAngle t N
    let k := nextMultiSearchIterations t N
    0 < θ ∧ θ < Real.pi / 2 ∧ (Real.sin θ) ^ 2 = t / N ∧
    |(2 * (k : ℝ) + 1) * θ - Real.pi / 2| ≤ θ ∧
    (k : ℝ) ≤ Real.pi * Real.sqrt (N / t) / 4 ∧
    (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≥ 1 - t / N := by
  intro θ k
  have hNpos : (0 : ℝ) < N := by linarith
  have htNpos : (0 : ℝ) < t / N := div_pos ht0 hNpos
  have htN1 : t / N ≤ 1 / 2 := by
    have h2t : 2 * t ≤ N := by linarith [htN]
    rw [div_le_iff₀ hNpos]
    nlinarith [h2t]
  have hsqrt1 : Real.sqrt (t / N) ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt htN1
  have hsqrt1lt : Real.sqrt (1 / 2) < 1 := by
    have hsq : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have h0 : 0 ≤ Real.sqrt (1 / 2) := Real.sqrt_nonneg _
    nlinarith
  have hsq1 : Real.sqrt (t / N) < 1 := lt_of_le_of_lt hsqrt1 hsqrt1lt
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos htNpos)
  have hθ1 : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hsq1
  have hsin : Real.sin θ = Real.sqrt (t / N) :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg (t / N)]) hsq1.le
  have hsin2 : (Real.sin θ) ^ 2 = t / N := by
    rw [hsin, Real.sq_sqrt htNpos.le]
  have hk0 : (0 : ℝ) ≤ Real.pi / (4 * θ) :=
    div_nonneg Real.pi_nonneg (by linarith)
  have hk_le : (k : ℝ) ≤ Real.pi / (4 * θ) := Nat.floor_le hk0
  have hk_lt : Real.pi / (4 * θ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk1 : (k : ℝ) * (4 * θ) ≤ Real.pi :=
    (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * θ)).mp hk_le
  have hk2 : Real.pi < ((k : ℝ) + 1) * (4 * θ) :=
    (div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * θ)).mp hk_lt
  have hgap : |(2 * (k : ℝ) + 1) * θ - Real.pi / 2| ≤ θ := by
    rw [abs_le]
    constructor <;> linarith
  have hsinθ_le : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hs1θ : Real.sqrt (t / N) ≤ θ := by
    rw [hsin] at hsinθ_le
    exact hsinθ_le
  have hsqrtdiv : Real.sqrt (t / N) = Real.sqrt t / Real.sqrt N :=
    Real.sqrt_div ht0.le N
  have hsqrtdiv' : Real.sqrt (N / t) = Real.sqrt N / Real.sqrt t :=
    Real.sqrt_div hNpos.le t
  have hinvθ : (1 : ℝ) / θ ≤ Real.sqrt (N / t) := by
    calc (1 : ℝ) / θ ≤ 1 / Real.sqrt (t / N) :=
          one_div_le_one_div_of_le (Real.sqrt_pos_of_pos htNpos) hs1θ
      _ = Real.sqrt N / Real.sqrt t := by rw [hsqrtdiv, div_eq_mul_inv, inv_div, one_mul]
      _ = Real.sqrt (N / t) := by rw [hsqrtdiv']
  have hkk : (k : ℝ) ≤ Real.pi * Real.sqrt (N / t) / 4 := by
    calc (k : ℝ) ≤ Real.pi / (4 * θ) := hk_le
      _ = (Real.pi / 4) * (1 / θ) := by ring
      _ ≤ (Real.pi / 4) * Real.sqrt (N / t) :=
          mul_le_mul_of_nonneg_left hinvθ (by positivity)
      _ = Real.pi * Real.sqrt (N / t) / 4 := by ring
  have hsuccess : (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≥ 1 - t / N := by
    set e := (2 * (k : ℝ) + 1) * θ - Real.pi / 2 with hedef
    have hang : (2 * (k : ℝ) + 1) * θ = e + Real.pi / 2 := by
      rw [hedef]
      ring
    have hsinE : Real.sin ((2 * (k : ℝ) + 1) * θ) = Real.cos e := by
      rw [hang, Real.sin_add_pi_div_two]
    have hθleπ : θ ≤ Real.pi := by linarith [Real.pi_pos]
    have hcos : Real.cos θ ≤ Real.cos |e| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg e) hθleπ hgap
    have hcosθ0 : 0 ≤ Real.cos θ :=
      (Real.cos_pos_of_mem_Ioo
        (show θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) from
          ⟨by linarith [Real.pi_pos], hθ1⟩)).le
    have hsqe : (Real.cos θ) ^ 2 ≤ (Real.cos e) ^ 2 := by
      rw [← Real.cos_abs e]
      exact pow_le_pow_left₀ hcosθ0 hcos 2
    have hcos2 : (Real.cos θ) ^ 2 = 1 - t / N := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [hsin2] at h
      linarith
    rw [hsinE]
    linarith
  exact ⟨hθ0, hθ1, hsin2, hgap, hkk, hsuccess⟩

/-- Hadamard preparation from the zero register assigns marked probability `S.card /
Fintype.card (Reg n)` to every set `S`. -/
theorem nextMultiSearch_uniform_mass {n : ℕ} (S : Finset (Reg n)) :
    MeasureProb (preparedAAState (HadamardN n) (ZeroStr n)) S
      = (S.card : ℝ) / (Fintype.card (Reg n) : ℝ) := by
  show MeasureProb
      (ApplyGate (HadamardN n) (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))) S = _
  rw [applyGate_hadamardN_ket_zero, measureProb_uniform]

/-- The prepared marking reflection for `S` equals the phase oracle for the Boolean membership
predicate of `S`. -/
theorem nextMultiSearch_mark_eq_phaseOracle {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) :
    preparedMark S = PhaseOracle (fun y => decide (y ∈ S)) := by
  ext i j
  simp only [preparedMark, PhaseOracle, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Projector, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    by_cases hx : i ∈ S
    · simp [hx]
      norm_num
    · simp [hx]
  · simp [h]

/-- Defines search success as membership of the data register in `S`, allowing every value of
the Boolean ancilla and workspace register. -/
def nextMultiSearchEvent {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S : Finset (Reg n)) : Finset ((Reg n × Bool) × W) :=
  (S ×ˢ (Finset.univ : Finset Bool)) ×ˢ (Finset.univ : Finset W)

/-- The workspace Grover circuit is unitary, uses `k` queries and `3 * k + 3` gates, and runs
the prepared amplitude-amplification computation on the data register. From the specified
basis input, its final state is the tensor product of that computation's output, `Minus`,
and the original workspace basis state. -/
theorem nextMultiSearch_program {W : Type} [Fintype W] [DecidableEq W]
    (n k : ℕ) (w : W) (f : Reg n → Bool) :
    IsUnitaryCircuit (workspaceGroverCircuit (W := W) n k) ∧
    QueryCount (workspaceGroverCircuit (W := W) n k) = k ∧
    GateCount (workspaceGroverCircuit (W := W) n k) = 3 * k + 3 ∧
    Run (workspaceBitOracle (W := W) f) (workspaceGroverCircuit (W := W) n k)
        (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w))
      = TensorState (TensorState
          (Run (PhaseOracle f) (preparedAACircuit (HadamardN n) (ZeroStr n) k)
            (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))) Minus) (Qatlib.Foundations.PureStateMath.Ket w) :=
  workspace_grover_bit_semantics_and_cost n k w f

/-- For a nonempty marked set of size at most half the register space and `n ≥ 2`, the selected
workspace Grover circuit succeeds with probability at least `1 - S.card / Fintype.card (Reg
n)`. It is unitary, uses exactly the selected iteration count in queries and `3 * k + 3`
gates, and its query count is at most `Real.pi * Real.sqrt (N / t) / 4`. -/
theorem nextMultiSearch_actual_upper {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (S : Finset (Reg n)) (hn : 2 ≤ n)
    (ht0 : (0 : ℝ) < S.card)
    (htN : (S.card : ℝ) ≤ (Fintype.card (Reg n) : ℝ) / 2) :
    let N := (Fintype.card (Reg n) : ℝ)
    let t := (S.card : ℝ)
    let k := nextMultiSearchIterations t N
    let C := workspaceGroverCircuit (W := W) n k
    MeasureProb (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y ∈ S))) C
        (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
      (nextMultiSearchEvent (W := W) S) ≥ 1 - t / N ∧
    (QueryCount C : ℝ) ≤ Real.pi * Real.sqrt (N / t) / 4 ∧
    QueryCount C = k ∧ GateCount C = 3 * k + 3 ∧ IsUnitaryCircuit C := by
  intro N t k C
  obtain ⟨hθ0, hθ1, hsin2, _, hkk, hsuccess⟩ :=
    nextMultiSearch_angle_and_rounding (t := t) (N := N) ht0 htN (by
      have hcard : (2 : ℕ) ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (show (1 : ℕ) ≤ n by omega)
      have hcardR : (2 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := by
        have : Fintype.card (Reg n) = 2 ^ n := card_reg n
        rw [this]
        exact_mod_cast hcard
      exact hcardR)
  obtain ⟨hClegal, hQC, hGC, hrun⟩ := workspace_grover_bit_semantics_and_cost n k w
    (fun y : Reg n => decide (y ∈ S))
  have hprob : MeasureProb (preparedAAState (HadamardN n) (ZeroStr n)) S
      = (Real.sin (nextMultiSearchAngle t N)) ^ 2 := by
    rw [nextMultiSearch_uniform_mass]
    exact hsin2.symm
  have hborn := prepared_aa_born_success (HadamardN n) (ZeroStr n) S
    (nextMultiSearchAngle t N) k (hadamardN_unitary n) hθ0 hθ1 hprob
  rw [nextMultiSearch_mark_eq_phaseOracle] at hborn
  have hmain : MeasureProb (Run (workspaceBitOracle (W := W)
        (fun y : Reg n => decide (y ∈ S)))
        (workspaceGroverCircuit (W := W) n k) (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (nextMultiSearchEvent (W := W) S)
      = (Real.sin ((2 * (k : ℝ) + 1) * nextMultiSearchAngle t N)) ^ 2 := by
    rw [hrun, nextMultiSearchEvent, measureProb_tensorState_prod,
      measureProb_univ (normalized_ket w), mul_one, measureProb_tensorState_prod,
      measureProb_univ normalized_minus, mul_one, hborn]
  refine ⟨?_, ?_, hQC, hGC, hClegal⟩
  · show MeasureProb (Run (workspaceBitOracle (W := W)
        (fun y : Reg n => decide (y ∈ S)))
        (workspaceGroverCircuit (W := W) n k) (Qatlib.Foundations.PureStateMath.Ket ((ZeroStr n, false), w)))
        (nextMultiSearchEvent (W := W) S) ≥ 1 - t / N
    rw [hmain]
    exact hsuccess
  · show (QueryCount (workspaceGroverCircuit (W := W) n k) : ℝ)
        ≤ Real.pi * Real.sqrt (N / t) / 4
    rw [hQC]
    exact hkk

/-- For an empty marked set, the Hadamard-prepared marked probability is zero and the prepared
marking operator is the identity. -/
theorem nextMultiSearch_zero_branch {n : ℕ} (S : Finset (Reg n)) (hS : S = ∅) :
    MeasureProb (preparedAAState (HadamardN n) (ZeroStr n)) S = 0 ∧
      preparedMark S = 1 := by
  constructor
  · rw [nextMultiSearch_uniform_mass, hS, Finset.card_empty, Nat.cast_zero]
    simp
  · ext i j
    simp [preparedMark, Projector, hS]

/-- A normalized unitary search circuit with query bound `Q` and uniform success lower bound `p`
extends to a circuit with a clean ancilla initialized at `j₀`, preserving the query bound
and measured success probabilities. -/
theorem nextSearch_upper_transport {I J F : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (O : F → Matrix I I ℂ) (Acc : F → Finset I) (j₀ : J) (Q : ℕ) (p : ℝ) :
    Qatlib.Concepts.StoppingCore.InterruptBridge.cleanUpperTransport O Acc j₀ Q p :=
  Qatlib.Concepts.StoppingCore.InterruptBridge.cleanUpperTransport_fixed O Acc j₀ Q p

/-- Provides the adversary lower-bound transport for circuits with a clean initialized ancilla.
Under the validity, error, normalization, and success premises in
`cleanAncillaLowerTransport`, the adversary inequality bounds the query count of the
enlarged circuit. -/
theorem nextSearch_lower_transport {J X : Type} [Fintype J] [DecidableEq J]
    [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ}
    (input : X → Fin n → Bool) (f : X → Bool) (Γ : Matrix X X ℂ) (ε : ℝ) :
    Qatlib.Concepts.StoppingCore.InterruptBridge.cleanAncillaLowerTransport J input f Γ ε :=
  Qatlib.Concepts.StoppingCore.InterruptBridge.cleanAncillaLowerTransport_fixed input f Γ ε

/-- Produces access ledgers witnessing `bitToPhaseSimulation` for the given circuit and input
state. The simulation preserves query count and every measured-event probability while
adding two fixed gates per query. -/
theorem nextSearch_bit_phase_simulation {I : Type} [Fintype I] [DecidableEq I]
    {W : Type} [Fintype W] [DecidableEq W] (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    ∃ (source target : Qatlib.Concepts.StoppingCore.InterruptBridge.AccessLedger),
      Qatlib.Concepts.StoppingCore.InterruptBridge.bitToPhaseSimulation f C ψ source target :=
  Qatlib.Concepts.StoppingCore.InterruptBridge.bitToPhaseSimulation_fixed W f C ψ

end AmplitudeReadoutRefined
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
