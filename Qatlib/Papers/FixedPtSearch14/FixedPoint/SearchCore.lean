/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchCoreDefs
import Qatlib.Papers.FixedPtSearch14.FixedPoint.Search
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds

/-!
# Relative estimation grids and search comparisons

This module verifies the refined relative-estimation grid and resource interfaces used in the
fixed-point-search development [YoderLowChuang2014]. It proves error and promise bounds, median
witnesses, and the exact sinusoidal response of phase-mark amplitude amplification.

The workspace-search results compare the implemented bit-kickback circuit with a lower-bound
record, including matching access models and equal sensitivity parameters.

## Main statements

* `relative_ae_tight_relative_error`: Relative accuracy on the selected tight grid.
* `phase_mark_peak_success`: Success at the floor-selected amplification peak.
* `clause25_actual_program_is_a_bounded_error_decoder`: Success probability at least `2/3` for
  the workspace decoder.
* `clause25_actual_circuit_is_within_a_constant_of_optimal`: Query bounds for the actual
  bit-model circuit.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib
open Qatlib.Papers.FixedPtSearch14.FixedPoint
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The tight relative grid has size at least two for `0 < a₀ ≤ 1` and `ε > 0`. -/
theorem tight_relative_grid_two (a₀ ε : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hε : 0 < ε) : 2 ≤ tightRelativeGrid a₀ ε := by
  have harg : 0 < tightGridArgument a₀ ε := by
    have h2 : 0 < Real.sqrt (a₀ * ε) := Real.sqrt_pos.2 (by positivity)
    have h2' : 0 < 2 * Real.pi / Real.sqrt (a₀ * ε) := by positivity
    have h3 : 0 ≤ 4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε := by
      have h1 : 0 ≤ (1 - a₀) / a₀ := div_nonneg (sub_nonneg.mpr ha₀1) (le_of_lt ha₀)
      positivity
    simp only [tightGridArgument]
    linarith
  have hceil : 1 ≤ Nat.ceil (tightGridArgument a₀ ε) := by
    have hlt : (0 : ℝ) < (Nat.ceil (tightGridArgument a₀ ε) : ℝ) := by
      have h := Nat.le_ceil (tightGridArgument a₀ ε)
      linarith
    have hne : Nat.ceil (tightGridArgument a₀ ε) ≠ 0 := by
      intro hz
      have hz' : (Nat.ceil (tightGridArgument a₀ ε) : ℝ) = 0 := by
        rw [hz]
        norm_num
      linarith
    omega
  simp only [tightRelativeGrid]
  omega

/-- The tight grid makes the relative sampling error at most `ε` for `0 < a₀ ≤ 1` and `ε > 0`. -/
theorem tight_relative_grid_sampling_error (a₀ ε : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hε : 0 < ε) :
    relativeAESamplingError (tightRelativeGrid a₀ ε) a₀ ≤ ε := by
  set M := tightRelativeGrid a₀ ε with hMdef
  have hMpos : 0 < (M : ℝ) := by
    have h2 : 2 ≤ M := tight_relative_grid_two a₀ ε ha₀ ha₀1 hε
    have h3 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
    linarith

  have hMX : (M : ℝ) > tightGridArgument a₀ ε := by
    have hceil : (tightGridArgument a₀ ε) ≤ (Nat.ceil (tightGridArgument a₀ ε) : ℝ) :=
      Nat.le_ceil _
    rw [hMdef]
    simp only [tightRelativeGrid, Nat.cast_add, Nat.cast_one]
    linarith

  have hlead : 2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / (M : ℝ) ≤ ε / 2 := by
    have hkey : 4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε < (M : ℝ) := by
      have hsecond : 0 ≤ 2 * Real.pi / Real.sqrt (a₀ * ε) := by positivity
      simp only [tightGridArgument] at hMX
      linarith
    have hkey' : 4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) < ε * (M : ℝ) := by
      have := (div_lt_iff₀ hε).1 hkey
      linarith
    have hhalf : 2 * Real.pi * Real.sqrt ((1 - a₀) / a₀) ≤ (ε / 2) * (M : ℝ) := by
      linarith
    exact (div_le_iff₀ hMpos).2 hhalf

  have hquad : Real.pi ^ 2 / (a₀ * (M : ℝ) ^ 2) ≤ ε / 4 := by
    have hkey : 2 * Real.pi / Real.sqrt (a₀ * ε) ≤ (M : ℝ) := by
      have hsecond : 0 ≤ 4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε := by positivity
      simp only [tightGridArgument] at hMX
      linarith
    have hsq : (2 * Real.pi / Real.sqrt (a₀ * ε)) ^ 2 ≤ (M : ℝ) ^ 2 := by
      simpa only [pow_two] using! (mul_self_le_mul_self (by positivity) hkey)
    have hc2 : (2 * Real.pi / Real.sqrt (a₀ * ε)) ^ 2 = 4 * Real.pi ^ 2 / (a₀ * ε) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg ha₀.le hε.le)]
      ring
    have hsq' : 4 * Real.pi ^ 2 / (a₀ * ε) ≤ (M : ℝ) ^ 2 := by
      nlinarith [hsq]
    have hmul : 4 * Real.pi ^ 2 ≤ (a₀ * ε) * (M : ℝ) ^ 2 := by
      have h := (div_le_iff₀ (mul_pos ha₀ hε)).1 hsq'
      linarith
    have htarget : Real.pi ^ 2 ≤ (ε / 4) * (a₀ * (M : ℝ) ^ 2) := by linarith
    exact (div_le_iff₀ (by positivity : 0 < a₀ * (M : ℝ) ^ 2)).2 htarget
  unfold relativeAESamplingError
  linarith

/-- When the marked mass is at least `a₀ > 0`, ideal amplitude estimation on the tight grid has
relative error at most `ε` with probability at least `8 / π²`. -/
theorem relative_ae_tight_relative_error (a₀ ε : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hε : 0 < ε) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    a₀ ≤ unknownAmplitude A j S →
    (∑ z ∈ Finset.univ.filter (fun z : Fin (tightRelativeGrid a₀ ε) =>
        |aeEstimate (tightRelativeGrid a₀ ε) z - unknownAmplitude A j S|
          ≤ unknownAmplitude A j S * ε),
      (aeLaw (tightRelativeGrid a₀ ε) A j S hA
        (tight_relative_grid_two a₀ ε ha₀ ha₀1 hε)).prob z) ≥ 8 / Real.pi ^ 2 := by
  intro ha
  have hM2 : 2 ≤ tightRelativeGrid a₀ ε :=
    tight_relative_grid_two a₀ ε ha₀ ha₀1 hε
  have hkey := relative_ae_relative_error (tightRelativeGrid a₀ ε) hM2 A j S hA
    a₀ ha₀ ha₀1 ha
  have htight : relativeAESamplingError (tightRelativeGrid a₀ ε) a₀ ≤ ε :=
    tight_relative_grid_sampling_error a₀ ε ha₀ ha₀1 hε
  have hstep : unknownAmplitude A j S * relativeAESamplingError (tightRelativeGrid a₀ ε) a₀
      ≤ unknownAmplitude A j S * ε :=
    mul_le_mul_of_nonneg_left htight (le_of_lt (lt_of_lt_of_le ha₀ ha))
  have hsub : (Finset.univ.filter (fun z : Fin (tightRelativeGrid a₀ ε) =>
        |aeEstimate (tightRelativeGrid a₀ ε) z - unknownAmplitude A j S|
          ≤ unknownAmplitude A j S * relativeAESamplingError (tightRelativeGrid a₀ ε) a₀))
      ⊆ (Finset.univ.filter (fun z : Fin (tightRelativeGrid a₀ ε) =>
        |aeEstimate (tightRelativeGrid a₀ ε) z - unknownAmplitude A j S|
          ≤ unknownAmplitude A j S * ε)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact le_trans (Finset.mem_filter.mp hz).2 hstep
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => (aeLaw (tightRelativeGrid a₀ ε) A j S hA hM2).nonneg z)
  exact hkey.2.trans hmass

/-- For `M ≥ 4`, a record within the BHMT error window yields a refined promise bounded above by
the true mass, provided the original promise is valid. -/
theorem refined_promise_valid (M : ℕ) (hM : 4 ≤ M) (a₀ a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : a₀ ≤ a) (z : Fin M)
    (hz : |aeEstimate M z - a|
      ≤ 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2) :
    refinedPromise M a₀ z ≤ a := by
  have hs : Real.sqrt (a * (1 - a)) ≤ 1 / 2 := by
    have hnonneg : 0 ≤ a * (1 - a) := by nlinarith [ha0, ha1]
    have h : a * (1 - a) ≤ 1 / 4 := by
      have hsq := sq_nonneg (a - 1 / 2)
      nlinarith
    have hs' := Real.sqrt_le_sqrt h
    have hsq : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    linarith
  have hMpi : (Real.pi : ℝ) ≤ (M : ℝ) := by
    have h4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega)
    have hpi : Real.pi < 4 := by
      have hlt := Real.pi_lt_four
      linarith
    linarith
  have hwidth : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ)
      + Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ 2 * Real.pi / (M : ℝ) := by
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega)
    have h1 : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) ≤ Real.pi / (M : ℝ) := by
      rw [div_le_div_iff₀ hMpos hMpos]
      have hmul : 2 * Real.pi * Real.sqrt (a * (1 - a)) ≤ Real.pi := by
        have hpi : 0 ≤ 2 * Real.pi := by positivity
        have hstep : 2 * Real.pi * Real.sqrt (a * (1 - a)) ≤ 2 * Real.pi * (1 / 2) :=
          mul_le_mul_of_nonneg_left hs hpi
        linarith
      have hstep := mul_le_mul_of_nonneg_right hmul (le_of_lt hMpos)
      linarith
    have h2 : Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ Real.pi / (M : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < (M : ℝ) ^ 2)]
      have hpiM : Real.pi ^ 2 ≤ Real.pi * (M : ℝ) := by
        have hmul : Real.pi * Real.pi ≤ Real.pi * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hMpi (le_of_lt Real.pi_pos)
        simpa only [pow_two] using! hmul
      have hrewrite : (Real.pi / (M : ℝ)) * (M : ℝ) ^ 2 = Real.pi * (M : ℝ) := by
        field_simp
      rw [hrewrite]
      exact hpiM
    have hsum := add_le_add h1 h2
    (convert! hsum using 1; ring)
  have habs : aeEstimate M z ≤ a + 2 * Real.pi / (M : ℝ) := by
    have hz' := (abs_le.mp hz).2
    linarith
  simp only [refinedPromise]
  exact max_le ha (by linarith)

/-- The refined promise is at least the original lower bound `a₀`. -/
theorem refined_promise_monotone (M : ℕ) (a₀ : ℝ) (z : Fin M) :
    a₀ ≤ refinedPromise M a₀ z := by
  simp only [refinedPromise]
  exact le_max_left _ _

/-- Increasing a positive lower bound within the unit interval cannot increase the tight
relative grid size. -/
theorem tight_grid_decreasing_in_promise (a₀ a₁ ε : ℝ) (ha₀ : 0 < a₀)
    (ha₀1 : a₀ ≤ 1) (ha₁ : 0 < a₁) (ha₁1 : a₁ ≤ 1) (hε : 0 < ε)
    (hle : a₀ ≤ a₁) :
    tightRelativeGrid a₁ ε ≤ tightRelativeGrid a₀ ε := by
  have hfrac0 : 0 ≤ (1 - a₀) / a₀ := div_nonneg (sub_nonneg.mpr ha₀1) (le_of_lt ha₀)
  have hfrac1 : 0 ≤ (1 - a₁) / a₁ := div_nonneg (sub_nonneg.mpr ha₁1) (le_of_lt ha₁)
  have hdec : (1 - a₁) / a₁ ≤ (1 - a₀) / a₀ := by
    have hpos : 0 < a₀ := ha₀
    have hpos1 : 0 < a₁ := ha₁
    rw [div_le_div_iff₀ hpos1 hpos]
    have h1 : a₀ * (1 - a₁) ≤ a₁ * (1 - a₀) := by linarith
    simpa [mul_comm] using! h1
  have hsqrt : Real.sqrt ((1 - a₁) / a₁) ≤ Real.sqrt ((1 - a₀) / a₀) :=
    Real.sqrt_le_sqrt hdec
  have hX1 : 2 * Real.pi / Real.sqrt (a₁ * ε)
      ≤ 2 * Real.pi / Real.sqrt (a₀ * ε) := by
    have hprod : a₀ * ε ≤ a₁ * ε := by nlinarith
    have hsq : Real.sqrt (a₀ * ε) ≤ Real.sqrt (a₁ * ε) :=
      Real.sqrt_le_sqrt hprod
    have hp0 : 0 < Real.sqrt (a₀ * ε) := Real.sqrt_pos.2 (by positivity)
    have hp1 : 0 < Real.sqrt (a₁ * ε) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_div_iff₀ hp1 hp0]
    have hmul : 2 * Real.pi * Real.sqrt (a₀ * ε) ≤ 2 * Real.pi * Real.sqrt (a₁ * ε) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    exact hmul
  have hfirst : 4 * Real.pi * Real.sqrt ((1 - a₁) / a₁) / ε
      ≤ 4 * Real.pi * Real.sqrt ((1 - a₀) / a₀) / ε := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hε' : 0 < ε := hε
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (le_of_lt hε')
  have hXle : tightGridArgument a₁ ε ≤ tightGridArgument a₀ ε := by
    simp only [tightGridArgument]
    linarith
  have hceil : Nat.ceil (tightGridArgument a₁ ε) ≤ Nat.ceil (tightGridArgument a₀ ε) := by
    have h2 : tightGridArgument a₀ ε ≤ (Nat.ceil (tightGridArgument a₀ ε) : ℝ) := by
      exact Nat.le_ceil (R := ℝ) _
    have h3 : tightGridArgument a₁ ε ≤ (Nat.ceil (tightGridArgument a₀ ε) : ℝ) := by
      linarith
    exact (Nat.ceil_le (α := ℝ)).mpr h3
  simp only [tightRelativeGrid]
  omega

/-- For positive `M`, the actual circuit has `M - 1` queries, `5 * (M - 1) + 3` gates, `2 * (M -
1) + 1` input accesses, and `M - 1` source reflections. -/
theorem ae_cost_ledger_actual (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (countedAECircuit M A j) = M - 1 ∧
    GateCount (countedAECircuit M A j) = 5 * (M - 1) + 3 ∧
    aeInputAccesses (aeAccessWord (I := I) M) = 2 * (M - 1) + 1 ∧
    aeSourceReflections (aeAccessWord (I := I) M) = M - 1 :=
  prepared_ae_access_ledger M hM A j

/-- On the tight grid, the unified relative error is at most `ε + 2⁻ᵏ / a₀`. -/
theorem relative_endpoint_unified_error (a₀ ε : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hε : 0 < ε) (k : ℕ) :
    relativeAEError (tightRelativeGrid a₀ ε) k a₀ ≤ ε + ((2 : ℝ)⁻¹) ^ k / a₀ := by
  have hs := tight_relative_grid_sampling_error a₀ ε ha₀ ha₀1 hε
  have hk : 0 ≤ ((2 : ℝ)⁻¹) ^ k / a₀ := by positivity
  unfold relativeAEError
  linarith

/-- If the decoding contribution is at most `ε / 2`, the tight-grid unified error is at most `3
* ε / 2`. -/
theorem relative_endpoint_decode_precision (a₀ ε : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ ≤ 1)
    (hε : 0 < ε) (k : ℕ) (hk : ((2 : ℝ)⁻¹) ^ k / a₀ ≤ ε / 2) :
    relativeAEError (tightRelativeGrid a₀ ε) k a₀ ≤ 3 * ε / 2 := by
  have hs := tight_relative_grid_sampling_error a₀ ε ha₀ ha₀1 hε
  unfold relativeAEError
  linarith

omit [Fintype I] [DecidableEq I] in

/-- Clipping about `μ` with positive radius `τ` gives absolute payoff at most `|μ| + τ`. -/
theorem truncated_centred_payoff_bounded (f : I → ℝ) (μ τ : ℝ) (hτ : 0 < τ) (i : I) :
    |truncatedCentredPayoff f μ τ i| ≤ |μ| + τ := by
  have hc := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip_bound τ (f i - μ) hτ.le
  have habs : |Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)| ≤ τ := hc
  have htri : |μ + Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)|
      ≤ |μ| + |Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)| := by
    rw [abs_le]
    constructor
    · have hm : -μ ≤ |μ| := neg_le_abs μ
      have hcv : -(Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)) ≤ |Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)| :=
        neg_le_abs _
      linarith
    · have hm : μ ≤ |μ| := le_abs_self μ
      have hcv : Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ) ≤ |Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)| :=
        le_abs_self _
      linarith
  calc |truncatedCentredPayoff f μ τ i|
      ≤ |μ| + |Qatlib.Concepts.AEMeanReadout.LocalAEBackend.boundedClip τ (f i - μ)| := by
        simp only [truncatedCentredPayoff, truncatedPayoff]
        exact htri
    _ ≤ |μ| + τ := by linarith

/-- A variance-only endpoint carries a nonnegative variance parameter and a positive scale. -/
theorem variance_only_endpoint_scale (e : VarianceOnlyEndpoint) :
    0 ≤ e.V ∧ 0 < e.σ := by
  exact ⟨e.V_nonneg, e.σ_pos⟩

/-- At a source value and two layer records, the signed-mean probability is the Born probability
times the conditional positive and negative layer probabilities. -/
theorem variance_only_actual_joint_law (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (σ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (x : I) (u v : LayerRecord k) :
    (signedMeanLaw k A j f σ hA).prob (x, (u, v)) = BornProb (ApplyGate A (Ket j)) x *
      (layerLaw k A j (centerPositive f σ x) hA (fun _ => le_max_right _ _)).prob u *
      (layerLaw k A j (centerNegative f σ x) hA (fun _ => le_max_right _ _)).prob v :=
  signed_centered_actual_joint_law I k A j f σ hA x u v

omit [Fintype I] in

/-- A compiled amplitude-estimation round has one query and length `aeRoundLength`. -/
theorem ae_round_is_atomic (M : ℕ) (A : Matrix I I ℂ) (j : I) (k : ℕ) :
    QueryCount (compiledRound M A j k) = 1 ∧
    (compiledRound M A j k).length = aeRoundLength :=
  compiledRound_single_query M A j k

/-- For positive `M`, the counted circuit has `M - 1` queries and its access word has `M - 1`
source reflections. -/
theorem ae_program_interrupt_points (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (countedAECircuit M A j) = M - 1 ∧
    aeSourceReflections (aeAccessWord (I := I) M) = M - 1 := by
  have h := prepared_ae_access_ledger M hM A j
  exact ⟨h.1, h.2.2.2⟩

/-- For positive `M`, every preparation matrix and initial basis label yield a counted circuit
with `M - 1` queries. -/
theorem ae_access_model_is_phase_mark (M : ℕ) (hM : 0 < M) :
    ∀ (A : Matrix I I ℂ) (j : I), QueryCount (countedAECircuit M A j) = M - 1 := by
  intro A j
  exact (prepared_ae_access_ledger M hM A j).1

/-- If the median of `2 * r + 1` decoded estimates has error greater than a nonnegative `ε`, at
least `r + 1` individual estimates have error greater than `ε`. -/
theorem multi_layer_median_majority_witness (M k r : ℕ) (ω : Fin (2 * r + 1) → Fin M)
    (a ε : ℝ) (hε : 0 ≤ ε)
    (hmed : ε < |multiLayerMedian M k r ω - a|) :
    r + 1 ≤ (Finset.univ.filter (fun l : Fin (2 * r + 1) =>
      ε < |(nativeAEDecode M k (ω l) : ℝ) - a|)).card := by
  exact heterogeneous_sorted_median_majority_witness r
    (fun l => (nativeAEDecode M k (ω l) : ℝ)) a ε hε hmed

/-- The readout list has one entry per layer and the assigned oracle cost is `L * (M - 1)`. -/
theorem multi_layer_ledger_cost (M k L : ℕ) (ω : Fin L → Fin M) :
    (multiLayerReadout M k L ω).length = L ∧
    multiLayerOracleCalls L M = L * (M - 1) := by
  constructor
  · simp [multiLayerReadout]
  · rfl

/-- For a unitary preparation with marked mass `sin² θ` and `0 < θ < π/2`, `k` phase-mark
amplification rounds have success probability `sin² ((2k + 1)θ)`. -/
theorem phase_mark_success_exact (A : Matrix I I ℂ) (j : I) (S : Finset I) (θ : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hp : MeasureProb (preparedAAState A j) S = (Real.sin θ) ^ 2) :
    MeasureProb (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) S
      = (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 :=
  prepared_aa_born_success A j S θ k hA hθ0 hθ1 hp

/-- For nonnegative `δ`, success probability at least `1 - δ` is equivalent to `|cos ((2k +
1)θ)| ≤ √δ` under the stated preparation and angle hypotheses. -/
theorem phase_mark_success_characterisation (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (θ : ℝ) (k : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2)
    (hp : MeasureProb (preparedAAState A j) S = (Real.sin θ) ^ 2) (δ : ℝ) (hδ : 0 ≤ δ) :
    (MeasureProb (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) S ≥ 1 - δ)
      ↔ |Real.cos ((2 * (k : ℝ) + 1) * θ)| ≤ Real.sqrt δ := by
  rw [phase_mark_success_exact A j S θ k hA hθ0 hθ1 hp]
  have hsc := Real.sin_sq_add_cos_sq ((2 * (k : ℝ) + 1) * θ)
  have hstep : (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≥ 1 - δ
      ↔ (Real.cos ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≤ δ := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hstep2 : (Real.cos ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≤ δ
      ↔ |Real.cos ((2 * (k : ℝ) + 1) * θ)| ≤ Real.sqrt δ := by
    have habs : |Real.cos ((2 * (k : ℝ) + 1) * θ)| ^ 2
        = (Real.cos ((2 * (k : ℝ) + 1) * θ)) ^ 2 := sq_abs _
    constructor
    · intro h
      have h1 : (Real.cos ((2 * (k : ℝ) + 1) * θ)) ^ 2 ≤ (Real.sqrt δ) ^ 2 := by
        rw [Real.sq_sqrt hδ]
        exact h
      rw [← habs] at h1
      exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg δ)).1 h1
    · intro h
      have h1 : |Real.cos ((2 * (k : ℝ) + 1) * θ)| ^ 2 ≤ (Real.sqrt δ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg δ)).2 h
      rw [habs] at h1
      rw [Real.sq_sqrt hδ] at h1
      exact h1
  exact hstep.trans hstep2

/-- For positive `θ`, the floor-selected peak rounds satisfy `4kθ ≤ π < 4(k + 1)θ`. -/
theorem phase_mark_peak_rounds_bound (θ : ℝ) (hθ : 0 < θ) :
    4 * (phaseMarkPeakRounds θ : ℝ) * θ ≤ Real.pi ∧
    Real.pi < 4 * ((phaseMarkPeakRounds θ : ℝ) + 1) * θ := by
  have hθ' : 0 < 4 * θ := by positivity
  have h1 : (phaseMarkPeakRounds θ : ℝ) ≤ Real.pi / (4 * θ) := by
    exact Nat.floor_le (div_nonneg (le_of_lt Real.pi_pos) (le_of_lt hθ'))
  have h2 : Real.pi / (4 * θ) < (phaseMarkPeakRounds θ : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (Real.pi / (4 * θ))
  constructor
  · have hmul := (le_div_iff₀ hθ').1 h1
    linarith
  · have hmul := (div_lt_iff₀ hθ').1 h2
    linarith

/-- At the floor-selected peak, phase-mark amplitude amplification succeeds with probability at
least `1 - sin² θ` under the stated preparation and angle hypotheses. -/
theorem phase_mark_peak_success (A : Matrix I I ℂ) (j : I) (S : Finset I) (θ : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hp : MeasureProb (preparedAAState A j) S = (Real.sin θ) ^ 2) :
    MeasureProb (Run (preparedMark S)
      (preparedAACircuit A j (phaseMarkPeakRounds θ)) (Ket j)) S
      ≥ 1 - (Real.sin θ) ^ 2 := by
  have hrounds := phase_mark_peak_rounds_bound θ hθ0
  have hchar := phase_mark_success_characterisation A j S θ (phaseMarkPeakRounds θ)
    hA hθ0 hθ1 hp ((Real.sin θ) ^ 2) (sq_nonneg (Real.sin θ))
  rw [hchar]
  have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hsqrt : Real.sqrt ((Real.sin θ) ^ 2) = Real.sin θ :=
    Real.sqrt_sq (le_of_lt hsinpos)
  rw [hsqrt]
  have hlow : Real.pi / 2 - θ < (2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ := by
    have h2 := hrounds.2
    linarith
  have hupp : (2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ ≤ Real.pi / 2 + θ := by
    have h1 := hrounds.1
    linarith
  have hcos_low : Real.cos ((2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ)
      ≤ Real.cos (Real.pi / 2 - θ) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 2 - θ)
      (y := (2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ)
      (by linarith [hθ0, hθ1]) (by linarith [hupp, hθ1]) (by linarith [hlow])
  have hcos_upp : Real.cos (Real.pi / 2 + θ)
      ≤ Real.cos ((2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ) := by
    exact Real.cos_le_cos_of_nonneg_of_le_pi (x := (2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ)
      (y := Real.pi / 2 + θ) (by linarith [hθ0, hupp]) (by linarith [hθ1])
      (by linarith [hupp])
  have hlow' : -Real.sin θ ≤ Real.cos ((2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ) := by
    have h := hcos_upp
    have h2 : Real.cos (Real.pi / 2 + θ) = -Real.sin θ := by
      rw [show Real.pi / 2 + θ = θ + Real.pi / 2 by ring, Real.cos_add_pi_div_two]
    linarith
  have hupp' : Real.cos ((2 * (phaseMarkPeakRounds θ : ℝ) + 1) * θ) ≤ Real.sin θ := by
    have h := hcos_low
    rwa [Real.cos_pi_div_two_sub] at h
  rw [abs_le]
  exact ⟨hlow', hupp'⟩

/-- The table-loading bit count is the number of rows times their width. -/
theorem table_load_bits (t : DatabaseTable) :
    tableLoadBits t = t.rows * t.width := rfl

/-- The scan ledger has bit cost `(2 * rows - 1) * width` and space count `width + rows`. -/
theorem database_access_cost (t : DatabaseTable) :
    ComparisonLedger.bitCost (linearScanMinimum t).2 t.width
        = (2 * t.rows - 1) * t.width ∧
    ComparisonLedger.spaceBits (linearScanMinimum t).2 t.width = t.width + t.rows := by
  constructor
  · exact (linear_scan_ledger t).2.2
  · simp only [ComparisonLedger.spaceBits]
    rw [(linear_scan_ledger t).1]

/-- For a table with at least one row, the table-loading bit count is bounded above by the
scan-ledger bit cost. -/
theorem table_load_dominates (t : DatabaseTable) (hrows : 1 ≤ t.rows) :
    tableLoadBits t ≤ ComparisonLedger.bitCost (linearScanMinimum t).2 t.width := by
  have h := (linear_scan_ledger t)
  simp only [tableLoadBits]
  have hkey : t.rows ≤ 2 * t.rows - 1 := by omega
  have hkey2 : t.rows ≤ (linearScanMinimum t).2.loads + (linearScanMinimum t).2.comparisons := by
    rw [h.1, h.2.1]
    calc t.rows ≤ 2 * t.rows - 1 := hkey
      _ = t.rows + (t.rows - 1) := by omega
  exact mul_le_mul_of_nonneg_right hkey2 (Nat.zero_le t.width)

/-- The event where the workspace decoder returns `some x` is exactly the query fiber at `x`. -/
theorem clause25_decoder_event_is_the_query_fiber {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (x : Reg n) :
    (Finset.univ : Finset ((Reg n × Bool) × W)).filter
        (fun p => workspaceDataDecoder p = some x) = workspaceQueryFiber (W := W) x := by
  ext p
  simp [workspaceDataDecoder, workspaceQueryFiber, Option.some.injEq]

/-- For at least two data bits, the workspace Grover circuit decodes the unique marked string
with probability at least `2/3`. -/
theorem clause25_actual_program_is_a_bounded_error_decoder {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (w : W) (x : Reg n) (hn : 2 ≤ n) :
    MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Ket ((ZeroStr n, false), w)))
        (Finset.univ.filter (fun p => workspaceDataDecoder p = some x)) ≥ 2 / 3 := by
  obtain ⟨hborn, _, _, _, _, _, _, _⟩ :=
    workspace_singleton_search_actual_upper (W := W) n w x hn
  have hN : (4 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := by
    have h : (4 : ℕ) ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    show (4 : ℝ) ≤ (Fintype.card (Reg n) : ℝ)
    rw [card_reg]
    exact_mod_cast h
  calc
    MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Ket ((ZeroStr n, false), w)))
        (Finset.univ.filter (fun p => workspaceDataDecoder p = some x))
        = MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
          (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
          (Ket ((ZeroStr n, false), w)))
          (workspaceQueryFiber (W := W) x) := by
          rw [clause25_decoder_event_is_the_query_fiber (W := W) x]
    _ ≥ 1 - 1 / (Fintype.card (Reg n) : ℝ) := hborn
    _ ≥ 2 / 3 := by
      have hone : (1 : ℝ) / (Fintype.card (Reg n) : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith

/-- For at least three data bits, the data-register cardinality is at most `64` times the square
of the implemented Grover query count. -/
theorem clause25_actual_circuit_meets_the_lower_bound {n : ℕ} {W : Type} [Fintype W]
    [DecidableEq W] (w : W) (hn : 3 ≤ n) :
    (Fintype.card (Reg n) : ℝ) ≤
      64 * (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ^ 2 := by
  obtain ⟨_, _, _, _, hunit, _, _, _⟩ :=
    workspace_singleton_search_actual_upper (W := W) n w (ZeroStr n) (by omega)
  refine workspace_search_query_lower_bound (W := W)
    (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
    (Ket ((ZeroStr n, false), w)) workspaceDataDecoder hunit (normalized_ket _) ?_ ?_
  · have h : (8 : ℕ) ≤ 2 ^ n := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    show (6 : ℕ) ≤ Fintype.card (Reg n)
    rw [card_reg]
    omega
  · intro x
    exact clause25_actual_program_is_a_bounded_error_decoder w x (by omega)

/-- For at least three data bits, the actual Grover query count lies between the bit-model
lower-bound record and `π * √N / 4`, where `N` is the data-register cardinality. -/
theorem clause25_actual_circuit_is_within_a_constant_of_optimal {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (w : W) (hn : 3 ≤ n) :
    (bitModelMinimalComplexity (Fintype.card (Reg n))).queries ≤
        (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ∧
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ≤
        Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 := by
  obtain ⟨hlower, hupper, _, _, _, _, _, _⟩ :=
    workspace_singleton_search_actual_upper (W := W) n w (ZeroStr n) (by omega)
  have hlow := clause25_actual_circuit_meets_the_lower_bound w hn
  have hQC0 : (0 : ℝ) ≤ (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) :=
    Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := Nat.cast_nonneg _
  have hsq : (Fintype.card (Reg n) : ℝ)
      ≤ (8 * (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ)) ^ 2 := by
    nlinarith [hlow]
  have hsqrt : Real.sqrt (Fintype.card (Reg n) : ℝ)
      ≤ 8 * (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) := by
    have hle := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (mul_nonneg (by norm_num) hQC0)] at hle
    exact hle
  constructor
  · simp only [bitModelMinimalComplexity]
    linarith
  · exact hupper

/-- The actual bit-model complexity record and its lower-bound record have matching access
models. -/
theorem clause25_the_comparison_is_well_formed (n : ℕ) :
    matchedModel (bitModelActualComplexity n).model
      (bitModelMinimalComplexity (Fintype.card (Reg n))).model := by
  simp [matchedModel, bitModelActualComplexity, minimalComplexityOf,
    bitModelProgramComplexity, bitModelMinimalComplexity]

/-- The phase-mark complexity record and the actual bit-kickback complexity record have
incompatible access models. -/
theorem clause25_cross_model_comparison_is_not_well_formed (n : ℕ) (k : ℕ) (θ : ℝ) :
    ¬ matchedModel (phaseMarkComplexity k θ).model (bitModelActualComplexity n).model := by
  simp [matchedModel, phaseMarkComplexity, bitModelActualComplexity, minimalComplexityOf,
    bitModelProgramComplexity]

/-- For at least two data bits, both the actual and lower-bound bit-model records have
sensitivity `bitModelSensitivity` at the data-register cardinality. -/
theorem clause25_both_records_carry_the_same_sensitivity (n : ℕ) (hn : 2 ≤ n) :
    (bitModelActualComplexity n).sensitivity = bitModelSensitivity (Fintype.card (Reg n)) ∧
    (bitModelMinimalComplexity (Fintype.card (Reg n))).sensitivity
      = bitModelSensitivity (Fintype.card (Reg n)) := by
  obtain ⟨hθ0, hθ1, hsin2, _, _, _⟩ := workspace_singleton_angle_and_rounding n hn
  have hNpos : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by
    have h : (4 : ℕ) ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    show (0 : ℝ) < (Fintype.card (Reg n) : ℝ)
    rw [card_reg]
    exact_mod_cast (by omega : (0 : ℕ) < 2 ^ n)
  have hsin0 : (0 : ℝ) ≤ Real.sin (singletonSearchAngle n) :=
    (Real.sin_pos_of_pos_of_lt_pi hθ0 (hθ1.trans (by linarith [Real.pi_pos]))).le
  have hsin : Real.sin (singletonSearchAngle n)
      = Real.sqrt (1 / (Fintype.card (Reg n) : ℝ)) := by
    have hsq : (Real.sin (singletonSearchAngle n)) ^ 2
        = (Real.sqrt (1 / (Fintype.card (Reg n) : ℝ))) ^ 2 := by
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (Fintype.card (Reg n) : ℝ)),
        hsin2]
    exact (sq_eq_sq₀ hsin0 (Real.sqrt_nonneg _)).mp hsq
  constructor
  · simp only [bitModelActualComplexity, minimalComplexityOf, bitModelProgramComplexity,
      bitModelSensitivity]
    rw [hsin, Real.sqrt_div' (1 : ℝ) hNpos.le, Real.sqrt_one]
  · simp only [bitModelMinimalComplexity, bitModelSensitivity]

end Qatlib.Papers.FixedPtSearch14.FixedPoint
