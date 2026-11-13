/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs

/-!
# Reweighting success and limits of lower-bound consumers

`reweighting_exact_word_success` certifies exact resampling and its access ledger.
`sourceQueryLowerBound_instance_constants` supplies an instance-dependent offset that makes its
lower bound zero, while `gext3_filtered_consumer_of_zero_query_word` rules out a positive
filtered lower-bound consumer whenever a successful word uses no source queries. A
one-dimensional example gives an explicit refutation.

Quantum rejection sampling [OzolsRoettelerRoland2013] provides context for these access
contracts; see [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.NativeNumerics.WaterFilling

namespace Qatlib.Concepts.Waterfill.LevelFidelity
variable {m : ℕ} (π σ : Fin m → ℝ)
variable {m : ℕ} (π σ : Fin m → ℚ)

/-- The constant-one rational source table on a single coordinate, used for the zero-query
counterexample. -/
private def gext3CounterPi : Fin 1 → ℚ := fun _ => 1

/-- The constant-one rational target table on a single coordinate, used for the zero-query
counterexample. -/
private def gext3CounterSig : Fin 1 → ℚ := fun _ => 1

/-- Certifies `ReweightingSuccess` for the exact resampling word with fidelity `levelDot^2 /
levelMass` under normalization, nonnegativity, and positive mass. Its ledger has `2 * rounds
+ 1` source calls, `4 * rounds + 2` known macros, and zero data queries, with the stated
inverse-square-root mass bound. -/
theorem reweighting_exact_word_success {m D : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (h : ∀ i, 0 ≤ π i ∧ 0 ≤ σ i) (hγ : 0 ≤ γ)
    (hπ : (∑ i, (π i : ℝ) ^ 2) = 1) (hσ : (∑ i, (σ i : ℝ) ^ 2) = 1)
    (hmass : 0 < levelMass π σ γ) (j₀ : Fin m × Fin D) :
    ReweightingSuccess j₀ π σ γ (levelDot π σ γ ^ 2 / levelMass π σ γ)
        (resamplingExactWord π σ γ j₀) ∧
      wordLedger (resamplingExactWord π σ γ j₀) =
        ⟨2 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 1,
          4 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 2, 0⟩ ∧
      ((2 * resamplingExactRounds (Real.sqrt (levelMass π σ γ)) + 1 : ℕ) : ℝ)
        ≤ Real.pi / (2 * Real.sqrt (levelMass π σ γ)) + 2 := by
  set β := Real.sqrt (levelMass π σ γ)
  have hβ : 0 < β := Real.sqrt_pos_of_pos hmass
  have hβ1 : β ≤ 1 := Real.sqrt_le_one.mpr
    (resamplingLevelMass_le_one π σ γ h hγ hπ)
  have hsched := resamplingExactSchedule β hβ hβ1
  have hsuccess : ReweightingSuccess j₀ π σ γ (levelDot π σ γ ^ 2 / levelMass π σ γ)
      (resamplingExactWord π σ γ j₀) := by
    refine ⟨hmass, rfl, ?_⟩
    intro ξ U hξ hU hsource
    have hout := resamplingExactOutput_actual m D π σ γ h hγ hπ hσ hmass ξ U j₀ hξ hU hsource
    obtain ⟨_, hnorm, hprob, hover, _, _, _, _⟩ := hout
    have hdef : ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
        (resamplingExactWord π σ γ j₀)) (Ket (j₀, false))
        = resamplingExactOutput π σ γ U j₀ := rfl
    refine ⟨hnorm, hprob, ?_⟩
    show levelDot π σ γ ^ 2 / levelMass π σ γ ≤
      Complex.normSq (Inner (resamplingFamily (fun i => (σ i : ℝ)) ξ)
        (ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
          (resamplingExactWord π σ γ j₀)) (Ket (j₀, false))))
    rw [hdef, hover]
  have ha : 0 ≤ resamplingExactScale β := le_trans (by norm_num) hsched.1
  have ha1 : resamplingExactScale β ≤ 1 := hsched.2.1
  have hword := resamplingPaidWord_actual m D π σ γ (resamplingExactScale β) j₀
    (resamplingExactRounds β) h hγ ha ha1
  obtain ⟨_, hq, hdata, hfixed, _⟩ := hword
  have hledger : wordLedger (resamplingExactWord π σ γ j₀) =
      ⟨2 * resamplingExactRounds β + 1, 4 * resamplingExactRounds β + 2, 0⟩ := by
    unfold wordLedger
    rw [show resamplingExactWord π σ γ j₀ =
        resamplingPaidWord π σ γ (resamplingExactScale β) j₀ (resamplingExactRounds β) from rfl,
      hq, hfixed, hdata]
  refine ⟨hsuccess, hledger, ?_⟩
  simpa only [β] using! hsched.2.2.2.2.2.2.1

/-- Establishes `SourceQueryLowerBound` with `c = 1` and offset `C = 1 / sqrt(levelMass)`. These
instance-dependent constants cancel the displayed lower-bound expression to zero. -/
theorem sourceQueryLowerBound_instance_constants {m D : ℕ} (π σ : Fin m → ℚ) (γ p : ℝ)
    (_hmass : 0 < levelMass π σ γ) :
    SourceQueryLowerBound (D := D) π σ γ p 1 (1 / Real.sqrt (levelMass π σ γ)) := by
  refine ⟨by norm_num, div_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro j₀ W _
  have hcancel : (1 : ℝ) / Real.sqrt (levelMass π σ γ)
      - 1 / Real.sqrt (levelMass π σ γ) = 0 := by ring
  rw [hcancel]
  exact Nat.cast_nonneg _

/-- A successful reweighting word with zero source queries rules out
`FilteredGamma2LowerConsumer` at the same instance and parameters, provided the level mass
is positive. -/
theorem gext3_filtered_consumer_of_zero_query_word {m D : ℕ} (π σ : Fin m → ℚ) (γ p c cδ δ : ℝ)
    (hmass : 0 < levelMass π σ γ)
    {j₀ : Fin m × Fin D} {W : List (PreparedStep ((Fin m × Fin D) × Bool))}
    (hsucc : ReweightingSuccess j₀ π σ γ p W) (hzero : preparedInputQueries W = 0) :
    ¬ FilteredGamma2LowerConsumer (D := D) π σ γ p δ c cδ := by
  intro hcons
  obtain ⟨_, hc, _, _, hex⟩ := hcons
  obtain ⟨X, hX, hXd, n, R, input, ρ, τ, hemp, hge, _⟩ := hex
  obtain ⟨hρ, _, himb⟩ := hemp
  obtain ⟨C, T, hT, hTle, hunit, hgram⟩ := himb j₀ W hsucc
  have hT0 : T = 0 := by omega
  have hcert := gram_exact_state_conversion_filteredCert input ρ τ C hT hunit hρ hgram
  have hfg := filteredGamma2_le_of_gramFilteredCert hcert
  have hcert0 : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix τ)
      (gramFilterDelta input) (2 * T) := hcert
  rw [hT0] at hcert0 hfg
  simp only [Nat.cast_zero, mul_zero, ENNReal.ofReal_zero] at hcert0 hfg
  have hle : ENNReal.ofReal (c / Real.sqrt (levelMass π σ γ)) ≤ 0 := le_trans hge hfg
  have hpos : 0 < c / Real.sqrt (levelMass π σ γ) :=
    div_pos hc (Real.sqrt_pos_of_pos hmass)
  have hpos' : (0 : ENNReal) < ENNReal.ofReal (c / Real.sqrt (levelMass π σ γ)) :=
    ENNReal.ofReal_pos.mpr hpos
  exact absurd (lt_of_lt_of_le hpos' hle) (lt_irrefl _)

/-- Refutes the filtered lower-bound consumer for the one-coordinate constant-one source and
target with ancillary dimension one, level and fidelity one, zero error, and unit constants. -/
theorem gext3_filtered_consumer_refutable :
    ¬ FilteredGamma2LowerConsumer (D := 1) gext3CounterPi gext3CounterSig (1:ℝ) 1
        (0:ℝ) 1 1 := by
  have hmass : 0 < levelMass gext3CounterPi gext3CounterSig (1:ℝ) := by
    have hm : levelMass gext3CounterPi gext3CounterSig (1:ℝ) = 1 := by
      unfold levelMass levelFill gext3CounterPi gext3CounterSig
      rw [Fin.sum_univ_one]
      norm_num
    rw [hm]; norm_num
  have hsucc : ReweightingSuccess (D := 1) ((0, 0) : Fin 1 × Fin 1)
      gext3CounterPi gext3CounterSig (1:ℝ) 1
      (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool))) := by
    have hm : levelMass gext3CounterPi gext3CounterSig (1:ℝ) = 1 := by
      unfold levelMass levelFill gext3CounterPi gext3CounterSig
      rw [Fin.sum_univ_one]
      norm_num
    have hd : levelDot gext3CounterPi gext3CounterSig (1:ℝ) = 1 := by
      unfold levelDot levelFill gext3CounterPi gext3CounterSig
      rw [Fin.sum_univ_one]
      norm_num
    refine ⟨hmass, by rw [hd, hm]; norm_num, ?_⟩
    intro ξ U hξ hU _
    have heval : (evaluatePrepared 1 (resamplingEmbeddedOracle U)
        (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool)))) = 1 := rfl
    have hout : ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
        (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool)))) (Ket ((0, 0), false))
        = Ket ((0, 0), false) := by
      rw [heval]
      exact Matrix.one_mulVec _
    refine ⟨?_, ?_, ?_⟩
    · rw [hout]
      exact normalized_ket _
    · rw [hout]
      show (∑ i ∈ waterEvent 1 1, BornProb (Ket ((0, 0), false)) i) = 0
      apply Finset.sum_eq_zero
      intro p hp
      have hb : p.2 = true := (Finset.mem_filter.mp hp).2
      have hne : p ≠ ((0, 0), false) := by
        intro hh
        rw [hh] at hb
        simp at hb
      simp [BornProb, Ket, hne]
    · have hinner : Inner (resamplingFamily (fun i => (gext3CounterSig i : ℝ)) ξ)
          (Ket ((0, 0), false)) = (starRingEnd ℂ) (ξ 0 0) := by
        rw [inner_apply]
        have hket : ∀ p : ((Fin 1 × Fin 1) × Bool),
            Ket ((0, 0), false) p = if p = ((0, 0), false) then 1 else 0 := fun _ => rfl
        conv_lhs => simp only [hket, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, if_true]
        simp [resamplingFamily, gext3CounterSig]
      have hnorm : Complex.normSq (ξ 0 0) = 1 := by
        have h := hξ 0
        have hsum : (∑ d : Fin 1, ‖(ξ 0) d‖ ^ 2) = 1 := h
        rw [Fin.sum_univ_one] at hsum
        rw [Complex.normSq_eq_norm_sq]
        exact hsum
      rw [hout, hinner]
      show (1:ℝ) ≤ Complex.normSq ((starRingEnd ℂ) (ξ 0 0))
      have hconj : Complex.normSq ((starRingEnd ℂ) (ξ 0 0)) = Complex.normSq (ξ 0 0) :=
        Complex.normSq_conj _
      rw [hconj, hnorm]
  exact gext3_filtered_consumer_of_zero_query_word gext3CounterPi gext3CounterSig (1:ℝ) 1
    1 1 0 hmass hsucc (by
      show preparedInputQueries (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool))) = 0
      rfl)
end Qatlib.Concepts.Waterfill.LevelFidelity
