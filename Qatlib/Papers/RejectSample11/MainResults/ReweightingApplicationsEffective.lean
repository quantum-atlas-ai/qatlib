/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RejectSample11.MainResults.ReweightingApplicationsEffectiveDefs
import Qatlib.Concepts.Waterfill.LevelFidelity.AccessReweighting

/-!
# Effective Fourier reweighting guarantees

Specializes exact resampling to rational Fourier magnitudes and a flat target profile. Under
normalization, positivity, and positive filled mass, the result identifies the clipped profile,
gives conditional success and resource formulas, and shows that the output retains the supplied
family of hidden states. See [OzolsRoettelerRoland2013].

## Main statements

* `gext4_complete`: combines clipping, conditional exact-word resource formulas, and
  preservation of the hidden-state family.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Papers.RejectSample11.MainResults

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open Qatlib
open Qatlib.Papers.RejectSample11.MainResults
open scoped BigOperators ComplexOrder ENNReal

/-- For normalized rational Fourier magnitudes and a positive normalized flat target with
nonnegative level and positive filled mass, identifies the clipped profile and derives
success and query/gate formulas from `ReweightingSuccess` of the exact word. A unitary
preparation of the normalized hidden-state family yields an output with real reweighting
coefficients on that same family [OzolsRoettelerRoland2013]. -/
theorem gext4_complete :
    ∀ (n D : ℕ) (fHat : Fin (2 ^ n) → ℚ) (c : ℚ) (γ p : ℝ)
      (j₀ : Fin (2 ^ n) × Fin D),
      0 < c → 0 ≤ γ →
      (∑ w : Fin (2 ^ n), |(fHat w : ℝ)| ^ 2) = 1 →
      (∑ _w : Fin (2 ^ n), (c : ℝ) ^ 2) = 1 →
      0 < levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ →

      (∀ w, levelFill (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ w
        = min |(fHat w : ℝ)| (γ * (c : ℝ))) ∧

      (ReweightingSuccess j₀ (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ p
          (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) →
        p = levelDot (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ ^ 2 /
              levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ ∧
        preparedInputQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) =
          2 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 1 ∧
        (preparedInputQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) : ℝ) ≤
          Real.pi / (2 * Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2 ∧
        preparedDataQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) = 0 ∧
        preparedFixedGates (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) =
          4 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2) ∧

      (∀ (U : Matrix (Fin (2 ^ n) × Fin D) (Fin (2 ^ n) × Fin D) ℂ)
        (ξ : Fin (2 ^ n) → QState (Fin D)),
        (∀ i, Normalized (ξ i)) → U ∈ Matrix.unitaryGroup _ ℂ →
        U *ᵥ Ket j₀ = waterSource (bhspPiQ fHat) ξ →
        ∃ v : Fin (2 ^ n) → ℝ,
          resamplingExactOutput (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ U j₀ = resamplingFamily v ξ) := by
  intro n D fHat c γ p j₀ hc hγ hπ hσ hmass

  have hclip : ∀ w, levelFill (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ w
      = min |(fHat w : ℝ)| (γ * (c : ℝ)) := by
    intro w
    unfold bhspPiQ flatSigmaQ levelFill
    have hcw : (fun x : Fin (2 ^ n) => c) w = c := rfl
    rw [hcw, Rat.cast_abs]

  have htab : ∀ i, 0 ≤ bhspPiQ fHat i ∧ 0 ≤ flatSigmaQ (2 ^ n) c i := by
    intro i
    constructor
    · simp [bhspPiQ]
    · simp [flatSigmaQ]; positivity
  have hπ' : (∑ i, (bhspPiQ fHat i : ℝ) ^ 2) = 1 := by
    have hsum : (∑ i, (bhspPiQ fHat i : ℝ) ^ 2) = ∑ w : Fin (2 ^ n), |(fHat w : ℝ)| ^ 2 := by
      apply Finset.sum_congr rfl; intro w _
      simp [bhspPiQ, Rat.cast_abs]
    calc (∑ i, (bhspPiQ fHat i : ℝ) ^ 2) = ∑ w : Fin (2 ^ n), |(fHat w : ℝ)| ^ 2 := hsum
      _ = 1 := hπ
  have hσ' : (∑ i, (flatSigmaQ (2 ^ n) c i : ℝ) ^ 2) = 1 := by
    have hsum : (∑ i, (flatSigmaQ (2 ^ n) c i : ℝ) ^ 2) = ∑ _w : Fin (2 ^ n), (c : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl; intro w _
      simp [flatSigmaQ]
    calc (∑ i, (flatSigmaQ (2 ^ n) c i : ℝ) ^ 2) = ∑ _w : Fin (2 ^ n), (c : ℝ) ^ 2 := hsum
      _ = 1 := hσ

  have hword := reweighting_exact_word_success (m := 2 ^ n) (D := D)
    (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ htab hγ hπ' hσ' hmass j₀
  obtain ⟨hsucc, hledger, hbudget⟩ := hword
  have hq : preparedInputQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀)
      = 2 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 1 := by
    have hsrc := congrArg SourceCostLedger.sourceCalls hledger
    simpa [wordLedger] using! hsrc
  have hg : preparedFixedGates (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀)
      = 4 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2 := by
    have hmac := congrArg SourceCostLedger.knownMacros hledger
    simpa [wordLedger] using! hmac
  have hd : preparedDataQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) = 0 := by
    have hdat := congrArg SourceCostLedger.dataQueries hledger
    simpa [wordLedger] using! hdat
  have hcarry : ReweightingSuccess j₀ (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ p
      (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) →
      p = levelDot (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ ^ 2 /
            levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ ∧
        preparedInputQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) =
          2 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 1 ∧
        (preparedInputQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) : ℝ) ≤
          Real.pi / (2 * Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2 ∧
        preparedDataQueries (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) = 0 ∧
        preparedFixedGates (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) =
          4 * resamplingExactRounds (Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2 := by
    intro h
    have hp : p = levelDot (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ ^ 2 /
        levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ := by
      rw [← h.2.1]
    have hbud : (preparedInputQueries
          (resamplingExactWord (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ j₀) : ℝ) ≤
        Real.pi / (2 * Real.sqrt (levelMass (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ)) + 2 :=
      by simpa [hq] using! hbudget
    exact ⟨hp, hq, hbud, hd, hg⟩

  have hdisc : ∀ (U : Matrix (Fin (2 ^ n) × Fin D) (Fin (2 ^ n) × Fin D) ℂ)
      (ξ : Fin (2 ^ n) → QState (Fin D)),
      (∀ i, Normalized (ξ i)) → U ∈ Matrix.unitaryGroup _ ℂ →
      U *ᵥ Ket j₀ = waterSource (bhspPiQ fHat) ξ →
      ∃ v : Fin (2 ^ n) → ℝ,
        resamplingExactOutput (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ U j₀ = resamplingFamily v ξ := by
    intro U ξ hξ hU hsource
    have := hidden_state_discipline (m := 2 ^ n) (D := D) (bhspPiQ fHat) (flatSigmaQ (2 ^ n) c) γ
      U j₀ ξ htab hγ hπ' hσ' hmass hξ hU hsource
    exact this
  exact ⟨hclip, hcarry, hdisc⟩

end Qatlib.Papers.RejectSample11.MainResults
