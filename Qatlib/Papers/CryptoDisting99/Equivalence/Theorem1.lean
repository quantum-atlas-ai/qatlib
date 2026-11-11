/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition1.Proposition1HelstromError
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition1.HelstromAchievability
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition2
import Qatlib.Papers.CryptoDisting99.Equivalence.Proposition5.Proposition5ClassicalInequalities
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance

/-!
# Quantum distinguishability bounds

This module proves quantum distinguishability bounds for density operators. It combines
trace-distance and root-fidelity inequalities with bounds on the Shannon distinguishability of
finite POVM outcome laws.

These constructions accompany the results of [FuchsVanDeGraaf1999].

## Main statements

* `theorem1_trace_fidelity_bounds`: gives the two trace-distance bounds in terms of root
  fidelity.
* `theorem1_shannon_upper`: bounds quantum Shannon distinguishability by trace distance.
* `theorem1_entropy_lower`: gives a binary-entropy lower bound for quantum Shannon
  distinguishability.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Matrix
open scoped BigOperators

/-- For density operators, trace distance lies between one minus root fidelity and the square
root of one minus squared root fidelity, as in Theorem 1 of [FuchsVanDeGraaf1999]. -/
theorem theorem1_trace_fidelity_bounds {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 - Froot ρ σ ≤ traceDistance ρ σ ∧
      traceDistance ρ σ ≤ Real.sqrt (1 - (Froot ρ σ) ^ 2) :=
  (Qatlib.Concepts.MixedFidelity.FidelityMetric.g3 D ρ σ hρ hσ).1

/-- The Shannon distinguishability of the outcome laws of a finite POVM is bounded above by the
trace distance of the input density operators. -/
lemma shannonDist_povmRecordLaw_le_traceDistance {D m : ℕ} (E : FinitePOVM (Fin m) D)
    (ρ σ : Operator D) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) ≤ traceDistance ρ σ := by
  have h44 := proposition5_44_right
    (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)
  have h2 := proposition2_error_eq_kolmogorov
    (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)
  have htv := Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le
    E ρ σ hρ hσ
  unfold classicalKolmogorov traceDistance at *
  linarith

/-- Quantum Shannon distinguishability is bounded above by trace distance, as in Theorem 1 of
[FuchsVanDeGraaf1999]. -/
theorem theorem1_shannon_upper {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    quantumShannon ρ σ hρ hσ ≤ traceDistance ρ σ := by
  apply csSup_le
  · exact ⟨shannonDist
      (povmRecordLaw (trivialPOVM D) ρ hρ) (povmRecordLaw (trivialPOVM D) σ hσ),
      1, trivialPOVM D, rfl⟩
  · intro b hb
    obtain ⟨m, E, rfl⟩ := hb
    exact shannonDist_povmRecordLaw_le_traceDistance E ρ σ hρ hσ

/-- One minus quantum Bhattacharyya overlap is bounded above by quantum Shannon
distinguishability, as in Theorem 1 of [FuchsVanDeGraaf1999]. -/
theorem theorem1_bhattacharyya_shannon {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 - quantumBhattacharyya ρ σ hρ hσ ≤ quantumShannon ρ σ hρ hσ := by
  unfold quantumShannon quantumBhattacharyya
  have hne : ({ x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
      x = bhattacharyya (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }).Nonempty :=
    ⟨_, 1, trivialPOVM D, rfl⟩
  have hbdd : BddAbove ({ x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
      x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }) :=
    ⟨1, by
      intro b hb
      obtain ⟨m, E, rfl⟩ := hb
      exact shannonDist_le_one (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)⟩
  have hkey : 1 - sSup ({ x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
      x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }) ≤
      sInf ({ x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
        x = bhattacharyya (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) }) := by
    apply le_csInf hne
    intro b hb
    obtain ⟨m, E, rfl⟩ := hb
    have h45 := proposition5_45_left (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)
    have hsup :=
        le_csSup hbdd
        (show shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) ∈ _ from ⟨m, E, rfl⟩)
    linarith
  linarith

/-- Quantum Shannon distinguishability is at least one minus the binary entropy of half of one
minus trace distance, as in Theorem 1 of [FuchsVanDeGraaf1999]. -/
theorem theorem1_entropy_lower {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    1 - binaryEntropy (1 / 2 - traceDistance ρ σ / 2) ≤ quantumShannon ρ σ hρ hσ := by
  obtain ⟨E, htv⟩ := helstrom_recordLaw_tv ρ σ hρ hσ
  unfold quantumShannon
  have h44 := proposition5_44_left (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)
  have hPE : classicalErrProb (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) =
      1 / 2 - traceDistance ρ σ / 2 := by
    rw [proposition2_error_eq_kolmogorov, htv]
  rw [hPE] at h44
  have hbdd : BddAbove { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
      x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) } := by
    refine ⟨1, ?_⟩
    rintro x ⟨m, E', rfl⟩
    exact shannonDist_le_one (povmRecordLaw E' ρ hρ) (povmRecordLaw E' σ hσ)
  have hmem := le_csSup hbdd (show
    shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) ∈
      { x : ℝ | ∃ (m : ℕ) (E : FinitePOVM (Fin m) D),
        x = shannonDist (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ) } from ⟨2, E, rfl⟩)
  linarith

end Qatlib.Papers.CryptoDisting99.Equivalence
