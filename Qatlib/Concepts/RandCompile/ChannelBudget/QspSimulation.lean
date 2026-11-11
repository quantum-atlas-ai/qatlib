/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.QspSimulationDefs

/-!
# Quantum signal processing simulation and resource bounds

This module proves Jacobi-Anger approximation bounds and a constant-factor comparison between
`jaCount` and `jaIdealShape`, in the Hamiltonian simulation setting of [LowChuang2017]. It also
verifies finite phase-search ledgers and compiles sparse simulation words from phase data.

The sparse embedding results provide normalized projected unitary encodings and block encodings,
within the broader framework of [GilyenSuLowWiebe2019]. The phase-search results expose the
actual search counters and their relation to the separately defined inversion-cost bound.

## Main statements

* `jaCount_near_optimal`: combines the count comparison and approximation-tail bound.
* `honestPhaseRun_packet`: extracts unit-modulus phase data with a uniform approximation
  guarantee.
* `effective_block_encoding`: constructs a normalized sparse block encoding.
* `sparseSimulationLedger_spec`: identifies circuit and phase-search resource fields.

## References

* [Low and Chuang, 2017][LowChuang2017]
* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix
open Polynomial
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The clipped Jacobi-Anger accuracy is positive when `ε` is positive. -/
theorem jaAccuracy_pos (ε : ℝ) (hε : 0 < ε) : 0 < jaAccuracy ε := by
  unfold jaAccuracy
  exact lt_min hε (by norm_num)

/-- The clipped Jacobi-Anger accuracy is at most one. -/
theorem jaAccuracy_le_one (ε : ℝ) : jaAccuracy ε ≤ 1 := by
  unfold jaAccuracy
  exact min_le_right _ _

/-- For positive `ε`, the clipped Jacobi-Anger accuracy is at most `ε`. -/
theorem jaAccuracy_le_eps (ε : ℝ) (hε : 0 < ε) : jaAccuracy ε ≤ ε := by
  unfold jaAccuracy
  exact min_le_left _ _

/-- The Jacobi-Anger logarithmic budget is positive for positive `ε`. -/
theorem jaLogBudget_pos (ε : ℝ) (hε : 0 < ε) : 0 < jaLogBudget ε := by
  have hpos : 0 < jaAccuracy ε := jaAccuracy_pos ε hε
  have hle : jaAccuracy ε ≤ 1 := jaAccuracy_le_one ε
  have hge : (32 : ℝ) ≤ 32 / jaAccuracy ε := by
    have h1 : (32 : ℝ) * jaAccuracy ε ≤ 32 * 1 :=
      mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 32)
    exact (le_div_iff₀ hpos).mpr (by simpa using! h1)
  unfold jaLogBudget
  exact Real.log_pos (lt_of_lt_of_le (by norm_num) hge)

/-- The logarithmic denominator in the Jacobi-Anger shape is positive for positive `ε`. -/
theorem jaShapeDen_pos (τ ε : ℝ) (hε : 0 < ε) :
    0 < Real.log (1 + jaLogBudget ε / max τ 1) := by
  have hL : 0 < jaLogBudget ε := jaLogBudget_pos ε hε
  have hmax : (1 : ℝ) ≤ max τ 1 := le_max_right _ _
  have hu : 0 < jaLogBudget ε / max τ 1 :=
    div_pos hL (lt_of_lt_of_le (by norm_num) hmax)
  exact Real.log_pos (by linarith)

/-- The selected Jacobi-Anger count is at least four. -/
theorem jaCount_ge_four (τ ε : ℝ) : 4 ≤ jaCount τ ε := by
  unfold jaCount
  exact le_trans (le_max_left 4 _) (le_max_right _ _)

/-- The selected Jacobi-Anger count, viewed as a real number, is at least `τ + 1`. -/
theorem jaCount_ge_time (τ ε : ℝ) : τ + 1 ≤ (jaCount τ ε : ℝ) := by
  unfold jaCount
  exact lcCorrectedQ_length_budget τ (jaAccuracy ε)

/-- On `JaDomain`, the factorial tail evaluated at `jaCount τ ε` is at most `ε / 8`. -/
theorem jaCount_tail (τ ε : ℝ) (h : JaDomain τ ε) :
    4 * τ ^ (jaCount τ ε : ℝ) /
        (2 ^ (jaCount τ ε : ℝ) * (jaCount τ ε).factorial : ℝ) ≤ ε / 8 := by
  obtain ⟨hτ, hε⟩ := h
  have hε' : 0 < jaAccuracy ε := jaAccuracy_pos ε hε
  have htail :=
    (jacobiAngerCorrectedDegree τ (jaAccuracy ε) hτ hε' (jaAccuracy_le_one ε)).1
  unfold jaCount at htail ⊢
  have hstep : jaAccuracy ε / 8 ≤ ε / 8 :=
    div_le_div_of_nonneg_right (jaAccuracy_le_eps ε hε) (by norm_num)
  exact htail.trans hstep

/-- On `JaDomain`, there exist even and odd real polynomials with the stated degree bounds whose
uniform Jacobi-Anger error is bounded by the factorial tail. -/
theorem jaCount_pair (τ ε : ℝ) (h : JaDomain τ ε) :
    ∃ (A Qt : Polynomial ℝ),
      A.comp (-X) = A ∧ Qt.comp (-X) = -Qt ∧
      A.degree ≤ ((2 * (jaCount τ ε - 1) : ℕ) : WithBot ℕ) ∧
      Qt.degree < ((2 * (jaCount τ ε - 1) : ℕ) : WithBot ℕ) ∧
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        jaError A Qt τ θ ≤ 4 * τ ^ (jaCount τ ε : ℝ) /
          (2 ^ (jaCount τ ε : ℝ) * (jaCount τ ε).factorial : ℝ)) := by
  obtain ⟨hτ, hε⟩ := h
  have hq1 : 1 ≤ jaCount τ ε := by
    have h4 := jaCount_ge_four τ ε
    omega
  have hlen := jaCount_ge_time τ ε
  have hle : τ ≤ ((jaCount τ ε - 1 : ℕ) : ℝ) := by
    have hcast : ((jaCount τ ε - 1 : ℕ) : ℝ) = (jaCount τ ε : ℝ) - 1 :=
      Nat.cast_pred (by
        have h4 := jaCount_ge_four τ ε
        omega)
    rw [hcast]
    linarith
  exact jacobiAngerTruncation (jaCount τ ε) τ hq1 hτ hle

/-- On `JaDomain`, the ideal count shape is at most the selected Jacobi-Anger count. -/
theorem jaCount_shape_lower (τ ε : ℝ) (h : JaDomain τ ε) :
    jaIdealShape τ ε ≤ (jaCount τ ε : ℝ) := by
  obtain ⟨hτ, hε⟩ := h
  have hD0 : 0 < Real.log (1 + jaLogBudget ε / max τ 1) := jaShapeDen_pos τ ε hε
  set L : ℝ := jaLogBudget ε with hLdef
  set D : ℝ := Real.log (1 + L / max τ 1) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact hD0
  have hL : L = Real.log (32 / jaAccuracy ε) := by
    rw [hLdef]
    unfold jaLogBudget jaAccuracy
    rfl
  have hQ4 : 4 ≤ lcCorrectedQ τ (jaAccuracy ε) := by
    unfold lcCorrectedQ
    exact le_trans (le_max_left 4 _) (le_max_right _ _)
  have hQτ : 3 * τ ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
    have hmax : ⌈3 * τ⌉₊ + 1 ≤ lcCorrectedQ τ (jaAccuracy ε) := by
      unfold lcCorrectedQ
      exact le_max_left _ _
    have hmax' : (⌈3 * τ⌉₊ + 1 : ℝ) ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
      exact_mod_cast hmax
    have hceil : 3 * τ ≤ (⌈3 * τ⌉₊ : ℝ) := by
      exact_mod_cast (Nat.le_ceil (3 * τ))
    linarith
  have hQLceil : ⌈3 * L / D⌉₊ + 1 ≤ lcCorrectedQ τ (jaAccuracy ε) := by
    have hraw : ⌈3 * Real.log (32 / jaAccuracy ε) /
        Real.log (1 + Real.log (32 / jaAccuracy ε) / max τ 1)⌉₊ + 1
        ≤ lcCorrectedQ τ (jaAccuracy ε) := by
      unfold lcCorrectedQ
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    rw [← hL, ← hDdef] at hraw
    exact hraw
  have hQLceil' : (⌈3 * L / D⌉₊ + 1 : ℝ) ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
    exact_mod_cast hQLceil
  have hceil : 3 * L / D ≤ (⌈3 * L / D⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (3 * L / D))
  have hQL : 3 * L / D ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
    have h2 : (⌈3 * L / D⌉₊ : ℝ) ≤ (⌈3 * L / D⌉₊ + 1 : ℝ) := by norm_num
    linarith
  have hshape : jaIdealShape τ ε = τ + 1 + L / D := by
    unfold jaIdealShape
    have hL' : Real.log (32 / min ε 1) = L := by
      have hLL : L = Real.log (32 / min ε 1) := by
        rw [hLdef]
        unfold jaLogBudget jaAccuracy
        rfl
      exact hLL.symm
    rw [hL', ← hDdef]
  rw [hshape]
  unfold jaCount
  have h1 : 3 * (τ + 1 + L / D) = 3 * τ + 3 + 3 * L / D := by ring
  have h2 : 3 * τ + 3 + 3 * L / D ≤ 3 * τ + 4 + 3 * L / D := by linarith
  have h3 : 3 * τ + 4 + 3 * L / D ≤ 3 * (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
    have hτ' : 3 * τ ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := hQτ
    have h4 : 4 ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by exact_mod_cast hQ4
    have hL' : 3 * L / D ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := hQL
    linarith
  linarith

/-- On `JaDomain`, the selected Jacobi-Anger count is at most eleven times the ideal shape. -/
theorem jaCount_shape_upper (τ ε : ℝ) (h : JaDomain τ ε) :
    (jaCount τ ε : ℝ) ≤ 11 * jaIdealShape τ ε := by
  obtain ⟨hτ, hε⟩ := h
  have hε' : 0 < jaAccuracy ε := jaAccuracy_pos ε hε
  have hupper := lcCorrectedQ_upper τ (jaAccuracy ε) hτ hε' (jaAccuracy_le_one ε)
  unfold jaCount
  have hshape : jaIdealShape τ ε
      = τ + 1 + Real.log (32 / jaAccuracy ε) /
        Real.log (1 + Real.log (32 / jaAccuracy ε) / max τ 1) := by
    unfold jaIdealShape jaAccuracy
    rfl
  rw [hshape]
  exact hupper

/-- On `JaDomain`, the selected count lies between the ideal shape and eleven times that shape,
and its factorial tail is at most `ε / 8`. -/
theorem jaCount_near_optimal (τ ε : ℝ) (h : JaDomain τ ε) :
    jaIdealShape τ ε ≤ (jaCount τ ε : ℝ) ∧
      (jaCount τ ε : ℝ) ≤ 11 * jaIdealShape τ ε ∧
      4 * τ ^ (jaCount τ ε : ℝ) /
          (2 ^ (jaCount τ ε : ℝ) * (jaCount τ ε).factorial : ℝ) ≤ ε / 8 := by
  exact ⟨jaCount_shape_lower τ ε h, jaCount_shape_upper τ ε h, jaCount_tail τ ε h⟩

/-- For positive `ε`, zero time has an even-odd polynomial pair satisfying the selected degree
bounds and having zero Jacobi-Anger error on `[0, 2π]`. -/
theorem jaCount_zero_time (ε : ℝ) (hε : 0 < ε) :
    ∃ (A Qt : Polynomial ℝ),
      A.comp (-X) = A ∧ Qt.comp (-X) = -Qt ∧
      A.degree ≤ ((2 * (jaCount 0 ε - 1) : ℕ) : WithBot ℕ) ∧
      Qt.degree < ((2 * (jaCount 0 ε - 1) : ℕ) : WithBot ℕ) ∧
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi), jaError A Qt 0 θ = 0) := by
  have hq1 : 1 ≤ jaCount 0 ε := by
    have h4 := jaCount_ge_four 0 ε
    omega
  have hlen := jaCount_ge_time 0 ε
  have hle : (0 : ℝ) ≤ ((jaCount 0 ε - 1 : ℕ) : ℝ) := by
    have hcast : ((jaCount 0 ε - 1 : ℕ) : ℝ) = (jaCount 0 ε : ℝ) - 1 :=
      Nat.cast_pred (by
        have h4 := jaCount_ge_four 0 ε
        omega)
    rw [hcast]
    linarith
  obtain ⟨A, Qt, hA, hQt, hdegA, hdegQt, herr⟩ :=
    jacobiAngerTruncation (jaCount 0 ε) (0 : ℝ) hq1 (by norm_num) hle
  refine ⟨A, Qt, hA, hQt, hdegA, hdegQt, ?_⟩
  intro θ hθ
  have hzero : (4 * (0 : ℝ) ^ (jaCount 0 ε : ℝ) /
      (2 ^ (jaCount 0 ε : ℝ) * (jaCount 0 ε).factorial : ℝ)) = 0 := by
    have h4 := jaCount_ge_four 0 ε
    have h4' : (4 : ℝ) ≤ (jaCount 0 ε : ℝ) := by exact_mod_cast h4
    have hne : (jaCount 0 ε : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (jaCount 0 ε : ℝ) := by linarith
      exact ne_of_gt hpos
    rw [Real.zero_rpow hne, mul_zero, zero_div]
  have hbound := herr θ hθ
  rw [hzero] at hbound
  exact le_antisymm hbound (norm_nonneg _)

/-- For `0 ≤ τ ≤ 1` and positive `ε`, the selected count equals the stated ceiling formula
depending only on the logarithmic accuracy budget. -/
theorem jaCount_small_time (ε : ℝ) (hε : 0 < ε) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    jaCount τ ε = max 4 (⌈3 * jaLogBudget ε / Real.log (1 + jaLogBudget ε)⌉₊ + 1) := by
  have hmax : max τ 1 = 1 := max_eq_right hτ1
  have hceil : ⌈3 * τ⌉₊ < 4 := by
    have h1 : (3 * τ : ℝ) ≤ 3 := by linarith [hτ1]
    have h2 : (⌈3 * τ⌉₊ : ℝ) < 3 * τ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : (⌈3 * τ⌉₊ : ℝ) < 4 := by linarith
    exact_mod_cast h3
  have hbranch : ⌈3 * τ⌉₊ + 1 ≤ 4 := by omega
  unfold jaCount
  unfold lcCorrectedQ
  rw [hmax]
  have hbranch' : ⌈3 * τ⌉₊ + 1 ≤ max 4 (⌈3 * Real.log (32 / jaAccuracy ε) /
      Real.log (1 + Real.log (32 / jaAccuracy ε) / 1)⌉₊ + 1) :=
    le_trans hbranch (le_max_left _ _)
  rw [max_eq_right hbranch']
  have h1 : Real.log (32 / jaAccuracy ε) = jaLogBudget ε := by
    unfold jaLogBudget jaAccuracy
    rfl
  rw [h1]
  have h2 : Real.log (1 + jaLogBudget ε / 1) = Real.log (1 + jaLogBudget ε) := by
    congr 1
    simp
  rw [h2]

/-- For `τ ≥ 1` and positive `ε`, the selected count is at least `3 * τ`. -/
theorem jaCount_large_time (τ ε : ℝ) (hε : 0 < ε) (hτ : (1 : ℝ) ≤ τ) :
    3 * τ ≤ (jaCount τ ε : ℝ) := by
  have hmax : ⌈3 * τ⌉₊ + 1 ≤ lcCorrectedQ τ (jaAccuracy ε) := by
    unfold lcCorrectedQ
    exact le_max_left _ _
  have hmax' : (⌈3 * τ⌉₊ + 1 : ℝ) ≤ (lcCorrectedQ τ (jaAccuracy ε) : ℝ) := by
    exact_mod_cast hmax
  have hceil : 3 * τ ≤ (⌈3 * τ⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (3 * τ))
  unfold jaCount
  linarith

/-- The honest phase-run ledger records the exact number of words tested by finite phase
synthesis. -/
theorem honestPhaseRun_tested (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).ledger.testedWords = (finitePhaseSynthesis p d eps).tested := by
  rfl

/-- The honest phase-run ledger records the coefficient visits of finite phase synthesis. -/
theorem honestPhaseRun_visits (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).ledger.coefficientVisits =
      (finitePhaseSynthesis p d eps).coefficientVisits := by
  rfl

/-- The honest phase-run ledger records the response rounds of finite phase synthesis. -/
theorem honestPhaseRun_rounds (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).ledger.responseRounds =
      (finitePhaseSynthesis p d eps).responseRounds := by
  rfl

/-- The honest phase-run ledger records the backend calls of finite phase synthesis. -/
theorem honestPhaseRun_backends (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).ledger.backendCalls =
      (finitePhaseSynthesis p d eps).backendCalls := by
  rfl

/-- The honest phase-run ledger records the table multiplications of finite phase synthesis. -/
theorem honestPhaseRun_tables (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).ledger.tableMultiplications =
      (finitePhaseSynthesis p d eps).tableMultiplications := by
  rfl

/-- The honest phase run returns the same value as finite phase synthesis. -/
theorem honestPhaseRun_value (p : List ℚ) (d : ℕ) (eps : ℚ) :
    (honestPhaseRun p d eps).value = (finitePhaseSynthesis p d eps).value := by
  rfl

/-- Searching a nonempty list of candidate words tests at least one word. -/
private theorem findGridWord_tested_pos (p : List ℚ) (d : ℕ) (tol : ℚ)
    (points : List GaussianRat) :
    ∀ words : List (List ℕ), words ≠ [] → 1 ≤ (findGridWord p d tol points words).tested := by
  intro words
  induction words with
  | nil => intro h; exact absurd h (by simp)
  | cons w tail ih =>
    intro _
    simp only [findGridWord]
    split
    · simp
    · have h1 : 1 ≤ (findGridWord p d tol points tail).tested + 1 := by omega
      exact h1

/-- If the initial constant phase candidate fails its score tolerance, the honest phase run
tests at least two words. -/
theorem honestPhaseRun_search_tested (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hnot : ¬ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 ≤
      (1 / 2 : ℚ) ^ phaseToleranceBits eps) :
    2 ≤ (honestPhaseRun p d eps).ledger.testedWords := by
  have hlen : (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1)).length
      = (2 ^ phaseGridBits d (phaseToleranceBits eps)) ^ (d + 1) :=
    gridWords_length _ _
  have hne : (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1)) ≠ [] := by
    intro hc
    have hz : (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1)).length = 0 := by
      rw [hc]
      rfl
    rw [hlen] at hz
    have hpos : 0 < (2 ^ phaseGridBits d (phaseToleranceBits eps)) ^ (d + 1) := by
      positivity
    omega
  have hpos := findGridWord_tested_pos p d ((1 / 2 : ℚ) ^ phaseToleranceBits eps)
    (phaseTable (numericalDyadicPhase (phaseGridBits d (phaseToleranceBits eps)) false
      (phaseBackendBits d (phaseToleranceBits eps)))
      (2 ^ phaseGridBits d (phaseToleranceBits eps))).1
    (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1)) hne
  have htested : (finitePhaseSynthesis p d eps).tested
      = (findGridWord p d ((1 / 2 : ℚ) ^ phaseToleranceBits eps)
          (phaseTable (numericalDyadicPhase (phaseGridBits d (phaseToleranceBits eps)) false
            (phaseBackendBits d (phaseToleranceBits eps)))
            (2 ^ phaseGridBits d (phaseToleranceBits eps))).1
          (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1))).tested + 1 := by
    simp only [finitePhaseSynthesis, hnot, if_false]
  have hledger : (honestPhaseRun p d eps).ledger.testedWords
      = (findGridWord p d ((1 / 2 : ℚ) ^ phaseToleranceBits eps)
          (phaseTable (numericalDyadicPhase (phaseGridBits d (phaseToleranceBits eps)) false
            (phaseBackendBits d (phaseToleranceBits eps)))
            (2 ^ phaseGridBits d (phaseToleranceBits eps))).1
          (gridWords (2 ^ phaseGridBits d (phaseToleranceBits eps)) (d + 1))).tested + 1 := by
    rw [honestPhaseRun_tested]
    exact htested
  rw [hledger]
  omega

/-- For legal phase inversion, response rounds and coefficient visits equal tested words times
`d` and `d + 1`, respectively, and at least one word is tested. -/
theorem honestPhaseRun_counters (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    (honestPhaseRun p d eps).ledger.responseRounds =
        (honestPhaseRun p d eps).ledger.testedWords * d ∧
      (honestPhaseRun p d eps).ledger.coefficientVisits =
        (honestPhaseRun p d eps).ledger.testedWords * (d + 1) ∧
      1 ≤ (honestPhaseRun p d eps).ledger.testedWords := by
  obtain ⟨hε, hd, hpar, hbound⟩ := hleg
  obtain ⟨data, hval, hlen, hbase, hphases, hscore, happ, htested, htestedle,
    hrounds, hvisits, hbackend⟩ :=
    finite_rational_phase_synthesis_terminates p d eps hε hd hpar hbound
  refine ⟨?_, ?_, ?_⟩
  · rw [honestPhaseRun_rounds]
    exact hrounds
  · rw [honestPhaseRun_visits]
    exact hvisits
  · rw [honestPhaseRun_tested]
    exact htested

/-- Legal phase inversion returns `d` unit-modulus phases and a unit-modulus base satisfying the
score tolerance and uniform real-response error at most `eps` on `[-1, 1]`. -/
theorem honestPhaseRun_packet (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    ∃ data : PhaseData,
      (honestPhaseRun p d eps).value = some data ∧
        data.phases.length = d ∧
        ‖gaussianRatComplex data.base‖ = 1 ∧
        (∀ z ∈ data.phases, ‖gaussianRatComplex z‖ = 1) ∧
        (scoreData p d data).1.1 ≤ (1 / 2 : ℚ) ^ phaseToleranceBits eps ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          |((responseP (gaussianRatComplex data.base)
              (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re -
            (realTarget p).eval x| ≤ (eps : ℝ)) := by
  obtain ⟨hε, hd, hpar, hbound⟩ := hleg
  obtain ⟨data, hval, hlen, hbase, hphases, hscore, happ, htested, htestedle,
    hrounds, hvisits, hbackend⟩ :=
    finite_rational_phase_synthesis_terminates p d eps hε hd hpar hbound
  refine ⟨data, ?_, hlen, hbase, hphases, hscore, happ⟩
  rw [honestPhaseRun_value]
  exact hval

/-- For legal inversion whose initial candidate fails, the efficient-inversion coefficient-visit
count is strictly smaller than the honest phase-run count. -/
theorem efficientInversion_understates_visits (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps)
    (hnot : ¬ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 ≤
      (1 / 2 : ℚ) ^ phaseToleranceBits eps) :
    (efficientInversion p d eps).cost.coefficientVisits
        < (honestPhaseRun p d eps).ledger.coefficientVisits := by
  have hcnt := honestPhaseRun_counters p d eps hleg
  have htested := honestPhaseRun_search_tested p d eps hnot
  have hvisits : (honestPhaseRun p d eps).ledger.coefficientVisits
      = (honestPhaseRun p d eps).ledger.testedWords * (d + 1) := hcnt.2.1
  have hfrozen : (efficientInversion p d eps).cost.coefficientVisits = d + 1 := rfl
  rw [hvisits, hfrozen]
  have h1 : 2 ≤ (honestPhaseRun p d eps).ledger.testedWords := htested
  have h2 : (d + 1) * 2 ≤ (d + 1) * (honestPhaseRun p d eps).ledger.testedWords :=
    Nat.mul_le_mul_left (d + 1) h1
  have h3 : 2 * (d + 1) ≤ (honestPhaseRun p d eps).ledger.testedWords * (d + 1) := by
    simpa [Nat.mul_comm] using! h2
  omega

/-- For positive degree and legal inversion whose initial candidate fails, the
efficient-inversion response-round count is strictly smaller than the honest phase-run
count. -/
theorem efficientInversion_understates_rounds (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hd : 1 ≤ d)
    (hleg : PhaseInversionLegal p d eps)
    (hnot : ¬ (scoreData p d ⟨gone, List.replicate d gone⟩).1.1 ≤
      (1 / 2 : ℚ) ^ phaseToleranceBits eps) :
    (efficientInversion p d eps).cost.responseRounds
        < (honestPhaseRun p d eps).ledger.responseRounds := by
  have hcnt := honestPhaseRun_counters p d eps hleg
  have htested := honestPhaseRun_search_tested p d eps hnot
  have hrounds : (honestPhaseRun p d eps).ledger.responseRounds
      = (honestPhaseRun p d eps).ledger.testedWords * d := hcnt.1
  have hfrozen : (efficientInversion p d eps).cost.responseRounds = d := rfl
  rw [hrounds, hfrozen]
  have h1 : 2 ≤ (honestPhaseRun p d eps).ledger.testedWords := htested
  have h2 : d * 2 ≤ d * (honestPhaseRun p d eps).ledger.testedWords :=
    Nat.mul_le_mul_left d h1
  have h3 : 2 * d ≤ (honestPhaseRun p d eps).ledger.testedWords * d := by
    simpa [Nat.mul_comm] using! h2
  omega

/-- For legal inversion, response rounds and coefficient visits are bounded by one plus the
phase-search word count, multiplied by `d` and `d + 1`, respectively. -/
theorem honestPhaseRun_worst_case (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    (honestPhaseRun p d eps).ledger.responseRounds ≤
        (1 + phaseSearchWords d (phaseToleranceBits eps)) * d ∧
      (honestPhaseRun p d eps).ledger.coefficientVisits ≤
        (1 + phaseSearchWords d (phaseToleranceBits eps)) * (d + 1) := by
  obtain ⟨hε, hd, hpar, hbound⟩ := hleg
  obtain ⟨data, hval, hlen, hbase, hphases, hscore, happ, htested, htestedle,
    hrounds, hvisits, hbackend⟩ :=
    finite_rational_phase_synthesis_terminates p d eps hε hd hpar hbound
  have hN : (2 ^ phaseGridBits d (phaseToleranceBits eps)) ^ (d + 1)
      = phaseSearchWords d (phaseToleranceBits eps) := by
    unfold phaseSearchWords
    rw [pow_add, pow_one]
  refine ⟨?_, ?_⟩
  · rw [honestPhaseRun_rounds, hrounds]
    have h1 : (finitePhaseSynthesis p d eps).tested
        ≤ 1 + (2 ^ phaseGridBits d (phaseToleranceBits eps)) ^ (d + 1) := htestedle
    have h2 := Nat.mul_le_mul_left d h1
    rw [hN] at h2
    simpa [Nat.mul_comm] using! h2
  · rw [honestPhaseRun_visits, hvisits]
    have h1 : (finitePhaseSynthesis p d eps).tested
        ≤ 1 + (2 ^ phaseGridBits d (phaseToleranceBits eps)) ^ (d + 1) := htestedle
    have h2 := Nat.mul_le_mul_left (d + 1) h1
    rw [hN] at h2
    simpa [Nat.mul_comm] using! h2

/-- At degree eight and precision four, the full-search response-round expression exceeds
`phaseInversionCostBound 8 4`. -/
theorem honest_cost_exceeds_frozen_polynomial :
    (1 + phaseSearchWords 8 4) * 8 > phaseInversionCostBound 8 4 := by
  have hc : phaseConstant 8 = 59049 := by norm_num [phaseConstant]
  have hclog : Nat.clog 2 (32 * phaseConstant 8) = 21 := by
    rw [hc]
    decide
  have hbits : phaseGridBits 8 4 = 25 := by
    simp [phaseGridBits, hclog]
  rw [phaseSearchWords, hbits]
  norm_num [phaseInversionCostBound]

/-- A legal sparse entry's precision-`K` rational value differs from its real value by at most
`(1/2)^K`. -/
theorem quantization_entry_error {S : EffectiveSparseHamiltonianData}
    {V : EffectiveSparseEntry → ℝ} (hV : EffectiveSparseLegal S V)
    {K : ℕ} {e : EffectiveSparseEntry} (he : e ∈ S.entries) :
    |((e.value K : ℚ) : ℝ) - V e| ≤ (1 / 2 : ℝ) ^ K := by
  obtain ⟨-, -, hbound, -, -, -⟩ := hV
  have h1 := hbound e he K
  simpa [abs_sub_comm] using! h1

/-- A legal sparse entry's precision-`K` rational approximation has absolute value at most the
entry-norm bound plus `(1/2)^K`. -/
theorem quantized_value_bound {S : EffectiveSparseHamiltonianData}
    {V : EffectiveSparseEntry → ℝ} (hV : EffectiveSparseLegal S V)
    {K : ℕ} {e : EffectiveSparseEntry} (he : e ∈ S.entries) :
    |((e.value K : ℚ) : ℝ)| ≤ (S.entryNorm : ℝ) + (1 / 2 : ℝ) ^ K := by
  have hV' := hV
  obtain ⟨-, -, hbound, hVle, -, -⟩ := hV
  have herr := quantization_entry_error hV' (K := K) he
  have h1 : |((e.value K : ℚ) : ℝ)| ≤ |V e| + |((e.value K : ℚ) : ℝ) - V e| := by
    have h1a : -|V e| ≤ V e := neg_abs_le _
    have h1b : -|((e.value K : ℚ) : ℝ) - V e| ≤ ((e.value K : ℚ) : ℝ) - V e := neg_abs_le _
    have h2a : V e ≤ |V e| := le_abs_self _
    have h2b : ((e.value K : ℚ) : ℝ) - V e ≤ |((e.value K : ℚ) : ℝ) - V e| := le_abs_self _
    rw [abs_le]
    constructor <;> linarith
  have h2 : |V e| ≤ (S.entryNorm : ℝ) := hVle e he
  calc
    |((e.value K : ℚ) : ℝ)| ≤ |V e| + |((e.value K : ℚ) : ℝ) - V e| := h1
    _ ≤ (S.entryNorm : ℝ) + (1 / 2 : ℝ) ^ K := add_le_add h2 herr

/-- The assigned hosting width, after subtracting two, has enough binary states to contain `dim`
states. -/
theorem hostingQubits_spec (dim : ℕ) :
    dim ≤ 2 ^ (hostingQubits dim - 2) := by
  have h1 : dim < 2 ^ (dim.log2 + 1) := (Nat.lt_log2_self : dim < 2 ^ (dim.log2 + 1))
  have h2 : hostingQubits dim - 2 = dim.log2 + 1 := by
    unfold hostingQubits
    omega
  rw [h2]
  exact le_of_lt h1

/-- Positive sparsity and entry bounds give a projected unitary encoding of the sparse matrix
normalized by `k * b`, together with the operator-norm bound `k * b`. -/
theorem effective_sparse_embedding {S : EffectiveSparseHamiltonianData}
    {V : EffectiveSparseEntry → ℝ} (k : ℕ) (b : ℝ) (hk : 0 < k) (hb : 0 < b)
    (hrow : ∀ o : Fin S.dim,
      (Finset.univ.filter fun i => effectiveSparseMatrix S V o i ≠ 0).card ≤ k)
    (hcol : ∀ i : Fin S.dim,
      (Finset.univ.filter fun o => effectiveSparseMatrix S V o i ≠ 0).card ≤ k)
    (hentry : ∀ o i : Fin S.dim, ‖effectiveSparseMatrix S V o i‖ ≤ b) :
    ProjectedUnitaryEncoding
        (((k : ℂ) * (b : ℂ))⁻¹ • effectiveSparseMatrix S V)
      (1 : Matrix ((Fin S.dim × Fin S.dim) ⊕ (Fin S.dim ⊕ Fin S.dim))
        ((Fin S.dim × Fin S.dim) ⊕ (Fin S.dim ⊕ Fin S.dim)) ℂ)
      (sparseOverlapLeft (effectiveSparseMatrix S V) (k * b))
      (sparseOverlapRight (effectiveSparseMatrix S V) (k * b)) ∧
      ‖effectiveSparseMatrix S V‖ ≤ k * b := by
  exact sparse_overlap_derived_sparse_entry_norm_consumer (I := Fin S.dim) (O := Fin S.dim)
    (effectiveSparseMatrix S V) k b hb (by exact_mod_cast hk) hrow hcol hentry

/-- Positive sparsity and entry bounds give an exact block encoding of the sparse matrix
normalized by `k * b`, together with the operator-norm bound `k * b`. -/
theorem effective_block_encoding {S : EffectiveSparseHamiltonianData}
    {V : EffectiveSparseEntry → ℝ} {k : ℕ} {b : ℝ} (hk : 0 < k) (hb : 0 < b)
    (hrow : ∀ o : Fin S.dim,
      (Finset.univ.filter fun i => effectiveSparseMatrix S V o i ≠ 0).card ≤ k)
    (hcol : ∀ i : Fin S.dim,
      (Finset.univ.filter fun o => effectiveSparseMatrix S V o i ≠ 0).card ≤ k)
    (hentry : ∀ o i : Fin S.dim, ‖effectiveSparseMatrix S V o i‖ ≤ b) :
    BlockEncoding (((k : ℂ) * (b : ℂ))⁻¹ • effectiveSparseMatrix S V)
      (1 : Matrix ((Fin S.dim × Fin S.dim) ⊕ (Fin S.dim ⊕ Fin S.dim))
        ((Fin S.dim × Fin S.dim) ⊕ (Fin S.dim ⊕ Fin S.dim)) ℂ)
      (sparseOverlapLeft (effectiveSparseMatrix S V) (k * b))
      (sparseOverlapRight (effectiveSparseMatrix S V) (k * b)) 1 0 ∧
      ‖effectiveSparseMatrix S V‖ ≤ k * b := by
  obtain ⟨henc, hnorm⟩ :=
    effective_sparse_embedding k b (by exact_mod_cast hk) hb hrow hcol hentry
  exact ⟨Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding henc,
      hnorm⟩

/-- The compiled Hamiltonian word uses the sum of the cosine and sine phase-list lengths in
queries, and five additional gates. -/
theorem sparseSimulationWord_counts {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileHamiltonian F bc zc bs zs) = zc.length + zs.length ∧
      adjointGateCount (compileHamiltonian F bc zc bs zs) = zc.length + zs.length + 5 := by
  exact counts_compileHamiltonian F bc zc bs zs

/-- Legal phase inversion yields a sparse simulation word with exactly `2 * d` queries and `2 *
d + 5` gates. -/
theorem sparseSimulationWord_counts_of_run {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    adjointQueryCount (sparseSimulationWord F p d eps) = 2 * d ∧
      adjointGateCount (sparseSimulationWord F p d eps) = 2 * d + 5 := by
  obtain ⟨data, hval, hlen, hbase, hphases, hscore, happ⟩ :=
    honestPhaseRun_packet p d eps hleg
  have hval' : (honestPhaseRun p d eps).value = some data := by
    rw [honestPhaseRun_value]
    exact hval
  have hcount := sparseSimulationWord_counts F (gaussianRatComplex data.base)
    (data.phases.map gaussianRatComplex) (gaussianRatComplex data.base)
    (data.phases.map gaussianRatComplex)
  rw [sparseSimulationWord, hval']
  constructor
  · rw [hcount.1]
    simp [hlen]
    omega
  · rw [hcount.2]
    simp [hlen]
    omega

/-- Evaluating the compiled Hamiltonian word with the controlled parallel oracle gives
`hamiltonianCircuit`. -/
theorem sparseSimulationWord_evaluate {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (U : Matrix H H ℂ) (F : Matrix H I ℂ) (bc : ℂ) (zc : List ℂ)
    (bs : ℂ) (zs : List ℂ) :
    evaluate (controlOracle (parallelOracle (J := Bool) U))
      (compileHamiltonian F bc zc bs zs) = hamiltonianCircuit U F bc zc bs zs := by
  exact evaluate_compileHamiltonian U F bc zc bs zs

/-- The sparse simulation ledger records the compiled word's queries and gates, hosting width,
target error, search-word count, and honest coefficient visits. -/
theorem sparseSimulationLedger_spec {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ) (e : ℝ) :
    (sparseSimulationLedger F p d eps e).oracleQueries =
        adjointQueryCount (sparseSimulationWord F p d eps) ∧
      (sparseSimulationLedger F p d eps e).macroGates =
        adjointGateCount (sparseSimulationWord F p d eps) ∧
      (sparseSimulationLedger F p d eps e).qubits = hostingQubits (Fintype.card H) ∧
      (sparseSimulationLedger F p d eps e).targetError = e ∧
      (sparseSimulationLedger F p d eps e).phaseSearchWords =
        phaseSearchWords d (phaseToleranceBits eps) ∧
      (sparseSimulationLedger F p d eps e).phaseCoefficientVisits =
        (honestPhaseRun p d eps).ledger.coefficientVisits := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end Qatlib.Concepts.RandCompile.ChannelBudget
