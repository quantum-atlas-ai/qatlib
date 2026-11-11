/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined
import Qatlib.Concepts.FourierRecovery.ModularFourier.FourierGradientDefs

/-!
# Finite precision Fourier gradient assembly

This module transports Fourier gradient readout guarantees through finite precision phase
recording and assembles explicit parameters for a target error budget. The algorithmic
background is quantum numerical gradient estimation [Jordan2005Gradient]. Sharp recording
examples and minimality results describe the chosen precision and grid size.

The module also verifies basis setup and elementary QFT counts, register budgets, centered
output bounds, certified parameter intervals, and inner product guarantees for approximate
gradients.

## Main statements

* `gradient_assembled_window_probability`: the assembled parameters give success probability at
  least `1 - ε` under the residual budget.
* `gradientAssemblyM_minimal_is_least`: the minimal grid size is least among those meeting the
  window budget.
* `gradientAssemblyK_is_minimal`: lower precisions fail the recording budget.
* `estimated_gradient_descent_direction_strict`: a sufficient error budget gives positive inner
  product with the true gradient.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.FullRange
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
open Qatlib.Concepts.SignalPrimitive.GridGradient

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.FourierGradient

set_option autoImplicit false

open Qatlib
open scoped ComplexOrder ENNReal
open Classical BigOperators
set_option warningAsError false

/-- Replacing phase values by their precision `k` records changes each stationary phase residual
by at most `2^(-(k + 1))`. -/
theorem record_stationary_phase_residual_error :
    ∀ (d M k : ℕ) (g : Fin d → ℝ) (φ : GradientGrid d M → ℝ) (x : GradientGrid d M),
      |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
        - stationaryPhaseResidual d M φ g x| ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
  intro d M k g φ x
  have h := realRecord_error k (φ x)
  rw [abs_sub_comm] at h
  have hres : stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
      - stationaryPhaseResidual d M φ g x = realRecord k (φ x) - φ x := by
    simp only [stationaryPhaseResidual]
    ring
  rw [hres]
  exact h

set_option linter.unusedVariables false in

/-- A stationary phase residual bound `B` gives a recorded readout window probability at least
`1 - 16 * d / (M * w) - 4 * π * B - 4 * π / 2^(k + 1)` under the stated positivity
hypotheses. -/
theorem stationary_phase_window_transport_of_record :
    ∀ (d M k : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
  intro d M k hM g c w B φ hM2 hw hB herror
  have hshift : ∀ x, |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
      - (c : ℝ)| ≤ B + (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
    intro x
    have hrec := record_stationary_phase_residual_error d M k g φ x
    have h1 : |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
        - stationaryPhaseResidual d M φ g x| ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1) :=
      abs_le.mpr (abs_le.mp hrec)
    have h2 : |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B := herror x
    have htri : |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x - (c : ℝ)|
        ≤ |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
            - stationaryPhaseResidual d M φ g x|
          + |stationaryPhaseResidual d M φ g x - (c : ℝ)| := by
      exact abs_sub_le _ _ _
    linarith
  have hmain := stationary_phase_window_transport d M hM g c w (B + (1 : ℝ) / (2 : ℝ) ^ (k + 1))
    (fun x => realRecord k (φ x)) hM2 hw (by positivity) hshift
  have hmain' :
      1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * (B + (1 : ℝ) / (2 : ℝ) ^ (k + 1))
        = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by ring
  rw [hmain'] at hmain
  exact hmain

set_option linter.unusedVariables false in

/-- If every phase is already an exact precision `k` record, the window probability bound has no
additional recording loss. -/
theorem record_window_exact_on_dyadic :
    ∀ (d M k : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B)
      (hdyadic : ∀ x, GeneralRealRecord k (φ x)),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
  intro d M k hM g c w B φ hM2 hw hB herror hdyadic
  have hrec : ∀ x, realRecord k (φ x) = φ x := by
    intro x
    obtain ⟨n, hn⟩ := hdyadic x
    exact realRecord_eq_of_exact k (φ x) n hn
  have hread : gradientReadout d M hM (fun x => realRecord k (φ x))
      = gradientReadout d M hM φ := by
    congr 1
    funext x
    exact hrec x
  rw [hread]
  exact stationary_phase_window_transport d M hM g c w B φ hM2 hw hB herror

/-- Every precision `k` real record is an integer multiple of `2^(-k)`. -/
theorem record_is_dyadic :
    ∀ (k : ℕ) (θ : ℝ), ∃ n : ℤ, realRecord k θ = (n : ℝ) / (2 : ℝ) ^ k := by
  intro k θ
  exact ⟨realRecordIndex k θ, rfl⟩

/-- The absolute record index is at most `|θ| * 2^k + 1 / 2`. -/
theorem record_index_bound :
    ∀ (k : ℕ) (θ : ℝ), |(realRecordIndex k θ : ℝ)| ≤ |θ| * (2 : ℝ) ^ k + 1 / 2 := by
  intro k θ
  have h := abs_sub_round (θ * (2 : ℝ) ^ k)
  have h' : |θ * (2 : ℝ) ^ k - (realRecordIndex k θ : ℝ)| ≤ 1 / 2 := by
    simpa [realRecordIndex] using! h
  have h'2 : |(realRecordIndex k θ : ℝ) - θ * (2 : ℝ) ^ k| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact h'
  have hpow : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  calc |(realRecordIndex k θ : ℝ)|
      ≤ |(realRecordIndex k θ : ℝ) - θ * (2 : ℝ) ^ k| + |θ * (2 : ℝ) ^ k| := by
        calc |(realRecordIndex k θ : ℝ)|
            = |((realRecordIndex k θ : ℝ) - θ * (2 : ℝ) ^ k) + θ * (2 : ℝ) ^ k| := by
              have h : ((realRecordIndex k θ : ℝ) - θ * (2 : ℝ) ^ k) + θ * (2 : ℝ) ^ k
                  = (realRecordIndex k θ : ℝ) := by ring
              rw [h]
          _ ≤ |(realRecordIndex k θ : ℝ) - θ * (2 : ℝ) ^ k| + |θ * (2 : ℝ) ^ k| :=
            abs_add_le _ _
    _ ≤ 1 / 2 + |θ| * (2 : ℝ) ^ k := by
      rw [abs_mul, abs_of_nonneg hpow]
      linarith
    _ = |θ| * (2 : ℝ) ^ k + 1 / 2 := by ring

/-- The assembled gradient grid size is positive for all dimensions and tolerances. -/
theorem gradientAssemblyM_pos (d : ℕ) (ε : ℝ) : 0 < gradientAssemblyM d ε := by
  show 0 < Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2
  omega

set_option linter.unusedVariables false in

/-- For positive `ε`, the assembled width, grid size, and record precision satisfy the stated
window and recording error budgets. -/
theorem gradient_parameter_assembly :
    ∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε),
      0 < gradientAssemblyW ε ∧
      gradientAssemblyW ε ≤ ε / 4 ∧
      2 ≤ gradientAssemblyM d ε ∧
      16 * (d : ℝ) / ((gradientAssemblyM d ε : ℝ) * gradientAssemblyW ε) ≤ ε / 2 ∧
      4 * Real.pi / (2 : ℝ) ^ (gradientAssemblyK ε hε + 1) ≤ ε / 4 := by
  intro d ε hε
  have hW : gradientAssemblyW ε = ε / 4 := rfl
  have hWpos : 0 < gradientAssemblyW ε := by
    rw [hW]; linarith
  have hWle : gradientAssemblyW ε ≤ ε / 4 := by rw [hW]
  have hMceil : (128 * (d : ℝ) / (ε * ε)) ≤ (gradientAssemblyM d ε : ℝ) := by
    have h2 : (128 * (d : ℝ) / (ε * ε))
        ≤ ((Nat.ceil (128 * (d : ℝ) / (ε * ε)) : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (128 * (d : ℝ) / (ε * ε)) : ℕ) : ℝ)
        ≤ ((Nat.ceil (128 * (d : ℝ) / (ε * ε)) : ℕ) + 2 : ℝ) := by norm_num
    have h4 := le_trans h2 h3
    simpa [gradientAssemblyM] using! h4
  have hM2 : 2 ≤ gradientAssemblyM d ε := by
    show 2 ≤ Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2
    omega
  have hwindow :
      16 * (d : ℝ) / ((gradientAssemblyM d ε : ℝ) * gradientAssemblyW ε) ≤ ε / 2 := by
    rw [hW]
    have hden : 0 < (gradientAssemblyM d ε : ℝ) * (ε / 4) := by positivity
    rw [div_le_iff₀ hden]
    have hM : (128 * (d : ℝ) / (ε * ε)) ≤ (gradientAssemblyM d ε : ℝ) := hMceil
    have heps2 : (0 : ℝ) < ε * ε := by positivity
    have hkey : (128 * (d : ℝ)) ≤ (gradientAssemblyM d ε : ℝ) * (ε * ε) := by
      have hdiv := (div_le_iff₀ heps2).mp hM
      linarith
    nlinarith [hkey]
  have hk : 16 * Real.pi / ε ≤ (2 : ℝ) ^ (gradientAssemblyK ε hε + 1) := by
    exact Nat.find_spec (exists_two_pow_ge (by positivity : 0 < 16 * Real.pi / ε))
  have henc : 4 * Real.pi / (2 : ℝ) ^ (gradientAssemblyK ε hε + 1) ≤ ε / 4 := by
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (gradientAssemblyK ε hε + 1) := by positivity
    rw [div_le_iff₀ hpow]
    have hmul : 4 * Real.pi ≤ (ε / 4) * (2 : ℝ) ^ (gradientAssemblyK ε hε + 1) := by
      have h1 : (16 * Real.pi / ε) * (ε / 4) = 4 * Real.pi := by
        field_simp
        ring
      rw [← h1]
      nlinarith [mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ ε / 4)]
    nlinarith
  exact ⟨hWpos, hWle, hM2, hwindow, henc⟩

set_option linter.unusedVariables false in

/-- The assembled parameters give window probability at least `1 - ε` when the stationary phase
residual contributes at most `ε / 4` to the loss. -/
theorem gradient_assembled_window_probability :
    ∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 ≤ B)
      (g : Fin d → ℝ) (c : ℝ)
      (φ : GradientGrid d (gradientAssemblyM d ε) → ℝ)
      (herror : ∀ x, |stationaryPhaseResidual d (gradientAssemblyM d ε) φ g x - (c : ℝ)| ≤ B)
      (hB4 : 4 * Real.pi * B ≤ ε / 4),
      MeasureProb (gradientReadout d (gradientAssemblyM d ε) (gradientAssemblyM_pos d ε)
          (fun x => realRecord (gradientAssemblyK ε hε) (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / ((gradientAssemblyM d ε : ℝ))) (g j)
            ≤ gradientAssemblyW ε))
        ≥ 1 - ε := by
  intro d ε hε B hB g c φ herror hB4
  obtain ⟨hWpos, hWle, hM2, hwindow, henc⟩ := gradient_parameter_assembly d ε hε
  have hmain := stationary_phase_window_transport_of_record d (gradientAssemblyM d ε)
    (gradientAssemblyK ε hε) (gradientAssemblyM_pos d ε) g c (gradientAssemblyW ε) B φ hM2
    hWpos hB herror
  linarith [hmain, hwindow, henc, hB4]

set_option linter.unusedVariables false in

/-- For `ε ≤ 1 / 2` and gradients bounded by `1 / 4`, a sample in the assembled window gives
coordinate errors at most `ε / 4`. -/
theorem gradient_assembled_estimate_error :
    ∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
      (g : Fin d → ℝ) (hg : ∀ j : Fin d, |g j| ≤ 1 / 4)
      (z : GradientGrid d (gradientAssemblyM d ε))
      (hgood : ∀ j : Fin d,
        phaseDistance ((z j).val / ((gradientAssemblyM d ε : ℝ))) (g j)
          ≤ gradientAssemblyW ε),
      ∀ j : Fin d, |gradientEstimate d (gradientAssemblyM d ε) z j - g j| ≤ ε / 4 := by
  intro d ε hε hε2 g hg z hgood j
  have hW : gradientAssemblyW ε = ε / 4 := rfl
  have hw : gradientAssemblyW ε ≤ 1 / 8 := by
    rw [hW]; linarith
  have h := centered_output_estimate_error d (gradientAssemblyM d ε)
    (gradientAssemblyM_pos d ε) g (gradientAssemblyW ε) hg hw z hgood j
  rwa [hW] at h

set_option linter.unusedVariables false in

/-- The combined value kickback and gradient words have total query count three and total gate
count `2 * d + 1` in their respective ledgers. -/
theorem gradient_assembly_ledger :
    ∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M),
      adjointQueryCount (valueComputeKickbackUncomputeWord d M Q)
          + QueryCount (gradientWord d M) = 3 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q)
          + GateCount (gradientWord d M) = 2 * d + 1 := by
  intro d M Q _ hM
  obtain ⟨-, hq, hg, -⟩ := value_compute_kickback_uncompute_resources d M Q
  obtain ⟨-, hq2, hg2⟩ := clause3_readout_word_ledger d M hM
  constructor
  · rw [hq, hq2]
  · rw [hg, hg2]
    ring

/-- The recording error reaches `2^(-(k + 1))` at the first positive half step. -/
theorem realRecord_error_attained :
    ∀ (k : ℕ),
      |(1 : ℝ) / (2 : ℝ) ^ (k + 1) - realRecord k ((1 : ℝ) / (2 : ℝ) ^ (k + 1))|
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
  intro k
  have hscaled : ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ k = 1 / 2 := by
    have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hne : (2 : ℝ) ^ k * 2 ≠ 0 := by positivity
    field_simp [hne]
    ring
  have hround : realRecordIndex k ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) = 1 := by
    rw [realRecordIndex, hscaled]
    rw [round_eq_iff]
    constructor <;> norm_num
  have hrec : realRecord k ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) = (1 : ℝ) / (2 : ℝ) ^ k := by
    simp only [realRecord, hround, Int.cast_one]
  rw [hrec]
  have hkey : (1 : ℝ) / (2 : ℝ) ^ (k + 1) - (1 : ℝ) / (2 : ℝ) ^ k
      = -((1 : ℝ) / (2 : ℝ) ^ (k + 1)) := by
    have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hne : (2 : ℝ) ^ k * 2 ≠ 0 := by positivity
    field_simp [hne]
    ring
  rw [hkey, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ (k + 1))]

/-- The recording error reaches `2^(-(k + 1))` at every nonnegative odd half step of the
precision `k` grid. -/
theorem realRecord_error_attained_family :
    ∀ (k : ℕ) (m : ℕ),
      abs ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)
        - realRecord k ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)))
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
  intro k m
  have hscaled : ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ k
      = (m : ℝ) + 1 / 2 := by
    have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hne : (2 : ℝ) ^ k * 2 ≠ 0 := by positivity
    field_simp [hne]
    ring
  have hround : realRecordIndex k ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1))
      = (m + 1 : ℤ) := by
    rw [realRecordIndex, hscaled]
    have h1 : (m : ℝ) + 1 / 2 = 1 / 2 + (m : ℕ) := by ring
    rw [h1, round_add_natCast]
    have h2 : round (1 / 2 : ℝ) = 1 := by
      rw [round_eq_iff]
      constructor <;> norm_num
    rw [h2]
    omega
  have hrec : realRecord k ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1))
      = ((m : ℝ) + 1) / (2 : ℝ) ^ k := by
    simp only [realRecord, hround]
    push_cast
    ring
  rw [hrec]
  have hkey : (2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)
      - ((m : ℝ) + 1) / (2 : ℝ) ^ k
      = -((1 : ℝ) / (2 : ℝ) ^ (k + 1)) := by
    have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hne : (2 : ℝ) ^ k * 2 ≠ 0 := by positivity
    field_simp [hne]
    ring
  rw [hkey, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ (k + 1))]

/-- Every precision below `gradientAssemblyK ε hε` exceeds the recording loss budget `ε / 4`. -/
theorem gradientAssemblyK_is_minimal :
    ∀ (ε : ℝ) (hε : 0 < ε) (j : ℕ), j < gradientAssemblyK ε hε →
      4 * Real.pi / (2 : ℝ) ^ (j + 1) > ε / 4 := by
  intro ε hε j hj
  have hnot : ¬(16 * Real.pi / ε ≤ (2 : ℝ) ^ (j + 1)) := by
    exact Nat.find_min (exists_two_pow_ge (by positivity : 0 < 16 * Real.pi / ε)) hj
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have h1 : 16 * Real.pi / ε > (2 : ℝ) ^ (j + 1) := lt_of_not_ge hnot
  have h2 : 16 * Real.pi > ε * (2 : ℝ) ^ (j + 1) := by
    have h3 := (lt_div_iff₀ hε).mp (by linarith : (2 : ℝ) ^ (j + 1) < 16 * Real.pi / ε)
    linarith
  have h4 : ε / 4 * (2 : ℝ) ^ (j + 1) < 4 * Real.pi := by
    linarith
  have h5 : ε / 4 < 4 * Real.pi / (2 : ℝ) ^ (j + 1) := by
    exact (lt_div_iff₀ hpos).mpr h4
  linarith

/-- The minimal assembled grid size is at least two. -/
theorem gradientAssemblyM_minimal_at_least_two (d : ℕ) (ε : ℝ) :
    2 ≤ gradientAssemblyM_minimal d ε := by
  show 2 ≤ max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))
  exact le_max_left _ _

set_option linter.unusedVariables false in

/-- For positive `ε`, the minimal assembled grid size meets the window loss budget `ε / 2`. -/
theorem gradientAssemblyM_minimal_meets_window :
    ∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε),
      16 * (d : ℝ) / ((gradientAssemblyM_minimal d ε : ℝ) * gradientAssemblyW ε) ≤ ε / 2 := by
  intro d ε hε
  have hW : gradientAssemblyW ε = ε / 4 := rfl
  have hden : (0 : ℝ) < (gradientAssemblyM_minimal d ε : ℝ) * (ε / 4) := by
    have h1 : (0 : ℝ) < (gradientAssemblyM_minimal d ε : ℝ) := by
      have : 2 ≤ gradientAssemblyM_minimal d ε :=
        gradientAssemblyM_minimal_at_least_two d ε
      exact Nat.cast_pos.mpr (by omega)
    have h2 : (0 : ℝ) < ε / 4 := by linarith
    positivity
  rw [hW, div_le_iff₀ hden]
  have hceil : (128 * (d : ℝ) / (ε * ε)) ≤ (gradientAssemblyM_minimal d ε : ℝ) := by
    have h2 : (128 * (d : ℝ) / (ε * ε))
        ≤ ((Nat.ceil (128 * (d : ℝ) / (ε * ε)) : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (128 * (d : ℝ) / (ε * ε)) : ℕ) : ℝ)
        ≤ (gradientAssemblyM_minimal d ε : ℝ) := by
      have hh : Nat.ceil (128 * (d : ℝ) / (ε * ε))
          ≤ max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε))) := le_max_right _ _
      rw [gradientAssemblyM_minimal]
      exact Nat.cast_le.mpr hh
    exact le_trans h2 h3
  have heps2 : (0 : ℝ) < ε * ε := by positivity
  have hkey : (128 * (d : ℝ)) ≤ (gradientAssemblyM_minimal d ε : ℝ) * (ε * ε) :=
    (div_le_iff₀ heps2).mp hceil
  calc 16 * (d : ℝ) = (128 * (d : ℝ)) / 8 := by ring
    _ ≤ ((gradientAssemblyM_minimal d ε : ℝ) * (ε * ε)) / 8 :=
      div_le_div_of_nonneg_right hkey (by norm_num)
    _ = (ε / 2) * ((gradientAssemblyM_minimal d ε : ℝ) * (ε / 4)) := by ring

set_option linter.unusedVariables false in

/-- The minimal assembled grid size is no larger than any grid of size at least two satisfying
the window loss budget. -/
theorem gradientAssemblyM_minimal_is_least :
    ∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε) (M' : ℕ) (hM2 : 2 ≤ M'),
      16 * (d : ℝ) / ((M' : ℝ) * gradientAssemblyW ε) ≤ ε / 2 →
        gradientAssemblyM_minimal d ε ≤ M' := by
  intro d ε hε M' hM2 hwin
  have hW : gradientAssemblyW ε = ε / 4 := rfl
  have hden : (0 : ℝ) < (M' : ℝ) * (ε / 4) := by
    have h1 : (0 : ℝ) < (M' : ℝ) := by
      have : (0 : ℕ) < M' := by omega
      exact Nat.cast_pos.mpr this
    have h2 : (0 : ℝ) < ε / 4 := by linarith
    positivity
  rw [hW, div_le_iff₀ hden] at hwin
  have heps2 : (0 : ℝ) < ε * ε := by positivity
  have hkey : (128 * (d : ℝ)) ≤ (M' : ℝ) * (ε * ε) := by
    have h1 : 16 * (d : ℝ) ≤ (M' : ℝ) * (ε * ε) / 8 := by
      calc 16 * (d : ℝ) ≤ (ε / 2) * ((M' : ℝ) * (ε / 4)) := hwin
        _ = (M' : ℝ) * (ε * ε) / 8 := by ring
    calc 128 * (d : ℝ) = 8 * (16 * (d : ℝ)) := by ring
      _ ≤ 8 * ((M' : ℝ) * (ε * ε) / 8) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = (M' : ℝ) * (ε * ε) := by ring
  have hceil : (128 * (d : ℝ) / (ε * ε)) ≤ (M' : ℝ) :=
    (div_le_iff₀ heps2).mpr hkey
  have hceil' : Nat.ceil (128 * (d : ℝ) / (ε * ε)) ≤ M' :=
    Nat.ceil_le.mpr hceil
  show max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε))) ≤ M'
  exact max_le hM2 hceil'

/-- The minimal grid size is at most the assembled size, and the assembled size exceeds it by at
most two. -/
theorem gradientAssemblyM_excess :
    ∀ (d : ℕ) (ε : ℝ),
      gradientAssemblyM_minimal d ε ≤ gradientAssemblyM d ε ∧
        gradientAssemblyM d ε - gradientAssemblyM_minimal d ε ≤ 2 := by
  intro d ε
  have hmax : max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))
      ≤ Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2 := by
    refine max_le (by omega) (by omega)
  constructor
  · exact hmax
  · show Nat.ceil (128 * (d : ℝ) / (ε * ε)) + 2
        - max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε))) ≤ 2
    generalize hM : max 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε))) = m
    have h2m : 2 ≤ m := by
      have hh := le_max_left 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))
      rw [hM] at hh
      exact hh
    have hxm : Nat.ceil (128 * (d : ℝ) / (ε * ε)) ≤ m := by
      have hh := le_max_right 2 (Nat.ceil (128 * (d : ℝ) / (ε * ε)))
      rw [hM] at hh
      exact hh
    omega

/-- When `K + k > 0`, the full range character index is zero exactly when `k = 0`. -/
theorem fullRangeCharacterIndex_eq_zero_iff (K k : ℕ) (h : 0 < K + k) :
    fullRangeCharacterIndex K k = 0 ↔ k = 0 := by
  constructor
  · intro hz
    rw [fullRangeCharacterIndex, ZMod.natCast_eq_zero_iff] at hz
    by_contra hk
    have hk1 : 1 ≤ k := by omega
    have hpow : 2 ^ (K + k) = 2 ^ K * 2 ^ k := by rw [← pow_add]
    have h2k : 2 ≤ 2 ^ k := by
      cases k with
      | zero => omega
      | succ k =>
          rw [pow_succ]
          have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
    have hge : 2 ^ K * 2 ≤ 2 ^ (K + k) := by
      rw [hpow]; exact Nat.mul_le_mul_left _ h2k
    have hlt : 2 ^ K < 2 ^ (K + k) := by omega
    have hmod : 2 ^ K % 2 ^ (K + k) = 2 ^ K := Nat.mod_eq_of_lt hlt
    have hmod0 : 2 ^ K % 2 ^ (K + k) = 0 := (Nat.dvd_iff_mod_eq_zero.mp hz)
    have hz2 : 2 ^ K = 0 := by rw [← hmod]; exact hmod0
    have : 0 < 2 ^ K := by positivity
    omega
  · intro hk
    subst hk
    have hpow : 2 ^ (K + 0) = 2 ^ K := by simp
    rw [fullRangeCharacterIndex, hpow]
    exact ZMod.natCast_self (2 ^ K)

/-- Swapping two specified basis labels twice returns the original label. -/
theorem knownBasisSwap_involutive {I : Type} [DecidableEq I] (o a : I) :
    Function.Involutive (knownBasisSwap o a) := by
  intro x
  by_cases hxo : x = o
  · rw [hxo]
    by_cases hao : o = a
    · rw [hao]
      simp [knownBasisSwap]
    · have ha : a ≠ o := fun e => hao e.symm
      have h1 : knownBasisSwap o a o = a := by simp [knownBasisSwap]
      have h2 : knownBasisSwap o a a = o := by simp [knownBasisSwap, ha]
      rw [h1, h2]
  · by_cases hxa : x = a
    · rw [hxa]
      by_cases hao : o = a
      · rw [hao]
        simp [knownBasisSwap]
      · have ha : a ≠ o := fun e => hao e.symm
        have h1 : knownBasisSwap o a a = o := by simp [knownBasisSwap, ha]
        have h2 : knownBasisSwap o a o = a := by simp [knownBasisSwap]
        rw [h1, h2]
    · have h1 : knownBasisSwap o a x = x := by simp [knownBasisSwap, hxo, hxa]
      rw [h1, h1]

/-- The known basis setup matrix is unitary. -/
theorem knownBasisSetUpGate_unitary {I : Type} [Fintype I] [DecidableEq I]
    (o a : I) :
    knownBasisSetUpGate o a ∈ Matrix.unitaryGroup I ℂ := by
  exact permMatrix_unitary (knownBasisSwap_involutive o a)

/-- An involutive permutation matrix maps a basis ket to the ket of its image. -/
theorem applyGate_permMatrix_ket {I : Type} [Fintype I] [DecidableEq I]
    {σ : I → I} (hσ : Function.Involutive σ) (x : I) :
    ApplyGate (permMatrix σ) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (σ x) := by
  funext y
  rw [applyGate_permMatrix hσ (Qatlib.Foundations.PureStateMath.Ket x) y]
  by_cases hy : σ y = x
  · have hxy : σ x = y := by rw [← hσ y, hy]
    simp [Qatlib.Foundations.PureStateMath.Ket, hy, hxy]
  · have hne : ¬(y = σ x) := by
      intro e
      apply hy
      have h2 : σ y = σ (σ x) := by rw [e]
      rwa [hσ x] at h2
    simp [Qatlib.Foundations.PureStateMath.Ket, hy, hne]

/-- The known basis setup word is unitary, uses zero queries, and has gate count
`knownBasisSetUpGates K k`. -/
theorem knownBasisSetUpWord_isUnitary (K k : ℕ) :
    IsUnitaryCircuit (knownBasisSetUpWord K k) ∧
      QueryCount (knownBasisSetUpWord K k) = 0 ∧
      GateCount (knownBasisSetUpWord K k) = knownBasisSetUpGates K k := by
  by_cases hk : k = 0
  · subst hk
    simp [knownBasisSetUpWord, knownBasisSetUpGates]
  · rw [knownBasisSetUpWord, if_neg hk]
    refine ⟨?_, rfl, ?_⟩
    intro U hU
    rw [List.mem_cons] at hU
    rcases hU with hU | hU
    · have hU' : U = knownBasisSetUpGate 0 (fullRangeCharacterIndex K k) := by
        exact Step.gate.inj hU
      rw [hU']
      exact knownBasisSetUpGate_unitary 0 _
    · simp at hU
    simp [knownBasisSetUpGates, hk]

/-- For positive total register width, the setup word maps the zero basis ket to the full range
character index ket. -/
theorem knownBasisSetUpWord_maps_origin :
    ∀ (K k : ℕ) (h : 0 < K + k),
      Run (1 : Matrix (ZMod (2 ^ (K + k))) (ZMod (2 ^ (K + k))) ℂ)
          (knownBasisSetUpWord K k) (Qatlib.Foundations.PureStateMath.Ket 0) =
        Qatlib.Foundations.PureStateMath.Ket (fullRangeCharacterIndex K k) := by
  intro K k h
  by_cases hk : k = 0
  · subst hk
    have hz : fullRangeCharacterIndex K 0 = 0 :=
      (fullRangeCharacterIndex_eq_zero_iff K 0 (by omega)).2 rfl
    simp [knownBasisSetUpWord, hz]
  · have hne : fullRangeCharacterIndex K k ≠ 0 := by
      intro hz
      exact absurd ((fullRangeCharacterIndex_eq_zero_iff K k h).mp hz) hk
    rw [knownBasisSetUpWord, if_neg hk]
    have hgate : ApplyGate (knownBasisSetUpGate 0 (fullRangeCharacterIndex K k))
          (Qatlib.Foundations.PureStateMath.Ket 0) =
        Qatlib.Foundations.PureStateMath.Ket (fullRangeCharacterIndex K k) := by
      have hinv : ApplyGate (knownBasisSetUpGate 0 (fullRangeCharacterIndex K k))
          (Qatlib.Foundations.PureStateMath.Ket 0) =
        Qatlib.Foundations.PureStateMath.Ket (knownBasisSwap 0 (fullRangeCharacterIndex K k) 0) := by
        have h := applyGate_permMatrix_ket
          (knownBasisSwap_involutive 0 (fullRangeCharacterIndex K k))
          (0 : ZMod (2 ^ (K + k)))
        simpa [knownBasisSetUpGate] using! h
      have hswap : knownBasisSwap 0 (fullRangeCharacterIndex K k) 0
          = fullRangeCharacterIndex K k := by
        simp [knownBasisSwap, hne]
      rw [hinv, hswap]
    simp [hgate]

/-- The local QFT contains `n` Hadamards, `n * (n - 1) / 2` controlled phase gates, and `n / 2`
swaps, with total length `qftElementaryGates n`. -/
theorem localQFT_elementary_gate_count (n : ℕ) :
    (localQFT n).countP (fun g => match g with | .h _ => true | _ => false) = n ∧
    (localQFT n).countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = n * (n - 1) / 2 ∧
    (localQFT n).countP (fun g => match g with | .swap _ _ => true | _ => false) = n / 2 ∧
    (localQFT n).length = qftElementaryGates n := by
  obtain ⟨hH, hCp, hSwap⟩ := localQFT_class_counts n
  refine ⟨hH, hCp, hSwap, ?_⟩
  rw [length_eq_countP_add, hH, hCp, hSwap]
  rfl

/-- The elementary QFT gate count is `n + n * (n - 1) / 2 + n / 2`. -/
theorem qftElementaryGates_shape (n : ℕ) :
    qftElementaryGates n = n + n * (n - 1) / 2 + n / 2 := rfl

/-- Expands the elementary QFT gate count for a character register of width `K + k`. -/
theorem charPrep_elementary_gate_count (K k : ℕ) :
    qftElementaryGates (K + k) = (K + k) + (K + k) * (K + k - 1) / 2 + (K + k) / 2 := rfl

/-- The readout space is the sum of the grid and character register widths, and the integer
width equals the character width. -/
theorem readoutSpaceBits_decomposition (d M K k : ℕ) :
    readoutSpaceBits d M K k = gridRegisterQubits d M + charRegisterQubits K k ∧
    readoutIntegerBits K k = charRegisterQubits K k := by
  simp [readoutSpaceBits, readoutIntegerBits, gridRegisterQubits, charRegisterQubits,
    Nat.add_assoc]

/-- The centered output bit budget includes one sign bit beyond `Nat.clog 2 (max 2 M)`. -/
theorem centeredOutputBits_is_signed (M : ℕ) :
    centeredOutputBits M = Nat.clog 2 (max 2 M) + 1 := rfl

/-- A centered output on the grid of size `2^m`, scaled by `2^m`, has magnitude at most `2^(m -
1)`. -/
theorem centered_output_scaled_bound :
    ∀ (m : ℕ) (z : Fin (2 ^ m)),
      |(2 : ℝ) ^ m * centeredGridOutput (2 ^ m) z| ≤ (2 : ℝ) ^ (m - 1) := by
  intro m z
  have hzlt : z.val < 2 ^ m := z.isLt
  have hMc : ∀ t : ℕ, ((2 ^ t : ℕ) : ℝ) = (2 : ℝ) ^ t := fun t => Nat.cast_pow 2 t
  have hscale : ∀ (t : ℕ) (q : ℝ), (2 : ℝ) ^ t * (q / ((2 ^ t : ℕ) : ℝ)) = q := by
    intro t q
    rw [hMc]
    have hne : (2 : ℝ) ^ t ≠ 0 := by positivity
    field_simp
  by_cases hcase : 2 * z.val ≤ 2 ^ m
  · have hmain : centeredGridOutput (2 ^ m) z = (z.val : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
      unfold centeredGridOutput signedGridValue
      rw [if_pos hcase]
    have hval : (2 : ℝ) ^ m * centeredGridOutput (2 ^ m) z = (z.val : ℝ) := by
      rw [hmain, hscale m]
    rw [hval, abs_of_nonneg (by positivity)]
    have hhalf : z.val ≤ 2 ^ (m - 1) := by
      cases m with
      | zero =>
          have hz0 : z.val = 0 := by omega
          simp [hz0]
      | succ m' =>
          have hsplit : 2 ^ (m' + 1) = 2 ^ m' * 2 := by rw [pow_succ]
          have h1 : 2 * z.val ≤ 2 * 2 ^ m' := by
            have h2 : 2 * 2 ^ m' = 2 ^ (m' + 1) := by rw [pow_succ]; omega
            omega
          have h2 : z.val ≤ 2 ^ m' := by omega
          simpa [Nat.succ_sub_one] using! h2
    have hcast : (z.val : ℝ) ≤ ((2 ^ (m - 1) : ℕ) : ℝ) := by
      exact_mod_cast hhalf
    rw [← hMc (m - 1)]
    exact hcast
  · have hmain : centeredGridOutput (2 ^ m) z
        = (z.val : ℝ) / ((2 ^ m : ℕ) : ℝ) - 1 := by
      unfold centeredGridOutput signedGridValue
      rw [if_neg hcase]
    have hval : (2 : ℝ) ^ m * centeredGridOutput (2 ^ m) z
        = (z.val : ℝ) - (2 : ℝ) ^ m := by
      rw [hmain]
      calc (2 : ℝ) ^ m * ((z.val : ℝ) / ((2 ^ m : ℕ) : ℝ) - 1)
          = (2 : ℝ) ^ m * ((z.val : ℝ) / ((2 ^ m : ℕ) : ℝ)) - (2 : ℝ) ^ m * 1 := by ring
        _ = (z.val : ℝ) - (2 : ℝ) ^ m := by rw [hscale m]; ring
    rw [hval]
    have hneg : (z.val : ℝ) - (2 : ℝ) ^ m ≤ 0 := by
      have hzlt' : (z.val : ℕ) < 2 ^ m := hzlt
      have hc : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := hMc m
      rw [← hc]
      have hle : (z.val : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hzlt')
      linarith
    rw [abs_of_nonpos hneg]
    have hbound : (2 : ℝ) ^ m - (z.val : ℝ) ≤ (2 : ℝ) ^ (m - 1) := by
      by_cases hm0 : m = 0
      · subst hm0
        have hz0 : z.val = 0 := by omega
        simp [hz0]
      · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        subst hm'
        have hsplit : 2 ^ (m' + 1) = 2 ^ m' * 2 := by rw [pow_succ]
        have h3 : 2 ^ m' < z.val := by
          have h2 : 2 * 2 ^ m' < 2 * z.val := by omega
          omega
        have h4 : (2 : ℝ) ^ (m' + 1) = (2 : ℝ) ^ m' + (2 : ℝ) ^ m' := by
          rw [pow_succ]; ring
        have h5 : (2 : ℝ) ^ (m' + 1) - (z.val : ℝ) ≤ (2 : ℝ) ^ m' := by
          have h6 : (2 : ℝ) ^ m' ≤ (z.val : ℝ) := by
            exact_mod_cast (Nat.le_of_lt h3)
          rw [h4]
          linarith
        have h8 : (m' + 1) - 1 = m' := Nat.succ_sub_one m'
        rw [h8]
        exact h5
    linarith [hbound]

/-- For gradients bounded by `1 / 4` and window width at most `1 / 8`, a good modular sample
places every gradient coordinate in its parameter interval. -/
theorem parameter_estimation_certified :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d,
        (parameterInterval M w z j).1 ≤ g j ∧ g j ≤ (parameterInterval M w z j).2 := by
  intro d M hM g w hg hw z hgood j
  have h := centered_output_estimate_error d M hM g w hg hw z hgood j
  rw [gradientEstimate, centeredGridOutput] at h
  rw [parameterInterval, centeredGridOutput]
  have h' := (abs_le.mp h)
  exact ⟨by linarith, by linarith⟩

/-- Two real values within positive distance `w` have floor quantizations at step `w` differing
by at most one. -/
theorem quantize_step_one_step :
    ∀ (w : ℝ) (hw : 0 < w) (x y : ℝ), |x - y| ≤ w →
      |(quantizeStep w x : ℝ) - (quantizeStep w y : ℝ)| ≤ 1 := by
  intro w hw x y hxy
  have hdiv : |x / w - y / w| ≤ 1 := by
    have hsame : x / w - y / w = (x - y) / w := by
      field_simp
    rw [hsame, abs_div, abs_of_pos hw]
    rw [div_le_iff₀ hw]
    simpa using! hxy
  have hkey : ∀ u v : ℝ, u ≤ v → v - u ≤ 1 →
      (⌊u⌋ : ℝ) ≤ (⌊v⌋ : ℝ) ∧ (⌊v⌋ : ℝ) - (⌊u⌋ : ℝ) ≤ 1 := by
    intro u v huv hdiff
    have h1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
    have h2 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le v
    have h3 : u < (⌊u⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one u
    have h4 : v < (⌊v⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one v
    have hmono : (⌊u⌋ : ℤ) ≤ ⌊v⌋ := Int.floor_mono huv
    refine ⟨by exact_mod_cast hmono, ?_⟩
    have hlt0 : (⌊v⌋ : ℝ) - (⌊u⌋ : ℝ) < 2 := by linarith
    have hlt1 : ((⌊v⌋ : ℤ) - ⌊u⌋ : ℤ) < 2 := by
      have hcastlt : (((⌊v⌋ : ℤ) - ⌊u⌋ : ℤ) : ℝ) < (2 : ℝ) := by
        simp only [Int.cast_sub]
        linarith
      exact_mod_cast hcastlt
    have hle1 : ((⌊v⌋ : ℤ) - ⌊u⌋ : ℤ) ≤ 1 := by omega
    have hcastle : (((⌊v⌋ : ℤ) - ⌊u⌋ : ℤ) : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast hle1
    simp only [Int.cast_sub] at hcastle
    exact hcastle
  rcases le_total (x / w) (y / w) with hle | hle
  · have hdiff' : y / w - x / w ≤ 1 := by
      have hh := (abs_le.mp hdiv).1
      linarith
    obtain ⟨hmono, hdiff⟩ := hkey (x / w) (y / w) hle hdiff'
    rw [quantizeStep, quantizeStep]
    have hval : |(⌊x / w⌋ : ℝ) - (⌊y / w⌋ : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact hval
  · have hdiff' : x / w - y / w ≤ 1 := by
      have hh := (abs_le.mp hdiv).2
      linarith
    obtain ⟨hmono, hdiff⟩ := hkey (y / w) (x / w) hle hdiff'
    rw [quantizeStep, quantizeStep]
    have hval : |(⌊x / w⌋ : ℝ) - (⌊y / w⌋ : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact hval

/-- A coordinatewise gradient error bound `w` bounds the loss of inner product with the true
gradient by `w` times its sum of absolute coordinates. -/
theorem estimated_gradient_descent_direction :
    ∀ (d : ℕ) (g ê : Fin d → ℝ) (w : ℝ),
      (∀ j : Fin d, |ê j - g j| ≤ w) →
      (∑ j : Fin d, ê j * g j) - (∑ j : Fin d, g j ^ 2) ≥ -w * ∑ j : Fin d, |g j| := by
  intro d g ê w herr
  have hstep : ∀ j : Fin d, -w * |g j| ≤ ê j * g j - g j ^ 2 := by
    intro j
    have h1 : ê j * g j - g j ^ 2 = g j * (ê j - g j) := by ring
    rw [h1]
    have habs : |g j * (ê j - g j)| ≤ |g j| * w := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (herr j) (abs_nonneg _)
    have hlow : -(|g j| * w) ≤ g j * (ê j - g j) := by
      have h1' : -|g j * (ê j - g j)| ≤ g j * (ê j - g j) := by
        have := neg_le_abs (g j * (ê j - g j))
        linarith
      linarith
    have h2 : -w * |g j| = -(|g j| * w) := by ring
    linarith
  have hsum : (∑ j : Fin d, -w * |g j|) ≤ ∑ j : Fin d, (ê j * g j - g j ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact hstep j
  have hsub : ∑ j : Fin d, (ê j * g j - g j ^ 2)
      = (∑ j : Fin d, ê j * g j) - (∑ j : Fin d, g j ^ 2) := by
    rw [Finset.sum_sub_distrib]
  calc (∑ j : Fin d, ê j * g j) - (∑ j : Fin d, g j ^ 2)
      = ∑ j : Fin d, (ê j * g j - g j ^ 2) := hsub.symm
    _ ≥ ∑ j : Fin d, (-w * |g j|) := hsum
    _ = -w * (∑ j : Fin d, |g j|) := by rw [Finset.mul_sum]

/-- The estimated gradient has positive inner product with the true gradient when the stated
error budget is smaller than the squared gradient norm. -/
theorem estimated_gradient_descent_direction_strict :
    ∀ (d : ℕ) (g ê : Fin d → ℝ) (w : ℝ),
      (∀ j : Fin d, |ê j - g j| ≤ w) →
      w * (∑ j : Fin d, |g j|) < ∑ j : Fin d, g j ^ 2 →
      0 < ∑ j : Fin d, ê j * g j := by
  intro d g ê w herr hstrict
  have h := estimated_gradient_descent_direction d g ê w herr
  have hsq : 0 ≤ ∑ j : Fin d, g j ^ 2 := by positivity
  linarith

/-- The recorded readout window probability is at least one minus `gradientReadoutLoss` under
the stationary phase hypotheses. -/
theorem gradient_readout_loss_certificate :
    ∀ (d M k : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ)
      (φ : GradientGrid d M → ℝ) (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - gradientReadoutLoss d M k B w := by
  intro d M k hM g c w B φ hM2 hw hB herror
  have h := stationary_phase_window_transport_of_record d M k hM g c w B φ hM2 hw hB herror
  have heq : 1 - gradientReadoutLoss d M k B w
      = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
        - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
    simp [gradientReadoutLoss]
    ring
  rw [heq]
  exact h

/-- The probability lower bound `1 - gradientReadoutLoss` is at most `1 - 4 * π * B` for
positive grid size and window width. -/
theorem gradient_nonsmooth_ceiling :
    ∀ (d M k : ℕ) (hM : 0 < M) (B w : ℝ) (hw : 0 < w),
      1 - gradientReadoutLoss d M k B w ≤ 1 - 4 * Real.pi * B := by
  intro d M k hM B w hw
  have hgrid : 0 ≤ 16 * (d : ℝ) / ((M : ℝ) * w) := by
    have h1 : 0 ≤ (d : ℝ) := by positivity
    have h2 : 0 < (M : ℝ) * w := by positivity
    positivity
  have henc : 0 ≤ 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by positivity
  simp only [gradientReadoutLoss]
  linarith

/-- For nonnegative dimension and positive accuracy and failure tolerances, `gradientHeadlineM`
is the least grid size at least two satisfying the window loss budget. -/
theorem gradientHeadlineM_is_least :
    ∀ (d ε δ : ℝ) (hd : 0 ≤ d) (hε : 0 < ε) (hδ : 0 < δ),
      2 ≤ gradientHeadlineM d ε δ ∧
      16 * (d : ℝ) / ((gradientHeadlineM d ε δ : ℝ) * ε) ≤ δ ∧
      (∀ (M' : ℕ) (hM2 : 2 ≤ M'),
        16 * (d : ℝ) / ((M' : ℝ) * ε) ≤ δ → gradientHeadlineM d ε δ ≤ M') := by
  intro d ε δ hd hε hδ
  have hX : 0 ≤ 16 * d / (ε * δ) := by
    have h2 : 0 < ε * δ := by positivity
    positivity
  have hceil : (16 * (d : ℝ) / (ε * δ)) ≤ (Nat.ceil (16 * (d : ℝ) / (ε * δ)) : ℕ) :=
    Nat.le_ceil _
  have hMceil : (Nat.ceil (16 * (d : ℝ) / (ε * δ)) : ℕ)
      ≤ gradientHeadlineM d ε δ := by
    show Nat.ceil (16 * (d : ℝ) / (ε * δ)) ≤ max 2 (Nat.ceil (16 * (d : ℝ) / (ε * δ)))
    exact le_max_right _ _
  have hMge : (16 * (d : ℝ) / (ε * δ)) ≤ (gradientHeadlineM d ε δ : ℝ) := by
    have h1 : (16 * (d : ℝ) / (ε * δ)) ≤ ((Nat.ceil (16 * (d : ℝ) / (ε * δ)) : ℕ) : ℝ) := by
      exact_mod_cast hceil
    have h2 : ((Nat.ceil (16 * (d : ℝ) / (ε * δ)) : ℕ) : ℝ)
        ≤ (gradientHeadlineM d ε δ : ℝ) := by
      exact_mod_cast hMceil
    linarith
  have htwo : 2 ≤ gradientHeadlineM d ε δ := by
    show 2 ≤ max 2 (Nat.ceil (16 * (d : ℝ) / (ε * δ)))
    exact le_max_left _ _
  have hMpos : 0 < gradientHeadlineM d ε δ := by omega
  have hbudget : 16 * (d : ℝ) / ((gradientHeadlineM d ε δ : ℝ) * ε) ≤ δ := by
    have hden : 0 < (gradientHeadlineM d ε δ : ℝ) * ε := by
      have : 0 < (gradientHeadlineM d ε δ : ℝ) := by exact_mod_cast hMpos
      positivity
    rw [div_le_iff₀ hden]
    have hεδ : 0 < ε * δ := by positivity
    have hdiv : 16 * (d : ℝ) ≤ (gradientHeadlineM d ε δ : ℝ) * (ε * δ) := by
      rw [div_le_iff₀ hεδ] at hMge
      nlinarith [hMge]
    nlinarith [hdiv]
  have hleast : ∀ (M' : ℕ) (hM2 : 2 ≤ M'),
      16 * (d : ℝ) / ((M' : ℝ) * ε) ≤ δ → gradientHeadlineM d ε δ ≤ M' := by
    intro M' hM2 hwin
    have hden : 0 < (M' : ℝ) * ε := by
      have : 0 < (M' : ℝ) := by exact_mod_cast (show 0 < M' from by omega)
      positivity
    rw [div_le_iff₀ hden] at hwin
    have hεδ : 0 < ε * δ := by positivity
    have hmul : δ * ((M' : ℝ) * ε) = (M' : ℝ) * (ε * δ) := by ring
    have hdiv : 16 * d ≤ (M' : ℝ) * (ε * δ) := by
      rw [hmul] at hwin
      nlinarith [hwin]
    have hXe : 16 * (d : ℝ) / (ε * δ) ≤ (M' : ℝ) := by
      rw [div_le_iff₀ hεδ]
      nlinarith [hdiv]
    have hceil' : Nat.ceil (16 * (d : ℝ) / (ε * δ)) ≤ M' := by
      exact Nat.ceil_le.mpr hXe
    show max 2 (Nat.ceil (16 * (d : ℝ) / (ε * δ))) ≤ M'
    exact max_le hM2 hceil'
  exact ⟨htwo, hbudget, hleast⟩

/-- A positive window and failure tolerance satisfying the Fourier loss bound must obey `w ≥ 16
* d / (M * δ)`. -/
theorem gradient_confidence_accuracy_floor :
    ∀ (d M : ℕ) (hM : 0 < M) (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ),
      16 * (d : ℝ) / ((M : ℝ) * w) ≤ δ → w ≥ 16 * (d : ℝ) / ((M : ℝ) * δ) := by
  intro d M hM w δ hw hδ hwin
  have hden : 0 < (M : ℝ) * w := by
    have : 0 < (M : ℝ) := by exact_mod_cast hM
    positivity
  have hMδ : 0 < (M : ℝ) * δ := by
    have : 0 < (M : ℝ) := by exact_mod_cast hM
    positivity
  have h1 : 16 * (d : ℝ) ≤ (M : ℝ) * w * δ := by
    have := (div_le_iff₀ hden).mp hwin
    nlinarith [this]
  have h2 : 16 * (d : ℝ) / ((M : ℝ) * δ) ≤ w := by
    rw [div_le_iff₀ hMδ]
    nlinarith [h1]
  exact h2

/-- Establishes the specification combining sharp recording error examples and minimal assembled
precision and grid size. -/
theorem gext_next_endpoint : stageB_fourier_gradient_gext_next_spec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact realRecord_error_attained k
  · intro k m
    exact realRecord_error_attained_family k m
  · intro ε hε j hj
    exact gradientAssemblyK_is_minimal ε hε j hj
  · intro d ε hε
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact gradientAssemblyM_minimal_at_least_two d ε
    · exact gradientAssemblyM_minimal_meets_window d ε hε
    · intro M' hM2 hwin
      exact gradientAssemblyM_minimal_is_least d ε hε M' hM2 hwin
    · exact (gradientAssemblyM_excess d ε).1
    · exact (gradientAssemblyM_excess d ε).2

/-- Combines the base first gradient specification with recorded window bounds, assembled
success probability, and minimal parameter guarantees. -/
theorem gext1_endpoint :
    Qatlib.Concepts.SignalPrimitive.GridGradient.stageB_fourier_gradient_gext1_spec ∧
    (∀ (d M k : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1)) ∧
    (∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hB : 0 ≤ B)
      (g : Fin d → ℝ) (c : ℝ)
      (φ : GradientGrid d (gradientAssemblyM d ε) → ℝ)
      (herror : ∀ x, |stationaryPhaseResidual d (gradientAssemblyM d ε) φ g x - (c : ℝ)| ≤ B)
      (hB4 : 4 * Real.pi * B ≤ ε / 4),
      MeasureProb (gradientReadout d (gradientAssemblyM d ε) (gradientAssemblyM_pos d ε)
          (fun x => realRecord (gradientAssemblyK ε hε) (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / ((gradientAssemblyM d ε : ℝ))) (g j)
            ≤ gradientAssemblyW ε))
        ≥ 1 - ε) ∧
    (∀ (ε : ℝ) (hε : 0 < ε) (j : ℕ), j < gradientAssemblyK ε hε →
      4 * Real.pi / (2 : ℝ) ^ (j + 1) > ε / 4) ∧
    (∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε),
      2 ≤ gradientAssemblyM_minimal d ε ∧
        16 * (d : ℝ) / ((gradientAssemblyM_minimal d ε : ℝ) * gradientAssemblyW ε) ≤ ε / 2 ∧
        (∀ (M' : ℕ) (hM2 : 2 ≤ M'),
          16 * (d : ℝ) / ((M' : ℝ) * gradientAssemblyW ε) ≤ ε / 2 →
            gradientAssemblyM_minimal d ε ≤ M') ∧
        gradientAssemblyM_minimal d ε ≤ gradientAssemblyM d ε ∧
        gradientAssemblyM d ε - gradientAssemblyM_minimal d ε ≤ 2) := by
  refine ⟨Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation.gext1_endpoint,
      ?_, ?_, ?_, ?_⟩
  · intro d M k hM g c w B φ hM2 hw hB herror
    exact stationary_phase_window_transport_of_record d M k hM g c w B φ hM2 hw hB herror
  · intro d ε hε B hB g c φ herror hB4
    exact gradient_assembled_window_probability d ε hε B hB g c φ herror hB4
  · intro ε hε j hj
    exact gradientAssemblyK_is_minimal ε hε j hj
  · intro d ε hε
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact gradientAssemblyM_minimal_at_least_two d ε
    · exact gradientAssemblyM_minimal_meets_window d ε hε
    · intro M' hM2 hwin
      exact gradientAssemblyM_minimal_is_least d ε hε M' hM2 hwin
    · exact (gradientAssemblyM_excess d ε).1
    · exact (gradientAssemblyM_excess d ε).2

/-- Establishes the specification for the least headline grid size, the residual loss ceiling,
and the confidence versus accuracy bound. -/
theorem gext_next2_endpoint : stageB_fourier_gradient_gext_next2_spec := by
  refine ⟨?_, ?_, ?_⟩
  · intro d ε δ hd hε hδ
    exact gradientHeadlineM_is_least d ε δ hd hε hδ
  · intro d M k hM B w hw
    exact gradient_nonsmooth_ceiling d M k hM B w hw
  · intro d M hM w δ hw hδ hwin
    exact gradient_confidence_accuracy_floor d M hM w δ hw hδ hwin

/-- Establishes the specification for setup and QFT resource counts, register widths, centered
outputs, parameter intervals, and the estimated gradient inner product bound. -/
theorem gext_next3_endpoint : stageB_fourier_gradient_gext_next3_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K k
    refine ⟨?_, ?_, ?_⟩
    · unfold knownBasisSetUpGates
      split <;> omega
    · exact (knownBasisSetUpWord_isUnitary K k).2.1
    · exact (knownBasisSetUpWord_isUnitary K k).2.2
  · intro n
    exact localQFT_elementary_gate_count n
  · intro d M K k
    exact readoutSpaceBits_decomposition d M K k
  · intro m z
    exact centered_output_scaled_bound m z
  · intro d M hM g w hg hw z hgood
    exact parameter_estimation_certified d M hM g w hg hw z hgood
  · intro d g ê w herr
    exact estimated_gradient_descent_direction d g ê w herr

/-- Combines the base second gradient specification with residual transport, exact dyadic
records, assembled estimate accuracy, sharp recording errors, and the next parameter
specification. -/
theorem gext2_endpoint :
    Qatlib.Concepts.SignalPrimitive.GridGradient.stageB_fourier_gradient_gext2_spec ∧
    (∀ (d M k : ℕ) (g : Fin d → ℝ) (φ : GradientGrid d M → ℝ) (x : GradientGrid d M),
      |stationaryPhaseResidual d M (fun y => realRecord k (φ y)) g x
        - stationaryPhaseResidual d M φ g x| ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1)) ∧
    (∀ (d M k : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B)
      (hdyadic : ∀ x, GeneralRealRecord k (φ x)),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (φ x)))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) ∧
    (∀ (k : ℕ) (θ : ℝ), ∃ n : ℤ, realRecord k θ = (n : ℝ) / (2 : ℝ) ^ k) ∧
    (∀ (d : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
      (g : Fin d → ℝ) (hg : ∀ j : Fin d, |g j| ≤ 1 / 4)
      (z : GradientGrid d (gradientAssemblyM d ε))
      (hgood : ∀ j : Fin d,
        phaseDistance ((z j).val / ((gradientAssemblyM d ε : ℝ))) (g j)
          ≤ gradientAssemblyW ε),
      ∀ j : Fin d, |gradientEstimate d (gradientAssemblyM d ε) z j - g j| ≤ ε / 4) ∧
    (∀ (k : ℕ),
      abs ((1 : ℝ) / (2 : ℝ) ^ (k + 1) - realRecord k ((1 : ℝ) / (2 : ℝ) ^ (k + 1)))
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1)) ∧
    (∀ (k : ℕ) (m : ℕ),
      abs ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)
        - realRecord k ((2 * (m : ℝ) + 1) / (2 : ℝ) ^ (k + 1)))
        = (1 : ℝ) / (2 : ℝ) ^ (k + 1)) ∧
    stageB_fourier_gradient_gext_next2_spec := by
  refine ⟨Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation.gext2_endpoint,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d M k g φ x
    exact record_stationary_phase_residual_error d M k g φ x
  · intro d M k hM g c w B φ hM2 hw hB herror hdyadic
    exact record_window_exact_on_dyadic d M k hM g c w B φ hM2 hw hB herror hdyadic
  · intro k θ
    exact record_is_dyadic k θ
  · intro d ε hε hε2 g hg z hgood j
    exact gradient_assembled_estimate_error d ε hε hε2 g hg z hgood j
  · intro k
    exact gext_next_endpoint.1 k
  · intro k m
    exact gext_next_endpoint.2.1 k m
  · exact gext_next2_endpoint

/-- Combines the base third gradient specification with the record index bound, the combined
query and gate ledger, and the next implementation specification. -/
theorem gext3_endpoint :
    Qatlib.Concepts.SignalPrimitive.GridGradient.stageB_fourier_gradient_gext3_spec ∧
    (∀ (k : ℕ) (θ : ℝ), |(realRecordIndex k θ : ℝ)| ≤ |θ| * (2 : ℝ) ^ k + 1 / 2) ∧
    (∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M),
      adjointQueryCount (valueComputeKickbackUncomputeWord d M Q)
          + QueryCount (gradientWord d M) = 3 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q)
          + GateCount (gradientWord d M) = 2 * d + 1) ∧
    stageB_fourier_gradient_gext_next3_spec := by
  refine ⟨Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation.gext3_endpoint,
      ?_, ?_, ?_⟩
  · intro k θ
    exact record_index_bound k θ
  · intro d M Q _ hM
    exact gradient_assembly_ledger d M Q hM
  · exact gext_next3_endpoint

end Qatlib.Concepts.FourierRecovery.ModularFourier.FourierGradient
