/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DysonSeries22.HistorySystem

@[expose] public section

/-!
# Endpoint readout as a norm ratio

This module rewrites the native endpoint readout of the padded Dyson history in the direct
Euclidean norm-ratio form used for amplitude amplification.  The nonzero initial state is an
explicit premise, so the denominator is proved nonzero rather than hidden behind an inverse.

The mathematical setting follows [Berry and Costa, 2024, Eqs. (96)--(101)][BerryCosta2024].
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DysonSeries22.HistorySystem

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.TimeEvolution.DysonError
open Qatlib.Papers.DysonSeries22.HistoryReadout
open Qatlib.Papers.DysonSeries22.HistorySystem

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The native endpoint readout is the endpoint-clock multiplicity times the squared Euclidean
norm ratio between the padded endpoint and the complete history. -/
theorem actual_history_endpoint_Born_ratio
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (t : ℕ → ℝ) (K r N : ℕ) (x₀ : EuclideanSpace ℂ I) (hx₀ : x₀ ≠ 0) :
    (((Qatlib.Concepts.ChannelTheory.Naimark.ContractionInstrument.readout
      (clockProjector (I := I) (endpointClocks r N)) (clockProjector_norm _)).measure
      (MState.pure (Qatlib.Concepts.ChannelTheory.Naimark.ContractionBorn.ketOfUnit
        (normalizedHistory A b t K r N x₀)
        (normalizedHistory_norm A b t K r N x₀
          (norm_ne_zero_iff.mpr (historyVector_ne_zero A b t K r N x₀ hx₀)))))) true : ℝ) =
      ((endpointClocks r N).card : ℝ) *
        (‖paddedTrajectory A b t K r x₀ r‖ /
          ‖historyVector A b t K r N x₀‖) ^ 2 := by
  have hvec : historyVector A b t K r N x₀ ≠ 0 :=
    historyVector_ne_zero A b t K r N x₀ hx₀
  have hnorm : ‖historyVector A b t K r N x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hvec
  rw [actual_history_endpoint_Born A b t K r N x₀ hnorm]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [inv_mul_eq_div]

/-- At the final padded clock, the endpoint set contains exactly one clock label. -/
theorem endpointClocks_last_card (N : ℕ) : (endpointClocks N N).card = 1 := by
  have hset : endpointClocks N N = {⟨N, Nat.lt_succ_self N⟩} := by
    ext c
    simp only [endpointClocks, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ c.isLt) h
    · intro h
      subst h
      exact le_rfl
  rw [hset]
  simp

end Qatlib.Papers.DysonSeries22.HistorySystem
