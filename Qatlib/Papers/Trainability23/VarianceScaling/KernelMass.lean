/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.VarianceScaling.CorrelationMass
import Mathlib.Analysis.SpecialFunctions.Exp
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators

noncomputable def pSigma (σ : ℝ) : ℝ := (1 - Real.exp (-(1 / (2 * σ)))) / 2

theorem pSigma_pos {σ : ℝ} (hσ : 0 < σ) : 0 < pSigma σ := by
  have hlt : Real.exp (-(1 / (2 * σ))) < Real.exp 0 := by
    rw [Real.exp_lt_exp]
    have hpos : 0 < 1 / (2 * σ) := by positivity
    linarith
  rw [Real.exp_zero] at hlt
  unfold pSigma
  linarith

theorem pSigma_le_half (σ : ℝ) : pSigma σ ≤ 1 / 2 := by
  have h : 0 < Real.exp (-(1 / (2 * σ))) := Real.exp_pos _
  unfold pSigma
  linarith

theorem correlationVariance_base_lt_one {p : ℝ} (h0 : 0 < p) (h1 : p ≤ 1) :
    (1 - p) ^ 2 + p ^ 2 / 3 < 1 := by
  have hkey : (1 - p) ^ 2 + p ^ 2 / 3 = 1 - p * (2 - 4 * p / 3) := by ring
  have hpos : 0 < p * (2 - 4 * p / 3) := mul_pos h0 (by linarith)
  rw [hkey]
  linarith

theorem correlationVariance_le_exp {N : ℕ} (p : FinDist (Reg N)) {σ : ℝ} (hσ : 0 < σ) :
    correlationVariance p (pSigma σ) ≤ ((1 - pSigma σ) ^ 2 + pSigma σ ^ 2 / 3) ^ N ∧
      (1 - pSigma σ) ^ 2 + pSigma σ ^ 2 / 3 < 1 :=
  ⟨correlationVariance_le p (pSigma σ),
    correlationVariance_base_lt_one (pSigma_pos hσ) ((pSigma_le_half σ).trans (by norm_num))⟩

end Qatlib.Papers.Trainability23.VarianceScaling
