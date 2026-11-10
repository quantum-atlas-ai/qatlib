/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.VarianceScaling.KernelMass
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators

noncomputable def kernelGap (σ : ℝ) : ℝ := Real.exp (-(1 / (2 * σ)))

noncomputable def bSigmaBaseA (σ : ℝ) : ℝ :=
  (7 + 6 * kernelGap σ + 2 * kernelGap σ ^ 2) / 15

noncomputable def bSigmaBaseB (σ : ℝ) : ℝ :=
  (4 + 4 * kernelGap σ + kernelGap σ ^ 2) / 9

noncomputable def bSigma (n : ℕ) (σ : ℝ) : ℝ := bSigmaBaseA σ ^ n - bSigmaBaseB σ ^ n

theorem kernelGap_pos (σ : ℝ) : 0 < kernelGap σ := Real.exp_pos _

theorem kernelGap_lt_one {σ : ℝ} (hσ : 0 < σ) : kernelGap σ < 1 := by
  have hlt : Real.exp (-(1 / (2 * σ))) < Real.exp 0 := by
    rw [Real.exp_lt_exp]
    have hpos : 0 < 1 / (2 * σ) := by positivity
    linarith
  simpa [kernelGap, Real.exp_zero] using hlt

theorem bSigmaBaseA_sub_bSigmaBaseB (σ : ℝ) :
    bSigmaBaseA σ - bSigmaBaseB σ = (1 - kernelGap σ) ^ 2 / 45 := by
  unfold bSigmaBaseA bSigmaBaseB
  ring

theorem bSigmaBaseB_nonneg (σ : ℝ) : 0 ≤ bSigmaBaseB σ := by
  have h0 : 0 < kernelGap σ := Real.exp_pos _
  have h : 4 + 4 * kernelGap σ + kernelGap σ ^ 2 = (kernelGap σ + 2) ^ 2 := by ring
  unfold bSigmaBaseB
  rw [h]
  positivity

theorem bSigmaBaseB_pos (σ : ℝ) : 0 < bSigmaBaseB σ := by
  have h0 : 0 < kernelGap σ := kernelGap_pos σ
  have h : 4 + 4 * kernelGap σ + kernelGap σ ^ 2 = (kernelGap σ + 2) ^ 2 := by ring
  unfold bSigmaBaseB
  rw [h]
  positivity

theorem bSigmaBaseB_le_bSigmaBaseA (σ : ℝ) : bSigmaBaseB σ ≤ bSigmaBaseA σ := by
  have h := bSigmaBaseA_sub_bSigmaBaseB σ
  have : 0 ≤ (1 - kernelGap σ) ^ 2 / 45 := by positivity
  linarith

theorem bSigmaBaseA_lt_one {σ : ℝ} (hσ : 0 < σ) : bSigmaBaseA σ < 1 := by
  have h0 := kernelGap_pos σ
  have h1 := kernelGap_lt_one hσ
  have hkey : bSigmaBaseA σ = 1 + 2 * ((kernelGap σ - 1) * (kernelGap σ + 4)) / 15 := by
    unfold bSigmaBaseA
    ring
  rw [hkey]
  have hneg : (kernelGap σ - 1) * (kernelGap σ + 4) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have : 2 * ((kernelGap σ - 1) * (kernelGap σ + 4)) / 15 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hneg) (by norm_num)
  linarith

theorem bSigmaBaseB_lt_one {σ : ℝ} (hσ : 0 < σ) : bSigmaBaseB σ < 1 := by
  have h0 := kernelGap_pos σ
  have h1 := kernelGap_lt_one hσ
  have hkey : bSigmaBaseB σ = 1 + ((kernelGap σ - 1) * (kernelGap σ + 5)) / 9 := by
    unfold bSigmaBaseB
    ring
  rw [hkey]
  have hneg : (kernelGap σ - 1) * (kernelGap σ + 5) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have : ((kernelGap σ - 1) * (kernelGap σ + 5)) / 9 < 0 :=
    div_neg_of_neg_of_pos hneg (by norm_num)
  linarith

theorem bSigma_nonneg (n : ℕ) (σ : ℝ) : 0 ≤ bSigma n σ := by
  have hb := bSigmaBaseB_nonneg σ
  have hba := bSigmaBaseB_le_bSigmaBaseA σ
  unfold bSigma
  exact sub_nonneg.mpr (pow_le_pow_left₀ hb hba n)

theorem bSigma_le_baseA_pow (n : ℕ) (σ : ℝ) : bSigma n σ ≤ bSigmaBaseA σ ^ n := by
  have h : 0 ≤ bSigmaBaseB σ ^ n := pow_nonneg (bSigmaBaseB_nonneg σ) n
  unfold bSigma
  linarith

theorem bSigma_lt_one {σ : ℝ} (hσ : 0 < σ) (n : ℕ) : bSigma n σ < 1 := by
  have hA := bSigmaBaseA_lt_one hσ
  have h0 : 0 ≤ bSigmaBaseA σ := by
    have hb := bSigmaBaseB_nonneg σ
    have hba := bSigmaBaseB_le_bSigmaBaseA σ
    linarith
  have hApow : bSigmaBaseA σ ^ n ≤ 1 := pow_le_one₀ h0 (le_of_lt hA)
  have hBpow : 0 < bSigmaBaseB σ ^ n := pow_pos (bSigmaBaseB_pos σ) n
  unfold bSigma
  linarith

end Qatlib.Papers.Trainability23.VarianceScaling
