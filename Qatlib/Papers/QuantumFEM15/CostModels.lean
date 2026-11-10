/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumFEM15.CostModels

open Real

def modeledQleCost (C s κ uNorm u1Norm ε : ℝ) : ℝ :=
  C * (s * (κ ^ 2 * uNorm + κ * u1Norm)) / ε

def modeledNoPrecondBound (C : ℝ) (k : ℕ) (uNorm u1Norm semNorm ε : ℝ) : ℝ :=
  C * (uNorm * semNorm ^ ((4 : ℝ) / (k + 1)) /
        ε ^ (((k : ℝ) + 5) / (k + 1))
      + u1Norm * semNorm ^ ((2 : ℝ) / (k + 1)) /
        ε ^ (((k : ℝ) + 3) / (k + 1)))

def modeledNoPrecondKappa (k : ℕ) (semNorm ε : ℝ) : ℝ :=
  (semNorm / ε) ^ ((2 : ℝ) / (k + 1))

theorem modeledNo_preconditioning_bound (C : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (uNorm u1Norm semNorm ε : ℝ) (_hu : 0 ≤ uNorm) (_hu1 : 0 ≤ u1Norm)
    (hsem : 0 < semNorm) (hε : 0 < ε) :
    C * (modeledNoPrecondKappa k semNorm ε ^ 2 * uNorm +
          modeledNoPrecondKappa k semNorm ε * u1Norm) / ε =
      modeledNoPrecondBound C k uNorm u1Norm semNorm ε := by
  have hbase : (0 : ℝ) < semNorm / ε := div_pos hsem hε
  have hexp2 : (2 : ℝ) / ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1)
      = 4 / ((k : ℝ) + 1) := by rw [← add_div]; norm_num
  have hsplit5 : (4 : ℝ) / ((k : ℝ) + 1) + 1 = ((k : ℝ) + 5) / ((k : ℝ) + 1) := by
    field_simp; try ring
  have hsplit3 : (2 : ℝ) / ((k : ℝ) + 1) + 1 = ((k : ℝ) + 3) / ((k : ℝ) + 1) := by
    field_simp; try ring

  have hκ2 : ((semNorm / ε) ^ ((2 : ℝ) / ((k : ℝ) + 1))) ^ 2
      = (semNorm / ε) ^ ((4 : ℝ) / ((k : ℝ) + 1)) := by
    rw [sq, ← Real.rpow_add hbase, hexp2]
  have hε5 : ε ^ ((4 : ℝ) / ((k : ℝ) + 1)) * ε
      = ε ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) := by
    rw [← hsplit5, Real.rpow_add hε, Real.rpow_one]
  have hε3 : ε ^ ((2 : ℝ) / ((k : ℝ) + 1)) * ε
      = ε ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) := by
    rw [← hsplit3, Real.rpow_add hε, Real.rpow_one]
  rw [modeledNoPrecondKappa, hκ2, modeledNoPrecondBound,
    Real.div_rpow hsem.le hε.le, Real.div_rpow hsem.le hε.le, ← hε5, ← hε3]
  have hea : ε ^ ((4 : ℝ) / ((k : ℝ) + 1)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  have heb : ε ^ ((2 : ℝ) / ((k : ℝ) + 1)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hε _)
  have he : ε ≠ 0 := ne_of_gt hε
  field_simp [hea, heb, he]
  try ring

theorem modeledOptimal_preconditioning_bound (C κ K uNorm u1Norm ε : ℝ)
    (hC : 0 ≤ C) (hκ0 : 0 ≤ κ) (hκK : κ ≤ K) (hK : 1 ≤ K)
    (hu : 0 ≤ uNorm) (hu1 : 0 ≤ u1Norm) (hule : uNorm ≤ u1Norm)
    (hε : 0 < ε) :
    modeledQleCost C 1 κ uNorm u1Norm ε ≤ (2 * K ^ 2 * C) * u1Norm / ε := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hκu : κ ^ 2 * uNorm ≤ K ^ 2 * u1Norm := by
    have hκ2 : κ ^ 2 ≤ K ^ 2 := by
      have : κ ≤ K := hκK
      nlinarith [hκ0, hK0.le, sq_nonneg κ, sq_nonneg K]
    exact mul_le_mul hκ2 hule hu (by positivity)
  have hκu1 : κ * u1Norm ≤ K ^ 2 * u1Norm := by
    have h1 : κ ≤ K ^ 2 := by nlinarith [hκ0, hK0.le]
    exact mul_le_mul_of_nonneg_right h1 hu1
  have hsum : κ ^ 2 * uNorm + κ * u1Norm ≤ 2 * (K ^ 2 * u1Norm) := by
    nlinarith [hκu, hκu1]
  have hsum0 : 0 ≤ κ ^ 2 * uNorm + κ * u1Norm := by
    have : 0 ≤ κ ^ 2 := sq_nonneg κ
    nlinarith [mul_nonneg this hu, mul_nonneg hκ0 hu1]
  rw [modeledQleCost]
  have hstep : C * (1 * (κ ^ 2 * uNorm + κ * u1Norm)) / ε
      ≤ C * (2 * (K ^ 2 * u1Norm)) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_left _ hC
    simpa using hsum
  calc C * (1 * (κ ^ 2 * uNorm + κ * u1Norm)) / ε
      ≤ C * (2 * (K ^ 2 * u1Norm)) / ε := hstep
    _ = (2 * K ^ 2 * C) * u1Norm / ε := by ring

theorem modeledOptimal_accuracy_exponent_is_one (C0 u1Norm ε : ℝ) (hC0 : 0 ≤ C0) :
    ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → 0 ≤ u1Norm → 0 < ε →
      modeledQleCost C0 1 κ u1Norm u1Norm ε ≤ 2 * C0 * u1Norm / ε := by
  intro κ hκ0 hκ1 hu1 hε
  have := modeledOptimal_preconditioning_bound C0 κ 1 u1Norm u1Norm ε
    hC0 hκ0 hκ1 le_rfl hu1 hu1 le_rfl hε
  simpa using this

def modeledClassicalNoPrecondExp (d k : ℕ) : ℝ := ((d : ℝ) + 1) / ((k : ℝ) + 1)

def modeledClassicalOptExp (d : ℕ) : ℝ := (d : ℝ) / 2

def modeledQuantumNoPrecondExp (k : ℕ) : ℝ := ((k : ℝ) + 5) / ((k : ℝ) + 1)

def modeledQuantumOptExp : ℝ := 1

def modeledClassicalNoPrecondRuntime (d k : ℕ) (ε : ℝ) : ℝ :=
  (1 / ε) ^ modeledClassicalNoPrecondExp d k

def modeledQuantumNoPrecondRuntime (k : ℕ) (ε : ℝ) : ℝ :=
  (1 / ε) ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) +
    (1 / ε) ^ (((k : ℝ) + 3) / ((k : ℝ) + 1))

def modeledQuantumOptRuntime (ε : ℝ) : ℝ := 1 / ε

def modeledClassicalOptRuntime (d : ℕ) (ε : ℝ) : ℝ := (1 / ε) ^ modeledClassicalOptExp d

theorem modeledSpeedup_is_at_most_polynomial (d k : ℕ) (_hk : 1 ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      modeledClassicalNoPrecondRuntime d k ε / modeledQuantumNoPrecondRuntime k ε
        ≤ (1 / ε) ^ B := by

  refine ⟨max 0 (modeledClassicalNoPrecondExp d k -
      ((k : ℝ) + 3) / ((k : ℝ) + 1)), le_max_left _ _, ?_⟩
  intro ε hε0 hε1
  have h1ε : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]
    linarith

  rw [modeledQuantumNoPrecondRuntime, modeledClassicalNoPrecondRuntime]

  set X : ℝ := 1 / ε with hX_def
  have hX1 : (1 : ℝ) ≤ X := h1ε
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX1
  have hden_pos : 0 < X ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) +
      X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) := by
    have h1 : 0 < X ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hXpos _
    have h2 : 0 < X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hXpos _
    linarith
  have hden_ge : X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) ≤
      X ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) +
      X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) := by
    have : 0 ≤ X ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) := by positivity
    linarith
  have hratio : X ^ modeledClassicalNoPrecondExp d k /
      (X ^ (((k : ℝ) + 5) / ((k : ℝ) + 1)) +
       X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)))
      ≤ X ^ modeledClassicalNoPrecondExp d k /
        X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1)) := by
    exact div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ X ^ modeledClassicalNoPrecondExp d k)
      (Real.rpow_pos_of_pos hXpos _) hden_ge
  have hpow : X ^ modeledClassicalNoPrecondExp d k /
      X ^ (((k : ℝ) + 3) / ((k : ℝ) + 1))
      = X ^ (modeledClassicalNoPrecondExp d k -
          ((k : ℝ) + 3) / ((k : ℝ) + 1)) := by
    rw [← Real.rpow_sub hXpos]
  rw [hpow] at hratio
  refine le_trans hratio ?_

  apply Real.rpow_le_rpow_of_exponent_le hX1
  exact le_max_right _ _

theorem modeledDimension_four_exponents :
    modeledClassicalNoPrecondExp 4 1 = 5 / 2 ∧
    modeledQuantumNoPrecondExp 1 = 3 ∧
    modeledClassicalOptExp 4 = 2 ∧
    modeledQuantumOptExp = 1 ∧
    modeledQuantumNoPrecondExp 1 > modeledClassicalNoPrecondExp 4 1 ∧
    modeledClassicalOptExp 4 > modeledQuantumOptExp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [
    modeledClassicalNoPrecondExp, modeledQuantumNoPrecondExp, modeledClassicalOptExp, modeledQuantumOptExp]

theorem modeledDimension_dependence (k : ℕ) (d d' : ℕ) (hd : d < d') (hk : 1 ≤ k) :
    modeledClassicalNoPrecondExp d k < modeledClassicalNoPrecondExp d' k ∧
    modeledQuantumNoPrecondExp k = modeledQuantumNoPrecondExp k := by
  refine ⟨?_, rfl⟩
  unfold modeledClassicalNoPrecondExp
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : (d : ℝ) < (d' : ℝ) := by exact_mod_cast hd
  have : ((d : ℝ) + 1) / ((k : ℝ) + 1) < ((d' : ℝ) + 1) / ((k : ℝ) + 1) := by
    apply div_lt_div_of_pos_right _ hk1
    linarith
  exact this

end Qatlib.Papers.QuantumFEM15.CostModels
