/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QMAAmplify09.MainResults.Defs

noncomputable def blockAngle (p : ℝ) : ℝ := Real.arccos (Real.sqrt p)

noncomputable def phaseOfProbability (p : ℝ) : ℝ :=
  blockAngle p / Real.pi

noncomputable def probabilityOfPhase (φ : ℝ) : ℝ :=
  (Real.cos (Real.pi * φ)) ^ 2

theorem cos_sq_blockAngle {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Real.cos (blockAngle p)) ^ 2 = p := by
  have h0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have h1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hm1 : -1 ≤ Real.sqrt p := by linarith
  unfold blockAngle
  rw [Real.cos_arccos hm1 h1, Real.sq_sqrt hp0]

theorem blockAngle_mem (p : ℝ) :
    0 ≤ blockAngle p ∧ blockAngle p ≤ Real.pi / 2 := by
  constructor
  · exact Real.arccos_nonneg _
  · exact Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg p)

theorem phaseOfProbability_eq_blockAngle_div_pi (p : ℝ) :
    phaseOfProbability p = blockAngle p / Real.pi := rfl

theorem probabilityOfPhase_eq_cos_sq (φ : ℝ) :
    probabilityOfPhase φ = (Real.cos (Real.pi * φ)) ^ 2 := rfl

theorem probabilityOfPhase_phaseOfProbability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probabilityOfPhase (phaseOfProbability p) = p := by
  unfold probabilityOfPhase phaseOfProbability
  rw [mul_comm, div_mul_cancel₀ _ Real.pi_ne_zero,
    cos_sq_blockAngle hp0 hp1]

theorem phaseOfProbability_nonneg (p : ℝ) : 0 ≤ phaseOfProbability p := by
  unfold phaseOfProbability
  exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le

theorem phaseOfProbability_le_half (p : ℝ) :
    phaseOfProbability p ≤ 1 / 2 := by
  unfold phaseOfProbability blockAngle
  rw [div_le_iff₀ Real.pi_pos]
  have h : Real.arccos (Real.sqrt p) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg p)
  nlinarith [h, Real.pi_pos]

theorem phaseOfProbability_antitone {p q : ℝ} (hpq : p ≤ q) :
    phaseOfProbability q ≤ phaseOfProbability p := by
  unfold phaseOfProbability
  exact div_le_div_of_nonneg_right
    (Real.arccos_le_arccos (Real.sqrt_le_sqrt hpq)) Real.pi_pos.le

structure PromiseBounds where

  a : ℝ

  b : ℝ
  b_nonneg : 0 ≤ b
  lt : b < a
  a_le_one : a ≤ 1

namespace PromiseBounds

theorem a_pos (P : PromiseBounds) : 0 < P.a := lt_of_le_of_lt P.b_nonneg P.lt

theorem a_nonneg (P : PromiseBounds) : 0 ≤ P.a := P.a_pos.le

theorem gap_pos (P : PromiseBounds) : 0 < P.a - P.b := sub_pos.mpr P.lt

theorem b_le_one (P : PromiseBounds) : P.b ≤ 1 := le_trans P.lt.le P.a_le_one

noncomputable def phaseGap (P : PromiseBounds) : ℝ :=
  phaseOfProbability P.b - phaseOfProbability P.a

theorem phaseGap_nonneg (P : PromiseBounds) : 0 ≤ phaseGap P := by
  unfold phaseGap
  exact sub_nonneg.mpr (phaseOfProbability_antitone P.lt.le)

noncomputable def phasePrecision (P : PromiseBounds) : ℝ := phaseGap P / 2

end PromiseBounds

end Qatlib.Papers.QMAAmplify09.MainResults.Defs
