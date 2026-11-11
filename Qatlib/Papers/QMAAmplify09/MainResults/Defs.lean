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

/-!
# Acceptance probabilities and phases for QMA amplification

The functions `blockAngle`, `phaseOfProbability`, and `probabilityOfPhase` relate acceptance
probabilities to rotation phases. Their range, inversion, and monotonicity properties support
phase-threshold comparisons.

The structure `PromiseBounds` records `0 ≤ b < a ≤ 1`, while `phaseGap` and `phasePrecision`
encode the corresponding phase separation and half-gap precision. See [NagajWocjanZhang2009] for
the paper's setting.

## Main statements

* `blockAngle`: The angle `arccos (sqrt p)` associated with acceptance probability `p`.
* `phasePrecision`: The phase-estimation precision defined as half of the promise phase gap.

## References

* [Nagaj et al., 2009][NagajWocjanZhang2009]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QMAAmplify09.MainResults.Defs

/-- The angle `arccos (sqrt p)` associated with acceptance probability `p`. -/
noncomputable def blockAngle (p : ℝ) : ℝ := Real.arccos (Real.sqrt p)

/-- The normalized angle `blockAngle p / π` associated with acceptance probability `p`. -/
noncomputable def phaseOfProbability (p : ℝ) : ℝ :=
  blockAngle p / Real.pi

/-- The acceptance probability `(cos (π*φ))²` associated with phase `φ`. -/
noncomputable def probabilityOfPhase (φ : ℝ) : ℝ :=
  (Real.cos (Real.pi * φ)) ^ 2

/-- For `p ∈ [0, 1]`, the squared cosine of `blockAngle p` is `p`. -/
theorem cos_sq_blockAngle {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Real.cos (blockAngle p)) ^ 2 = p := by
  have h0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have h1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hm1 : -1 ≤ Real.sqrt p := by linarith
  unfold blockAngle
  rw [Real.cos_arccos hm1 h1, Real.sq_sqrt hp0]

/-- For every real `p`, the angle `blockAngle p` lies in `[0, π/2]`. -/
theorem blockAngle_mem (p : ℝ) :
    0 ≤ blockAngle p ∧ blockAngle p ≤ Real.pi / 2 := by
  constructor
  · exact Real.arccos_nonneg _
  · exact Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg p)

/-- The phase associated with `p` is its block angle divided by `π`. -/
theorem phaseOfProbability_eq_blockAngle_div_pi (p : ℝ) :
    phaseOfProbability p = blockAngle p / Real.pi := rfl

/-- The probability associated with `φ` is the squared cosine of `π*φ`. -/
theorem probabilityOfPhase_eq_cos_sq (φ : ℝ) :
    probabilityOfPhase φ = (Real.cos (Real.pi * φ)) ^ 2 := rfl

/-- For `p ∈ [0, 1]`, converting `p` to a phase and back recovers `p`. -/
theorem probabilityOfPhase_phaseOfProbability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probabilityOfPhase (phaseOfProbability p) = p := by
  unfold probabilityOfPhase phaseOfProbability
  rw [mul_comm, div_mul_cancel₀ _ Real.pi_ne_zero,
    cos_sq_blockAngle hp0 hp1]

/-- The phase associated with any real `p` is nonnegative. -/
theorem phaseOfProbability_nonneg (p : ℝ) : 0 ≤ phaseOfProbability p := by
  unfold phaseOfProbability
  exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le

/-- The phase associated with any real `p` is at most `1 / 2`. -/
theorem phaseOfProbability_le_half (p : ℝ) :
    phaseOfProbability p ≤ 1 / 2 := by
  unfold phaseOfProbability blockAngle
  rw [div_le_iff₀ Real.pi_pos]
  have h : Real.arccos (Real.sqrt p) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (Real.sqrt_nonneg p)
  nlinarith [h, Real.pi_pos]

/-- The function `phaseOfProbability` reverses order on real inputs. -/
theorem phaseOfProbability_antitone {p q : ℝ} (hpq : p ≤ q) :
    phaseOfProbability q ≤ phaseOfProbability p := by
  unfold phaseOfProbability
  exact div_le_div_of_nonneg_right
    (Real.arccos_le_arccos (Real.sqrt_le_sqrt hpq)) Real.pi_pos.le

/-- Completeness and soundness thresholds `a, b` satisfying `0 ≤ b < a ≤ 1`. -/
structure PromiseBounds where

  a : ℝ

  b : ℝ
  b_nonneg : 0 ≤ b
  lt : b < a
  a_le_one : a ≤ 1

namespace PromiseBounds

/-- The completeness threshold of `PromiseBounds` is positive. -/
theorem a_pos (P : PromiseBounds) : 0 < P.a := lt_of_le_of_lt P.b_nonneg P.lt

/-- The completeness threshold of `PromiseBounds` is nonnegative. -/
theorem a_nonneg (P : PromiseBounds) : 0 ≤ P.a := P.a_pos.le

/-- The difference between the completeness and soundness thresholds is positive. -/
theorem gap_pos (P : PromiseBounds) : 0 < P.a - P.b := sub_pos.mpr P.lt

/-- The soundness threshold of `PromiseBounds` is at most one. -/
theorem b_le_one (P : PromiseBounds) : P.b ≤ 1 := le_trans P.lt.le P.a_le_one

/-- The phase separation `phaseOfProbability P.b - phaseOfProbability P.a` of the promise
thresholds. -/
noncomputable def phaseGap (P : PromiseBounds) : ℝ :=
  phaseOfProbability P.b - phaseOfProbability P.a

/-- The phase gap associated with `PromiseBounds` is nonnegative. -/
theorem phaseGap_nonneg (P : PromiseBounds) : 0 ≤ phaseGap P := by
  unfold phaseGap
  exact sub_nonneg.mpr (phaseOfProbability_antitone P.lt.le)

/-- The phase-estimation precision defined as half of the promise phase gap. -/
noncomputable def phasePrecision (P : PromiseBounds) : ℝ := phaseGap P / 2

end PromiseBounds

end Qatlib.Papers.QMAAmplify09.MainResults.Defs
