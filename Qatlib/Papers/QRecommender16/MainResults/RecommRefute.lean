/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.MainResults.SamplingErrors
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section


/-! One-atom counterexamples to the complete legacy sampled-approximation contracts.

All matrices have one row and two columns. The target and low-rank comparison
are zero, whereas the alleged random approximation is constantly nonzero.
The original headers do not relate that approximation to a sampling law.
-/
set_option autoImplicit false
noncomputable section

open MeasureTheory
open Qatlib.Papers.QRecommender16.MainResults.MatrixSampling
open scoped Matrix.Norms.Frobenius

namespace Qatlib.Papers.QRecommender16.MainResults.SamplingRefute

/-- The one-point probability space has every set measurable. -/
local instance unitSpace : MeasurableSpace Unit := ⊤

/-- The positive finite matrix dimensions used throughout the counterexamples. -/
abbrev Mat := Matrix (Fin 1) (Fin 2) ℝ

/-- A nonzero constant approximation, unrelated to the zero target matrix. -/
def badMatrix : Mat := fun _ _ => 1

/-- An entry of the alleged approximation equals one, so the matrix is nonzero. -/
theorem bad_matrix_ne_zero : badMatrix ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Mat => A 0 0) h
  norm_num [badMatrix] at hentry

/-- The actual Frobenius norm of the nonzero finite matrix is strictly positive. -/
theorem bad_matrix_norm_pos : 0 < ‖badMatrix‖ :=
  norm_pos_iff.mpr bad_matrix_ne_zero

/-- The approximation event collapses to an empty set when the target is zero. -/
theorem bad_event_empty : {_ω : Unit | ‖badMatrix‖ ≤ 0} = ∅ := by
  ext _ω
  constructor
  · intro h
    exact (not_le_of_gt bad_matrix_norm_pos) h
  · intro h
    exact False.elim h

/-- The source confidence lower bound is strictly positive at two columns. -/
theorem confidence_pos :
    0 < 1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hneg : -19 * (Real.log (2 : ℝ)) ^ 4 < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) (pow_pos hlog 4)
  have hexp : Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) < 1 := by
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr hneg)
  exact sub_pos.mpr hexp

/-- The chosen single-atom measure satisfies the complete probability-measure assumption. -/
theorem point_probability :
    IsProbabilityMeasure (Measure.dirac () : Measure Unit) := by
  constructor
  exact Measure.dirac_apply_of_mem (Set.mem_univ ())

/-- the stated model fails with all original assumptions at a one-point sample space. -/
theorem theorem42_contract_false :
    ¬ (∀ (P : Measure Unit) (_hP : IsProbabilityMeasure P)
      (A Ak : Mat) (Ah : Unit → Mat) (k : ℕ) (η μ p : ℝ),
      0 < k → 0 < η → 0 < μ → 0 < p → p ≤ 1 →
      (1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4)) ≤
        (P {ω | ‖A - Ah ω‖ ≤ ‖A - Ak‖ +
          (samplingError η μ k + Real.sqrt (μ / p)) * ‖A‖}).toReal) := by
  intro h
  have hbound := h (Measure.dirac ()) point_probability
    0 0 (fun _ => badMatrix) 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_sub, norm_neg, norm_zero, mul_zero, add_zero] at hbound
  rw [bad_event_empty] at hbound
  have hzero : 1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) ≤ 0 := by
    simpa using hbound
  exact (not_le_of_gt confidence_pos) hzero

/-- the stated model fails while its complete sampling-parameter inequality is satisfied. -/
theorem theorem42_cor_contract_false :
    ¬ (∀ (P : Measure Unit) (_hP : IsProbabilityMeasure P)
      (A _Ak : Mat) (Ah : Unit → Mat) (k : ℕ) (η μ p ε : ℝ),
      0 < k → 0 < η → 0 < μ → 0 < p → p ≤ 1 → 0 < ε →
      samplingError η μ k + Real.sqrt (μ / p) ≤ 2 * ε →
      (1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4)) ≤
        (P {ω | ‖A - Ah ω‖ ≤ 3 * ε * ‖A‖}).toReal) := by
  intro h
  have hdev :
      samplingError 1 1 1 + Real.sqrt ((1 : ℝ) / 1) ≤ 2 * (2 : ℝ) := by
    norm_num [samplingError]
  have hbound := h (Measure.dirac ()) point_probability
    0 0 (fun _ => badMatrix) 1 1 1 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hdev
  simp only [zero_sub, norm_neg, norm_zero, mul_zero] at hbound
  rw [bad_event_empty] at hbound
  have hzero : 1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) ≤ 0 := by
    simpa using hbound
  exact (not_le_of_gt confidence_pos) hzero

/-- the stated model fails with positive parameters and admissible precision zero. -/
theorem theorem43_contract_false :
    ¬ (∀ (P : Measure Unit) (_hP : IsProbabilityMeasure P)
      (A Ak : Mat) (Ah : Unit → Mat) (k : ℕ) (η μ p κ : ℝ),
      0 < k → 0 < η → 0 < μ → 0 < p → p ≤ 1 → 0 ≤ κ → κ < 1 →
      (1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4)) ≤
        (P {ω | ‖A - Ah ω‖ ≤ 3 * ‖A - Ak‖ +
          (precisionError η μ κ k + (3 - κ) * Real.sqrt (2 * μ / p)) * ‖A‖}).toReal) := by
  intro h
  have hbound := h (Measure.dirac ()) point_probability
    0 0 (fun _ => badMatrix) 1 1 1 (1 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_sub, norm_neg, norm_zero, mul_zero, add_zero] at hbound
  rw [bad_event_empty] at hbound
  have hzero : 1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) ≤ 0 := by
    simpa using hbound
  exact (not_le_of_gt confidence_pos) hzero

/-- the stated model fails while all original precision and deviation hypotheses hold. -/
theorem theorem43_cor_contract_false :
    ¬ (∀ (P : Measure Unit) (_hP : IsProbabilityMeasure P)
      (A _Ak : Mat) (Ah : Unit → Mat) (k : ℕ) (η μ p κ ε : ℝ),
      0 < k → 0 < η → 0 < μ → 0 < p → p ≤ 1 → 0 ≤ κ → κ < 1 → 0 < ε →
      precisionError η μ κ k + (3 - κ) * Real.sqrt (2 * μ / p) ≤ 6 * ε →
      (1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4)) ≤
        (P {ω | ‖A - Ah ω‖ ≤ 9 * ε * ‖A‖}).toReal) := by
  intro h
  have hdev :
      precisionError 1 1 0 1 + (3 - (0 : ℝ)) *
        Real.sqrt (2 * (1 : ℝ) / (1 / 2)) ≤ 6 * (3 : ℝ) := by
    norm_num [precisionError]
  have hbound := h (Measure.dirac ()) point_probability
    0 0 (fun _ => badMatrix) 1 1 1 (1 / 2) 0 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdev
  simp only [zero_sub, norm_neg, norm_zero, mul_zero] at hbound
  rw [bad_event_empty] at hbound
  have hzero : 1 - Real.exp (-19 * (Real.log (2 : ℝ)) ^ 4) ≤ 0 := by
    simpa using hbound
  exact (not_le_of_gt confidence_pos) hzero

end Qatlib.Papers.QRecommender16.MainResults.SamplingRefute
