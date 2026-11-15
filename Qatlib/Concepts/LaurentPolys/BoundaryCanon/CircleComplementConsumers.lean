/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.CircleComplement

@[expose] public section
set_option autoImplicit false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection
noncomputable section
namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The scalar circle completion matrix is unitary when the two squared evaluation norms sum to
one. -/
private theorem circle_scalar_unitary (P Q : Polynomial ℂ) (z : ℂ)
    (hs : ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) : circleCompletion P Q z ∈ Matrix.unitaryGroup Bool ℂ := by
  have hn : P.eval z*star (P.eval z)+Q.eval z*star (Q.eval z) = 1 := by
    calc
      _ = ((‖P.eval z‖^2+‖Q.eval z‖^2 : ℝ) : ℂ) := by
        simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [hs]; rfl
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, circleCompletion, Bool.false_eq_true, ite_false, ite_true,
      star_neg, star_star, Matrix.one_apply, Bool.true_eq_false, mul_neg]
  · linear_combination hn
  · ring
  · ring
  · linear_combination hn

/-- The circle completion maps the false basis vector to the vector of the two polynomial
evaluations. -/
private theorem circle_scalar_output (P Q : Polynomial ℂ) (z : ℂ) :
    (circleCompletion P Q z).mulVec (fun b : Bool => if b then 0 else 1) =
      (fun b : Bool => if b then Q.eval z else P.eval z) := by
  ext b
  cases b <;> simp [circleCompletion, Matrix.mulVec, dotProduct]

/-- The complementary polynomial identity gives a unitary circle completion whose false basis
output consists of the two polynomial evaluations. -/
theorem circle_complement_actual_filter_consumer (P Q : Polynomial ℂ) (z : ℂ)
    (hz : ‖z‖ = 1) (hs : ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) :
    circleCompletion P Q z ∈ Matrix.unitaryGroup Bool ℂ ∧
    (circleCompletion P Q z).mulVec (fun b : Bool => if b then 0 else 1) =
      (fun b : Bool => if b then Q.eval z else P.eval z) := by
  have hzero : circleResidual (C (P.eval z)) (C (Q.eval z)) z ≤ 0 := by
    have hc := circle_complement_coefficient_residual_certificate
      (C (P.eval z)) (C (Q.eval z)) (C (P.eval z)) (C (Q.eval z)) 0
      (by norm_num) (by simp) (by simp)
      (fun w _ => by simpa only [eval_C] using hs) z hz
    simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hc
  have habs : |‖P.eval z‖^2+‖Q.eval z‖^2-1| = 0 :=
    le_antisymm (by simpa only [circleResidual, eval_C] using hzero) (abs_nonneg _)
  have hnorm : ‖P.eval z‖^2+‖Q.eval z‖^2 = 1 := by
    have hh := abs_eq_zero.mp habs
    linarith
  exact ⟨circle_scalar_unitary P Q z hnorm, circle_scalar_output P Q z⟩

/-- Every degree bounded polynomial with unit circle modulus at most one admits a complement of
the same degree bound realizing the stated unitary filter output. -/
theorem circle_complement_exists_actual_filter (P : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ d ∧
      ∀ z : ℂ, ‖z‖ = 1 →
      circleCompletion P Q z ∈ Matrix.unitaryGroup Bool ℂ ∧
      (circleCompletion P Q z).mulVec (fun b : Bool => if b then 0 else 1) =
        (fun b : Bool => if b then Q.eval z else P.eval z) := by
  obtain ⟨Q,hQ,hcomp⟩ := circle_complement_zero_margin_exists P d hp hb
  exact ⟨Q,hQ,fun z hz => circle_complement_actual_filter_consumer P Q z hz (hcomp z hz)⟩

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
