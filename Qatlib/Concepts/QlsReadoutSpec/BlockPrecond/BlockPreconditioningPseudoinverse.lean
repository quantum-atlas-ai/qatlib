/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.BlockPreconditioning

/-!
# Pseudoinverse identities under state scaling

This module proves the product formula for the pseudoinverse of `stateScaling s b * A` when the
scaling commutes with the range projector `A * matrixPseudoinverse A`. Consistency of the
right-hand side implies this commutation and gives inverse scaling of the solution direction. An
explicit two-dimensional counterexample shows that the product formula need not hold without the
range condition.

Range projections and generalized inverses belong to the matrix-analysis background
[Bhatia1997].

## Main statements

* `stateScaling_pseudoinverse_counterexample`: Exhibits failure of the unrestricted product
  formula.
* `stateScaling_pseudoinverse_of_consistent`: Proves the product formula for a consistent
  normalized right-hand side.
* `stateScaling_pseudoinverse_direction_of_consistent`: Computes the preconditioned solution
  vector.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

variable {H O : Type} [Fintype H] [DecidableEq H] [Fintype O] [DecidableEq O]

namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
noncomputable section

/-- The normalized counterexample state with amplitudes `3 / 5` at `false` and `4 / 5` at
`true`. -/
def preconditioningCounterState : QState Bool :=
  fun j => if j then ((4 / 5 : ℝ) : ℂ) else ((3 / 5 : ℝ) : ℂ)
end
noncomputable section

/-- The diagonal two-dimensional matrix with diagonal entries one at `false` and zero at `true`. -/
def preconditioningCounterMatrix : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun j => if j then (0 : ℂ) else 1)
end
noncomputable section

/-- The explicit counterexample state is normalized. -/
theorem preconditioningCounterState_normalized : Normalized preconditioningCounterState := by
  norm_num [Normalized, BornProb, preconditioningCounterState, Fintype.sum_bool,
    Complex.norm_real, Real.norm_eq_abs]
end
noncomputable section

/-- The counterexample diagonal projector equals its own pseudoinverse. -/
private theorem preconditioningCounterMatrix_pseudoinverse :
    matrixPseudoinverse preconditioningCounterMatrix = preconditioningCounterMatrix := by
  symm
  apply matrixPseudoinverse_unique
  all_goals
    ext i j
    cases i <;> cases j <;>
      norm_num [preconditioningCounterMatrix, Matrix.mul_apply, Fintype.sum_bool,
        Matrix.conjTranspose_apply]
end
noncomputable section

/-- For scale `1 / 2` and the explicit counterexample state and matrix, the pseudoinverse of the
state-scaled matrix differs from the original pseudoinverse multiplied by the inverse
scaling. -/
theorem stateScaling_pseudoinverse_counterexample :
    matrixPseudoinverse (stateScaling (1 / 2) preconditioningCounterState *
        preconditioningCounterMatrix) ≠
      matrixPseudoinverse preconditioningCounterMatrix *
        stateScalingInverse (1 / 2) preconditioningCounterState := by
  intro he
  have hh := mul_matrixPseudoinverse_adjoint
    (stateScaling (1 / 2) preconditioningCounterState * preconditioningCounterMatrix)
  rw [he, preconditioningCounterMatrix_pseudoinverse] at hh
  have hentry := congrArg (fun A : Matrix Bool Bool ℂ => A false true) hh
  norm_num [stateScaling, stateScalingInverse, preconditioningCounterState,
    preconditioningCounterMatrix, outerProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_bool, map_ofNat] at hentry
end
noncomputable section

/-- The counterexample state does not belong to the range of the counterexample matrix. -/
theorem preconditioningCounterState_not_in_range :
    ¬ ∃ z : QState Bool, preconditioningCounterMatrix *ᵥ z = preconditioningCounterState := by
  rintro ⟨z, hz⟩
  have he := congrFun hz true
  norm_num [preconditioningCounterMatrix, preconditioningCounterState,
    Matrix.mulVec, dotProduct, Fintype.sum_bool] at he
end
noncomputable section

/-- For a nonzero scale and normalized `b`, commutation of the state scaling with `A *
matrixPseudoinverse A` implies the pseudoinverse product formula. -/
theorem stateScaling_pseudoinverse_of_range_commutation {I : Type}
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (s : ℝ) (b : QState O)
    (hs : s ≠ 0) (hb : Normalized b)
    (hcomm : stateScaling s b * (A * matrixPseudoinverse A) =
      (A * matrixPseudoinverse A) * stateScaling s b) :
    matrixPseudoinverse (stateScaling s b * A) =
      matrixPseudoinverse A * stateScalingInverse s b := by
  have hinv := stateScaling_inverse s b hs hb
  have hAB : (stateScaling s b * A) *
        (matrixPseudoinverse A * stateScalingInverse s b) = A * matrixPseudoinverse A := by
    calc
      _ = (stateScaling s b * (A * matrixPseudoinverse A)) * stateScalingInverse s b := by
        simp only [Matrix.mul_assoc]
      _ = ((A * matrixPseudoinverse A) * stateScaling s b) * stateScalingInverse s b := by rw [hcomm]
      _ = _ := by rw [Matrix.mul_assoc, hinv.1, Matrix.mul_one]
  have hBA : (matrixPseudoinverse A * stateScalingInverse s b) *
        (stateScaling s b * A) = matrixPseudoinverse A * A := by
    calc
      _ = matrixPseudoinverse A * (stateScalingInverse s b * stateScaling s b) * A := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv.2, Matrix.mul_one]
  symm
  apply matrixPseudoinverse_unique
  · rw [hAB]
    calc
      _ = ((A * matrixPseudoinverse A) * stateScaling s b) * A := (Matrix.mul_assoc _ _ _).symm
      _ = (stateScaling s b * (A * matrixPseudoinverse A)) * A := by rw [hcomm]
      _ = stateScaling s b * (A * matrixPseudoinverse A * A) := Matrix.mul_assoc _ _ _
      _ = _ := by rw [mul_matrixPseudoinverse_mul]
  · rw [hBA]
    simp only [← Matrix.mul_assoc, matrixPseudoinverse_mul_self]
  · rw [hAB]
    exact mul_matrixPseudoinverse_adjoint A
  · rw [hBA]
    exact matrixPseudoinverse_mul_adjoint A
end
noncomputable section

/-- For normalized `b` in the range of `A`, state scaling commutes with the range projector `A *
matrixPseudoinverse A`. -/
theorem stateScaling_commutes_range_of_consistent {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (s : ℝ) (b : QState O) (hb : Normalized b)
    (hc : ∃ z : QState I, A *ᵥ z = b) :
    stateScaling s b * (A * matrixPseudoinverse A) =
      (A * matrixPseudoinverse A) * stateScaling s b := by
  have hPb : (A * matrixPseudoinverse A) *ᵥ b = b := by
    obtain ⟨z, rfl⟩ := hc
    rw [Matrix.mulVec_mulVec, mul_matrixPseudoinverse_mul]
  have hPOuter : (A * matrixPseudoinverse A) * outerProduct b = outerProduct b := by
    ext i j
    simp only [Matrix.mul_apply, outerProduct_apply]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    change (((A * matrixPseudoinverse A) *ᵥ b) i) * (starRingEnd ℂ) (b j) =
      b i * (starRingEnd ℂ) (b j)
    rw [hPb]
  have hOuterAdj : (outerProduct b)ᴴ = outerProduct b := (isOrthogonalProjector_outerProduct hb).2
  have hOuterP : outerProduct b * (A * matrixPseudoinverse A) = outerProduct b := by
    have h := congrArg Matrix.conjTranspose hPOuter
    rw [Matrix.conjTranspose_mul, hOuterAdj, mul_matrixPseudoinverse_adjoint] at h
    exact h
  simp only [stateScaling, one_smul, mul_sub, sub_mul, mul_one, one_mul,
    smul_mul_assoc, Matrix.mul_smul, hPOuter, hOuterP]
end
noncomputable section

/-- For a nonzero scale and normalized consistent right-hand side, the preconditioned
pseudoinverse equals the original pseudoinverse multiplied by the inverse state scaling. -/
theorem stateScaling_pseudoinverse_of_consistent {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (s : ℝ) (b : QState O) (hs : s ≠ 0) (hb : Normalized b)
    (hc : ∃ z : QState I, A *ᵥ z = b) :
    matrixPseudoinverse (stateScaling s b * A) =
      matrixPseudoinverse A * stateScalingInverse s b :=
  stateScaling_pseudoinverse_of_range_commutation A s b hs hb
    (stateScaling_commutes_range_of_consistent A s b hb hc)
end
noncomputable section

/-- For a nonzero scale and normalized consistent right-hand side, applying the preconditioned
pseudoinverse to `b` multiplies the original solution vector by `s⁻¹`. -/
theorem stateScaling_pseudoinverse_direction_of_consistent {I : Type}
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (s : ℝ) (b : QState O)
    (hs : s ≠ 0) (hb : Normalized b) (hc : ∃ z : QState I, A *ᵥ z = b) :
    matrixPseudoinverse (stateScaling s b * A) *ᵥ b =
      ((s : ℝ)⁻¹ : ℂ) • (matrixPseudoinverse A *ᵥ b) := by
  rw [stateScaling_pseudoinverse_of_consistent A s b hs hb hc,
    ← Matrix.mulVec_mulVec, (stateScaling_direction s b hb).2, Matrix.mulVec_smul]
end
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
