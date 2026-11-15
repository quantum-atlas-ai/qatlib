/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentWeightedForm
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentGap

@[expose] public section
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra

namespace Qatlib.Concepts.QuantumGibbs.CkgBounds

open Matrix

variable {D : ℕ}

/-- Scaling the first argument of the Hilbert-Schmidt inner product conjugates the scalar. -/
theorem hsInner_smul_left (c : ℂ) (U V : Operator D) :
    hsInner (c • U) V = star c * hsInner U V := by
  simp [hsInner, Matrix.conjTranspose_smul, Matrix.trace_smul]

/-- The parent factor is complex-linear in its family operator argument. -/
theorem parentFactor_smul (ρ : Operator D) (c : ℂ) (B O : Operator D) :
    parentFactor ρ (c • B) O = c • parentFactor ρ B O := by
  simp [parentFactor_apply, sharp, flat, smul_sub]

/-- The sum of the damped forms for an operator pair and its oppositely phase-rotated pair
equals the corresponding sum of plain forms. -/
theorem pairFamily_cancel {β : ℝ} {ρ M N O : Operator D} {ν : Fin 2 → ℝ}
    (W : ℝ → ℝ → ℝ) :
    wdampedForm (fun a b => W (ν a) (ν b)) β ρ ν ![M, N] O
      + wdampedForm (fun a b => W (ν a) (ν b)) β ρ ν ![Complex.I • M, -Complex.I • N] O
    = wplainForm (fun a b => W (ν a) (ν b)) ρ ![M, N] O
      + wplainForm (fun a b => W (ν a) (ν b)) ρ ![Complex.I • M, -Complex.I • N] O := by
  have h0 : phaseKernel β (ν 0 - ν 0) = 1 / 2 := by
    rw [sub_self]; exact phaseKernel_self β
  have h1 : phaseKernel β (ν 1 - ν 1) = 1 / 2 := by
    rw [sub_self]; exact phaseKernel_self β
  have sII : star (Complex.I) * Complex.I = 1 := by
    norm_num [Complex.conj_I, Complex.I_mul_I]
  have sInI : star (Complex.I) * (-Complex.I) = -1 := by
    norm_num [Complex.conj_I, Complex.I_mul_I]
  have sInI2 : star (-Complex.I) * Complex.I = -1 := by
    norm_num [Complex.conj_I, Complex.I_mul_I, star_neg]
  have snn : star (-Complex.I) * (-Complex.I) = 1 := by
    norm_num [Complex.conj_I, Complex.I_mul_I, star_neg]
  have e00 : hsInner (parentFactor ρ (Complex.I • M) O) (parentFactor ρ (Complex.I • M) O)
      = hsInner (parentFactor ρ M O) (parentFactor ρ M O) := by
    rw [parentFactor_smul, hsInner_smul_left, hsInner_smul_right, ← mul_assoc, sII, one_mul]
  have e01 : hsInner (parentFactor ρ (Complex.I • M) O) (parentFactor ρ (-Complex.I • N) O)
      = -(hsInner (parentFactor ρ M O) (parentFactor ρ N O)) := by
    rw [parentFactor_smul, parentFactor_smul, hsInner_smul_left, hsInner_smul_right,
      ← mul_assoc, sInI, neg_one_mul]
  have e10 : hsInner (parentFactor ρ (-Complex.I • N) O) (parentFactor ρ (Complex.I • M) O)
      = -(hsInner (parentFactor ρ N O) (parentFactor ρ M O)) := by
    rw [parentFactor_smul, parentFactor_smul, hsInner_smul_left, hsInner_smul_right,
      ← mul_assoc, sInI2, neg_one_mul]
  have e11 : hsInner (parentFactor ρ (-Complex.I • N) O) (parentFactor ρ (-Complex.I • N) O)
      = hsInner (parentFactor ρ N O) (parentFactor ρ N O) := by
    rw [parentFactor_smul, hsInner_smul_left, hsInner_smul_right, ← mul_assoc, snn, one_mul]
  simp only [wdampedForm, wplainForm, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, e00, e01, e10, e11]
  rw [h0, h1]
  push_cast
  ring

/-- For a single operator at one frequency, the weighted damped and plain forms agree. -/
theorem singleFamily_eq {β ν0 : ℝ} {ρ P O : Operator D} (W : ℝ → ℝ → ℝ) :
    wdampedForm (fun a b => W (![ν0] a) (![ν0] b)) β ρ ![ν0] ![P] O
      = wplainForm (fun a b => W (![ν0] a) (![ν0] b)) ρ ![P] O := by
  simp only [wdampedForm, wplainForm, Fin.sum_univ_one, Matrix.cons_val_zero]
  rw [sub_self, phaseKernel_self]
  push_cast
  ring

end Qatlib.Concepts.QuantumGibbs.CkgBounds
