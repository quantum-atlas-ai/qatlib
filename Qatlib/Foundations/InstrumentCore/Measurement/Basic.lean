/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.InstrumentCore.Measurement

open Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def Projector (S : Finset I) : Matrix I I ℂ :=
  Matrix.diagonal fun i => if i ∈ S then 1 else 0

theorem projector_mul_self (S : Finset I) : Projector S * Projector S = Projector S := by
  unfold Projector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem projector_conjTranspose (S : Finset I) : (Projector S)ᴴ = Projector S := by
  unfold Projector
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem projector_univ : Projector (Finset.univ : Finset I) = 1 := by
  unfold Projector
  simp

noncomputable def Collapse (ψ : QState I) (S : Finset I) : QState I :=
  ApplyGate (Projector S) ψ

theorem collapse_apply (ψ : QState I) (S : Finset I) (i : I) :
    Collapse ψ S i = if i ∈ S then ψ i else 0 := by
  unfold Collapse ApplyGate Projector
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem bornProb_collapse (ψ : QState I) (S : Finset I) (i : I) :
    BornProb (Collapse ψ S) i = if i ∈ S then BornProb ψ i else 0 := by
  unfold BornProb
  rw [collapse_apply]
  split_ifs <;> simp

theorem sum_normSq_collapse (ψ : QState I) (S : Finset I) :
    ∑ i, ‖Collapse ψ S i‖ ^ 2 = MeasureProb ψ S := by
  unfold MeasureProb
  rw [show (fun i => ‖Collapse ψ S i‖ ^ 2) = fun i => BornProb (Collapse ψ S) i from rfl]
  simp_rw [bornProb_collapse]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

noncomputable def PostMeasure (ψ : QState I) (S : Finset I) : QState I :=
  fun i => (Real.sqrt (MeasureProb ψ S) : ℂ)⁻¹ * Collapse ψ S i

theorem postMeasure_eq_zero_of_measureProb_eq_zero {ψ : QState I} {S : Finset I}
    (h : MeasureProb ψ S = 0) : PostMeasure ψ S = 0 := by
  funext i
  simp [PostMeasure, h]

theorem normalized_postMeasure {ψ : QState I} {S : Finset I} (h : 0 < MeasureProb ψ S) :
    Normalized (PostMeasure ψ S) := by
  have hsqrt : (0 : ℝ) < Real.sqrt (MeasureProb ψ S) := Real.sqrt_pos_of_pos h
  unfold Normalized PostMeasure
  simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
  rw [sum_normSq_collapse, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsqrt.le, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

theorem postMeasure_apply_of_not_mem (ψ : QState I) (S : Finset I) {i : I} (hi : i ∉ S) :
    PostMeasure ψ S i = 0 := by
  unfold PostMeasure
  rw [collapse_apply, if_neg hi, mul_zero]

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def MarginalProbLeft (ψ : QState (I × J)) (S : Finset I) : ℝ :=
  MeasureProb ψ (S ×ˢ Finset.univ)

noncomputable def MarginalProbRight (ψ : QState (I × J)) (T : Finset J) : ℝ :=
  MeasureProb ψ (Finset.univ ×ˢ T)

theorem marginalProbLeft_tensorState (ψ : QState I) {φ : QState J} (hφ : Normalized φ)
    (S : Finset I) : MarginalProbLeft (TensorState ψ φ) S = MeasureProb ψ S :=
  measureProb_tensorState_left hφ ψ S

theorem marginalProbRight_tensorState {ψ : QState I} (hψ : Normalized ψ) (φ : QState J)
    (T : Finset J) : MarginalProbRight (TensorState ψ φ) T = MeasureProb φ T :=
  measureProb_tensorState_right hψ φ T

end Qatlib.Foundations.InstrumentCore.Measurement
