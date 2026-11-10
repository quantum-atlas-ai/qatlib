/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem suzuki_unitary_observable_error {I : Type} [Fintype I] [DecidableEq I]
    (U V O : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    ‖Vᴴ * O * V - Uᴴ * O * U‖ ≤ 2 * ‖O‖ * ‖V - U‖ := by
  have hUn : ‖Uᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact l2_norm_unitary_le_one hU
  have hVn : ‖V‖ ≤ 1 := l2_norm_unitary_le_one hV
  have hd : ‖Vᴴ - Uᴴ‖ = ‖V - U‖ := by
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  have he : Vᴴ * O * V - Uᴴ * O * U =
      (Vᴴ - Uᴴ) * O * V + Uᴴ * O * (V - U) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(Vᴴ - Uᴴ) * O * V‖ + ‖Uᴴ * O * (V - U)‖ := norm_add_le _ _
    _ ≤ ‖V - U‖ * ‖O‖ + ‖O‖ * ‖V - U‖ := by
      apply add_le_add
      · calc
          _ ≤ (‖Vᴴ - Uᴴ‖ * ‖O‖) * ‖V‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg V))
          _ ≤ _ := by rw [hd]; nlinarith [mul_nonneg (norm_nonneg (V - U)) (norm_nonneg O)]
      · calc
          _ ≤ (‖Uᴴ‖ * ‖O‖) * ‖V - U‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg O) (norm_nonneg (V - U))]
    _ = _ := by ring

theorem suzuki_fourth_order_same_word_observable_consumer :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A B O : Matrix I I ℂ)
      (t : ℝ) (r : ℕ), A.IsHermitian → B.IsHermitian → 0 < r →
      let V := suzuki4Run A B t r
      let U := hamiltonianEvolution (A + B) t
      ‖Vᴴ * O * V - Uᴴ * O * U‖ ≤
        200 * ‖O‖ * (‖A‖ + ‖B‖) ^ 5 * |t| ^ 5 / (r : ℝ) ^ 4 := by
  intro I _ _ A B O t r hA hB hr
  obtain ⟨hV, _, herr⟩ := suzuki_fourth_order_actual_word_and_cost I A B t r hA hB hr
  have hU := Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary (hA.add hB) t
  exact (suzuki_unitary_observable_error _ _ O hU hV).trans
    ((mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 2 * ‖O‖)).trans_eq (by ring))

end Qatlib.Concepts.TrotterFormula.SuzukiFourth
