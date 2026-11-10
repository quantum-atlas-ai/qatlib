/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.BlockPrecond.PreconditionedNormGap
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator
variable {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

theorem preconditioning_scale_and_solution (A : Matrix O I ℂ) (b : QState O) (κ t c s : ℝ)
    (hb : Normalized b) (hκ : 1<κ) (hc : 1< c) (ht : 0< t) (hs : s=t/(c*κ))
    (hgap : ∀ i : Fin (Fintype.card I),0< matrixSingularValues A i→ κ⁻¹≤ matrixSingularValues A i)
    (hconsistent : ∃ z : QState I,A*ᵥz=b)
    (hτ : t/c<‖stateVector (matrixPseudoinverse A*ᵥb)‖) :
    0< s ∧ s<1 ∧ κ≤‖stateVector (matrixPseudoinverse (stateScaling s b*A)*ᵥb)‖ := by
  have hκ0 : 0<κ := by linarith
  have hc0 : 0< c := by linarith
  have hs0 : 0< s := by rw [hs];positivity
  have hA : ‖matrixPseudoinverse A‖≤κ := by
    simpa only [inv_inv] using! matrixPseudoinverse_norm_le (inv_pos.mpr hκ0) hgap
  have hτκ : ‖stateVector (matrixPseudoinverse A*ᵥb)‖≤κ := by
    have hh : ‖stateVector (matrixPseudoinverse A*ᵥb)‖≤‖matrixPseudoinverse A‖*‖stateVector b‖ :=
        l2_norm_mulVec_fromVec_le (matrixPseudoinverse A) b
    rw [(normalized_iff_stateVector_norm b).mp hb,mul_one] at hh
    exact hh.trans hA
  have htκ : t< c*κ := by have hh:=(div_lt_iff₀ hc0).mp hτ;nlinarith
  have hs1 : s<1 := by
    rw [hs];apply (div_lt_one (mul_pos hc0 hκ0)).mpr;simpa only [mul_comm] using! htκ
  refine ⟨hs0,hs1,?_⟩
  rw [stateScaling_pseudoinverse_direction_of_consistent A s b hs0.ne' hb hconsistent]
  change κ≤‖((s:ℝ)⁻¹:ℂ)•stateVector (matrixPseudoinverse A*ᵥb)‖
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs0]
  have hτs : s*κ<‖stateVector (matrixPseudoinverse A*ᵥb)‖ := by
    have he : s*κ=t/c := by rw [hs];field_simp
    rwa [he]
  have hh:=mul_le_mul_of_nonneg_left hτs.le (inv_pos.mpr hs0).le
  have he : s⁻¹*(s*κ)=κ := by field_simp
  exact he ▸ hh

theorem preconditioning_normalized_target (A : Matrix O I ℂ) (b : QState O) (s c₀ : ℝ)
    (hs : 0< s) (hc : 0< c₀) (hb : Normalized b) (hconsistent : ∃ z : QState I,A*ᵥz=b) :
    NormedSpace.normalize (stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb))=
      NormedSpace.normalize (stateVector (matrixPseudoinverse A*ᵥb)) := by
  have hd:=stateScaling_pseudoinverse_direction_of_consistent A s b hs.ne' hb hconsistent
  have he : stateVector (((c₀:ℂ)•matrixPseudoinverse (stateScaling s b*A))*ᵥb)=
      (c₀*s⁻¹)•stateVector (matrixPseudoinverse A*ᵥb) := by
    rw [Matrix.smul_mulVec,hd,smul_smul]
    ext i
    simp only [stateVector,PiLp.smul_apply,Pi.smul_apply,Complex.real_smul,smul_eq_mul]
    push_cast
    rfl
  rw [he]
  exact NormedSpace.normalize_smul_of_pos (mul_pos hc (inv_pos.mpr hs)) _
end Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
