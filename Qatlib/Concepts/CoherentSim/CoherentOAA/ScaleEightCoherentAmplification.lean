/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical Matrix.Norms.L2Operator

noncomputable def scaleEightRotation (c : ℝ) : Matrix Bool Bool ℂ := fun b b' =>
  if b then (if b' then (c : ℂ) else (Real.sqrt (1-c^2) : ℂ))
  else (if b' then -(Real.sqrt (1-c^2) : ℂ) else (c : ℂ))

noncomputable def scaleEightAttenuation : Matrix Bool Bool ℂ :=
  scaleEightRotation (8*Real.sin (Real.pi/54))

noncomputable def scaleEightDemoRotation : Matrix Bool Bool ℂ := scaleEightRotation (1/8)

noncomputable def scaleEightFrame {H I : Type} [Fintype H] [Fintype I]
    (R : Matrix H I ℂ) : Matrix (Bool × H) I ℂ := fun x i =>
  if x.1 = false then R x.2 i else 0

noncomputable def scaleEightLiftStep {H : Type} : AdjointStep H → AdjointStep (Bool × H)
  | .gate G => .gate (TensorGate (1 : Matrix Bool Bool ℂ) G)
  | .forward => .forward
  | .backward => .backward

noncomputable def scaleEightLiftWord {H : Type} (cs : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  cs.map scaleEightLiftStep ++ [.gate (TensorGate scaleEightAttenuation 1)]

noncomputable def scaleEightLevels {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) :
    ℕ → List (AdjointStep H) → List (AdjointStep H)
  | 0, cs => cs
  | k+1, cs => substituteAdjointCircuit (scaleEightLevels R k cs) (coherentOAAWord R)

noncomputable def scaleEightAmplifyWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) (cs : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  scaleEightLevels (scaleEightFrame R) 3 (scaleEightLiftWord cs)

theorem scaleEightRotation_unitary (c : ℝ) (hc : |c| ≤ 1) :
    scaleEightRotation c ∈ Matrix.unitaryGroup Bool ℂ := by
  have hc2 : 0 ≤ 1-c^2 := by rcases abs_le.mp hc with ⟨hl,hu⟩; nlinarith
  have hs : (Real.sqrt (1-c^2))^2 = 1-c^2 := Real.sq_sqrt hc2
  have hsC : (Real.sqrt (1-c^2) : ℂ)^2 = 1-(c : ℂ)^2 := by exact_mod_cast hs
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext b b'
  cases b <;> cases b' <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, scaleEightRotation] <;>
    ring_nf <;> simp_all

theorem scaleEight_parameter_bounds :
    0 < 8*Real.sin (Real.pi/54) ∧ 8*Real.sin (Real.pi/54) ≤ 1 := by
  have hθ : 0 < Real.pi/54 := by positivity
  have hθπ : Real.pi/54 < Real.pi := by linarith [Real.pi_pos]
  have hp := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hs := Real.sin_le (le_of_lt hθ)
  constructor
  · positivity
  · linarith [Real.pi_lt_four]

theorem scaleEightFrame_isometry {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) (hR : IsIsometry R) :
    IsIsometry (scaleEightFrame R) := by
  unfold IsIsometry at *
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, scaleEightFrame,
    Fintype.sum_prod_type, Fintype.sum_bool] using! congrFun (congrFun hR i) j

private theorem lift_evaluate {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (cs.map scaleEightLiftStep) =
    TensorGate (1 : Matrix Bool Bool ℂ) (evaluate O cs) := by
  induction cs with
  | nil => simp [evaluate, tensorGate_one]
  | cons c cs ih =>
    cases c <;> simp [List.map_cons, scaleEightLiftStep, evaluate, instructionMatrix, ih,
      tensorGate_conjTranspose, tensorGate_mul]

private theorem lift_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (cs.map scaleEightLiftStep) := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons, scaleEightLiftStep,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
      WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨tensorGate_unitary (Submonoid.one_mem _) hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

theorem scaleEightLiftWord_counts {H : Type} (cs : List (AdjointStep H)) :
    adjointQueryCount (scaleEightLiftWord cs) = adjointQueryCount cs ∧
    adjointGateCount (scaleEightLiftWord cs) = adjointGateCount cs+1 := by
  have hm : adjointQueryCount (cs.map scaleEightLiftStep) = adjointQueryCount cs ∧
      adjointGateCount (cs.map scaleEightLiftStep) = adjointGateCount cs := by
    induction cs with
    | nil => exact ⟨rfl,rfl⟩
    | cons c cs ih => cases c <;> simp [scaleEightLiftStep, adjointQueryCount, adjointGateCount, ih]
  simp [scaleEightLiftWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount, hm]

theorem scaleEightFrame_compress {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ)
    (B : Matrix Bool Bool ℂ) (U : Matrix H H ℂ) :
    compress (scaleEightFrame R) (TensorGate B U) (scaleEightFrame R) =
    B false false • compress R U R := by
  ext i j
  simp [compress, Matrix.mul_apply, Matrix.conjTranspose_apply, scaleEightFrame,
    tensorGate_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm]

noncomputable def scaleEightCubic {I : Type} [Fintype I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  (3 : ℂ) • X - (4 : ℂ) • (X*Xᴴ*X)

theorem scaleEightCubic_sin {I : Type} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) (θ : ℝ) :
    scaleEightCubic ((Real.sin θ : ℂ) • V) = (Real.sin (3*θ) : ℂ) • V := by
  have hv : V*Vᴴ = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  rw [scaleEightCubic, Matrix.conjTranspose_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [hv, Matrix.one_mul, ← sub_smul, Real.sin_three_mul]
  congr 1
  push_cast
  ring

theorem scaleEightCubic_lipschitz {I : Type} [Fintype I] [DecidableEq I]
    (X Y : Matrix I I ℂ) (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖scaleEightCubic X - scaleEightCubic Y‖ ≤ 15*‖X-Y‖ := by
  have hc := l2_norm_cubic_sub_cubic_le X Y
  have hb : ‖X‖^2+‖X‖*‖Y‖+‖Y‖^2 ≤ 3 := by
    nlinarith [norm_nonneg X,norm_nonneg Y,
      mul_le_mul hX hY (norm_nonneg Y) (by norm_num : (0 : ℝ) ≤ 1)]
  have hc' : ‖X*Xᴴ*X-Y*Yᴴ*Y‖ ≤ 3*‖X-Y‖ :=
    hc.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  calc
    ‖scaleEightCubic X - scaleEightCubic Y‖ =
        ‖(3 : ℂ)•(X-Y)-(4 : ℂ)•(X*Xᴴ*X-Y*Yᴴ*Y)‖ := by
          congr 1; simp only [scaleEightCubic, smul_sub]; abel
    _ ≤ ‖(3 : ℂ)•(X-Y)‖+‖(4 : ℂ)•(X*Xᴴ*X-Y*Yᴴ*Y)‖ := norm_sub_le _ _
    _ = 3*‖X-Y‖+4*‖X*Xᴴ*X-Y*Yᴴ*Y‖ := by rw [norm_smul,norm_smul]; norm_num
    _ ≤ 15*‖X-Y‖ := by linarith

theorem scaleEight_clean_from_compression {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (W : Matrix H H ℂ)
    (R : Matrix H I ℂ) (δ : ℝ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hW : W ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R) (heta : 0 ≤ δ)
    (herr : ‖compress R W R - V‖ ≤ δ) (ψ : QState I) :
    ‖toEuclidean_fromVec (W*ᵥ(R*ᵥψ)-R*ᵥ(V*ᵥψ))‖ ≤
    Real.sqrt (2*δ)*‖toEuclidean_fromVec ψ‖ := by
  have hc : BlockEncoding V W R R 1 δ := by
    refine ⟨hW, hR, hR, by norm_num, heta, ?_⟩
    simpa only [one_smul, norm_sub_rev] using! herr
  have hb := shared_frame_defect V W R δ hV hc
  simpa only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] using!
    (l2_norm_mulVec_fromVec_le (W * R - R * V) ψ).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

end Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

theorem scale_eight_attenuation_actual_unitary :
    scaleEightAttenuation ∈ Matrix.unitaryGroup Bool ℂ ∧
    scaleEightAttenuation false false = (8*Real.sin (Real.pi/54) : ℝ) ∧
    0 < 8*Real.sin (Real.pi/54) ∧ 8*Real.sin (Real.pi/54) ≤ 1 := by
  have hb := scaleEight_parameter_bounds
  refine ⟨scaleEightRotation_unitary _ ?_, rfl, hb⟩
  rw [abs_of_pos hb.1]; exact hb.2

theorem scale_eight_lift_frame_and_body (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (hR : IsIsometry R) (hcs : WellFormedAdjointCircuit cs) :
    IsIsometry (scaleEightFrame R) ∧ WellFormedAdjointCircuit (scaleEightLiftWord cs) ∧
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightLiftWord cs) =
      TensorGate scaleEightAttenuation (evaluate O cs) := by
  refine ⟨scaleEightFrame_isometry R hR,?_,?_⟩
  · rw [scaleEightLiftWord, WellFormedAdjointCircuit.append_iff]
    refine ⟨lift_wellFormed cs hcs,?_⟩
    have hu := tensorGate_unitary scale_eight_attenuation_actual_unitary.1
      (Submonoid.one_mem (Matrix.unitaryGroup H ℂ))
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    convert! hu using 1
    ext ⟨b,h⟩ ⟨c,k⟩
    simp [tensorGate_apply, Matrix.one_apply]
  · rw [scaleEightLiftWord, evaluate_append, lift_evaluate]
    simp [evaluate, instructionMatrix, tensorGate_mul]

private theorem scaleEightLevels_properties {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) (hR : IsIsometry R)
    (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) (k : ℕ) :
    WellFormedAdjointCircuit (scaleEightLevels R k cs) ∧
    adjointQueryCount (scaleEightLevels R k cs) = 3^k * adjointQueryCount cs ∧
    adjointGateCount (scaleEightLevels R k cs)+2 = 3^k*(adjointGateCount cs+2) := by
  induction k with
  | zero => simp [scaleEightLevels, hcs]
  | succ k ih =>
    have he := coherent_oaa_expanded_subroutine (1 : Matrix H H ℂ)
      (scaleEightLevels R k cs) R ih.1 hR
    refine ⟨he.2.2.2,?_,?_⟩
    · rw [scaleEightLevels, he.2.1, ih.2.1, pow_succ]; ring
    · rw [scaleEightLevels, he.2.2.1, pow_succ]
      nlinarith [ih.2.2]

theorem scale_eight_three_level_actual_counts (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (hR : IsIsometry R) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (scaleEightAmplifyWord R cs) ∧
    adjointQueryCount (scaleEightAmplifyWord R cs) = 27*adjointQueryCount cs ∧
    adjointGateCount (scaleEightAmplifyWord R cs) = 27*adjointGateCount cs+79 := by
  have h := scale_eight_lift_frame_and_body H I 1 R cs hR hcs
  have hc := scaleEightLiftWord_counts cs
  have hl := scaleEightLevels_properties (scaleEightFrame R) h.1
    (scaleEightLiftWord cs) h.2.1 3
  change WellFormedAdjointCircuit
      (scaleEightLevels (scaleEightFrame R) 3 (scaleEightLiftWord cs)) ∧ _
  refine ⟨hl.1,?_,?_⟩
  · simpa [scaleEightAmplifyWord, hc.1] using! hl.2.1
  · simp only [show (3 : ℕ)^3 = 27 by norm_num, hc.2] at hl
    change adjointGateCount (scaleEightLevels (scaleEightFrame R) 3 (scaleEightLiftWord cs)) = _
    omega

private theorem scaleEightLevels_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (body : List (AdjointStep H)) (V : Matrix I I ℂ) (θ ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R)
    (hbody : WellFormedAdjointCircuit body) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (hbase : ‖compress R (evaluate O body) R - (Real.sin θ : ℂ) • V‖ ≤ ε) (k : ℕ) :
    ‖compress R (evaluate O (scaleEightLevels R k body)) R -
      (Real.sin ((3 : ℝ)^k*θ) : ℂ) • V‖ ≤ (15 : ℝ)^k*ε := by
  induction k with
  | zero => simpa [scaleEightLevels] using! hbase
  | succ k ih =>
    have hwf := (scaleEightLevels_properties R hR body hbody k).1
    have hU := hwf.evaluate_unitary hO
    have he := coherent_oaa_expanded_subroutine O (scaleEightLevels R k body) R hwf hR
    have hpoly := (coherent_oaa_word_correct _ R hR hU).2.2.2.2
    have hX : ‖compress R (evaluate O (scaleEightLevels R k body)) R‖ ≤ 1 :=
      (compress_norm_le hR hR _).trans (unitary_norm_le_one hU)
    have hY : ‖(Real.sin ((3 : ℝ)^k*θ) : ℂ) • V‖ ≤ 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (Real.abs_sin_le_one _) (unitary_norm_le_one hV)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)
    rw [scaleEightLevels, he.1, hpoly]
    change ‖scaleEightCubic (compress R (evaluate O (scaleEightLevels R k body)) R) - _‖ ≤ _
    have hangle : (3 : ℝ)^(k+1)*θ = 3*((3 : ℝ)^k*θ) := by rw [pow_succ]; ring
    rw [hangle, ← scaleEightCubic_sin V hV]
    calc
      _ ≤ 15*‖compress R (evaluate O (scaleEightLevels R k body)) R -
        (Real.sin ((3 : ℝ)^k*θ) : ℂ) • V‖ := scaleEightCubic_lipschitz _ _ hX hY
      _ ≤ 15*((15 : ℝ)^k*ε) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (15 : ℝ)^(k+1)*ε := by rw [pow_succ]; ring

theorem scaleEight_compressed_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ) (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V (evaluate O cs) R R 8 ε) :
    ‖compress (scaleEightFrame R)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightAmplifyWord R cs))
      (scaleEightFrame R)-V‖ ≤ 3375*ε := by
  have hl := scale_eight_lift_frame_and_body H I O R cs h.right_isometry hcs
  have hbase : ‖compress (scaleEightFrame R)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightLiftWord cs))
      (scaleEightFrame R)-(Real.sin (Real.pi/54) : ℂ) • V‖ ≤ ε := by
    rw [hl.2.2, scaleEightFrame_compress]
    have he : scaleEightAttenuation false false • compress R (evaluate O cs) R -
        (Real.sin (Real.pi/54) : ℂ) • V =
        Real.sin (Real.pi/54) • ((8 : ℝ) • compress R (evaluate O cs) R - V) := by
      ext i j
      simp [scaleEightAttenuation, scaleEightRotation, Complex.real_smul]
      ring
    rw [he, norm_smul, Real.norm_eq_abs]
    have hb : ‖(8 : ℝ) • compress R (evaluate O cs) R - V‖ ≤ ε := by
      rw [norm_sub_rev]; exact h.error_le
    calc
      _ ≤ |Real.sin (Real.pi/54)| * ε := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ ε := by nlinarith [Real.abs_sin_le_one (Real.pi/54), h.error_nonneg]
  have he := scaleEightLevels_error (TensorGate (1 : Matrix Bool Bool ℂ) O)
    (scaleEightFrame R) (scaleEightLiftWord cs) V (Real.pi/54) ε
    (tensorGate_unitary (Submonoid.one_mem _) hO) hl.1 hl.2.1 hV hbase 3
  have ha : (3 : ℝ)^3*(Real.pi/54) = Real.pi/2 := by ring
  simpa only [ha, Real.sin_pi_div_two, Complex.ofReal_one, one_smul,
    show (15 : ℝ)^3 = 3375 by norm_num, scaleEightAmplifyWord] using! he

theorem scale_eight_noisy_clean_workspace_bound (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ) (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V (evaluate O cs) R R 8 ε)
    (ψ : QState I) :
    ‖toEuclidean_fromVec
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightAmplifyWord R cs)*ᵥ
        (scaleEightFrame R*ᵥψ)-scaleEightFrame R*ᵥ(V*ᵥψ))‖ ≤
    Real.sqrt (6750*ε)*‖toEuclidean_fromVec ψ‖ := by
  have hwf := (scale_eight_three_level_actual_counts H I R cs h.right_isometry hcs).1
  have he := scaleEight_clean_from_compression V
    (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightAmplifyWord R cs))
    (scaleEightFrame R) (3375*ε) hV
    (hwf.evaluate_unitary (tensorGate_unitary (Submonoid.one_mem _) hO))
    (scaleEightFrame_isometry R h.right_isometry) (mul_nonneg (by norm_num) h.error_nonneg)
    (scaleEight_compressed_error O R cs V ε hO hcs hV h) ψ
  simpa only [show (2 : ℝ)*(3375*ε) = 6750*ε by ring] using! he

theorem scale_eight_exact_clean_amplification (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (h : BlockEncoding V (evaluate O cs) R R 8 0)
    (ψ : QState I) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightAmplifyWord R cs)*ᵥ
      (scaleEightFrame R*ᵥψ) = scaleEightFrame R*ᵥ(V*ᵥψ) := by
  have he := scale_eight_noisy_clean_workspace_bound H I O R cs V 0 hO hcs hV h ψ
  simp only [mul_zero, Real.sqrt_zero, zero_mul] at he
  have hz := norm_eq_zero.mp (le_antisymm he (norm_nonneg _))
  have hz' : evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O)
      (scaleEightAmplifyWord R cs)*ᵥ(scaleEightFrame R*ᵥψ)-
      scaleEightFrame R*ᵥ(V*ᵥψ) = 0 := by
    funext i
    simpa only [toEuclidean_fromVec_apply, Pi.zero_apply] using! congrArg (fun v => v i) hz
  exact sub_eq_zero.mp hz'
end Qatlib.Concepts.CoherentSim.CoherentOAA
