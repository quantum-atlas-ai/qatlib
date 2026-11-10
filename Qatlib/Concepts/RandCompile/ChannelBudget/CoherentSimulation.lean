/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.CoherentSimulationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib
open Matrix Encoding SignalProcessing
open scoped Classical Matrix.Norms.L2Operator BigOperators

theorem generalScaleAngle_bounds (k : ℕ) :
    0 < generalScaleAngle k ∧ generalScaleAngle k < Real.pi := by
  have hd : (0 : ℝ) < 2 * 3 ^ k := by positivity
  have hone : (1 : ℝ) ≤ 3 ^ k := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by positivity : (3 : ℕ) ^ k ≠ 0))
  have h2 : (1 : ℝ) < 2 * 3 ^ k := by
    have h := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  constructor
  · exact div_pos Real.pi_pos hd
  · rw [generalScaleAngle, div_lt_iff₀ hd]
    nlinarith [Real.pi_pos]

theorem generalScaleAngle_sin_nonneg (k : ℕ) : 0 ≤ Real.sin (generalScaleAngle k) := by
  have h := generalScaleAngle_bounds k
  exact (Real.sin_pos_of_pos_of_lt_pi h.1 h.2).le

theorem generalScaleAngle_tripling (k : ℕ) :
    (3 : ℝ) ^ k * generalScaleAngle k = Real.pi / 2 := by
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  rw [generalScaleAngle]
  field_simp

theorem generalScaleAttenuation_entry (s : ℝ) (k : ℕ) :
    generalScaleAttenuation s k false false =
      (s * Real.sin (generalScaleAngle k) : ℂ) := by
  simp [generalScaleAttenuation, scaleEightRotation]

theorem generalScaleAttenuation_unitary {s : ℝ} {k : ℕ}
    (h : generalScaleAdmissible s k) :
    generalScaleAttenuation s k ∈ Matrix.unitaryGroup Bool ℂ := by
  refine scaleEightRotation_unitary _ ?_
  rw [abs_of_nonneg (mul_nonneg h.1 (generalScaleAngle_sin_nonneg k))]
  exact h.2

private theorem generalScaleLift_evaluate {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (cs.map scaleEightLiftStep) =
    TensorGate (1 : Matrix Bool Bool ℂ) (evaluate O cs) := by
  induction cs with
  | nil => simp [evaluate, tensorGate_one]
  | cons c cs ih =>
    cases c <;> simp [List.map_cons, scaleEightLiftStep, evaluate, instructionMatrix, ih,
      tensorGate_conjTranspose, tensorGate_mul]

private theorem generalScaleLift_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (generalScaleLiftWord cs) := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons, scaleEightLiftStep, generalScaleLiftWord,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
      WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨tensorGate_unitary (Submonoid.one_mem _) hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

private theorem generalScaleLiftWord_counts {H : Type} (cs : List (AdjointStep H)) :
    adjointQueryCount (cs.map scaleEightLiftStep) = adjointQueryCount cs ∧
    adjointGateCount (cs.map scaleEightLiftStep) = adjointGateCount cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    cases c <;> simp [List.map_cons, scaleEightLiftStep, adjointQueryCount,
      adjointGateCount, ih]

private theorem generalScaleAttenuationWord_counts {H : Type} (s : ℝ) (k : ℕ)
    (cs : List (AdjointStep H)) :
    adjointQueryCount (generalScaleAttenuationWord s k cs) = adjointQueryCount cs ∧
    adjointGateCount (generalScaleAttenuationWord s k cs) = adjointGateCount cs + 1 := by
  have hm := generalScaleLiftWord_counts cs
  simp [generalScaleAttenuationWord, generalScaleLiftWord, adjointQueryCount_append,
    adjointGateCount_append, adjointQueryCount, adjointGateCount, hm]

theorem generalScaleAttenuationWord_wellFormed {H : Type} [Fintype H] [DecidableEq H]
    {s : ℝ} {k : ℕ} (O : Matrix H H ℂ)
    (h : generalScaleAdmissible s k)
    (cs : List (AdjointStep H)) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (generalScaleAttenuationWord s k cs) ∧
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAttenuationWord s k cs) =
      TensorGate (generalScaleAttenuation s k) (evaluate O cs) := by
  refine ⟨?_, ?_⟩
  · rw [generalScaleAttenuationWord, WellFormedAdjointCircuit.append_iff]
    refine ⟨generalScaleLift_wellFormed cs hcs, ?_⟩
    have hu := tensorGate_unitary (generalScaleAttenuation_unitary h)
      (Submonoid.one_mem (Matrix.unitaryGroup H ℂ))
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    convert! hu using 1
    ext ⟨b,h⟩ ⟨c,k⟩
    simp [tensorGate_apply, Matrix.one_apply]
  · rw [generalScaleAttenuationWord, evaluate_append]
    simp only [generalScaleLiftWord]
    rw [generalScaleLift_evaluate]
    simp [evaluate, instructionMatrix, tensorGate_mul]

private theorem generalScaleLevels_properties {H I : Type} [Fintype H] [DecidableEq H]
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

theorem generalScaleAmplifyWord_counts {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] {s : ℝ} {k : ℕ}
    (h : generalScaleAdmissible s k)
    (R : Matrix H I ℂ) (cs : List (AdjointStep H))
    (hR : IsIsometry R) (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (generalScaleAmplifyWord s k R cs) ∧
    adjointQueryCount (generalScaleAmplifyWord s k R cs) = 3^k * adjointQueryCount cs ∧
    adjointGateCount (generalScaleAmplifyWord s k R cs)+2 = 3^k*(adjointGateCount cs+3) := by
  have hbody := generalScaleAttenuationWord_wellFormed (1 : Matrix H H ℂ) h cs hcs
  have hcnt := generalScaleAttenuationWord_counts s k cs
  have hl := generalScaleLevels_properties (scaleEightFrame R) (scaleEightFrame_isometry R hR)
    (generalScaleAttenuationWord s k cs) hbody.1 k
  change WellFormedAdjointCircuit
      (scaleEightLevels (scaleEightFrame R) k (generalScaleAttenuationWord s k cs)) ∧ _
  refine ⟨hl.1, ?_, ?_⟩
  · simpa [generalScaleAmplifyWord, hcnt.1] using! hl.2.1
  · have hg : adjointGateCount (generalScaleAttenuationWord s k cs) + 2 =
        (adjointGateCount cs + 3) := by omega
    simpa [generalScaleAmplifyWord, hcnt.2, hg] using! hl.2.2

private theorem generalScaleLevels_error {H I : Type} [Fintype H] [DecidableEq H]
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
    have hwf := (generalScaleLevels_properties R hR body hbody k).1
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

theorem generalScale_compressed_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ) {s : ℝ} {k : ℕ} (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : generalScaleAdmissible s k)
    (henc : BlockEncoding V (evaluate O cs) R R s ε) :
    ‖compress (scaleEightFrame R)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAmplifyWord s k R cs))
      (scaleEightFrame R)-V‖ ≤ (15 : ℝ)^k*ε := by
  have hbody := generalScaleAttenuationWord_wellFormed O h cs hcs
  have heval : evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O)
      (generalScaleAttenuationWord s k cs) =
      TensorGate (generalScaleAttenuation s k) (evaluate O cs) := hbody.2
  have hbase : ‖compress (scaleEightFrame R)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAttenuationWord s k cs))
      (scaleEightFrame R)-(Real.sin (generalScaleAngle k) : ℂ) • V‖ ≤ ε := by
    rw [heval, scaleEightFrame_compress]
    rw [generalScaleAttenuation_entry]
    have he : (s * Real.sin (generalScaleAngle k) : ℂ) • compress R (evaluate O cs) R -
        (Real.sin (generalScaleAngle k) : ℂ) • V =
        Real.sin (generalScaleAngle k) • ((s : ℝ) • compress R (evaluate O cs) R - V) := by
      ext i j
      simp [Complex.real_smul]
      ring
    rw [he, norm_smul, Real.norm_eq_abs]
    have hb : ‖(s : ℝ) • compress R (evaluate O cs) R - V‖ ≤ ε := by
      rw [norm_sub_rev]; exact henc.error_le
    calc
      _ ≤ |Real.sin (generalScaleAngle k)| * ε :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ ε := by nlinarith [Real.abs_sin_le_one (generalScaleAngle k), henc.error_nonneg]
  have he := generalScaleLevels_error (TensorGate (1 : Matrix Bool Bool ℂ) O)
    (scaleEightFrame R) (generalScaleAttenuationWord s k cs) V (generalScaleAngle k) ε
    (tensorGate_unitary (Submonoid.one_mem _) hO) (scaleEightFrame_isometry R henc.right_isometry)
    hbody.1 hV hbase k
  rw [generalScaleAngle_tripling, Real.sin_pi_div_two,
    Complex.ofReal_one, one_smul] at he
  simpa only [generalScaleAmplifyWord] using! he

theorem generalScale_workspace_bound {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ) {s : ℝ} {k : ℕ} (ε : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : generalScaleAdmissible s k)
    (henc : BlockEncoding V (evaluate O cs) R R s ε) (ψ : QState I) :
    ‖toEuclidean_fromVec
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAmplifyWord s k R cs)*ᵥ
        (scaleEightFrame R*ᵥψ)-scaleEightFrame R*ᵥ(V*ᵥψ))‖ ≤
    Real.sqrt (2*((15 : ℝ)^k*ε))*‖toEuclidean_fromVec ψ‖ := by
  have hwf := (generalScaleAmplifyWord_counts h R cs henc.right_isometry hcs).1
  have he := scaleEight_clean_from_compression V
    (evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAmplifyWord s k R cs))
    (scaleEightFrame R) ((15 : ℝ)^k*ε) hV
    (hwf.evaluate_unitary (tensorGate_unitary (Submonoid.one_mem _) hO))
    (scaleEightFrame_isometry R henc.right_isometry)
    (mul_nonneg (by positivity) henc.error_nonneg)
    (generalScale_compressed_error O R cs V ε hO hcs hV h henc) ψ
  simpa only [show (2 : ℝ)*((15 : ℝ)^k*ε) = 2*(15 : ℝ)^k*ε by ring] using! he

theorem generalScale_exact_amplification {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) (V : Matrix I I ℂ) {s : ℝ} {k : ℕ}
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (h : generalScaleAdmissible s k)
    (henc : BlockEncoding V (evaluate O cs) R R s 0) (ψ : QState I) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (generalScaleAmplifyWord s k R cs)*ᵥ
      (scaleEightFrame R*ᵥψ) = scaleEightFrame R*ᵥ(V*ᵥψ) := by
  have he := generalScale_workspace_bound O R cs V 0 hO hcs hV h henc ψ
  simp only [mul_zero, Real.sqrt_zero, zero_mul] at he
  have hz := norm_eq_zero.mp (le_antisymm he (norm_nonneg _))
  have hz' : evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O)
      (generalScaleAmplifyWord s k R cs)*ᵥ(scaleEightFrame R*ᵥψ)-
      scaleEightFrame R*ᵥ(V*ᵥψ) = 0 := by
    funext i
    simpa only [toEuclidean_fromVec_apply, Pi.zero_apply] using! congrArg (fun v => v i) hz
  exact sub_eq_zero.mp hz'

theorem applyGate_smul {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (c : ℂ) (ψ : QState I) :
    ApplyGate U (c • ψ) = c • ApplyGate U ψ := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, Pi.smul_apply]
  calc
    ∑ j, U i j * (c * ψ j) = ∑ j, c * (U i j * ψ j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = c * ∑ j, U i j * ψ j := by rw [Finset.mul_sum]

theorem demoLeakProjector_apply_success :
    demoLeakProjector *ᵥ demoSuccessState = demoSuccessState := by
  funext i
  cases i <;> rw [Matrix.mulVec, dotProduct, Fintype.sum_bool] <;>
    simp [demoLeakProjector, demoSuccessState]

theorem demoLeakProjector_apply_leak :
    demoLeakProjector *ᵥ demoLeakState = 0 := by
  funext i
  cases i <;> rw [Matrix.mulVec, dotProduct, Fintype.sum_bool] <;>
    simp [demoLeakProjector, demoLeakState]

theorem demoSuccessBranch :
    ProjectiveBranch demoLeakProjector true demoSuccessState = demoSuccessState ∧
    ProjectiveBranch demoLeakProjector true demoLeakState = 0 := by
  constructor
  · have h := demoLeakProjector_apply_success
    simpa [ProjectiveBranch, ApplyGate] using! h
  · have h := demoLeakProjector_apply_leak
    simpa [ProjectiveBranch, ApplyGate] using! h

theorem demoSuccessMass :
    ProjectiveBranchMass demoLeakProjector true demoSuccessState = 1 ∧
    ProjectiveBranchMass demoLeakProjector true demoLeakState = 0 := by
  constructor
  · have h := demoSuccessBranch.1
    simp [ProjectiveBranchMass, h, MeasureProb, BornProb, demoSuccessState]
  · have h := demoSuccessBranch.2
    simp [ProjectiveBranchMass, h, MeasureProb, BornProb]

theorem normalizedSuccessBranch_success :
    normalizedSuccessBranch demoLeakProjector demoSuccessState = demoSuccessState := by
  funext i
  simp [normalizedSuccessBranch, ProjectiveBranch, ApplyGate, Matrix.mulVec, dotProduct,
    MeasureProb, BornProb, demoLeakProjector, demoSuccessState]

theorem normalizedSuccessBranch_scaled :
    normalizedSuccessBranch demoLeakProjector (2 • demoSuccessState) = demoSuccessState := by
  funext i
  simp [normalizedSuccessBranch, ProjectiveBranch, ApplyGate, Matrix.mulVec, dotProduct,
    MeasureProb, BornProb, demoLeakProjector, demoSuccessState]

theorem successConditionedState_not_a_unary :
    normalizedSuccessBranch demoLeakProjector (2 • demoSuccessState) =
      normalizedSuccessBranch demoLeakProjector demoSuccessState ∧
    (2 • demoSuccessState) ≠ demoSuccessState ∧
    (∀ (U : Matrix Bool Bool ℂ) (ψ : QState Bool),
      ApplyGate U ((2 : ℂ) • ψ) = (2 : ℂ) • ApplyGate U ψ) := by
  refine ⟨by rw [normalizedSuccessBranch_scaled, normalizedSuccessBranch_success], ?_, ?_⟩
  · intro h
    have h2 := congrFun h false
    simp [demoSuccessState] at h2
  · intro U ψ
    exact applyGate_smul U 2 ψ

theorem coherent_oaa_distorts_scaled_target {I : Type} [Fintype I] [DecidableEq I]
    (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    scaleEightCubic ((Real.sin (Real.pi/6) : ℂ) • V) = (1 : ℂ) • V := by
  have hang : 3 * (Real.pi/6) = Real.pi/2 := by ring
  rw [scaleEightCubic_sin V hV, hang, Real.sin_pi_div_two]
  simp

theorem coherent_oaa_distorts_scaled_target_strict {I : Type} [Fintype I]
    [DecidableEq I] [Nonempty I] (V : Matrix I I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    scaleEightCubic ((Real.sin (Real.pi/6) : ℂ) • V) ≠ ((Real.sin (Real.pi/6) : ℂ) • V) := by
  rw [coherent_oaa_distorts_scaled_target V hV]
  intro h
  have hv : V * Vᴴ = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  obtain ⟨i⟩ : Nonempty I := ‹Nonempty I›
  have h2 := congrArg (fun M : Matrix I I ℂ => M * Vᴴ) h
  simp only [Matrix.smul_mul] at h2
  rw [hv] at h2
  have h3 := congrArg (fun M : Matrix I I ℂ => M i i) h2
  simp at h3

end Qatlib.Concepts.RandCompile.ChannelBudget
