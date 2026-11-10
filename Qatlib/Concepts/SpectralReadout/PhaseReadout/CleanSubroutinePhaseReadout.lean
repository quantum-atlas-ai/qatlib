/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CleanQPEBands
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
open Qatlib.Foundations.InstrumentCore.Measurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.SpectralReadout.PhaseReadout

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

inductive CleanCircuitBridge {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (R : Matrix H I ℂ) : Circuit H → Circuit I → Prop
  | nil : CleanCircuitBridge R [] []
  | gate {C D} (U : Matrix H H ℂ) (T : Matrix I I ℂ)
      (hU : U ∈ Matrix.unitaryGroup H ℂ) (hT : T ∈ Matrix.unitaryGroup I ℂ)
      (hR : U * R = R * T) (tail : CleanCircuitBridge R C D) :
      CleanCircuitBridge R (.gate U :: C) (.gate T :: D)
  | query {C D} (tail : CleanCircuitBridge R C D) :
      CleanCircuitBridge R (.query :: C) (.query :: D)

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

theorem CleanCircuitBridge.unitary {R : Matrix H I ℂ} {C : Circuit H} {D : Circuit I}
    (h : CleanCircuitBridge R C D) : IsUnitaryCircuit C ∧ IsUnitaryCircuit D := by
  induction h with
  | nil => simp
  | gate U T hU hT _ _ ih => simp [hU, hT, ih.1, ih.2]
  | query _ ih => simpa using! ih

theorem CleanCircuitBridge.append {R : Matrix H I ℂ} {C C' : Circuit H}
    {D D' : Circuit I} (h : CleanCircuitBridge R C D)
    (h' : CleanCircuitBridge R C' D') : CleanCircuitBridge R (C ++ C') (D ++ D') := by
  induction h with
  | nil => exact h'
  | gate U T hU hT hR _ ih => exact .gate U T hU hT hR ih
  | query _ ih => exact .query ih

theorem CleanCircuitBridge.error {R : Matrix H I ℂ} {C : Circuit H} {D : Circuit I}
    (h : CleanCircuitBridge R C D) (O : Matrix H H ℂ) (V : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (η : ℝ) (_hη : 0 ≤ η) (he : ‖O * R - R * V‖ ≤ η) (ψ : QState I) :
    ‖toEuclidean_fromVec (Run O C (R *ᵥ ψ) - R *ᵥ Run V D ψ)‖ ≤
      (QueryCount D : ℝ) * η * ‖toEuclidean_fromVec ψ‖ := by
  induction h generalizing ψ with
  | nil => simp [Run, QueryCount, toEuclidean_fromVec]
  | gate U T hU hT hR tail ih =>
    simp only [Run, ApplyGate, QueryCount]
    rw [Matrix.mulVec_mulVec, hR, ← Matrix.mulVec_mulVec]
    have hh := ih (T *ᵥ ψ)
    have hnorm : ‖toEuclidean_fromVec (T *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
      norm_applyGate_of_mem_unitaryGroup hT ψ
    rw [hnorm] at hh
    exact hh
  | @query C D tail ih =>
    have hs : Run O (.query :: C) (R *ᵥ ψ) - R *ᵥ Run V (.query :: D) ψ =
        Run O C ((O * R - R * V) *ᵥ ψ) +
          (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ)) := by
      simp only [Run, ApplyGate, Matrix.sub_mulVec, Matrix.mulVec_mulVec, run_sub]
      module
    have hh := (norm_run_le O hO tail.unitary.1 ((O * R - R * V) *ᵥ ψ)).trans
      ((l2_norm_mulVec_fromVec_le _ ψ).trans
        (mul_le_mul_of_nonneg_right he (norm_nonneg _)))
    have ht := ih (V *ᵥ ψ)
    have hnorm : ‖toEuclidean_fromVec (V *ᵥ ψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
      norm_applyGate_of_mem_unitaryGroup hV ψ
    rw [hnorm] at ht
    rw [hs]
    have hn : ‖toEuclidean_fromVec
        (Run O C ((O * R - R * V) *ᵥ ψ) +
          (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ)))‖ ≤
        ‖toEuclidean_fromVec (Run O C ((O * R - R * V) *ᵥ ψ))‖ +
        ‖toEuclidean_fromVec (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ))‖ :=
      by
        have hadd := norm_add_le
          (toEuclidean_fromVec (Run O C ((O * R - R * V) *ᵥ ψ)))
          (toEuclidean_fromVec (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ)))
        rw [show toEuclidean_fromVec (Run O C ((O * R - R * V) *ᵥ ψ)) +
            toEuclidean_fromVec (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ)) =
            toEuclidean_fromVec (Run O C ((O * R - R * V) *ᵥ ψ) +
              (Run O C (R *ᵥ (V *ᵥ ψ)) - R *ᵥ Run V D (V *ᵥ ψ))) from rfl] at hadd
        exact hadd
    simp only [QueryCount, Nat.cast_add, Nat.cast_one]
    nlinarith

private theorem controlled_frame_defect (W : Matrix H H ℂ) (V : Matrix I I ℂ)
    (R : Matrix H I ℂ) :
    controlOracle W * ((1 : Matrix Bool Bool ℂ) ⊗ₖ R) -
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ R) * controlOracle V =
        Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0) ⊗ₖ
          (W * R - R * V) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;>
    simp [controlOracle, select, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply]

private theorem clean_frame_defect_bound (M : ℕ) (W : Matrix H H ℂ)
    (V : Matrix I I ℂ) (R : Matrix H I ℂ) (η : ℝ) (hη : 0 ≤ η)
    (he : ∀ ξ : QState I,
      ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ξ) - R *ᵥ (V *ᵥ ξ))‖ ≤
        η * ‖toEuclidean_fromVec ξ‖) :
    ‖TensorGate (1 : Operator M) (controlOracle W) * cleanQPEFrame M R -
      cleanQPEFrame M R * TensorGate (1 : Operator M) (controlOracle V)‖ ≤ η := by
  have hd : ‖W * R - R * V‖ ≤ η :=
    l2_opNorm_le_of_mulVec_le hη _ (by simpa [Matrix.sub_mulVec, Matrix.mulVec_mulVec] using! he)
  have hp : ‖Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by intro b; cases b <;> norm_num)
  have hm : ‖(1 : Operator M)‖ ≤ 1 := unitary_norm_le_one (Submonoid.one_mem _)
  have hsub (A B : Matrix (Bool × H) (Bool × I) ℂ) :
      (1 : Operator M) ⊗ₖ A - (1 : Operator M) ⊗ₖ B = (1 : Operator M) ⊗ₖ (A - B) := by
    ext p q
    exact (mul_sub _ _ _).symm
  simp only [TensorGate, cleanQPEFrame, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [hsub, controlled_frame_defect]
  calc
    _ ≤ ‖(1 : Operator M)‖ *
        (‖Matrix.diagonal (fun b : Bool => if b then (1 : ℂ) else 0)‖ * ‖W * R - R * V‖) :=
      (l2_norm_kronecker_le _ _).trans
        (mul_le_mul_of_nonneg_left (l2_norm_kronecker_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * η) := by gcongr
    _ = η := by ring

private theorem clean_phase_gate_bridge (M : ℕ) (R : Matrix H I ℂ)
    (T : Operator M) :
    TensorGate T (1 : Matrix (Bool × H) (Bool × H) ℂ) * cleanQPEFrame M R =
      cleanQPEFrame M R * TensorGate T (1 : Matrix (Bool × I) (Bool × I) ℂ) := by
  simp only [TensorGate, cleanQPEFrame, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

private theorem clean_threshold_gate_bridge (M k : ℕ) (R : Matrix H I ℂ) :
    permMatrix (phaseThresholdFlip (I := H) M k) * cleanQPEFrame M R =
      cleanQPEFrame M R * permMatrix (phaseThresholdFlip (I := I) M k) := by
  ext ⟨x, b, i⟩ ⟨y, c, j⟩
  have hl : (permMatrix (phaseThresholdFlip (I := H) M k) * cleanQPEFrame M R)
      (x,b,i) (y,c,j) = cleanQPEFrame M R (phaseThresholdFlip M k (x,b,i)) (y,c,j) :=
    applyGate_permMatrix (phaseThresholdFlip_involutive M k)
      (fun p => cleanQPEFrame M R p (y,c,j)) (x,b,i)
  have hr : (cleanQPEFrame M R * permMatrix (phaseThresholdFlip (I := I) M k))
      (x,b,i) (y,c,j) = cleanQPEFrame M R (x,b,i) (phaseThresholdFlip M k (y,c,j)) := by
    simp [Matrix.mul_apply, permMatrix]
  rw [hl, hr]
  by_cases hxy : x = y
  · subst y
    by_cases hx : k < x.val <;> cases b <;> cases c <;>
      simp [cleanQPEFrame, phaseThresholdFlip, hx]
  · simp [cleanQPEFrame, phaseThresholdFlip, Matrix.one_apply, hxy]

private theorem clean_counted_circuit_bridge (M : ℕ) (hM : 0 < M) (R : Matrix H I ℂ) :
    CleanCircuitBridge (cleanQPEFrame M R)
      (countedPhaseCircuit (I := H) M) (countedPhaseCircuit (I := I) M) := by
  have ht (k : ℕ) : CleanCircuitBridge (cleanQPEFrame M R)
      (phaseThresholdBlock (I := H) M k) (phaseThresholdBlock (I := I) M k) :=
    .gate _ _ (permMatrix_unitary (phaseThresholdFlip_involutive M k))
      (permMatrix_unitary (phaseThresholdFlip_involutive M k))
      (clean_threshold_gate_bridge M k R)
      (.query (.gate _ _ (permMatrix_unitary (phaseThresholdFlip_involutive M k))
        (permMatrix_unitary (phaseThresholdFlip_involutive M k))
        (clean_threshold_gate_bridge M k R) .nil))
  have hl (n : ℕ) : CleanCircuitBridge (cleanQPEFrame M R)
      (phaseThresholdLoop (I := H) M n) (phaseThresholdLoop (I := I) M n) := by
    induction n with
    | zero => exact .nil
    | succ n ih => exact ih.append (ht n)
  have hg (T : Operator M) (hT : T ∈ Matrix.unitaryGroup (Fin M) ℂ) :
      CleanCircuitBridge (cleanQPEFrame M R)
        [.gate (TensorGate T (1 : Matrix (Bool × H) (Bool × H) ℂ))]
        [.gate (TensorGate T (1 : Matrix (Bool × I) (Bool × I) ℂ))] :=
    .gate _ _ (tensorGate_unitary hT (Submonoid.one_mem _))
      (tensorGate_unitary hT (Submonoid.one_mem _)) (clean_phase_gate_bridge M R T) .nil
  exact ((hg _ (qftMatrix_unitary hM)).append (hl (M - 1))).append
    (hg _ (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM)))

private theorem clean_frame_input (M : ℕ) (hM : 0 < M) (R : Matrix H I ℂ)
    (ψ : QState I) :
    cleanQPEFrame M R *ᵥ cleanQPEInput M hM ψ = cleanQPEInput M hM (R *ᵥ ψ) := by
  simp only [cleanQPEFrame, cleanQPEInput, kronecker_mulVec_tensorState, Matrix.one_mulVec]

theorem clean_qpe_full_workspace_leakage_telescope
    (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 0 < M) (O : Matrix H H ℂ) (R : Matrix H I ℂ)
    (V : Matrix I I ℂ) (body : List (AdjointStep H)) (η : ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (_hR : IsIsometry R)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hbody : WellFormedAdjointCircuit body)
    (hη : 0 ≤ η)
    (he : ∀ ξ : QState I,
      ‖toEuclidean_fromVec (evaluate O body *ᵥ (R *ᵥ ξ) - R *ᵥ (V *ᵥ ξ))‖ ≤
        η * ‖toEuclidean_fromVec ξ‖) (ψ : QState I) :
    ‖toEuclidean_fromVec
      (evaluate (TensorGate (1 : Operator M) (controlOracle O)) (cleanQPEWord M body) *ᵥ
        cleanQPEInput M hM (R *ᵥ ψ) - cleanQPEFrame M R *ᵥ
          Run (TensorGate (1 : Operator M) (controlOracle V)) (countedPhaseCircuit M)
            (cleanQPEInput M hM ψ))‖ ≤
      (M - 1 : ℕ) * η * ‖toEuclidean_fromVec ψ‖ := by
  rw [(clean_qpe_actual_expansion_semantics_and_paid_inverse H M O body hM hbody).2.2.2.2.2]
  rw [← clean_frame_input M hM R ψ]
  have h := (clean_counted_circuit_bridge M hM R).error
    (TensorGate (1 : Operator M) (controlOracle (evaluate O body)))
    (TensorGate (1 : Operator M) (controlOracle V))
    (tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary (hbody.evaluate_unitary hO)))
    (tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary hV)) η hη
    (clean_frame_defect_bound M (evaluate O body) V R η hη he) (cleanQPEInput M hM ψ)
  have hn : ‖toEuclidean_fromVec (cleanQPEInput M hM ψ)‖ = ‖toEuclidean_fromVec ψ‖ := by
    simp only [cleanQPEInput, tensorState_l2_norm,
      (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket _), one_mul]
  rw [hn, (counted_offgrid_qpe_clean_flag M hM V ψ).2.1] at h
  exact h

theorem cleanQPEFrame_isometry (M : ℕ) {R : Matrix H I ℂ} (hR : IsIsometry R) :
    IsIsometry (cleanQPEFrame M R) := by
  change Rᴴ * R = 1 at hR
  simp only [IsIsometry, cleanQPEFrame, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hR,
    Matrix.one_kronecker_one]

private theorem clean_event_marginal (M : ℕ)
    (out : QState (Fin M × (Bool × H))) (E : Finset (Fin M)) :
    cleanQPEEventMass M out E = MarginalProbLeft out E := by
  unfold cleanQPEEventMass MarginalProbLeft MeasureProb BornProb
  congr 1
  ext p
  simp

private theorem clean_frame_slice (M : ℕ) (R : Matrix H I ℂ)
    (ξ : QState (Fin M × (Bool × I))) (z : Fin M) :
    (fun p : Bool × H => (cleanQPEFrame M R *ᵥ ξ) (z,p)) =
      ((1 : Matrix Bool Bool ℂ) ⊗ₖ R) *ᵥ (fun p => ξ (z,p)) := by
  funext p
  simp [cleanQPEFrame, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply]

private theorem clean_event_frame (M : ℕ) {R : Matrix H I ℂ} (hR : IsIsometry R)
    (ξ : QState (Fin M × (Bool × I))) (E : Finset (Fin M)) :
    cleanQPEEventMass M (cleanQPEFrame M R *ᵥ ξ) E = cleanQPEEventMass M ξ E := by
  rw [clean_event_marginal, clean_event_marginal]
  simp only [MarginalProbLeft, MeasureProb, BornProb, Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hb : IsIsometry ((1 : Matrix Bool Bool ℂ) ⊗ₖ R) := by
    change Rᴴ * R = 1 at hR
    simp only [IsIsometry, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, hR, Matrix.one_kronecker_one]
  have hn := congrArg (fun x : ℝ => x ^ 2)
    (isometry_mulVec_norm hb (fun p => ξ (z,p)))

  rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq] at hn
  rw [← clean_frame_slice M R ξ z] at hn
  exact hn

private theorem clean_ideal_event_spectral (M : ℕ) (hM : 0 < M) (V : Matrix I I ℂ)
    (J : Type) [Fintype J] [DecidableEq J] (v : J → QState I)
    (c : J → ℂ) (φ : J → ℝ)
    (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (he : ∀ j, V *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (E : Finset (Fin M)) :
    cleanQPEEventMass M
      (Run (TensorGate (1 : Operator M) (controlOracle V)) (countedPhaseCircuit M)
        (cleanQPEInput M hM (∑ j, c j • v j))) E =
      ∑ j, ‖c j‖ ^ 2 * (∑ z ∈ E, ‖qpeKernel M (φ j) z‖ ^ 2) := by
  rw [show cleanQPEInput M hM (∑ j, c j • v j) =
    TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (∑ j, c j • v j)) from rfl,
    (counted_offgrid_qpe_clean_flag M hM V (∑ j, c j • v j)).1,
    clean_event_marginal]
  simp only [MarginalProbLeft, MeasureProb, BornProb, Finset.sum_product,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add]
  have hl := (offgrid_qpe_eigen_and_spectral_law M V (0 : QState I) 0 hM).2
    J v c φ (by intro j l; by_cases h : j = l <;> simpa [h] using! hv j l) he
  have hz (z : Fin M) : (∑ i, ‖qpeOutput M V (∑ j, c j • v j) (z,i)‖ ^ 2) =
      ∑ j, ‖c j‖ ^ 2 * ‖qpeKernel M (φ j) z‖ ^ 2 := by
    simpa [MarginalProbLeft, MeasureProb, BornProb, Finset.sum_product] using! hl z
  simp_rw [hz]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem clean_qpe_actual_spectral_born_event_error
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M : ℕ) (hM : 0 < M)
    (O : Matrix H H ℂ) (R : Matrix H I ℂ) (V : Matrix I I ℂ)
    (body : List (AdjointStep H)) (η : ℝ) (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (hO : O ∈ Matrix.unitaryGroup H ℂ) (hR : IsIsometry R)
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (hbody : WellFormedAdjointCircuit body)
    (hη : 0 ≤ η)
    (he : ∀ ξ : QState I,
      ‖toEuclidean_fromVec (evaluate O body *ᵥ (R *ᵥ ξ) - R *ᵥ (V *ᵥ ξ))‖ ≤
        η * ‖toEuclidean_fromVec ξ‖)
    (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (hev : ∀ j, V *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (E : Finset (Fin M)) :
    let ψ := ∑ j, c j • v j
    let out := evaluate (TensorGate (1 : Operator M) (controlOracle O))
      (cleanQPEWord M body) *ᵥ cleanQPEInput M hM (R *ᵥ ψ)
    |cleanQPEEventMass M out E -
      (∑ j, ‖c j‖ ^ 2 * (∑ z ∈ E, ‖qpeKernel M (φ j) z‖ ^ 2))| ≤
        2 * (M - 1 : ℕ) * η := by
  classical
  let ψ := ∑ j, c j • v j
  have hψ : Normalized ψ := by
    change (∑ i, ‖ψ i‖ ^ 2) = 1
    exact (sum_norm_sq_orthonormal v c
      (by intro j l; by_cases h : j = l <;> simpa [h] using! hv j l)).trans hc
  have hnψ := (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hRψ : Normalized (R *ᵥ ψ) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
    rw [isometry_mulVec_norm hR, hnψ]
  have hinput : Normalized (cleanQPEInput M hM ψ) :=
    normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) hψ)
  have hinputR : Normalized (cleanQPEInput M hM (R *ᵥ ψ)) :=
    normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _) hRψ)
  let out := evaluate (TensorGate (1 : Operator M) (controlOracle O))
    (cleanQPEWord M body) *ᵥ cleanQPEInput M hM (R *ᵥ ψ)
  let ideal := Run (TensorGate (1 : Operator M) (controlOracle V))
    (countedPhaseCircuit M) (cleanQPEInput M hM ψ)
  have ha : Normalized out := normalized_applyGate
    ((clean_qpe_actual_expansion_semantics_and_paid_inverse H M O body hM hbody).1.evaluate_unitary
      (tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary hO))) hinputR
  have hi : Normalized ideal :=
    (counted_offgrid_qpe_clean_flag M hM V ψ).2.2.2.normalized_run
      (tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary hV)) hinput
  have hfi : Normalized (cleanQPEFrame M R *ᵥ ideal) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
    rw [isometry_mulVec_norm (cleanQPEFrame_isometry M hR)]
    exact (normalized_iff_norm_toEuclidean_fromVec _).mp hi
  have hb := measureProb_sub_le_two_mul_l2 out (cleanQPEFrame M R *ᵥ ideal)
    (Finset.univ.filter (fun p => p.1 ∈ E)) ha hfi
  change |cleanQPEEventMass M out E -
    cleanQPEEventMass M (cleanQPEFrame M R *ᵥ ideal) E| ≤ _ at hb
  rw [clean_event_frame M hR, clean_ideal_event_spectral M hM V J v c φ
    (by intro j l; by_cases h : j = l <;> simpa [h] using! hv j l) hev E] at hb
  have hd := clean_qpe_full_workspace_leakage_telescope H I M hM O R V body η
    hO hR hV hbody hη he ψ
  rw [hnψ, mul_one] at hd
  exact hb.trans (by dsimp [out, ideal] at *; linarith)

end Qatlib.Concepts.SpectralReadout.PhaseReadout
