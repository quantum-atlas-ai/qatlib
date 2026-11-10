/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.QspSimulation.Achievability
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem computed_signal_unitary_vector_norm {I : Type} [Fintype I] [DecidableEq I]
    {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ‖toEuclidean_fromVec (U*ᵥψ)‖ = ‖toEuclidean_fromVec ψ‖ :=
  isometry_mulVec_norm (by simpa only [IsIsometry,Matrix.star_eq_conjTranspose] using! hU.1) ψ

theorem computed_signal_wrap_add {I : Type} [Fintype I] (ψ φ : QState I) :
    toEuclidean_fromVec (ψ+φ) = toEuclidean_fromVec ψ + toEuclidean_fromVec φ := rfl

theorem computed_signal_repeated_workspace_bound {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (V : Matrix I I ℂ) (W : Matrix H H ℂ) (R : Matrix H I ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hV : V ∈ Matrix.unitaryGroup I ℂ) (hW : W ∈ Matrix.unitaryGroup H ℂ)
    (hstepBound : ∀ ψ : QState I,
      ‖toEuclidean_fromVec (W*ᵥ(R*ᵥψ)-R*ᵥ(V*ᵥψ))‖ ≤ ε*‖toEuclidean_fromVec ψ‖) :
    ∀ (n : ℕ) (ψ : QState I),
      ‖toEuclidean_fromVec ((W^n)*ᵥ(R*ᵥψ)-R*ᵥ((V^n)*ᵥψ))‖ ≤
        (n:ℝ)*ε*‖toEuclidean_fromVec ψ‖ := by
  intro n
  induction n with
  | zero =>
    intro ψ
    have h0 : (W ^ 0) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ 0) *ᵥ ψ) = 0 := by
      rw [pow_zero, pow_zero, Matrix.one_mulVec, Matrix.one_mulVec, sub_self]
    rw [h0, show toEuclidean_fromVec (0 : QState H) = 0 from rfl, norm_zero]
    positivity
  | succ n ih =>
    intro ψ
    have hsplit : (W ^ (n + 1)) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ (n + 1)) *ᵥ ψ) =
        W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)) +
          (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ))) := by
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec (R *ᵥ ψ) W (W ^ n),
        ← Matrix.mulVec_mulVec ψ V (V ^ n), Matrix.mulVec_sub]
      abel
    have hVn : V ^ n ∈ Matrix.unitaryGroup I ℂ := pow_mem hV n
    have hstep := hstepBound ((V ^ n) *ᵥ ψ)
    rw [computed_signal_unitary_vector_norm hVn ψ] at hstep
    calc ‖toEuclidean_fromVec ((W ^ (n + 1)) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ (n + 1)) *ᵥ ψ))‖
        = ‖toEuclidean_fromVec (W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)) +
            (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ))))‖ := by rw [hsplit]
      _ ≤ ‖toEuclidean_fromVec (W *ᵥ ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ)))‖ +
          ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ)))‖ := by
        rw [computed_signal_wrap_add]
        exact norm_add_le _ _
      _ = ‖toEuclidean_fromVec ((W ^ n) *ᵥ (R *ᵥ ψ) - R *ᵥ ((V ^ n) *ᵥ ψ))‖ +
          ‖toEuclidean_fromVec (W *ᵥ (R *ᵥ ((V ^ n) *ᵥ ψ)) - R *ᵥ (V *ᵥ ((V ^ n) *ᵥ ψ)))‖ := by
        rw [computed_signal_unitary_vector_norm hW]
      _ ≤ (n : ℝ) * ε * ‖toEuclidean_fromVec ψ‖ +
          ε * ‖toEuclidean_fromVec ψ‖ :=
        add_le_add (ih ψ) hstep
      _ = ((n + 1 : ℕ) : ℝ) * ε * ‖toEuclidean_fromVec ψ‖ := by
        push_cast
        ring

theorem computed_signal_evolution_segment_power {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (t : ℝ) (r : ℕ) (hr : 0 < r) :
    (hamiltonianEvolution A (t/r))^r = hamiltonianEvolution A t := by
  have hp : ∀ n : ℕ, (hamiltonianEvolution A (t/r))^n = hamiltonianEvolution A ((n:ℝ)*(t/r)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih]
      change HamiltonianEvolution A ((n:ℝ)*(t/r)) * HamiltonianEvolution A (t/r) = _
      rw [← hamiltonianEvolution_add]
      congr 1
      push_cast
      ring
  rw [hp]
  have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [mul_div_cancel₀ _ hr0]

theorem computed_signal_full_segmented_program_and_cost : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ),
  A.IsHermitian → ProjectedUnitaryEncoding A U F F →
  let n := computedSignalCutoff t k
  let r := computedSignalSegments t
  let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))
  WellFormedAdjointCircuit (computedSignalWord F t k) ∧
  adjointQueryCount (computedSignalWord F t k)=r*(27*(4*n+1)) ∧
  adjointGateCount (computedSignalWord F t k)=r*(27*(4*n+6)+79) ∧
  ∀ ψ : QState I,
    ‖toEuclidean_fromVec (evaluate O (computedSignalWord F t k)*ᵥ
      (scaleEightFrame (hamiltonianFrame F)*ᵥψ)-
      scaleEightFrame (hamiltonianFrame F)*ᵥ(hamiltonianEvolution A (t:ℝ)*ᵥψ))‖ ≤
      (1/2:ℝ)^k*‖toEuclidean_fromVec ψ‖ := by
  intro H I _ _ _ _ A U F t k hA h
  (try dsimp only)
  let n := computedSignalCutoff t k
  let r := computedSignalSegments t
  let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))
  let body := computedSignalBody F t k
  let cs := scaleEightAmplifyWord (hamiltonianFrame F) body
  let R := scaleEightFrame (hamiltonianFrame F)
  let V := hamiltonianEvolution A ((t:ℝ)/(r:ℝ))
  obtain ⟨_,hWF,hBE,hq,hg⟩ := computed_signal_phase_packets_and_body H I A U F t k hA h
  have hsc :=
      scale_eight_three_level_actual_counts (Bool×(Bool×H)) I
      (hamiltonianFrame F) body hBE.right_isometry hWF
  have hrep := repeat_adjoint_word_semantics_cost O cs r
  have hword : computedSignalWord F t k = repeatAdjointWord cs r := rfl
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary (Submonoid.one_mem _)
    (controlOracle_unitary (parallelOracle_unitary h.unitary))
  have hW : evaluate O cs ∈ Matrix.unitaryGroup _ ℂ := hsc.1.evaluate_unitary hO
  have hV : V ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hA _
  obtain ⟨hr,_,_,_,_,hbudget⟩ := computed_signal_explicit_segment_precision t k
  refine ⟨?_,?_,?_,?_⟩
  · rw [hword]
    exact hrep.2.2.2 hsc.1
  · rw [hword,hrep.2.1,hsc.2.1,hq]
  · rw [hword,hrep.2.2.1,hsc.2.2,hg]
  · intro ψ
    have herr := computed_signal_repeated_workspace_bound V (evaluate O cs) R
      (Real.sqrt (6750*(16*(1/2:ℝ)^n))) (Real.sqrt_nonneg _) hV hW
      (computed_signal_same_clean_segment H I A U F t k hA h) r ψ
    have hideal : V^r = hamiltonianEvolution A (t:ℝ) :=
      computed_signal_evolution_segment_power A (t:ℝ) r hr
    rw [hideal] at herr
    rw [hword,hrep.1]
    exact herr.trans (mul_le_mul_of_nonneg_right hbudget (norm_nonneg _))

theorem computed_signal_control_noise_le {H : Type} [Fintype H] [DecidableEq H]
    (U V : Matrix H H ℂ) : ‖controlOracle V-controlOracle U‖ ≤ ‖V-U‖ := by
  let P : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 1 else 0)
  have hP : ‖P‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).2
    intro b
    cases b <;> norm_num
  have he : controlOracle V-controlOracle U = TensorGate P (V-U) := by
    ext ⟨b,i⟩ ⟨c,j⟩
    cases b <;> cases c <;>
      simp [controlOracle,select,TensorGate,P,Matrix.diagonal,Matrix.of_apply,
        Matrix.kroneckerMap_apply]
  rw [he,l2_norm_tensorGate]
  exact (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _)

theorem computed_signal_lifted_oracle_noise_le {H : Type} [Fintype H] [DecidableEq H]
    (U V : Matrix H H ℂ) :
    ‖TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) V)) -
      TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))‖ ≤ ‖V-U‖ := by
  rw [TensorGate,TensorGate,kronecker_sub_right,l2_norm_kronecker,l2_norm_one_eq,one_mul]
  apply (computed_signal_control_noise_le _ _).trans
  rw [parallelOracle_eq_kronecker,parallelOracle_eq_kronecker,kronecker_sub_right,
    l2_norm_kronecker,l2_norm_one_eq,one_mul]

theorem computed_signal_oracle_noise_and_inverse : ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  (A : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ),
  A.IsHermitian → ProjectedUnitaryEncoding A U F F → V∈Matrix.unitaryGroup H ℂ →
  0≤δ → ‖V-U‖≤δ →
  let cs := computedSignalWord F t k
  let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) V))
  adjointQueryCount (adjointCircuit cs)=adjointQueryCount cs ∧
  adjointGateCount (adjointCircuit cs)=adjointGateCount cs ∧
  ∀ ψ : QState I,
    ‖toEuclidean_fromVec (evaluate O cs*ᵥ(scaleEightFrame (hamiltonianFrame F)*ᵥψ)-
      scaleEightFrame (hamiltonianFrame F)*ᵥ(hamiltonianEvolution A (t:ℝ)*ᵥψ))‖ ≤
      ((1/2:ℝ)^k+(adjointQueryCount cs:ℝ)*δ)*‖toEuclidean_fromVec ψ‖ := by
  intro H I _ _ _ _ A U V F t k δ hA h hV hδ hVU
  (try dsimp only)
  let cs := computedSignalWord F t k
  let R := scaleEightFrame (hamiltonianFrame F)
  let OU := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))
  let OV := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) V))
  obtain ⟨hWF,_,_,hcorrect⟩ := computed_signal_full_segmented_program_and_cost H I A U F t k hA h
  have hb := computed_signal_phase_packets_and_body H I A U F t k hA h
  have hR : IsIsometry R := scaleEightFrame_isometry (hamiltonianFrame F) hb.2.2.1.right_isometry
  have hOU : OU ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary (Submonoid.one_mem _)
    (controlOracle_unitary (parallelOracle_unitary h.unitary))
  have hOV : OV ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary (Submonoid.one_mem _)
    (controlOracle_unitary (parallelOracle_unitary hV))
  have hop : ‖evaluate OV cs-evaluate OU cs‖ ≤ (adjointQueryCount cs:ℝ)*δ :=
    evaluate_operator_error_le_queries cs OU OV δ hWF hOU hOV hδ
      ((computed_signal_lifted_oracle_noise_le U V).trans hVU)
  refine ⟨adjointQueryCount_adjointCircuit _,adjointGateCount_adjointCircuit _,?_⟩
  intro ψ
  have hdiff := l2_norm_mulVec_fromVec_le (evaluate OV cs-evaluate OU cs) (R*ᵥψ)
  rw [Matrix.sub_mulVec,isometry_mulVec_norm hR ψ] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  have hsplit : evaluate OV cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution A (t:ℝ)*ᵥψ) =
      (evaluate OV cs*ᵥ(R*ᵥψ)-evaluate OU cs*ᵥ(R*ᵥψ)) +
      (evaluate OU cs*ᵥ(R*ᵥψ)-R*ᵥ(hamiltonianEvolution A (t:ℝ)*ᵥψ)) := by abel
  rw [hsplit,computed_signal_wrap_add]
  exact (norm_add_le _ _).trans ((add_le_add hdiff' (hcorrect ψ)).trans_eq (by ring))

noncomputable def computedSignalComposeWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (t u : ℚ) (k l : ℕ) :=
  computedSignalWord F t k ++ computedSignalWord F u l

theorem computed_signal_two_time_consumer {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (t u : ℚ) (k l : ℕ) (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    let cs := computedSignalComposeWord F t u k l
    let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))
    WellFormedAdjointCircuit cs ∧
    adjointQueryCount cs = computedSignalSegments t*(27*(4*computedSignalCutoff t k+1)) +
      computedSignalSegments u*(27*(4*computedSignalCutoff u l+1)) ∧
    adjointGateCount cs = computedSignalSegments t*(27*(4*computedSignalCutoff t k+6)+79) +
      computedSignalSegments u*(27*(4*computedSignalCutoff u l+6)+79) ∧
    ∀ ψ : QState I,
      ‖toEuclidean_fromVec (evaluate O cs*ᵥ(scaleEightFrame (hamiltonianFrame F)*ᵥψ) -
        scaleEightFrame (hamiltonianFrame F)*ᵥ(hamiltonianEvolution A ((t+u:ℚ):ℝ)*ᵥψ))‖ ≤
        ((1/2:ℝ)^k+(1/2:ℝ)^l)*‖toEuclidean_fromVec ψ‖ := by
  (try dsimp only)
  let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) U))
  let R := scaleEightFrame (hamiltonianFrame F)
  let W := evaluate O (computedSignalWord F t k)
  let Z := evaluate O (computedSignalWord F u l)
  let V := hamiltonianEvolution A (t:ℝ)
  let Q := hamiltonianEvolution A (u:ℝ)
  obtain ⟨hWt,hqt,hgt,het⟩ := computed_signal_full_segmented_program_and_cost H I A U F t k hA h
  obtain ⟨hWu,hqu,hgu,heu⟩ := computed_signal_full_segmented_program_and_cost H I A U F u l hA h
  have hO : O ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary (Submonoid.one_mem _)
    (controlOracle_unitary (parallelOracle_unitary h.unitary))
  have hW : W ∈ Matrix.unitaryGroup _ ℂ := hWt.evaluate_unitary hO
  have hQ : Q ∈ Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hA _
  refine ⟨hWt.append hWu,?_,?_,?_⟩
  · rw [computedSignalComposeWord,adjointQueryCount_append,hqt,hqu]
  · rw [computedSignalComposeWord,adjointGateCount_append,hgt,hgu]
  · intro ψ
    have hstep := het (Q*ᵥψ)
    rw [computed_signal_unitary_vector_norm hQ ψ] at hstep
    have hsplit : (W*Z)*ᵥ(R*ᵥψ)-R*ᵥ((V*Q)*ᵥψ) =
        W*ᵥ(Z*ᵥ(R*ᵥψ)-R*ᵥ(Q*ᵥψ)) +
        (W*ᵥ(R*ᵥ(Q*ᵥψ))-R*ᵥ(V*ᵥ(Q*ᵥψ))) := by
      rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.mulVec_sub]
      abel
    have hideal : V*Q = hamiltonianEvolution A ((t+u:ℚ):ℝ) := by
      change HamiltonianEvolution A (t:ℝ)*HamiltonianEvolution A (u:ℝ) = _
      rw [← hamiltonianEvolution_add,Rat.cast_add]
      rfl
    change ‖toEuclidean_fromVec (evaluate O (computedSignalComposeWord F t u k l)*ᵥ(R*ᵥψ)-
      R*ᵥ(hamiltonianEvolution A ((t+u:ℚ):ℝ)*ᵥψ))‖ ≤ _
    rw [computedSignalComposeWord,evaluate_append,← hideal,hsplit,computed_signal_wrap_add]
    exact (norm_add_le _ _).trans (by
      rw [computed_signal_unitary_vector_norm hW]
      exact (add_le_add (heu ψ) hstep).trans_eq (by ring))

theorem computed_signal_same_word_round_trip {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ)
    (t : ℚ) (k : ℕ) (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) :
    let cs := computedSignalWord F t k
    let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J:=Bool) V))
    evaluate O (cs ++ adjointCircuit cs) = 1 ∧
    adjointQueryCount (cs ++ adjointCircuit cs) = 2*adjointQueryCount cs ∧
    adjointGateCount (cs ++ adjointCircuit cs) = 2*adjointGateCount cs := by
  (try dsimp only)
  have hWF := (computed_signal_full_segmented_program_and_cost H I A U F t k hA h).1
  have hO := tensorGate_unitary (Submonoid.one_mem (Matrix.unitaryGroup Bool ℂ))
    (controlOracle_unitary (parallelOracle_unitary (J:=Bool) hV))
  have hunit := hWF.evaluate_unitary hO
  refine ⟨?_,?_,?_⟩
  · rw [evaluate_append,evaluate_adjointCircuit]
    simpa only [Matrix.star_eq_conjTranspose] using! hunit.2
  · simp only [adjointQueryCount_append,adjointQueryCount_adjointCircuit]
    omega
  · simp only [adjointGateCount_append,adjointGateCount_adjointCircuit]
    omega

end Qatlib.Concepts.QspSimulation.Achievability
