/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.TaylorLCUProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def routedCoefficientWord (K : ℕ) (c : TaylorWordLabel J K → ℂ) (j₀ : J) :
    List (AdjointStep (TaylorWordLabel J K × (Bool × (J × I)))) :=
  [.gate (prepareRegister (I := Bool × (J × I))
      (coefficientPrepare c (taylorEmptyLabel J K)))ᴴ,
   .gate (select (phaseAbsorbed c
      (fun _ => (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))))] ++
    taylorBlockList j₀ K K le_rfl ++
  [.gate (prepareRegister (I := Bool × (J × I))
      (coefficientPrepare c (taylorEmptyLabel J K)))]

theorem routed_blocks_evaluate (U : J → Matrix I I ℂ) (j₀ : J) (K n : ℕ)
    (hn : n ≤ K) :
    evaluate (taylorQuery U K) (taylorBlockList j₀ K n hn) =
      taylorSelectProductAux U j₀ K n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [taylorBlockList, evaluate_append, ih, taylorQueryRouteStep,
      evaluate, instructionMatrix, Matrix.mul_one, taylorSelectProductAux, Matrix.mul_assoc]

omit [Fintype J] [Fintype I] in

theorem routed_blocks_cost (j₀ : J) (K n : ℕ) (hn : n ≤ K) :
    adjointQueryCount (taylorBlockList (I := I) j₀ K n hn) = n ∧
    adjointGateCount (taylorBlockList (I := I) j₀ K n hn) = 2 * n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hq, hg⟩ := ih (Nat.le_of_succ_le hn)
    simp only [taylorBlockList, adjointQueryCount_append, adjointGateCount_append,
      taylorQueryRouteStep, adjointQueryCount, adjointGateCount, hq, hg]
    constructor <;> omega

theorem routed_blocks_wellFormed (j₀ : J) (K n : ℕ) (hn : n ≤ K) :
    WellFormedAdjointCircuit (taylorBlockList (I := I) j₀ K n hn) := by
  induction n with
  | zero => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  | succ n ih =>
    apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [taylorQueryRouteStep, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.forward_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨taylorRouteMatrix_unitary j₀ _, taylorRouteMatrix_unitary j₀ _⟩
    · exact ih (Nat.le_of_succ_le hn)

omit [Fintype I] in

theorem routedCoefficientWord_cost (K : ℕ) (c : TaylorWordLabel J K → ℂ) (j₀ : J) :
    adjointQueryCount (routedCoefficientWord (I := I) K c j₀) = K ∧
    adjointGateCount (routedCoefficientWord (I := I) K c j₀) = 2 * K + 3 := by
  obtain ⟨hq, hg⟩ := routed_blocks_cost (I := I) j₀ K K le_rfl
  simp only [routedCoefficientWord, adjointQueryCount_append, adjointGateCount_append,
    adjointQueryCount, adjointGateCount, hq, hg]
  constructor <;> omega

theorem routedCoefficientWord_wellFormed (K : ℕ) (c : TaylorWordLabel J K → ℂ) (j₀ : J)
    (hc : 0 < coefficientMass c) :
    WellFormedAdjointCircuit (routedCoefficientWord (I := I) K c j₀) := by
  have hp := prepareRegister_unitary (I := Bool × (J × I))
    (coefficientPrepare_unitary c (taylorEmptyLabel J K) hc)
  have hd := select_unitary _ (phaseAbsorbed_unitary c
    (fun _ => (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))
    (fun _ => (Matrix.unitaryGroup _ ℂ).one_mem))
  apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
  · apply Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.append
    · simp only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff,
        Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      exact ⟨adjoint_unitary hp, hd⟩
    · exact routed_blocks_wellFormed j₀ K K le_rfl
  · simpa using hp

private def routedScratchFrame (j₀ : J) (K : ℕ) :
    Matrix (TaylorWordLabel J K × (Bool × (J × I))) (TaylorWordLabel J K × I) ℂ :=
  Matrix.of fun x y => if (y.1, (false, (j₀, y.2))) = x then 1 else 0

private theorem routedScratchFrame_isometry (j₀ : J) (K : ℕ) :
    IsIsometry (routedScratchFrame (I := I) j₀ K) := by
  unfold IsIsometry
  ext ⟨w, i⟩ ⟨v, j⟩
  simp [routedScratchFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

private theorem routedScratchFrame_mul {O : Type} (j₀ : J) (K : ℕ)
    (V : Matrix (TaylorWordLabel J K × I) O ℂ)
    (x : TaylorWordLabel J K × (Bool × (J × I))) (y : O) :
    (routedScratchFrame (I := I) j₀ K * V) x y =
      if x.2.1 = false ∧ x.2.2.1 = j₀ then V (x.1, x.2.2.2) y else 0 := by
  rcases x with ⟨wl, b, j, d⟩
  cases b <;> by_cases hj : j = j₀
  · have hs : ∀ z, routedScratchFrame (I := I) j₀ K (wl, false, j, d) z =
        if z = (wl, d) then 1 else 0 := by
      intro ⟨w, i⟩
      simp only [routedScratchFrame, Matrix.of_apply, Prod.mk.injEq, hj,
        true_and, eq_comm]
    simp only [Matrix.mul_apply, hs, ite_mul, one_mul, zero_mul]
    simp [hj]
  all_goals simp_all [Matrix.mul_apply, routedScratchFrame, eq_comm]

private theorem routedScratchFrame_select (j₀ : J) (K : ℕ)
    (V : TaylorWordLabel J K → Matrix I I ℂ)
    (x : TaylorWordLabel J K × (Bool × (J × I))) (w : TaylorWordLabel J K) (i : I) :
    (routedScratchFrame (I := I) j₀ K * select V) x (w, i) =
      (taylorBranchFrame (I := I) j₀ K w * V w) x i := by
  simp [Matrix.mul_apply, select, routedScratchFrame, taylorBranchFrame,
    Fintype.sum_prod_type, mul_ite, eq_comm]

private theorem routed_blocks_scratch (U : J → Matrix I I ℂ) (j₀ : J) (K : ℕ) :
    taylorSelectProductAux U j₀ K K le_rfl * routedScratchFrame (I := I) j₀ K =
      routedScratchFrame (I := I) j₀ K * select (taylorBranchWord U K K le_rfl) := by
  ext x ⟨w, i⟩
  rw [routedScratchFrame_select]
  change (taylorSelectProductAux U j₀ K K le_rfl * taylorBranchFrame (I := I) j₀ K w) x i = _
  exact congrFun (congrFun (taylorSelectProduct_branch U j₀ K K le_rfl w) x) i

private theorem mul_routedBranchFrame
    (j₀ : J) (K : ℕ)
    (M : Matrix (TaylorWordLabel J K × (Bool × (J × I)))
      (TaylorWordLabel J K × (Bool × (J × I))) ℂ)
    (w : TaylorWordLabel J K)
    (x : TaylorWordLabel J K × (Bool × (J × I))) (i : I) :
    (M * taylorBranchFrame (I := I) j₀ K w) x i = M x (w, false, j₀, i) := by
  simp [Matrix.mul_apply, taylorBranchFrame, mul_ite]

private theorem routed_prepare_frame (K : ℕ) (c : TaylorWordLabel J K → ℂ) (j₀ : J) :
    prepareRegister (I := Bool × (J × I)) (coefficientPrepare c (taylorEmptyLabel J K)) *
        taylorFrame (I := I) j₀ K =
      routedScratchFrame (I := I) j₀ K * prepareLift (I := I) (coefficientAmplitude c) := by
  have hcolumn (w : TaylorWordLabel J K) :
      coefficientPrepare c (taylorEmptyLabel J K) w (taylorEmptyLabel J K) =
        coefficientAmplitude c w := by
    simpa [Matrix.mulVec, dotProduct, Ket] using
      congrFun (coefficientPrepare_mulVec_ket c (taylorEmptyLabel J K)) w
  have hframe : taylorFrame (I := I) j₀ K =
      taylorBranchFrame (I := I) j₀ K (taylorEmptyLabel J K) := by
    ext x i
    simp [taylorFrame, taylorBranchFrame, eq_comm]
  ext ⟨w, b, j, d⟩ i
  rw [hframe, mul_routedBranchFrame, routedScratchFrame_mul]
  cases b <;> by_cases hj : j = j₀ <;>
    simp [prepareRegister, Matrix.kroneckerMap_apply, Matrix.one_apply,
      hcolumn, prepareLift, hj]

private theorem routed_phase_scratch (K : ℕ) (c : TaylorWordLabel J K → ℂ) (j₀ : J) :
    select (phaseAbsorbed c
      (fun _ => (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))) *
        routedScratchFrame (I := I) j₀ K =
      routedScratchFrame (I := I) j₀ K *
        select (phaseAbsorbed c (fun _ => (1 : Matrix I I ℂ))) := by
  ext ⟨w, b, j, d⟩ ⟨v, i⟩
  rw [routedScratchFrame_mul]
  change (select (phaseAbsorbed c
    (fun _ => (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ))) *
      taylorBranchFrame (I := I) j₀ K v) (w, b, j, d) i = _
  rw [mul_routedBranchFrame]
  cases b <;> by_cases hj : j = j₀ <;>
    simp [select, phaseAbsorbed, Matrix.smul_apply, Matrix.one_apply, hj]

theorem routedCoefficientWord_compress (K : ℕ) (c : TaylorWordLabel J K → ℂ)
    (j₀ : J) (U : J → Matrix I I ℂ) (hc : 0 < coefficientMass c) :
    compress (taylorFrame (I := I) j₀ K) (evaluate (taylorQuery U K) (routedCoefficientWord K c j₀))
      (taylorFrame (I := I) j₀ K) =
      ∑ w, (c w / (coefficientMass c : ℂ)) • taylorBranchWord U K K le_rfl w := by
  let P := prepareRegister (I := Bool × (J × I)) (coefficientPrepare c (taylorEmptyLabel J K))
  let D := select (phaseAbsorbed c
    (fun _ => (1 : Matrix (Bool × (J × I)) (Bool × (J × I)) ℂ)))
  let S := routedScratchFrame (I := I) j₀ K
  let F := prepareLift (I := I) (coefficientAmplitude c)
  let B := taylorBranchWord U K K le_rfl
  let E := select (phaseAbsorbed c (fun _ => (1 : Matrix I I ℂ)))
  have hPF : P * taylorFrame (I := I) j₀ K = S * F := routed_prepare_frame K c j₀
  have hS : Sᴴ * S = 1 := routedScratchFrame_isometry j₀ K
  have hD : D * S = S * E := routed_phase_scratch K c j₀
  have hB : taylorSelectProductAux U j₀ K K le_rfl * S = S * select B :=
    routed_blocks_scratch U j₀ K
  have hphase : E * select B = select (phaseAbsorbed c B) := by
    dsimp only [E]
    rw [parallel_select_mul]
    congr 1
    funext w
    simp [phaseAbsorbed]
  have hE : evaluate (taylorQuery U K) (routedCoefficientWord K c j₀) =
      Pᴴ * D * taylorSelectProductAux U j₀ K K le_rfl * P := by
    simp only [routedCoefficientWord, evaluate_append, routed_blocks_evaluate,
      evaluate, instructionMatrix, Matrix.mul_one, P, D, Matrix.mul_assoc]
  calc
    _ = (P * taylorFrame (I := I) j₀ K)ᴴ * D * taylorSelectProductAux U j₀ K K le_rfl *
        (P * taylorFrame (I := I) j₀ K) := by
      simp only [compress, hE, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Fᴴ * Sᴴ * D * taylorSelectProductAux U j₀ K K le_rfl * S * F := by
      rw [hPF]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Fᴴ * (Sᴴ * (D * S)) * select B * F := by
      simp only [Matrix.mul_assoc, hB]
    _ = Fᴴ * (Sᴴ * S) * (E * select B) * F := by
      rw [hD]
      simp only [Matrix.mul_assoc]
    _ = compress F (select (phaseAbsorbed c B)) F := by
      rw [hS, hphase]
      simp only [compress, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by
      rw [prepare_select_compress, coefficientLCU_matrix c B hc]

theorem routedCoefficientWord_blockEncoding (K : ℕ) (c : TaylorWordLabel J K → ℂ)
    (j₀ : J) (U : J → Matrix I I ℂ) (hc : 0 < coefficientMass c)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    BlockEncoding (∑ w, c w • taylorBranchWord U K K le_rfl w)
      (evaluate (taylorQuery U K) (routedCoefficientWord K c j₀))
      (taylorFrame (I := I) j₀ K) (taylorFrame (I := I) j₀ K) (coefficientMass c) 0 := by
  refine ⟨(routedCoefficientWord_wellFormed K c j₀ hc).evaluate_unitary
    (taylorQuery_unitary U hU K), taylorFrame_isIsometry j₀ K,
    taylorFrame_isIsometry j₀ K, hc, le_rfl, ?_⟩
  rw [routedCoefficientWord_compress K c j₀ U hc,
    coefficientLCU_rescale c (taylorBranchWord U K K le_rfl) hc,
    sub_self, norm_zero]

def routedPaddedCoefficients (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) : TaylorWordLabel J K → ℂ
  | .inl w => a w
  | .inr b => if b then (((2 - coefficientMass a) / 2 : ℝ) : ℂ)
      else -(((2 - coefficientMass a) / 2 : ℝ) : ℂ)

omit [DecidableEq J] in

theorem routedPaddedCoefficients_mass (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) (ha : coefficientMass a ≤ 2) :
    coefficientMass (routedPaddedCoefficients K a) = 2 := by
  have hp : 0 ≤ (2 - coefficientMass a) / 2 := by positivity
  rw [coefficientMass, Fintype.sum_sum_type]
  change coefficientMass a +
    (∑ b : Bool, ‖routedPaddedCoefficients K a (.inr b)‖) = 2
  simp only [Fintype.sum_bool, routedPaddedCoefficients, Bool.false_eq_true,
    ↓reduceIte, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  ring

omit [Fintype J] [DecidableEq J] in

theorem routed_padding_branch (U : J → Matrix I I ℂ) (K n : ℕ) (hn : n ≤ K)
    (b : Bool) : taylorBranchWord U K n hn (.inr b) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [taylorBranchWord, taylorBranchStep, ih]

omit [DecidableEq J] in

theorem routedPaddedCoefficients_operator (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) (U : J → Matrix I I ℂ) :
    (∑ w, routedPaddedCoefficients K a w • taylorBranchWord U K K le_rfl w) =
      ∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
        a w • taylorBranchWord U K K le_rfl (.inl w) := by
  rw [Fintype.sum_sum_type]
  simp [routedPaddedCoefficients, routed_padding_branch]

theorem routed_padded_lcu_counted (K : ℕ)
    (a : (Σ l : Fin (K + 1), Fin l.val → J) → ℂ) (j₀ : J)
    (U : J → Matrix I I ℂ) (ha : coefficientMass a ≤ 2)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    WellFormedAdjointCircuit (routedCoefficientWord (I := I) K
      (routedPaddedCoefficients K a) j₀) ∧
    taylorQuery U K ∈ Matrix.unitaryGroup (TaylorWordLabel J K × (Bool × (J × I))) ℂ ∧
    BlockEncoding (∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
      a w • taylorBranchWord U K K le_rfl (.inl w))
      (evaluate (taylorQuery U K) (routedCoefficientWord K (routedPaddedCoefficients K a) j₀))
      (taylorFrame j₀ K) (taylorFrame j₀ K) 2 0 ∧
    adjointQueryCount (routedCoefficientWord (I := I) K
      (routedPaddedCoefficients K a) j₀) = K ∧
    adjointGateCount (routedCoefficientWord (I := I) K
      (routedPaddedCoefficients K a) j₀) = 2 * K + 3 := by
  have hm := routedPaddedCoefficients_mass K a ha
  have hp : 0 < coefficientMass (routedPaddedCoefficients K a) := by rw [hm]; norm_num
  refine ⟨routedCoefficientWord_wellFormed K _ j₀ hp, taylorQuery_unitary U hU K,
    ?_, routedCoefficientWord_cost K _ j₀⟩
  have h := routedCoefficientWord_blockEncoding K (routedPaddedCoefficients K a) j₀ U hp hU
  rwa [hm, routedPaddedCoefficients_operator] at h

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
