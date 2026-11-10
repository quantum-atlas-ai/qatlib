/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalNativeInverse
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

private theorem wire_diagonal_basis {n : ℕ} (w : Fin n) (d : Bool → ℂ) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w (Matrix.diagonal d)) (Qatlib.Foundations.PureStateMath.Ket x)=
      d (x w) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_wireGate_ket]
  cases hx : x w with
  | false =>
    have hu : Function.update x w false=x := Function.update_eq_self_iff.mpr hx.symm
    simp [hu]
  | true =>
    have hu : Function.update x w true=x := Function.update_eq_self_iff.mpr hx.symm
    simp [hu]

theorem thermalNativeS_word_matrix {n : ℕ} (w : Fin n) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeLower (ThermalNativeStep.s w))=Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w thermalSMatrix := by
  have hm : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeLower (ThermalNativeStep.s w))=(Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate)^2 := by
    simp [thermalNativeLower,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt,pow_two]
  rw [hm,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_wire_pow,thermalT_two]

theorem thermalNativeSDG_word_matrix {n : ℕ} (w : Fin n) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeLower (ThermalNativeStep.sdg w))=Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w thermalSDGMatrix := by
  have hm : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalNativeLower (ThermalNativeStep.sdg w))=(Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj)^2 := by
    simp [thermalNativeLower,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt,pow_two]
  rw [hm,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_wire_pow,thermalTAdj_two]

private theorem s_basis {n : ℕ} (w : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeLower (ThermalNativeStep.s w)))
      (Qatlib.Foundations.PureStateMath.Ket x)=(if x w then Complex.I else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,thermalNativeS_word_matrix]
  exact wire_diagonal_basis w _ x

private theorem sdg_basis {n : ℕ} (w : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeLower (ThermalNativeStep.sdg w)))
      (Qatlib.Foundations.PureStateMath.Ket x)=(if x w then -Complex.I else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,thermalNativeSDG_word_matrix]
  exact wire_diagonal_basis w _ x

private theorem cx_basis {n : ℕ} (flag signal : Fin n) (hfs : flag≠signal) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.cx flag.val signal.val])
      (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket (Function.update x signal (x signal ^^ x flag)) := by
  have hv : flag.val≠signal.val := fun h => hfs (Fin.ext h)
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_cons,List.map_nil,Qatlib.Foundations.QueryWordCore.Circuit.run_gate,Qatlib.Foundations.QueryWordCore.Circuit.run_nil,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,dif_pos (show flag.val<n ∧ signal.val<n ∧ flag.val≠signal.val from
      ⟨flag.isLt,signal.isLt,hv⟩)]
  exact Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_cnotGate_ket n flag signal hfs x

private theorem finite_run_smul {n : ℕ} (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) (a : ℂ) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) (a • psi)=
      a • Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) psi := by
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionApplyGate_smul]

def thermalFlagPhaseSteps {n : ℕ} (phase : Fin 4) (flag : Fin n) : List (ThermalNativeStep n) :=
  match phase.val with
  | 0 => []
  | 1 => [.s flag]
  | 2 => [.z flag]
  | _ => [.sdg flag]

def thermalFlagPhaseWord {n : ℕ} (phase : Fin 4) (flag : Fin n) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  thermalNativeProgram (thermalFlagPhaseSteps phase flag)

def thermalFlagPhaseValue (phase : Fin 4) : ℂ :=
  match phase.val with
  | 0 => 1
  | 1 => Complex.I
  | 2 => -1
  | _ => -Complex.I

theorem thermalFlagPhase_basis {n : ℕ} (phase : Fin 4) (flag : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalFlagPhaseWord phase flag))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x flag then thermalFlagPhaseValue phase else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  fin_cases phase
  · simp [thermalFlagPhaseWord,thermalFlagPhaseSteps,thermalFlagPhaseValue,
      thermalNativeProgram,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit]
  · exact s_basis flag x
  · exact thermalZWord_basis flag x
  · exact sdg_basis flag x

theorem thermalFlagPhase_legal {n : ℕ} (phase : Fin 4) (flag : Fin n) :
    ∀ g∈thermalFlagPhaseSteps phase flag,thermalNativeLegal g := by
  fin_cases phase <;> simp [thermalFlagPhaseSteps,thermalNativeLegal]

theorem thermalFlagPhase_cost {n : ℕ} (phase : Fin 4) (flag : Fin n) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalFlagPhaseWord phase flag)) =
      (if phase.val=0 then 0 else if phase.val=2 then 4 else 2) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalFlagPhaseWord phase flag))=0 := by
  constructor
  · rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]
    fin_cases phase <;> rfl
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

def thermalSelectYSteps {n : ℕ} (flag signal : Fin n) : List (ThermalNativeStep n) :=
  [.sdg flag,.sdg signal,.fixed (.cx flag.val signal.val),.s signal]

def thermalSelectYWord {n : ℕ} (flag signal : Fin n) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  thermalNativeProgram (thermalSelectYSteps flag signal)

theorem thermalSelectY_basis {n : ℕ} (flag signal : Fin n) (hfs : flag≠signal) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal))
      (Qatlib.Foundations.PureStateMath.Ket x)=
      (if x flag && x signal then (-1:ℂ) else 1) •
        Qatlib.Foundations.PureStateMath.Ket (Function.update x signal (x signal ^^ x flag)) := by
  simp only [thermalSelectYWord,thermalSelectYSteps,thermalNativeProgram,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeLower (ThermalNativeStep.s signal)))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.cx flag.val signal.val])
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeLower (ThermalNativeStep.sdg signal)))
        (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalNativeLower (ThermalNativeStep.sdg flag)))
          (Qatlib.Foundations.PureStateMath.Ket x)))) = _
  rw [sdg_basis flag x]
  simp only [finite_run_smul]
  rw [sdg_basis signal x]
  simp only [finite_run_smul]
  rw [cx_basis flag signal hfs x,s_basis signal]
  simp only [Function.update_self,smul_smul]
  cases hf : x flag <;> cases hs : x signal
  all_goals simp

theorem thermalSelectY_coherent {n : ℕ} (flag signal : Fin n) (hfs : flag≠signal)
    (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • ((if x flag && x signal then (-1:ℂ) else 1) •
        Qatlib.Foundations.PureStateMath.Ket (Function.update x signal (x signal ^^ x flag))) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  have hk := thermalSelectY_basis flag signal hfs
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hk ⊢
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  exact Finset.sum_congr rfl (fun x _ => congrArg (fun v => psi x • v) (hk x))

theorem thermalSelectY_legal {n : ℕ} (flag signal : Fin n) (hfs : flag≠signal) :
    ∀ g∈thermalSelectYSteps flag signal,thermalNativeLegal g := by
  have hv : flag.val≠signal.val := fun h => hfs (Fin.ext h)
  simp [thermalSelectYSteps,thermalNativeLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,flag.isLt,signal.isLt,hv]

theorem thermalSelectY_public {n : ℕ} (flag signal : Fin n) (hfs : flag≠signal)
    (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalSelectYWord flag signal) psi = some (∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x •
      ((if x flag && x signal then (-1:ℂ) else 1) •
        Qatlib.Foundations.PureStateMath.Ket (Function.update x signal (x signal ^^ x flag)))) := by
  unfold Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun
  have hl : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalSelectYWord flag signal)=true :=
    thermalNative_program_legal _ (thermalSelectY_legal flag signal hfs)
  rw [hl,if_pos rfl]
  exact congrArg some (thermalSelectY_coherent flag signal hfs psi)

theorem thermalSelectY_cost {n : ℕ} (flag signal : Fin n) :
    thermalNativeProgramCost (thermalSelectYSteps flag signal)=4 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal))=7 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalSelectYWord flag signal))=0 := by
  constructor
  · rfl
  constructor
  · rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]; rfl
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

def thermalGlobalMinusSteps {n : ℕ} (signal : Fin n) : List (ThermalNativeStep n) :=
  [.fixed (.x signal.val),.z signal,.fixed (.x signal.val),.z signal]

def thermalGlobalMinusWord {n : ℕ} (signal : Fin n) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  thermalNativeProgram (thermalGlobalMinusSteps signal)

private theorem x_basis {n : ℕ} (w : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x w.val])
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x w (!x w)) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_cons,List.map_nil,Qatlib.Foundations.QueryWordCore.Circuit.run_gate,Qatlib.Foundations.QueryWordCore.Circuit.run_nil,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,dif_pos w.isLt]
  rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_wireGate_ket]
  cases hx :
      x w <;> simp
      [Qatlib.Foundations.PureStateMath.PauliX,Qatlib.Foundations.PureStateMath.permMatrix]

theorem thermalGlobalMinus_basis {n : ℕ} (signal : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalGlobalMinusWord signal))
      (Qatlib.Foundations.PureStateMath.Ket x) = (-1:ℂ) • Qatlib.Foundations.PureStateMath.Ket x := by
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n ([.x signal.val]++thermalZWord signal.val++
    [.x signal.val]++thermalZWord signal.val)) (Qatlib.Foundations.PureStateMath.Ket x)=_
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZWord signal.val))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x signal.val])
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZWord signal.val))
        (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x signal.val]) (Qatlib.Foundations.PureStateMath.Ket x))))=_
  rw [x_basis,thermalZWord_basis]
  simp only [finite_run_smul]
  rw [x_basis,thermalZWord_basis]
  simp only [Function.update_self,Function.update_idem,Bool.not_not,Function.update_eq_self,smul_smul]
  cases hx : x signal <;> simp

theorem thermalGlobalMinus_coherent {n : ℕ} (signal : Fin n) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalGlobalMinusWord signal)) psi =
      (-1:ℂ) • psi := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  have hk := thermalGlobalMinus_basis signal
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hk ⊢
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  conv_rhs => rw [he,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change psi x • Qatlib.Foundations.PureStateMath.ApplyGate _
      (Qatlib.Foundations.PureStateMath.Ket x) = _
  rw [hk]
  module

theorem thermalGlobalMinus_cost {n : ℕ} (signal : Fin n) :
    thermalNativeProgramCost (thermalGlobalMinusSteps signal)=4 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalGlobalMinusWord signal))=10 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalGlobalMinusWord signal))=0 := by
  constructor
  · rfl
  constructor
  · rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]; rfl
  · exact (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1

theorem thermalGlobalMinus_legal {n : ℕ} (signal : Fin n) :
    ∀ g∈thermalGlobalMinusSteps signal,thermalNativeLegal g := by
  simp [thermalGlobalMinusSteps,thermalNativeLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,signal.isLt]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
