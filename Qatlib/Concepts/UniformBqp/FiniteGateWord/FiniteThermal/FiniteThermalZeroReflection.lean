/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalMaskedX
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

theorem thermalT_four : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate^4=Qatlib.Foundations.PureStateMath.PauliZ := by
  unfold Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate Qatlib.Foundations.PureStateMath.Rz Qatlib.Foundations.PureStateMath.PauliZ
  rw [Matrix.diagonal_pow]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)^4 = -1
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp ((Real.pi:ℂ)*Complex.I) := by congr 1; push_cast; ring
      _ = -1 := Complex.exp_pi_mul_I

theorem thermalTAdj_four : Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj^4=Qatlib.Foundations.PureStateMath.PauliZ := by
  unfold Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj Qatlib.Foundations.PureStateMath.Rz Qatlib.Foundations.PureStateMath.PauliZ
  rw [Matrix.diagonal_pow]
  congr 1
  funext b
  cases b
  · simp
  · change Complex.exp (((-(Real.pi/4):ℝ):ℂ)*Complex.I)^4 = -1
    rw [← Complex.exp_nat_mul]
    calc
      _ = Complex.exp (-((Real.pi:ℂ)*Complex.I)) := by congr 1; push_cast; ring
      _ = -1 := by rw [Complex.exp_neg,Complex.exp_pi_mul_I]; norm_num

def thermalZWord (w : ℕ) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
    [.t w,.t w,.t w,.t w]

theorem thermalZWord_basis {n : ℕ} (w : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZWord w.val))
      (Qatlib.Foundations.PureStateMath.Ket x) = (if x w then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  have hm : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalZWord w.val)=(Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate)^4 := by
    simp [thermalZWord,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt,pow_succ,Matrix.mul_assoc]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,hm,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_wire_pow,thermalT_four,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_wireGate_ket]
  cases hx : x w <;> simp_all [Qatlib.Foundations.PureStateMath.PauliZ]
  all_goals congr 1; apply Function.update_eq_self_iff.mpr; exact hx.symm

def thermalZeroReflection {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n)) :
    List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  thermalMaskedX cs cs flag ws ++ thermalZWord flag.val ++ thermalMaskedX cs cs flag ws

private theorem finite_run_smul {n : ℕ} (gs : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode) (a : ℂ) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n)) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) (a • psi)=
      a • Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n gs) psi := by
  simp only [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run,Qatlib.Concepts.GateVocabulary.LocalReflectionGates.reflectionApplyGate_smul]

theorem thermalZeroReflection_basis_raw {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      (if x flag ^^ thermalMatch cs cs x then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  let b := x flag ^^ thermalMatch cs cs x
  let y := Function.update x flag b
  have hm :=
      thermalMaskedX_basis cs cs flag ws hn hn.of_append_left (by intro u hu;exact hu) hlen x hc
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs cs flag ws))
    (Qatlib.Foundations.PureStateMath.Ket x)=Qatlib.Foundations.PureStateMath.Ket y at hm
  have htcs : flag∉cs := by
    intro h
    exact (List.disjoint_left.mp hn.disjoint) h (by simp)
  have htws : flag∉ws := (List.nodup_cons.mp hn.of_append_right).1
  have hyc : ∀ u∈ws,y u=false := by
    intro u hu
    have hut : u≠flag := fun h => htws (h ▸ hu)
    simpa only [y,Function.update_of_ne hut] using hc u hu
  have hv (c : Fin n) (hc : c∈cs) : y c=x c := by
    have hct : c≠flag := fun h => htcs (h ▸ hc)
    exact Function.update_of_ne hct _ _
  have hmatch : thermalMatch cs cs y=thermalMatch cs cs x := by
    apply Bool.eq_iff_iff.mpr
    simp only [thermalMatch,List.all_eq_true]
    constructor
    · intro h c hc
      simpa only [hv c hc] using h c hc
    · intro h c hc
      rw [hv c hc]
      exact h c hc
  have hr :=
      thermalMaskedX_basis cs cs flag ws hn hn.of_append_left (by intro u hu;exact hu) hlen y hyc
  rw [hmatch] at hr
  have hr' : Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs cs flag ws))
      (Qatlib.Foundations.PureStateMath.Ket y)=Qatlib.Foundations.PureStateMath.Ket x := by
    simpa [y,b] using hr

  simp only [thermalZeroReflection,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
  change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs cs flag ws))
    (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZWord flag.val))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMaskedX cs cs flag ws)) (Qatlib.Foundations.PureStateMath.Ket x))) = _
  rw [hm,thermalZWord_basis,finite_run_smul,hr']
  simp [y,b]

theorem thermalZeroReflection_basis {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) (hflag : x flag=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      (if thermalMatch cs cs x then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x := by
  simpa only [hflag,Bool.false_xor] using thermalZeroReflection_basis_raw cs flag ws hn hlen x hc

theorem thermalZero_match_iff {n : ℕ} (cs : List (Fin n)) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    thermalMatch cs cs x=true ↔ ∀ c∈cs,x c=false := by
  simp only [thermalMatch,List.all_eq_true]
  constructor
  · intro h c hc
    simpa [hc] using h c hc
  · intro h c hc
    simp [hc,h c hc]

theorem thermalZeroReflection_legal {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalZeroReflection cs flag ws)=true := by
  have hm := thermalMaskedX_legal cs cs flag ws hn hlen
  have hz : Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalZWord flag.val)=true := by
    simp [thermalZWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,flag.isLt]
  simpa only [thermalZeroReflection,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true]
    using And.intro (And.intro hm hz) hm

theorem thermalZeroReflection_cost {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws)) =
      2*(2*cs.length+(if cs.length≤1 then 1 else 15*(2*cs.length-3)))+4 ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws))=0 := by
  refine ⟨?_,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  have hm := (thermalMaskedX_cost cs cs flag ws hlen).1
  rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2] at hm ⊢
  simp only [thermalZeroReflection,List.length_append,thermalZWord,List.length_cons,List.length_nil]
  rw [hm]
  omega

theorem thermalZeroReflection_coherent {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬(x flag=false ∧ ∀ w∈ws,x w=false)) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws)) psi =
      fun x => (if thermalMatch cs cs x then (-1 : ℂ) else 1)*psi x := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  have ht : (∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x •
      ((Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalZeroReflection cs flag ws)) *ᵥ Qatlib.Foundations.PureStateMath.Ket x)) =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • ((if thermalMatch cs cs x then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hcx : x flag=false ∧ ∀ w∈ws,x w=false
    · have hb := thermalZeroReflection_basis cs flag ws hn hlen x hcx.2 hcx.1
      rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
      exact congrArg (fun v => psi x • v) hb
    · simp only [hc x hcx,zero_smul]
  rw [ht]
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Qatlib.Foundations.PureStateMath.Ket]
  simp

theorem thermalZeroReflection_uniform {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hc : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬(x flag=false ∧ ∀ w∈ws,x w=false)) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalZeroReflection cs flag ws)) psi =
      fun x => (if ∀ c∈cs,x c=false then (-1 : ℂ) else 1)*psi x := by
  simpa only [thermalZero_match_iff] using thermalZeroReflection_coherent cs flag ws hn hlen psi hc

theorem thermalZeroReflection_public {n : ℕ} (cs : List (Fin n)) (flag : Fin n) (ws : List (Fin n))
    (hn : (cs++flag::ws).Nodup) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hc : ∀ w∈ws,x w=false) (hflag : x flag=false) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalZeroReflection cs flag ws) (Qatlib.Foundations.PureStateMath.Ket x) =
      some ((if thermalMatch cs cs x then (-1 : ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket x) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun,thermalZeroReflection_legal cs flag ws hn hlen,if_true]
  rw [thermalZeroReflection_basis cs flag ws hn hlen x hc hflag]

theorem thermalZWord_inverse_transport {n : ℕ} (w : Fin n) :
    Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalZWord w.val)) =
      Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalZWord w.val) ∧
    (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalZWord w.val)).length=4 := by
  have ht : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (thermalZWord w.val)=(Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGate)^4 := by
    simp [thermalZWord,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt,pow_succ,Matrix.mul_assoc]
  have htd : Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix n (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint (thermalZWord w.val))=
      (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.wireGate n w Qatlib.Concepts.GateVocabulary.LocalReflectionGates.tGateAdj)^4 := by
    simp [thermalZWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeAdjoint,Qatlib.Concepts.UniformBqp.FiniteGateWord.finiteCodeWordMatrix,
      Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,w.isLt,pow_succ,Matrix.mul_assoc]
  constructor
  · rw [ht,htd,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_wire_pow,Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_wire_pow,thermalT_four,thermalTAdj_four]
  · simp [thermalZWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordAdjoint]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
