/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalToffoli
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteGatePhaseBoundary
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib Matrix
open scoped BigOperators

def thermalMultiX {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) : List Qatlib.Concepts.GateVocabulary.FiniteGateDescription.FiniteGateCode :=
  match cs,ws with
  | [],_ => [.x t.val]
  | [a],_ => [.cx a.val t.val]
  | [a,b],_ => thermalToffoliWord a.val b.val t.val
  | a::b::c::rest,w::work =>
      thermalToffoliWord a.val b.val w.val ++
        thermalMultiX (w::c::rest) t work ++ thermalToffoliWord a.val b.val w.val

  | _,[] => [.cx t.val t.val]
termination_by cs.length

def thermalControl {n : ℕ} (cs : List (Fin n)) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Bool := cs.all x

private theorem control_update {n : ℕ} (cs : List (Fin n)) (x : Qatlib.Foundations.PureStateMath.Reg n)
    (w : Fin n) (b : Bool) (hne : w ∉ cs) :
    thermalControl cs (Function.update x w b) = thermalControl cs x := by
  apply Bool.eq_iff_iff.mpr
  simp only [thermalControl,List.all_eq_true]
  have he (c : Fin n) (hc : c ∈ cs) : Function.update x w b c = x c := by
    have hcw : c ≠ w := fun h => hne (h ▸ hc)
    exact Function.update_of_ne hcw _ _
  constructor
  · intro h c hc
    simpa only [he c hc] using h c hc
  · intro h c hc
    simpa only [he c hc] using h c hc

private theorem move_scratch {n : ℕ} (a b w t : Fin n) (cs ws : List (Fin n))
    (hn : (a::b::cs ++ t::w::ws).Nodup) :
    (w::cs ++ t::ws).Nodup := by
  have ht : (cs ++ t::w::ws).Nodup := hn.tail.tail
  have hp : (cs ++ t::w::ws).Perm (w::(cs ++ t::ws)) := by
    simpa [List.append_assoc] using (List.perm_middle (a:=w) (l₁:=cs++[t]) (l₂:=ws))
  exact hp.nodup_iff.mp ht

private theorem x_run {n : ℕ} (t : Fin n) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.x t.val])
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (!x t)) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_cons,List.map_nil,Qatlib.Foundations.QueryWordCore.Circuit.run_gate,Qatlib.Foundations.QueryWordCore.Circuit.run_nil,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,dif_pos t.isLt]
  rw [Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_wireGate_ket]
  cases hx :
      x t <;> simp
      [Qatlib.Foundations.PureStateMath.PauliX,Qatlib.Foundations.PureStateMath.permMatrix]

private theorem cx_run {n : ℕ} (c t : Fin n) (hct : c ≠ t) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n [.cx c.val t.val])
      (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ x c)) := by
  have hct' : c.val ≠ t.val := fun h => hct (Fin.ext h)
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_cons,List.map_nil,Qatlib.Foundations.QueryWordCore.Circuit.run_gate,Qatlib.Foundations.QueryWordCore.Circuit.run_nil,
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix,dif_pos (show c.val < n ∧ t.val < n ∧ c.val ≠ t.val from
      ⟨c.isLt,t.isLt,hct'⟩)]
  exact Qatlib.Concepts.GateVocabulary.LocalReflectionGates.applyGate_cnotGate_ket n c t hct x

private theorem tof_run {n : ℕ} (a b t : Fin n) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (x : Qatlib.Foundations.PureStateMath.Reg n) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ)
      (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val t.val))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
  rw [thermalToffoliWord_compile n a b t hab hat hbt]
  exact (Qatlib.Concepts.GateVocabulary.LocalReflectionGates.local_toffoli_fifteen_exact n a b t hab hat hbt).2.2 x

theorem thermalMultiX_basis {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (hn : (cs ++ t::ws).Nodup) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hclean : ∀ w∈ws,x w=false) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX cs t ws))
      (Qatlib.Foundations.PureStateMath.Ket x) =
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ thermalControl cs x)) := by
  induction cs,ws using thermalMultiX.induct generalizing x with
  | case1 ws =>
    simp only [thermalMultiX,thermalControl,List.all_nil,Bool.xor_true]
    exact x_run t x
  | case2 ws a =>
    have hat : a ≠ t := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    simpa [thermalMultiX,thermalControl] using cx_run a t hat x
  | case3 ws a b =>
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hat : a ≠ t := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hbt : b ≠ t := fun h => (List.nodup_cons.mp hn.tail).1 (by simp [h])
    simpa [thermalMultiX,thermalControl] using tof_run a b t hab hat hbt x
  | case4 a b c rest w work ih =>
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have haw : a ≠ w := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hbw : b ≠ w := fun h => (List.nodup_cons.mp hn.tail).1 (by simp [h])
    have hat : a ≠ t := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hbt : b ≠ t := fun h => (List.nodup_cons.mp hn.tail).1 (by simp [h])
    have hr := move_scratch a b w t (c::rest) work hn
    have hwt : w ≠ t := fun h => (List.nodup_cons.mp hr).1 (by simp [h])
    have hwr : w ∉ c::rest := fun h => (List.nodup_cons.mp hr).1
      (List.mem_append_left (t::work) h)
    have hwc : x w=false := hclean w (by simp)
    let y := Function.update x w (x a && x b)
    have hyclean : ∀ u∈work,y u=false := by
      intro u hu
      have huw : u ≠ w := by
        intro h
        have hwmem : w ∈ work := h ▸ hu
        exact (List.nodup_cons.mp hr).1 (List.mem_append_right (c::rest) (by simp [hwmem]))
      simpa [y,Function.update_of_ne huw] using hclean u (by simp [hu])
    have hcy : thermalControl (w::c::rest) y = thermalControl (a::b::c::rest) x := by
      change (y w && thermalControl (c::rest) y) = _
      rw [control_update (c::rest) x w (x a && x b) hwr]
      simp [y,thermalControl,Bool.and_assoc]
    have hyt : y t=x t := Function.update_of_ne hwt.symm _ _
    have hrec := ih hr (by simp only [List.length_cons] at hlen ⊢; omega) y hyclean
    rw [hcy,hyt] at hrec
    let z := Function.update y t (x t ^^ thermalControl (a::b::c::rest) x)
    have hrestore : Function.update z w (z w ^^ (z a && z b)) =
        Function.update x t (x t ^^ thermalControl (a::b::c::rest) x) := by
      funext i
      by_cases hiw : i=w
      · subst i
        simp [z,y,hwt,haw,hbw,hat,hbt,hwc]
      · by_cases hit : i=t
        · subst i
          simp [z,y,hiw]
        · simp [z,y,hiw,hit]
    simp only [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit,List.map_append,Qatlib.Foundations.QueryWordCore.Circuit.run_append]
    rw [show (thermalToffoliWord a.val b.val w.val).map (fun g => Qatlib.Foundations.QueryWordCore.Circuit.Step.gate (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeMatrix n g)) =
      Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val w.val) from rfl]
    rw [tof_run a b w hab haw hbw x]
    rw [hwc,Bool.false_xor]
    change Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalToffoliWord a.val b.val w.val))
      (Qatlib.Foundations.QueryWordCore.Circuit.Run 1 (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX (w::c::rest) t work))
        (Qatlib.Foundations.PureStateMath.Ket y)) = _
    rw [hrec,tof_run a b w hab haw hbw,hrestore]
  | case5 cs h0 h1 h2 =>
    cases cs with
    | nil => exact (h0 rfl).elim
    | cons a cs => cases cs with
      | nil => exact (h1 a rfl).elim
      | cons b cs => cases cs with
        | nil => exact (h2 a b rfl).elim
        | cons c cs => simp only [List.length_cons,List.length_nil] at hlen; omega

private theorem tof_legal {n : ℕ} (a b t : Fin n) (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalToffoliWord a.val b.val t.val) = true := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hat' : a.val ≠ t.val := fun h => hat (Fin.ext h)
  have hbt' : b.val ≠ t.val := fun h => hbt (Fin.ext h)
  simp [thermalToffoliWord,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,a.isLt,b.isLt,t.isLt,
    hab',hat',hbt']

theorem thermalMultiX_legal {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (hn : (cs ++ t::ws).Nodup) (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalMultiX cs t ws) = true := by
  induction cs,ws using thermalMultiX.induct with
  | case1 ws => simp [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,t.isLt]
  | case2 ws a =>
    have hat : a ≠ t := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hat' : a.val ≠ t.val := fun h => hat (Fin.ext h)
    simp [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal,a.isLt,t.isLt,hat']
  | case3 ws a b =>
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hat : a ≠ t := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hbt : b ≠ t := fun h => (List.nodup_cons.mp hn.tail).1 (by simp [h])
    simpa only [thermalMultiX] using tof_legal a b t hab hat hbt
  | case4 a b c rest w work ih =>
    have hab : a ≠ b := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have haw : a ≠ w := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hbw : b ≠ w := fun h => (List.nodup_cons.mp hn.tail).1 (by simp [h])
    have hr := ih (move_scratch a b w t (c::rest) work hn)
      (by simp only [List.length_cons] at hlen ⊢; omega)
    have ht := tof_legal a b w hab haw hbw
    simpa only [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append,Bool.and_eq_true]
      using And.intro (And.intro ht hr) ht
  | case5 cs h0 h1 h2 =>
    cases cs with
    | nil => exact (h0 rfl).elim
    | cons a cs => cases cs with
      | nil => exact (h1 a rfl).elim
      | cons b cs => cases cs with
        | nil => exact (h2 a b rfl).elim
        | cons c cs => simp only [List.length_cons,List.length_nil] at hlen; omega

theorem thermalMultiX_cost {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (hlen : cs.length ≤ ws.length+2) :
    Qatlib.Foundations.QueryWordCore.Circuit.GateCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX cs t ws)) =
      (if cs.length ≤ 1 then 1 else 15*(2*cs.length-3)) ∧
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX cs t ws)) = 0 := by
  refine ⟨?_,(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).1⟩
  rw [(Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit_counts n _).2]
  induction cs,ws using thermalMultiX.induct with
  | case1 ws => simp [thermalMultiX]
  | case2 ws a => simp [thermalMultiX]
  | case3 ws a b => simp [thermalMultiX,thermalToffoliWord]
  | case4 a b c rest w work ih =>
    have hi := ih (by simp only [List.length_cons] at hlen ⊢; omega)
    simp only [thermalMultiX,List.length_append] at ⊢
    change 15 + (thermalMultiX (w::c::rest) t work).length + 15 = _
    simp only [List.length_cons] at hi
    have hf : ¬rest.length+1+1 ≤ 1 := by omega
    have hf2 : ¬rest.length+1+1+1 ≤ 1 := by omega
    simp only [if_neg hf] at hi
    rw [hi]
    simp only [List.length_cons,if_neg hf2]
    omega
  | case5 cs h0 h1 h2 =>
    cases cs with
    | nil => exact (h0 rfl).elim
    | cons a cs => cases cs with
      | nil => exact (h1 a rfl).elim
      | cons b cs => cases cs with
        | nil => exact (h2 a b rfl).elim
        | cons c cs => simp only [List.length_cons,List.length_nil] at hlen; omega

theorem thermalMultiX_coherent {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (hn : (cs ++ t::ws).Nodup) (hlen : cs.length ≤ ws.length+2) (psi : Qatlib.Foundations.PureStateMath.QState (Qatlib.Foundations.PureStateMath.Reg n))
    (hclean : ∀ x : Qatlib.Foundations.PureStateMath.Reg n, (¬∀ w∈ws,x w=false) → psi x=0) :
    Qatlib.Foundations.QueryWordCore.Circuit.Run (1 : Matrix (Qatlib.Foundations.PureStateMath.Reg n) (Qatlib.Foundations.PureStateMath.Reg n) ℂ) (Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeCircuit n (thermalMultiX cs t ws)) psi =
      ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket
        (Function.update x t (x t ^^ thermalControl cs x)) := by
  have he : psi = ∑ x : Qatlib.Foundations.PureStateMath.Reg n, psi x • Qatlib.Foundations.PureStateMath.Ket x := by
    funext z
    simp [Qatlib.Foundations.PureStateMath.Ket,Finset.sum_apply]
  rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run]
  conv_lhs => rw [he]
  simp only [Qatlib.Foundations.PureStateMath.ApplyGate,Matrix.mulVec_sum,Matrix.mulVec_smul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : ∀ w∈ws,x w=false
  · have hb := thermalMultiX_basis cs t ws hn hlen x hc
    rw [Qatlib.Concepts.UniformBqp.FiniteGateWord.finite_phase_word_run] at hb
    exact congrArg (fun v => psi x • v) hb
  · simp only [hclean x hc,zero_smul]

theorem thermalMultiX_insufficient {n : ℕ} (cs : List (Fin n)) (t : Fin n)
    (ws : List (Fin n)) (hshort : ws.length+2 < cs.length) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal n (thermalMultiX cs t ws) = false := by
  induction cs,ws using thermalMultiX.induct with
  | case1 ws => simp only [List.length_nil] at hshort; omega
  | case2 ws a => simp only [List.length_cons,List.length_nil] at hshort; omega
  | case3 ws a b => simp only [List.length_cons,List.length_nil] at hshort; omega
  | case4 a b c rest w work ih =>
    have hr := ih (by simp only [List.length_cons] at hshort ⊢; omega)
    simp only [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,List.all_append] at hr ⊢
    rw [hr]
    simp
  | case5 cs h0 h1 h2 =>
    cases cs with
    | nil => exact (h0 rfl).elim
    | cons a cs => cases cs with
      | nil => exact (h1 a rfl).elim
      | cons b cs => cases cs with
        | nil => exact (h2 a b rfl).elim
        | cons c cs => simp [thermalMultiX,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordLegal,Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteCodeLegal]

theorem thermalMultiX_public {n : ℕ} (cs : List (Fin n)) (t : Fin n) (ws : List (Fin n))
    (hn : (cs ++ t::ws).Nodup) (hlen : cs.length ≤ ws.length+2)
    (x : Qatlib.Foundations.PureStateMath.Reg n) (hclean : ∀ w∈ws,x w=false) :
    Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun n (thermalMultiX cs t ws) (Qatlib.Foundations.PureStateMath.Ket x) =
      some (Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ thermalControl cs x))) := by
  simp only [Qatlib.Concepts.GateVocabulary.FiniteGateDescription.finiteWordRun,thermalMultiX_legal cs t ws hn hlen,if_true]
  rw [thermalMultiX_basis cs t ws hn hlen x hclean]

end Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
