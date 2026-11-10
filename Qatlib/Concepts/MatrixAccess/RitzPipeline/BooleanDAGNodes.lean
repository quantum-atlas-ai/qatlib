/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGData
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped Classical BigOperators

private theorem boolean_source_ne_target {n L : ℕ} (h : n < L) (a : Fin n) :
    Fin.castLE h.le a ≠ (⟨n,h⟩ : Fin L) := by
  intro he
  have hv := congrArg Fin.val he
  have ha := a.isLt
  simp only [Fin.val_castLE] at hv
  omega

private theorem boolean_sources_ne {n L : ℕ} (h : n < L) (a b : Fin n)
    (hab : a ≠ b) : Fin.castLE h.le a ≠ Fin.castLE h.le b := by
  intro he
  apply hab
  apply Fin.ext
  simpa only [Fin.val_castLE] using congrArg (fun i : Fin L => i.val) he

private theorem boolean_wire_x_basis {L : ℕ} (t : Fin L) (x : Reg L) :
    ApplyGate (wireGate L t PauliX) (Ket x) =
      Ket (Function.update x t (!(x t))) := by
  rw [applyGate_wireGate_ket]
  cases ht : x t <;> simp [PauliX,permMatrix]

theorem boolean_node_resources {n L : ℕ} (node : BooleanNode n) (h : n < L) :
    reflectionLegal (booleanNodeSteps node h) ∧
    (booleanNodeSteps node h).length ≤ 15 ∧
    QueryCount (reflectionCompile (booleanNodeSteps node h)) = 0 ∧
    GateCount (reflectionCompile (booleanNodeSteps node h)) = (booleanNodeSteps node h).length := by
  have hl : reflectionLegal (booleanNodeSteps node h) ∧
      (booleanNodeSteps node h).length ≤ 15 := by
    cases node with
    | constant b =>
      cases b <;> simp [booleanNodeSteps,reflectionLegal,reflectionGateLegal,pauliX_unitary]
    | neg a =>
      simp [booleanNodeSteps,reflectionLegal,reflectionGateLegal,
        boolean_source_ne_target h a,pauliX_unitary]
    | xor a b =>
      simp [booleanNodeSteps,reflectionLegal,reflectionGateLegal,
        boolean_source_ne_target h a,boolean_source_ne_target h b]
    | conj a b =>
      by_cases hab : a = b
      · subst b
        simp [booleanNodeSteps,reflectionLegal,reflectionGateLegal,
          boolean_source_ne_target h a]
      · have hlegal := toffoliLocalSteps_legal (Fin.castLE h.le a) (Fin.castLE h.le b)
          (⟨n,h⟩ : Fin L) (boolean_sources_ne h a b hab)
          (boolean_source_ne_target h a) (boolean_source_ne_target h b)
        have hlength := toffoliLocalSteps_length (Fin.castLE h.le a) (Fin.castLE h.le b)
          (⟨n,h⟩ : Fin L)
        simp only [booleanNodeSteps,if_neg hab]
        exact ⟨hlegal,by simpa only [hlength] using (le_rfl : (15:ℕ) ≤ 15)⟩
  exact ⟨hl.1,hl.2,queryCount_reflectionCompile _,gateCount_reflectionCompile _⟩

theorem boolean_node_basis {n L : ℕ} (node : BooleanNode n) (h : n < L) (x : Reg L) :
    Run (1 : Matrix (Reg L) (Reg L) ℂ) (reflectionCompile (booleanNodeSteps node h)) (Ket x) =
      Ket (Function.update x (⟨n,h⟩ : Fin L)
        (x ⟨n,h⟩ ^^ booleanNodeValue node (fun i => x (Fin.castLE h.le i)))) := by
  cases node with
  | constant b =>
    cases b with
    | false =>
      simp [booleanNodeSteps,booleanNodeValue,reflectionCompile]
    | true =>
      simp only [booleanNodeSteps,booleanNodeValue,reflectionCompile,
        List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
      rw [boolean_wire_x_basis]
      simp
  | neg a =>
    simp only [booleanNodeSteps,booleanNodeValue,reflectionCompile,
      List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
    rw [applyGate_cnotGate_ket L _ _ (boolean_source_ne_target h a),boolean_wire_x_basis]
    simp only [Function.update_self,Function.update_idem]
    congr 2
    cases ht : x (⟨n,h⟩ : Fin L) <;>
      cases ha : x (Fin.castLE h.le a) <;> simp
  | xor a b =>
    simp only [booleanNodeSteps,booleanNodeValue,reflectionCompile,
      List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
    rw [applyGate_cnotGate_ket L _ _ (boolean_source_ne_target h a),
      applyGate_cnotGate_ket L _ _ (boolean_source_ne_target h b)]
    simp [Function.update_of_ne (boolean_source_ne_target h b)]
  | conj a b =>
    by_cases hab : a = b
    · subst b
      simp only [booleanNodeSteps,ite_true,booleanNodeValue,
        reflectionCompile,List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
      rw [applyGate_cnotGate_ket L _ _ (boolean_source_ne_target h a)]
      simp
    · have ht := (local_toffoli_fifteen_exact L (Fin.castLE h.le a) (Fin.castLE h.le b)
        (⟨n,h⟩ : Fin L) (boolean_sources_ne h a b hab)
        (boolean_source_ne_target h a) (boolean_source_ne_target h b)).2.2 x
      simpa only [booleanNodeSteps,if_neg hab,booleanNodeValue] using ht

end Qatlib.Concepts.MatrixAccess.RitzPipeline
