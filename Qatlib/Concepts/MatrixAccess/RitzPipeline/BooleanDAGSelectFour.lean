/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSelectFourData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAddition
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
attribute [local irreducible] booleanWordMuxDAG

private theorem s4_sources_map {α : Type*} (H : ℕ) (a b : Fin H → α) (c : α) (f : α → Bool) :
    (fun j => f (booleanMuxSources H a b c j)) =
      booleanWordMuxInput H (fun j => f (a j)) (fun j => f (b j)) (f c) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*H < H := by omega
    simp [booleanMuxSources,booleanWordMuxInput,hn]
  · rw [booleanWordMuxInput,Fin.snoc_castSucc]
    by_cases hk : k.val < H
    · simp [booleanMuxSources,booleanWordAdderInput,hk]
    · simp [booleanMuxSources,booleanWordAdderInput,hk,k.isLt]

private theorem s4_mux {M K H : ℕ} (g : BooleanDAG M K) (a b : Fin H → Fin (M+K))
    (c : Fin (M+K)) (x : Reg M) :
    (fun j => booleanDAGValue (booleanDAGSplice g (booleanMuxSources H a b c) (booleanWordMuxDAG H)) x
      (booleanSpliceSource (booleanMuxSources H a b c) (booleanWordMuxSelect H j))) =
      if booleanDAGValue g x c then (fun j => booleanDAGValue g x (a j))
      else (fun j => booleanDAGValue g x (b j)) := by
  have hr : (fun j => booleanDAGValue (booleanDAGSplice g (booleanMuxSources H a b c) (booleanWordMuxDAG H)) x
      (booleanSpliceSource (booleanMuxSources H a b c) (booleanWordMuxSelect H j))) =
      booleanWordMuxResult H (fun j => booleanDAGValue g x (a j)) (fun j => booleanDAGValue g x (b j))
        (booleanDAGValue g x c) := by
    funext j
    rw [boolean_dag_splice_value,s4_sources_map]
    rfl
  rw [hr,boolean_word_mux_value]

private theorem s4_raw {M K : ℕ} (g : BooleanDAG M K) (x : Reg M) (j : Fin M) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc K g node ih =>
    change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right M K) j)) = x j
    simpa only [booleanDAGValue,Fin.lastCases_castSucc] using! ih

private theorem s4_raw_word (H K : ℕ) (g : BooleanDAG (4*H+2) K) (x : Reg (4*H+2)) (row : Fin 4) :
    (fun j => booleanDAGValue g x (booleanSelectFourRaw H K row j)) = booleanSelectFourWord H x row := by
  funext j
  exact s4_raw g x (booleanSelectFourRaw H 0 row j)

private theorem s4_low (H K : ℕ) (g : BooleanDAG (4*H+2) K) (x : Reg (4*H+2)) :
    booleanDAGValue g x (booleanSelectFourLow H K) = x (booleanSelectFourLow H 0) :=
  s4_raw g x (booleanSelectFourLow H 0)

private theorem s4_high (H K : ℕ) (g : BooleanDAG (4*H+2) K) (x : Reg (4*H+2)) :
    booleanDAGValue g x (booleanSelectFourHigh H K) = x (booleanSelectFourHigh H 0) :=
  s4_raw g x (booleanSelectFourHigh H 0)

private theorem s4_first (H : ℕ) (x : Reg (4*H+2)) :
    (fun j => booleanDAGValue (booleanSelectFourFirst H) x
      (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j))) =
      if x (booleanSelectFourLow H 0) then booleanSelectFourWord H x 1 else booleanSelectFourWord H x 0 := by
  rw [booleanSelectFourFirst,booleanSelectFourFirstInputs,s4_mux,s4_low,s4_raw_word,s4_raw_word]

private theorem s4_second (H : ℕ) (x : Reg (4*H+2)) :
    (fun j => booleanDAGValue (booleanSelectFourSecond H) x
      (booleanSpliceSource (booleanSelectFourSecondInputs H) (booleanWordMuxSelect H j))) =
      if x (booleanSelectFourLow H 0) then booleanSelectFourWord H x 3 else booleanSelectFourWord H x 2 := by
  rw [booleanSelectFourSecond,booleanSelectFourSecondInputs,s4_mux,s4_low,s4_raw_word,s4_raw_word]

private theorem s4_first_old (H : ℕ) (x : Reg (4*H+2)) :
    (fun j => booleanDAGValue (booleanSelectFourSecond H) x
      (Fin.castLE (by omega) (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j)))) =
      if x (booleanSelectFourLow H 0) then booleanSelectFourWord H x 1 else booleanSelectFourWord H x 0 := by
  have he : (fun j => booleanDAGValue (booleanSelectFourSecond H) x
      (Fin.castLE (by omega) (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j)))) =
      (fun j => booleanDAGValue (booleanSelectFourFirst H) x
        (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j))) := by
    funext j
    exact boolean_dag_splice_prefix _ _ _ _ _
  rw [he,s4_first]

theorem boolean_select_four_value (H : ℕ) (x : Reg (4*H+2)) :
    booleanSelectFourResult H x = booleanSelectFourWord H x
      (booleanSelectFourRow (x (booleanSelectFourHigh H 0)) (x (booleanSelectFourLow H 0))) := by
  change (fun j => booleanDAGValue (booleanSelectFourDAG H) x (booleanSelectFourOutput H j)) = _
  simp only [booleanSelectFourDAG,booleanSelectFourOutput,booleanSelectFourFinalInputs]
  rw [s4_mux,s4_high,s4_second,s4_first_old]
  cases hh : x (booleanSelectFourHigh H 0) <;> cases hl : x (booleanSelectFourLow H 0) <;>
    simp only [booleanSelectFourRow,Bool.false_eq_true,ite_false,ite_true]

private theorem s4_input_raw (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) (row : Fin 4) :
    booleanSelectFourWord H (booleanSelectFourInput H a high low) row = a row := by
  funext j
  have hH : 0 < H := Nat.pos_of_ne_zero (by intro h; subst H; exact Fin.elim0 j)
  have hlt : row.val*H+j.val < 4*H := by have := row.isLt; have := j.isLt; nlinarith
  have hd : (row.val*H+j.val)/H = row.val := by
    rw [Nat.mul_comm row.val H,Nat.mul_add_div hH,Nat.div_eq_of_lt j.isLt,add_zero]
  have hm : (row.val*H+j.val)%H = j.val := by
    simp only [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt j.isLt]
  simp only [booleanSelectFourWord,booleanSelectFourRaw,booleanSelectFourInput,Fin.val_mk,dif_pos hlt,hd,hm]

private theorem s4_input_high (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) :
    booleanSelectFourInput H a high low (booleanSelectFourHigh H 0) = high := by
  simp [booleanSelectFourInput,booleanSelectFourHigh]

private theorem s4_input_low (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) :
    booleanSelectFourInput H a high low (booleanSelectFourLow H 0) = low := by
  have hn : ¬4*H+1 < 4*H := by omega
  simp [booleanSelectFourInput,booleanSelectFourLow,hn]

theorem boolean_select_four_input_value (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) :
    booleanSelectFourResult H (booleanSelectFourInput H a high low) = a (booleanSelectFourRow high low) := by
  rw [boolean_select_four_value,s4_input_high,s4_input_low,s4_input_raw]

theorem boolean_select_four_resources (H : ℕ) :
    let gs := booleanDAGSteps (booleanSelectFourDAG H) (booleanSelectFourOutput H)
    reflectionLegal gs ∧ gs.length ≤ 271*H ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (4*H+2)+(((0+3*H)+3*H)+3*H)+H = 14*H+2 := by
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources (booleanSelectFourDAG H) (booleanSelectFourOutput H)
  refine ⟨hl,?_,hq,hc,by omega⟩
  omega

theorem boolean_select_four_basis (H : ℕ) (x : Reg (4*H+2)) (y : Reg H) :
    let K := ((0+3*H)+3*H)+3*H
    Run (1 : Matrix (Reg (4*H+2+K+H)) (Reg (4*H+2+K+H)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanSelectFourDAG H) (booleanSelectFourOutput H)))
      (Ket (booleanDAGInput (4*H+2) K H x y)) =
      Ket (booleanDAGInput (4*H+2) K H x (fun j => y j ^^ booleanSelectFourResult H x j)) :=
  boolean_dag_basis _ _ _ _

theorem boolean_select_four_coherent (H : ℕ) (ψ : QState (Reg (4*H+2) × Reg H)) :
    let K := ((0+3*H)+3*H)+3*H
    Run (1 : Matrix (Reg (4*H+2+K+H)) (Reg (4*H+2+K+H)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanSelectFourDAG H) (booleanSelectFourOutput H)))
      (booleanDAGEmbed (4*H+2) K H ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (4*H+2) K H xy.1
        (fun j => xy.2 j ^^ booleanSelectFourResult H xy.1 j)) :=
  boolean_dag_coherent _ _ _

end Qatlib.Concepts.MatrixAccess.RitzPipeline
