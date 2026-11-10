/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSplice
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
def booleanWordMuxPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAG (2*w+1) (3*i)
  | 0, _ => .nil
  | i+1, hi =>
    let g₀ := booleanWordMuxPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨i,by omega⟩ ⟨w+i,by omega⟩)
    let g₂ := g₁.snoc (.conj ⟨2*w+1+3*i,by omega⟩ ⟨2*w,by omega⟩)
    let g₃ := g₂.snoc (.xor ⟨w+i,by omega⟩ ⟨2*w+1+3*i+1,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using! g₃

def booleanWordMuxDAG (w : ℕ) : BooleanDAG (2*w+1) (3*w) :=
  booleanWordMuxPrefix w w (Nat.le_refl w)

def booleanWordMuxSelect (w : ℕ) : Fin w → Fin (2*w+1+3*w) :=
  fun j => ⟨2*w+1+3*j.val+2,by have := j.isLt; omega⟩

def booleanWordMuxInput (w : ℕ) (a b : Reg w) (selectA : Bool) : Reg (2*w+1) :=
  Fin.snoc (booleanWordAdderInput w a b) selectA

def booleanWordMuxResult (w : ℕ) (a b : Reg w) (selectA : Bool) : Reg w := fun j =>
  booleanDAGValue (booleanWordMuxDAG w) (booleanWordMuxInput w a b selectA) (booleanWordMuxSelect w j)

private theorem sa_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

private theorem sa_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [sa_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

private theorem sa_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [sa_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

private theorem mux_bool (a b c : Bool) : (b ^^ ((a ^^ b) && c)) = if c then a else b := by
  cases a <;> cases b <;> cases c <;> decide

private theorem mux_prefix_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w+1))
    (j : ℕ) (hj : j < 2*w+1+3*i) :
    booleanDAGValue (booleanWordMuxPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordMuxPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordMuxPrefix,Nat.mul_succ,Nat.add_assoc,sa_snoc_value]
  split_ifs <;> first | rfl | omega

private theorem mux_prefix_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w+1))
    (j : ℕ) (hj : j < 2*w+1) :
    booleanDAGValue (booleanWordMuxPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ :=
  sa_input_value _ x ⟨j,hj⟩

private theorem mux_prefix_bit (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w+1)) (j : Fin i) :
    booleanDAGValue (booleanWordMuxPrefix w i hi) x
      ⟨2*w+1+3*j.val+2,by have := j.isLt; omega⟩ =
      if x (Fin.last (2*w)) then x ⟨j.val,by have := j.isLt; omega⟩
      else x ⟨w+j.val,by have := j.isLt; omega⟩ := by
  induction i with
  | zero => exact Fin.elim0 j
  | succ i ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp (disch := omega) [booleanWordMuxPrefix,Nat.mul_succ,Nat.add_assoc,
        sa_snoc_value,booleanNodeValue,mux_prefix_input]
      have h0 : w+i < 2*w+(1+3*i) := by omega
      have h1 : w+i < 2*w+(1+(3*i+1)) := by omega
      rw [dif_pos h1,dif_pos h0]
      exact mux_bool (x ⟨i,by omega⟩) (x ⟨w+i,by omega⟩) (x (Fin.last (2*w)))
    · rw [mux_prefix_old w i hi x _ (by have := k.isLt; simp only [Fin.val_castSucc]; omega)]
      exact ih (by omega) k

theorem boolean_word_mux_value (w : ℕ) (a b : Reg w) (selectA : Bool) :
    booleanWordMuxResult w a b selectA = if selectA then a else b := by
  funext j
  have h := mux_prefix_bit w w (Nat.le_refl w) (booleanWordMuxInput w a b selectA) j
  have ha : booleanWordMuxInput w a b selectA ⟨j.val,by have := j.isLt; omega⟩ = a j := by
    change booleanWordMuxInput w a b selectA
      (Fin.castSucc (⟨j.val,by have := j.isLt; omega⟩ : Fin (2*w))) = a j
    rw [booleanWordMuxInput,Fin.snoc_castSucc]
    simp [booleanWordAdderInput,j.isLt]
  have hb : booleanWordMuxInput w a b selectA ⟨w+j.val,by have := j.isLt; omega⟩ = b j := by
    change booleanWordMuxInput w a b selectA
      (Fin.castSucc (⟨w+j.val,by have := j.isLt; omega⟩ : Fin (2*w))) = b j
    have hnot : ¬w+j.val < w := by omega
    rw [booleanWordMuxInput,Fin.snoc_castSucc]
    simp [booleanWordAdderInput,hnot]
  have hc : booleanWordMuxInput w a b selectA (Fin.last (2*w)) = selectA := by
    simp [booleanWordMuxInput]
  rw [ha,hb,hc] at h
  cases selectA <;> simpa only [booleanWordMuxResult,booleanWordMuxDAG,booleanWordMuxSelect] using!
      h

def booleanMuxSources {α : Type*} (H : ℕ) (a b : Fin H → α) (c : α) : Fin (2*H+1) → α :=
  fun j => if hj : j.val < H then a ⟨j.val,hj⟩
    else if hk : j.val < 2*H then b ⟨j.val-H,by omega⟩ else c

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
