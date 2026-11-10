/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplierData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSplice
import Mathlib.Algebra.BigOperators.Fin
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

private theorem mul_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

private theorem mul_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [mul_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

private theorem mul_and_prefix (w n : ℕ) (hn : n ≤ w) (x : Reg (w+1)) (j : Fin n) :
    booleanDAGValue (booleanWordAndPrefix w n hn) x ⟨w+1+j.val,by have := j.isLt; omega⟩ =
      (x ⟨j.val,by have := j.isLt; omega⟩ && x (Fin.last w)) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [booleanWordAndPrefix,mul_snoc_value]
      rw [dif_neg (by change ¬w+1+n < w+1+n; omega)]
      change (booleanDAGValue (booleanWordAndPrefix w n (by omega)) x
          (⟨n,by omega⟩ : Fin (w+1+n)) &&
        booleanDAGValue (booleanWordAndPrefix w n (by omega)) x
          (⟨w,by omega⟩ : Fin (w+1+n))) = _
      exact congrArg₂ (fun a b : Bool => a && b)
        (mul_input_value (booleanWordAndPrefix w n (by omega)) x ⟨n,by omega⟩)
        (mul_input_value (booleanWordAndPrefix w n (by omega)) x (Fin.last w))
    · rw [booleanWordAndPrefix,mul_snoc_value]
      have hk : w+1+k.val < w+1+n := by have := k.isLt; omega
      simp only [Fin.val_castSucc,dif_pos hk]
      exact ih (by omega) k

private def mulRoundInputs (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) : Fin (w+1) → Fin (2*w+p.nodes) := fun j =>
  if hj : j.val < w then ⟨j.val,by omega⟩ else ⟨w+i,by omega⟩

private def mulRoundAnd (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) : BooleanDAG (2*w) (p.nodes+w) :=
  booleanDAGSplice p.graph (mulRoundInputs w i hi p) (booleanWordAndDAG w)

private def mulRoundLeft (w i : ℕ) (p : BooleanDAGWord (2*w) (w+i)) :
    Fin (w+i) → Fin (2*w+(p.nodes+w)) :=
  fun j => Fin.castLE (by omega) (p.output j)

private def mulRoundRight (w i : ℕ) (p : BooleanDAGWord (2*w) (w+i)) :
    Fin (w+i) → Fin (2*w+(p.nodes+w)) := fun j =>
  if hj : j.val < i then Fin.castLE (by omega) p.zero
  else ⟨2*w+p.nodes+(j.val-i),by have := j.isLt; omega⟩

private theorem mul_and_old (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) (x : Reg (2*w)) (j : Fin (2*w+p.nodes)) :
    booleanDAGValue (mulRoundAnd w i hi p) x (Fin.castLE (by omega) j) =
      booleanDAGValue p.graph x j :=
  boolean_dag_splice_prefix _ _ _ _ _

private theorem mul_and_bit (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) (x : Reg (2*w)) (j : Fin w) :
    booleanDAGValue (mulRoundAnd w i hi p) x
      (⟨2*w+p.nodes+j.val,by have := j.isLt; omega⟩ : Fin (2*w+(p.nodes+w))) =
      (booleanWordAdderLeft w x j && booleanWordAdderRight w x ⟨i,hi⟩) := by
  let r := mulRoundInputs w i hi p
  let v : Fin ((w+1)+w) := ⟨w+1+j.val,by have := j.isLt; omega⟩
  have he : booleanSpliceSource (n := w) r v =
      (⟨2*w+p.nodes+j.val,by have := j.isLt; omega⟩ : Fin (2*w+(p.nodes+w))) := by
    have hv : ¬v.val < w+1 := by dsimp [v]; omega
    rw [booleanSpliceSource,dif_neg hv]
    apply Fin.ext
    dsimp only [v]
    omega
  have hs := boolean_dag_splice_value p.graph r (booleanWordAndDAG w) x v
  rw [he] at hs
  have ha : booleanDAGValue p.graph x (r (⟨j.val,by have := j.isLt; omega⟩ : Fin (w+1))) =
      booleanWordAdderLeft w x j := by
    simp only [r,mulRoundInputs,dif_pos j.isLt,booleanWordAdderLeft]
    exact mul_input_value p.graph x ⟨j.val,by have := j.isLt; omega⟩
  have hb : booleanDAGValue p.graph x (r (Fin.last w)) =
      booleanWordAdderRight w x ⟨i,hi⟩ := by
    simp only [r,mulRoundInputs,Fin.val_last,dif_neg (Nat.lt_irrefl w),booleanWordAdderRight]
    exact mul_input_value p.graph x ⟨w+i,by omega⟩
  calc
    _ = booleanDAGValue (booleanWordAndDAG w)
        (fun k => booleanDAGValue p.graph x (r k)) v := hs
    _ = (booleanDAGValue p.graph x (r ⟨j.val,by have := j.isLt; omega⟩) &&
        booleanDAGValue p.graph x (r (Fin.last w))) :=
      mul_and_prefix w w (Nat.le_refl w) _ j
    _ = _ := congrArg₂ (fun a b : Bool => a && b) ha hb

private theorem mul_round_old (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) (x : Reg (2*w)) (j : Fin (2*w+p.nodes)) :
    booleanDAGValue (booleanWordMulRound w i hi p).graph x (Fin.castLE (by
      dsimp only [booleanWordMulRound]; omega) j) = booleanDAGValue p.graph x j := by
  let g := mulRoundAnd w i hi p
  let a := mulRoundLeft w i p
  let b := mulRoundRight w i p
  let r : Fin (2*(w+i)) → Fin (2*w+(p.nodes+w)) := fun k =>
    if hk : k.val < w+i then a ⟨k.val,hk⟩ else b ⟨k.val-(w+i),by omega⟩
  have h := boolean_dag_splice_prefix g r (booleanWordAdderDAG (w+i)) x
    (Fin.castLE (by omega) j)
  exact h.trans (mul_and_old w i hi p x j)

private theorem mul_right_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) (j : Fin (w+i)) :
    booleanDAGValue (mulRoundAnd w i hi p) x (mulRoundRight w i p j) =
      if hj : j.val < i then false else
        (booleanWordAdderLeft w x ⟨j.val-i,by have := j.isLt; omega⟩ &&
          booleanWordAdderRight w x ⟨i,hi⟩) := by
  by_cases hj : j.val < i
  · rw [mulRoundRight,dif_pos hj,dif_pos hj]
    exact (mul_and_old w i hi p x p.zero).trans hz
  · rw [mulRoundRight,dif_neg hj,dif_neg hj]
    exact mul_and_bit w i hi p x ⟨j.val-i,by have := j.isLt; omega⟩

private def mulShift (w i : ℕ) (a : Reg w) (bit : Bool) : Reg (w+i) := fun j =>
  if hj : j.val < i then false else a ⟨j.val-i,by have := j.isLt; omega⟩ && bit

private theorem mul_shift_value (w i : ℕ) (a : Reg w) (bit : Bool) :
    booleanWordLSBValue (w+i) (mulShift w i a bit) =
      if bit then booleanWordLSBValue w a * (2 : ℕ)^i else 0 := by
  cases bit with
  | false => simp [boolean_word_lsb_value,mulShift]
  | true =>
    change booleanWordLSBValue (w+i) (mulShift w i a true) =
      booleanWordLSBValue w a * (2 : ℕ)^i
    rw [boolean_word_lsb_value]
    let f : Fin (i+w) → ℕ := fun j =>
      if hj : j.val < i then 0 else
        (if a ⟨j.val-i,by have := j.isLt; omega⟩ then 1 else 0) * (2 : ℕ)^j.val
    have hs : (∑ j : Fin (w+i),
        (if mulShift w i a true j then 1 else 0) * (2 : ℕ)^j.val) = ∑ j, f j := by
      apply Fintype.sum_equiv (finCongr (Nat.add_comm w i))
      intro j
      by_cases hj : j.val < i <;> simp [mulShift,f,finCongr_apply,hj]
    rw [hs,Fin.sum_univ_add]
    have hzero : (∑ j : Fin i, f (Fin.castAdd w j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [f,j.isLt]
    rw [hzero,zero_add,boolean_word_lsb_value,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hnot : ¬i+j.val < i := by omega
    change (if hj : i+j.val < i then 0 else
      (if a ⟨i+j.val-i,by have := j.isLt; omega⟩ then 1 else 0) * (2 : ℕ)^(i+j.val)) = _
    rw [dif_neg hnot]
    have he : (⟨i+j.val-i,by have := j.isLt; omega⟩ : Fin w) = j := by
      apply Fin.ext
      change i+j.val-i = j.val
      omega
    rw [he,pow_add]
    ring

private theorem mul_round_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    booleanWordLSBValue (w+i+1) (fun j =>
      booleanDAGValue (booleanWordMulRound w i hi p).graph x
        ((booleanWordMulRound w i hi p).output j)) =
      booleanWordLSBValue (w+i) (fun j => booleanDAGValue p.graph x (p.output j)) +
        (if booleanWordAdderRight w x ⟨i,hi⟩ then
          booleanWordLSBValue w (booleanWordAdderLeft w x) * (2 : ℕ)^i else 0) := by
  let g := mulRoundAnd w i hi p
  let a := mulRoundLeft w i p
  let b := mulRoundRight w i p
  have ha : (fun j => booleanDAGValue g x (a j)) =
      (fun j => booleanDAGValue p.graph x (p.output j)) := by
    funext j
    exact mul_and_old w i hi p x (p.output j)
  have hb : (fun j => booleanDAGValue g x (b j)) =
      mulShift w i (booleanWordAdderLeft w x) (booleanWordAdderRight w x ⟨i,hi⟩) := by
    funext j
    exact mul_right_value w i hi p x hz j
  calc
    _ = booleanWordLSBValue (w+i) (fun j => booleanDAGValue g x (a j)) +
        booleanWordLSBValue (w+i) (fun j => booleanDAGValue g x (b j)) :=
      boolean_dag_append_adder_value g (w+i) a b x
    _ = _ := by rw [ha,hb,mul_shift_value]

theorem boolean_word_mul_prefix (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    let p := booleanWordMulPrefix w i hi
    booleanDAGValue p.graph x p.zero = false ∧
      booleanWordLSBValue (w+i) (fun j => booleanDAGValue p.graph x (p.output j)) =
        booleanWordLSBValue w (booleanWordAdderLeft w x) *
          ∑ k : Fin i, (if booleanWordAdderRight w x ⟨k.val,by omega⟩ then 1 else 0) *
            (2 : ℕ)^k.val := by
  induction i with
  | zero =>
    dsimp only [booleanWordMulPrefix,booleanWordMulStart]
    constructor
    · simp [mul_snoc_value,booleanNodeValue]
    · simp [boolean_word_lsb_value,mul_snoc_value,booleanNodeValue]
  | succ i ih =>
    have hi' : i < w := by omega
    let p := booleanWordMulPrefix w i (by omega)
    obtain ⟨hz,hv⟩ := ih (by omega)
    refine ⟨?_,?_⟩
    · exact (mul_round_old w i hi' p x p.zero).trans hz
    · change booleanWordLSBValue (w+i+1) (fun j =>
          booleanDAGValue (booleanWordMulRound w i hi' p).graph x
            ((booleanWordMulRound w i hi' p).output j)) = _
      rw [mul_round_value w i hi' p x hz]
      rw [hv,Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      by_cases hb : booleanWordAdderRight w x ⟨i,hi'⟩ <;> simp [hb,Nat.mul_add]

private theorem mul_left_input (w : ℕ) (a b : Reg w) :
    booleanWordAdderLeft w (booleanWordAdderInput w a b) = a := by
  funext j
  simp [booleanWordAdderLeft,booleanWordAdderInput,j.isLt]

private theorem mul_right_input (w : ℕ) (a b : Reg w) :
    booleanWordAdderRight w (booleanWordAdderInput w a b) = b := by
  funext j
  have hnot : ¬w+j.val < w := by omega
  simp [booleanWordAdderRight,booleanWordAdderInput,hnot]

theorem boolean_word_mul_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (2*w) (booleanWordMulResult w a b) =
      booleanWordLSBValue w a * booleanWordLSBValue w b := by
  have h := (boolean_word_mul_prefix w w (Nat.le_refl w) (booleanWordAdderInput w a b)).2
  simp only [mul_left_input,mul_right_input] at h
  rw [← boolean_word_lsb_value] at h
  have he : booleanWordLSBValue (2*w) (booleanWordMulResult w a b) =
      booleanWordLSBValue (w+w) (fun j =>
        booleanDAGValue (booleanWordMulProgram w).graph (booleanWordAdderInput w a b)
          ((booleanWordMulProgram w).output j)) := by
    rw [boolean_word_lsb_value,boolean_word_lsb_value]
    apply Fintype.sum_equiv (finCongr (Nat.two_mul w))
    intro j
    simp only [booleanWordMulResult,booleanWordMulSelect,finCongr_apply,Fin.val_cast]
    rfl
  exact he.trans h

private theorem mul_prefix_nodes (w i : ℕ) (hi : i ≤ w) :
    (booleanWordMulPrefix w i hi).nodes ≤ 1+(11*w+1)*i := by
  induction i with
  | zero => simp [booleanWordMulPrefix,booleanWordMulStart]
  | succ i ih =>
    have hp := ih (by omega)
    change (booleanWordMulPrefix w i (by omega)).nodes+w+(5*(w+i)+1) ≤ _
    have hiw : i ≤ w := by omega
    nlinarith

theorem boolean_word_mul_resources (w : ℕ) :
    let p := booleanWordMulProgram w
    let gs := booleanDAGSteps p.graph (booleanWordMulSelect w)
    p.nodes ≤ 11*w^2+w+1 ∧ reflectionLegal gs ∧
      gs.length ≤ 330*w^2+32*w+30 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      2*w+p.nodes+2*w ≤ 11*w^2+5*w+1 := by
  let p := booleanWordMulProgram w
  have hn : p.nodes ≤ 11*w^2+w+1 := by
    have h := mul_prefix_nodes w w (Nat.le_refl w)
    change (booleanWordMulPrefix w w (Nat.le_refl w)).nodes ≤ _
    nlinarith
  obtain ⟨hlegal,hlen,hquery,hgate⟩ := boolean_dag_resources p.graph (booleanWordMulSelect w)
  refine ⟨hn,hlegal,?_,hquery,hgate,?_⟩
  · nlinarith
  · change 2*w+p.nodes+2*w ≤ _
    omega

theorem boolean_word_mul_basis (w : ℕ) (a b : Reg w) (y : Reg (2*w)) :
    let p := booleanWordMulProgram w
    Run (1 : Matrix (Reg (2*w+p.nodes+2*w)) (Reg (2*w+p.nodes+2*w)) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph (booleanWordMulSelect w)))
      (Ket (booleanDAGInput (2*w) p.nodes (2*w) (booleanWordAdderInput w a b) y)) =
      Ket (booleanDAGInput (2*w) p.nodes (2*w) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordMulResult w a b j)) :=
  boolean_dag_basis _ _ _ _

private theorem mul_input_views (w : ℕ) (x : Reg (2*w)) :
    booleanWordAdderInput w (booleanWordAdderLeft w x) (booleanWordAdderRight w x) = x := by
  funext i
  by_cases hi : i.val < w
  · simp [booleanWordAdderInput,booleanWordAdderLeft,hi]
  · have hle : w ≤ i.val := by omega
    simp [booleanWordAdderInput,booleanWordAdderRight,hi,Nat.add_sub_of_le hle]

theorem boolean_word_mul_coherent (w : ℕ) (ψ : QState (Reg (2*w) × Reg (2*w))) :
    let p := booleanWordMulProgram w
    Run (1 : Matrix (Reg (2*w+p.nodes+2*w)) (Reg (2*w+p.nodes+2*w)) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph (booleanWordMulSelect w)))
      (booleanDAGEmbed (2*w) p.nodes (2*w) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w) p.nodes (2*w) xy.1
        (fun j => xy.2 j ^^ booleanWordMulResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j)) := by
  (try dsimp only)
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordMulResult,mul_input_views]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
