/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDividerData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGConditionalSubtract
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

private theorem div_cons_value (w : ℕ) (bit : Bool) (a : Reg w) :
    booleanWordLSBValue (w+1) (Fin.cons bit a) =
      (if bit then 1 else 0)+2*booleanWordLSBValue w a := by
  simp only [boolean_word_lsb_value,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
    Fin.val_zero,Fin.val_succ,pow_zero,mul_one,pow_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private def divExtend (w i : ℕ) (a : Reg w) : Reg (w+i) := fun j =>
  if hj : j.val < w then a ⟨j.val,hj⟩ else false

private theorem div_extend_value (w i : ℕ) (a : Reg w) :
    booleanWordLSBValue (w+i) (divExtend w i a) = booleanWordLSBValue w a := by
  rw [boolean_word_lsb_value,Fin.sum_univ_add,boolean_word_lsb_value]
  have hleft : (∑ j : Fin w,
      (if divExtend w i a (Fin.castAdd i j) then 1 else 0)*2^(Fin.castAdd i j).val) =
      ∑ j : Fin w, (if a j then 1 else 0)*2^j.val := by
    apply Finset.sum_congr rfl
    intro j _
    simp [divExtend,j.isLt]
  have hright : (∑ j : Fin i,
      (if divExtend w i a (Fin.natAdd w j) then 1 else 0)*2^(Fin.natAdd w j).val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hn : ¬w+j.val < w := by omega
    simp [divExtend,hn]
  rw [hleft,hright,add_zero]

private theorem div_high_step (w i : ℕ) (hi : i < w) (a : Reg w) :
    booleanWordHighValue w (i+1) (by omega) a =
      (if a ⟨w-1-i,by omega⟩ then 1 else 0)+2*booleanWordHighValue w i (by omega) a := by
  have he : (fun j : Fin (i+1) => a ⟨w-(i+1)+j.val,by have := j.isLt; omega⟩) =
      Fin.cons (a ⟨w-1-i,by omega⟩)
        (fun j : Fin i => a ⟨w-i+j.val,by have := j.isLt; omega⟩) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.cons_zero,Fin.val_zero,add_zero]
      congr 1
      apply Fin.ext
      (try dsimp only)
      omega
    · simp only [Fin.cons_succ,Fin.val_succ]
      congr 1
      apply Fin.ext
      (try dsimp only)
      omega
  dsimp only [booleanWordHighValue]
  rw [he,div_cons_value]

private theorem div_high_full (w : ℕ) (a : Reg w) :
    booleanWordHighValue w w (Nat.le_refl w) a = booleanWordLSBValue w a := by
  simp [booleanWordHighValue]

private theorem div_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

private theorem div_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [div_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

private theorem div_nz_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(3*i+1)) :
    booleanDAGValue (booleanWordNonzeroPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordNonzeroPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordNonzeroPrefix,Nat.mul_succ,Nat.add_assoc,div_snoc_value]
  split_ifs <;> first | rfl | omega

private theorem div_nz_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w) :
    booleanDAGValue (booleanWordNonzeroPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ :=
  div_input_value _ x ⟨j,hj⟩

private def divNZ (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) : Bool :=
  booleanDAGValue (booleanWordNonzeroPrefix w i hi) x ⟨2*w+3*i,by omega⟩

private theorem div_nz_zero_wire (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    booleanDAGValue (booleanWordNonzeroPrefix w i hi) x ⟨2*w,by omega⟩ = false := by
  induction i with
  | zero => simp [booleanWordNonzeroPrefix,div_snoc_value,booleanNodeValue]
  | succ i ih =>
    rw [div_nz_old w i hi x (2*w) (by omega)]
    exact ih (by omega)

private theorem div_nz_step (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    divNZ w (i+1) hi x =
      ((divNZ w i (by omega) x ^^ x ⟨w+i,by omega⟩) ^^
        (divNZ w i (by omega) x && x ⟨w+i,by omega⟩)) := by
  simp (disch := omega) [divNZ,booleanWordNonzeroPrefix,Nat.mul_succ,Nat.add_assoc,
    div_snoc_value,booleanNodeValue,div_nz_input]
  split_ifs <;> first | rfl | omega

private theorem div_or_positive (s p : ℕ) (hp : 0 < p) (b : Bool) :
    ((decide (0 < s) ^^ b) ^^ (decide (0 < s) && b)) =
      decide (0 < s+(if b then 1 else 0)*p) := by
  cases b with
  | false => simp
  | true =>
    have hpos : 0 < s+p := by omega
    simp only [if_true,one_mul,Bool.xor_true,Bool.and_true,decide_eq_true hpos]
    cases (decide (0 < s)) <;> rfl

private theorem div_nz_value (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    divNZ w i hi x = decide (0 < ∑ j : Fin i,
      (if x ⟨w+j.val,by have := j.isLt; omega⟩ then 1 else 0)*(2 : ℕ)^j.val) := by
  induction i with
  | zero => simp [divNZ,booleanWordNonzeroPrefix,div_snoc_value,booleanNodeValue]
  | succ i ih =>
    rw [div_nz_step,ih (by omega),Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    exact div_or_positive _ (2^i) (by positivity) _

private def divQ {w i : ℕ} (p : BooleanDAGDivState w i) (x : Reg (2*w)) : Reg i :=
  fun j => booleanDAGValue p.graph x (p.quotient j)

private def divR {w i : ℕ} (p : BooleanDAGDivState w i) (x : Reg (2*w)) : Reg (w+i) :=
  fun j => booleanDAGValue p.graph x (p.remainder j)

private def divRoundInputs (w i : ℕ) (hi : i < w) (p : BooleanDAGDivState w i) :
    Fin (2*(w+i+1)) → Fin (2*w+p.nodes) := fun j =>
  if hj : j.val < w+i+1 then
    if hz : j.val = 0 then ⟨w-1-i,by omega⟩
    else p.remainder ⟨j.val-1,by omega⟩
  else if hb : j.val-(w+i+1) < w then ⟨w+(j.val-(w+i+1)),by omega⟩
    else p.zero

private def divA (w i : ℕ) (hi : i < w) (p : BooleanDAGDivState w i) (x : Reg (2*w)) :
    Reg (w+i+1) := Fin.cons (x ⟨w-1-i,by omega⟩) (divR p x)

private def divB (w i : ℕ) (x : Reg (2*w)) : Reg (w+i+1) :=
  divExtend w (i+1) (booleanWordAdderRight w x)

private def divTrial (w i : ℕ) (hi : i < w) (p : BooleanDAGDivState w i) (x : Reg (2*w)) :
    Reg (w+i+1+1) := booleanWordCondSubResult (w+i+1) (divA w i hi p x) (divB w i x)

private theorem div_round_input_left (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w)) (j : Fin (w+i+1)) :
    booleanDAGValue p.graph x (divRoundInputs w i hi p ⟨j.val,by have := j.isLt; omega⟩) =
      divA w i hi p x j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [divRoundInputs,Fin.val_zero,show (0:ℕ) < w+i+1 by omega,dif_pos,
      divA,Fin.cons_zero]
    exact div_input_value p.graph x ⟨w-1-i,by omega⟩
  · have hk : k.val+1 < w+i+1 := by have := k.isLt; omega
    simp only [divRoundInputs,Fin.val_succ,dif_pos hk,Nat.succ_ne_zero,dite_false,
      Nat.add_sub_cancel,divA,Fin.cons_succ,divR]

private theorem div_round_input_right (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) (j : Fin (w+i+1)) :
    booleanDAGValue p.graph x
      (divRoundInputs w i hi p ⟨w+i+1+j.val,by have := j.isLt; omega⟩) =
      divB w i x j := by
  have hnot : ¬w+i+1+j.val < w+i+1 := by omega
  simp only [divRoundInputs,dif_neg hnot,Nat.add_sub_cancel_left,divB,divExtend]
  by_cases hj : j.val < w
  · simp only [dif_pos hj,booleanWordAdderRight]
    exact div_input_value p.graph x ⟨w+j.val,by omega⟩
  · simp only [dif_neg hj]
    exact hz

private theorem div_round_inputs_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    (fun j => booleanDAGValue p.graph x (divRoundInputs w i hi p j)) =
      booleanWordAdderInput (w+i+1) (divA w i hi p x) (divB w i x) := by
  funext j
  by_cases hj : j.val < w+i+1
  · simpa only [booleanWordAdderInput,dif_pos hj] using!
      div_round_input_left w i hi p x ⟨j.val,hj⟩
  · have hk : j.val-(w+i+1) < w+i+1 := by have := j.isLt; omega
    have he : (⟨w+i+1+(j.val-(w+i+1)),by omega⟩ : Fin (2*(w+i+1))) = j := by
      apply Fin.ext
      (try dsimp only)
      omega
    have h := div_round_input_right w i hi p x hz ⟨j.val-(w+i+1),hk⟩
    rw [he] at h
    simpa only [booleanWordAdderInput,dif_neg hj] using! h

private theorem div_trial_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) (j : Fin (w+i+1+1)) :
    booleanDAGValue (booleanWordDivRound w i hi p).graph x
      (booleanSpliceSource (divRoundInputs w i hi p) (booleanWordCondSubSelect (w+i+1) j)) =
      divTrial w i hi p x j := by
  have h := boolean_dag_splice_value p.graph (divRoundInputs w i hi p)
    (booleanWordCondSubDAG (w+i+1)) x (booleanWordCondSubSelect (w+i+1) j)
  rw [div_round_inputs_value w i hi p x hz] at h
  exact h

private theorem div_round_old (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w)) (j : Fin (2*w+p.nodes)) :
    booleanDAGValue (booleanWordDivRound w i hi p).graph x
      (Fin.castLE (by dsimp only [booleanWordDivRound]; omega) j) =
      booleanDAGValue p.graph x j :=
  boolean_dag_splice_prefix _ _ _ _ _

private theorem div_round_remainder (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    divR (w := w) (i := i+1) (booleanWordDivRound w i hi p) x =
      fun j => divTrial w i hi p x j.castSucc := by
  funext j
  exact div_trial_value w i hi p x hz j.castSucc

private theorem div_round_quotient (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    divQ (booleanWordDivRound w i hi p) x =
      Fin.cons (divTrial w i hi p x (Fin.last (w+i+1))) (divQ p x) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [divQ,booleanWordDivRound,Fin.val_zero,Fin.cons_zero]
    exact div_trial_value w i hi p x hz (Fin.last (w+i+1))
  · simp only [divQ,booleanWordDivRound,Fin.val_succ,Nat.succ_ne_zero,dite_false,
      Nat.add_sub_cancel,Fin.cons_succ]
    exact div_round_old w i hi p x (p.quotient k)

private theorem div_cond_balance (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue w a =
      (if booleanWordCondSubResult w a b (Fin.last w) then 1 else 0)*booleanWordLSBValue w b +
        booleanWordLSBValue w (fun j => booleanWordCondSubResult w a b j.castSucc) := by
  obtain ⟨hf,hv⟩ := boolean_word_cond_sub_value w a b
  rw [hf,hv]
  by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a
  · simp [h]
  · simp [h]

private theorem div_a_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w)) :
    booleanWordLSBValue (w+i+1) (divA w i hi p x) =
      (if x ⟨w-1-i,by omega⟩ then 1 else 0)+2*booleanWordLSBValue (w+i) (divR p x) :=
  div_cons_value _ _ _

private theorem div_b_value (w i : ℕ) (x : Reg (2*w)) :
    booleanWordLSBValue (w+i+1) (divB w i x) =
      booleanWordLSBValue w (booleanWordAdderRight w x) :=
  div_extend_value w (i+1) (booleanWordAdderRight w x)

private theorem div_round_q_value (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    booleanWordLSBValue (i+1) (divQ (booleanWordDivRound w i hi p) x) =
      (if divTrial w i hi p x (Fin.last (w+i+1)) then 1 else 0)+
        2*booleanWordLSBValue i (divQ p x) := by
  rw [div_round_quotient w i hi p x hz,div_cons_value]

private theorem div_round_balance (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false) :
    (if x ⟨w-1-i,by omega⟩ then 1 else 0)+2*booleanWordLSBValue (w+i) (divR p x) =
      (if divTrial w i hi p x (Fin.last (w+i+1)) then 1 else 0)*
        booleanWordLSBValue w (booleanWordAdderRight w x) +
        booleanWordLSBValue (w+i+1) (divR (w := w) (i := i+1) (booleanWordDivRound w i hi p) x) := by
  rw [div_round_remainder w i hi p x hz]
  have h := div_cond_balance (w+i+1) (divA w i hi p x) (divB w i x)
  rw [div_a_value,div_b_value] at h
  exact h

private theorem div_round_small (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) (x : Reg (2*w))
    (hz : booleanDAGValue p.graph x p.zero = false)
    (hb : 0 < booleanWordLSBValue w (booleanWordAdderRight w x))
    (hr : booleanWordLSBValue (w+i) (divR p x) <
      booleanWordLSBValue w (booleanWordAdderRight w x)) :
    booleanWordLSBValue (w+i+1) (divR (w := w) (i := i+1) (booleanWordDivRound w i hi p) x) <
      booleanWordLSBValue w (booleanWordAdderRight w x) := by
  have hbit : (if x ⟨w-1-i,by omega⟩ then 1 else 0 : ℕ) ≤ 1 := by
    split_ifs <;> omega
  have hb' : 0 < booleanWordLSBValue (w+i+1) (divB w i x) := by
    rw [div_b_value]
    exact hb
  have ha : booleanWordLSBValue (w+i+1) (divA w i hi p x) <
      2*booleanWordLSBValue (w+i+1) (divB w i x) := by
    rw [div_a_value,div_b_value]
    omega
  have h := (boolean_word_cond_sub_step (w+i+1) (divA w i hi p x) (divB w i x) hb' ha).1
  rw [div_b_value] at h
  rw [div_round_remainder w i hi p x hz]
  exact h

theorem boolean_word_div_prefix (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    let p := booleanWordDivPrefix w i hi
    let B := booleanWordLSBValue w (booleanWordAdderRight w x)
    let Q := booleanWordLSBValue i (fun j => booleanDAGValue p.graph x (p.quotient j))
    let R := booleanWordLSBValue (w+i) (fun j => booleanDAGValue p.graph x (p.remainder j))
    booleanDAGValue p.graph x p.zero = false ∧
      booleanDAGValue p.graph x p.nonzero = decide (0 < B) ∧
      booleanWordHighValue w i hi (booleanWordAdderLeft w x) = Q*B+R ∧
      (0 < B → R < B) := by
  induction i with
  | zero =>
    dsimp only [booleanWordDivPrefix,booleanWordDivStart]
    refine ⟨div_nz_zero_wire w w (Nat.le_refl w) x,?_,?_,?_⟩
    · simpa only [divNZ,boolean_word_lsb_value,booleanWordAdderRight] using!
        div_nz_value w w (Nat.le_refl w) x
    · simp [booleanWordHighValue,boolean_word_lsb_value,div_nz_zero_wire]
    · intro hb
      simpa [boolean_word_lsb_value,div_nz_zero_wire] using! hb
  | succ i ih =>
    have hi' : i < w := by omega
    let p := booleanWordDivPrefix w i (by omega)
    obtain ⟨hz,hn,hbalance,hsmall⟩ := ih (by omega)
    refine ⟨(div_round_old w i hi' p x p.zero).trans hz,
      (div_round_old w i hi' p x p.nonzero).trans hn,?_,?_⟩
    · change booleanWordHighValue w (i+1) hi (booleanWordAdderLeft w x) =
        booleanWordLSBValue (i+1) (divQ (booleanWordDivRound w i hi' p) x)*
          booleanWordLSBValue w (booleanWordAdderRight w x) +
          booleanWordLSBValue (w+i+1) (divR (w := w) (i := i+1) (booleanWordDivRound w i hi' p) x)
      change booleanWordHighValue w i (by omega) (booleanWordAdderLeft w x) =
        booleanWordLSBValue i (divQ p x)*booleanWordLSBValue w (booleanWordAdderRight w x) +
          booleanWordLSBValue (w+i) (divR p x) at hbalance
      rw [div_high_step w i hi',div_round_q_value w i hi' p x hz]
      dsimp only [booleanWordAdderLeft]
      have hs := div_round_balance w i hi' p x hz
      nlinarith only [hbalance,hs]
    · intro hb
      exact div_round_small w i hi' p x hz hb (hsmall hb)

private theorem div_prefix_nodes (w i : ℕ) (hi : i ≤ w) :
    (booleanWordDivPrefix w i hi).nodes ≤ 3*w+1+(20*w+2)*i := by
  induction i with
  | zero => simp [booleanWordDivPrefix,booleanWordDivStart]
  | succ i ih =>
    have hp := ih (by omega)
    change (booleanWordDivPrefix w i (by omega)).nodes +
      (7*(w+i+1)+1+3*(w+i+1)+1) ≤ _
    have hiw : i+1 ≤ w := hi
    nlinarith

theorem boolean_word_div_resources (w : ℕ) :
    let n := (booleanWordDivProgram w).nodes+w
    let gs := booleanDAGSteps (booleanWordDivDAG w) (booleanWordDivSelect w)
    n ≤ 20*w^2+6*w+1 ∧ reflectionLegal gs ∧
      gs.length ≤ 600*w^2+183*w+30 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      2*w+n+3*w ≤ 20*w^2+11*w+1 := by
  have hn : (booleanWordDivProgram w).nodes+w ≤ 20*w^2+6*w+1 := by
    have h := div_prefix_nodes w w (Nat.le_refl w)
    dsimp only [booleanWordDivProgram]
    nlinarith
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources (booleanWordDivDAG w) (booleanWordDivSelect w)
  exact ⟨hn,hl,by nlinarith,hq,hc,by nlinarith⟩

theorem boolean_word_div_basis (w : ℕ) (a b : Reg w) (y : Reg (3*w)) :
    let n := (booleanWordDivProgram w).nodes+w
    Run (1 : Matrix (Reg (2*w+n+3*w)) (Reg (2*w+n+3*w)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordDivDAG w) (booleanWordDivSelect w)))
      (Ket (booleanDAGInput (2*w) n (3*w) (booleanWordAdderInput w a b) y)) =
      Ket (booleanDAGInput (2*w) n (3*w) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordDivResult w a b j)) :=
  boolean_dag_basis _ _ _ _

private theorem div_input_views (w : ℕ) (x : Reg (2*w)) :
    booleanWordAdderInput w (booleanWordAdderLeft w x) (booleanWordAdderRight w x) = x := by
  funext j
  by_cases hj : j.val < w
  · simp [booleanWordAdderInput,booleanWordAdderLeft,hj]
  · have hle : w ≤ j.val := by omega
    simp [booleanWordAdderInput,booleanWordAdderRight,hj,Nat.add_sub_of_le hle]

theorem boolean_word_div_coherent (w : ℕ) (ψ : QState (Reg (2*w) × Reg (3*w))) :
    let n := (booleanWordDivProgram w).nodes+w
    Run (1 : Matrix (Reg (2*w+n+3*w)) (Reg (2*w+n+3*w)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordDivDAG w) (booleanWordDivSelect w)))
      (booleanDAGEmbed (2*w) n (3*w) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w) n (3*w) xy.1
        (fun j => xy.2 j ^^ booleanWordDivResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j)) := by
  (try dsimp only)
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordDivResult,div_input_views]
  rfl

private theorem div_and_prefix (w n : ℕ) (hn : n ≤ w) (x : Reg (w+1)) (j : Fin n) :
    booleanDAGValue (booleanWordAndPrefix w n hn) x ⟨w+1+j.val,by have := j.isLt; omega⟩ =
      (x ⟨j.val,by have := j.isLt; omega⟩ && x (Fin.last w)) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [booleanWordAndPrefix,div_snoc_value]
      rw [dif_neg (by change ¬w+1+n < w+1+n; omega)]
      change (booleanDAGValue (booleanWordAndPrefix w n (by omega)) x
          (⟨n,by omega⟩ : Fin (w+1+n)) &&
        booleanDAGValue (booleanWordAndPrefix w n (by omega)) x
          (⟨w,by omega⟩ : Fin (w+1+n))) = _
      exact congrArg₂ (fun a b : Bool => a && b)
        (div_input_value (booleanWordAndPrefix w n (by omega)) x ⟨n,by omega⟩)
        (div_input_value (booleanWordAndPrefix w n (by omega)) x (Fin.last w))
    · rw [booleanWordAndPrefix,div_snoc_value]
      have hk : w+1+k.val < w+1+n := by have := k.isLt; omega
      simp only [Fin.val_castSucc,dif_pos hk]
      exact ih (by omega) k

private def divMaskInputs (w : ℕ) : Fin (w+1) → Fin (2*w+(booleanWordDivProgram w).nodes) :=
  fun j => if hj : j.val < w then (booleanWordDivProgram w).quotient ⟨j.val,hj⟩
    else (booleanWordDivProgram w).nonzero

private theorem div_mask_bit (w : ℕ) (x : Reg (2*w)) (j : Fin w) :
    booleanDAGValue (booleanWordDivDAG w) x
      ⟨2*w+(booleanWordDivProgram w).nodes+j.val,by have := j.isLt; omega⟩ =
      (divQ (booleanWordDivProgram w) x j &&
        booleanDAGValue (booleanWordDivProgram w).graph x (booleanWordDivProgram w).nonzero) := by
  let p := booleanWordDivProgram w
  let r := divMaskInputs w
  let v : Fin (w+1+w) := ⟨w+1+j.val,by have := j.isLt; omega⟩
  have he : booleanSpliceSource (n := w) r v =
      (⟨2*w+p.nodes+j.val,by have := j.isLt; omega⟩ : Fin (2*w+(p.nodes+w))) := by
    have hnot : ¬v.val < w+1 := by dsimp [v]; omega
    rw [booleanSpliceSource,dif_neg hnot]
    apply Fin.ext
    dsimp only [v,p]
    omega
  have h := boolean_dag_splice_value p.graph r (booleanWordAndDAG w) x v
  rw [he] at h
  have ha : booleanDAGValue p.graph x (r (⟨j.val,by have := j.isLt; omega⟩ : Fin (w+1))) =
      divQ p x j := by
    simp [r,divMaskInputs,p,divQ,j.isLt]
  have hb : booleanDAGValue p.graph x (r (Fin.last w)) =
      booleanDAGValue p.graph x p.nonzero := by
    simp [r,divMaskInputs,p]
  calc
    _ = booleanDAGValue (booleanWordAndDAG w)
        (fun k => booleanDAGValue p.graph x (r k)) v := h
    _ = (booleanDAGValue p.graph x (r ⟨j.val,by have := j.isLt; omega⟩) &&
        booleanDAGValue p.graph x (r (Fin.last w))) :=
      div_and_prefix w w (Nat.le_refl w) _ j
    _ = _ := congrArg₂ (fun a b : Bool => a && b) ha hb

private theorem div_quotient_word (w : ℕ) (a b : Reg w) :
    booleanWordDivQuotient w a b = fun j =>
      divQ (booleanWordDivProgram w) (booleanWordAdderInput w a b) j &&
        booleanDAGValue (booleanWordDivProgram w).graph (booleanWordAdderInput w a b)
          (booleanWordDivProgram w).nonzero := by
  funext j
  simp only [booleanWordDivQuotient,booleanWordDivResult,booleanWordDivSelect,dif_pos j.isLt]
  exact div_mask_bit w (booleanWordAdderInput w a b) j

private theorem div_mask_value (w : ℕ) (a : Reg w) (bit : Bool) :
    booleanWordLSBValue w (fun j => a j && bit) =
      if bit then booleanWordLSBValue w a else 0 := by
  cases bit <;> simp [boolean_word_lsb_value]

private theorem div_quotient_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue w (booleanWordDivQuotient w a b) =
      if booleanDAGValue (booleanWordDivProgram w).graph (booleanWordAdderInput w a b)
          (booleanWordDivProgram w).nonzero then
        booleanWordLSBValue w (divQ (booleanWordDivProgram w) (booleanWordAdderInput w a b))
      else 0 := by
  rw [div_quotient_word,div_mask_value]

private theorem div_remainder_bit (w : ℕ) (a b : Reg w) (j : Fin (2*w)) :
    booleanWordDivRemainder w a b j =
      divR (booleanWordDivProgram w) (booleanWordAdderInput w a b)
        ⟨j.val,by have := j.isLt; omega⟩ := by
  have hnot : ¬w+j.val < w := by omega
  simp only [booleanWordDivRemainder,booleanWordDivResult,booleanWordDivSelect,
    dif_neg hnot,Nat.add_sub_cancel_left]
  exact boolean_dag_splice_prefix _ _ _ _ _

private theorem div_remainder_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (2*w) (booleanWordDivRemainder w a b) =
      booleanWordLSBValue (w+w)
        (divR (booleanWordDivProgram w) (booleanWordAdderInput w a b)) := by
  rw [boolean_word_lsb_value,boolean_word_lsb_value]
  apply Fintype.sum_equiv (finCongr (Nat.two_mul w))
  intro j
  simp only [div_remainder_bit,finCongr_apply,Fin.val_cast]
  rfl

private theorem div_left_input (w : ℕ) (a b : Reg w) :
    booleanWordAdderLeft w (booleanWordAdderInput w a b) = a := by
  funext j
  simp [booleanWordAdderLeft,booleanWordAdderInput,j.isLt]

private theorem div_right_input (w : ℕ) (a b : Reg w) :
    booleanWordAdderRight w (booleanWordAdderInput w a b) = b := by
  funext j
  have hnot : ¬w+j.val < w := by omega
  simp [booleanWordAdderRight,booleanWordAdderInput,hnot]

theorem boolean_word_div_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue w (booleanWordDivQuotient w a b) =
      booleanWordLSBValue w a / booleanWordLSBValue w b ∧
    booleanWordLSBValue (2*w) (booleanWordDivRemainder w a b) =
      booleanWordLSBValue w a % booleanWordLSBValue w b := by
  let p := booleanWordDivProgram w
  let x := booleanWordAdderInput w a b
  obtain ⟨_,hn,hbalance,hsmall⟩ := boolean_word_div_prefix w w (Nat.le_refl w) x
  simp only [x,div_left_input,div_right_input,div_high_full] at hn hbalance hsmall
  change booleanDAGValue p.graph x p.nonzero = decide (0 < booleanWordLSBValue w b) at hn
  change booleanWordLSBValue w a =
    booleanWordLSBValue w (divQ p x)*booleanWordLSBValue w b +
      booleanWordLSBValue (w+w) (divR p x) at hbalance
  change 0 < booleanWordLSBValue w b →
    booleanWordLSBValue (w+w) (divR p x) < booleanWordLSBValue w b at hsmall
  have hq := div_quotient_value w a b
  change booleanWordLSBValue w (booleanWordDivQuotient w a b) =
    if booleanDAGValue p.graph x p.nonzero then booleanWordLSBValue w (divQ p x) else 0 at hq
  rw [hn] at hq
  have hr := div_remainder_value w a b
  by_cases hb : booleanWordLSBValue w b = 0
  · simp only [hb,lt_self_iff_false,decide_false,Bool.false_eq_true,if_false] at hq
    have hR : booleanWordLSBValue w a = booleanWordLSBValue (w+w) (divR p x) := by
      simpa only [hb,mul_zero,zero_add] using! hbalance
    constructor
    · simpa only [hb,Nat.div_zero] using! hq
    · rw [hb,Nat.mod_zero,hr]
      exact hR.symm
  · have hpos : 0 < booleanWordLSBValue w b := Nat.pos_of_ne_zero hb
    have hlt := hsmall hpos
    have hdiv : booleanWordLSBValue w a / booleanWordLSBValue w b =
        booleanWordLSBValue w (divQ p x) :=
      Nat.div_eq_of_lt_le (by omega) (by nlinarith only [hbalance,hlt])
    have hmod : booleanWordLSBValue w a % booleanWordLSBValue w b =
        booleanWordLSBValue (w+w) (divR p x) := by
      rw [Nat.mod_eq_sub_mul_div,hdiv,hbalance,Nat.mul_comm
        (booleanWordLSBValue w (divQ p x)) (booleanWordLSBValue w b),Nat.add_sub_cancel_left]
    simp only [decide_eq_true hpos,if_true] at hq
    exact ⟨hq.trans hdiv.symm,hr.trans hmod.symm⟩

end Qatlib.Concepts.MatrixAccess.RitzPipeline
