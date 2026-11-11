/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGConditionalSubtractData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdder

/-!
# Correctness of reversible conditional subtraction

This module proves that `booleanWordCondSubResult` subtracts the second unsigned word from the
first when the comparison permits it, and otherwise retains the first word. The final output bit
records whether subtraction occurred.

Borrow invariants establish the arithmetic result, and the local implementation follows the
reversible computation setting of [NielsenChuang2010], with clean workspace and a linear gate
bound.

## Main statements

* `boolean_word_cond_sub_value`: proves the comparison flag and conditional difference.
* `boolean_word_cond_sub_step`: gives a one-bit quotient and remainder when 0 < b and a < 2b.
* `boolean_word_cond_sub_resources`: gives the gate bound and total register width.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Converts a Boolean bit to the natural number zero or one. -/
private def subBit (b : Bool) : ℕ := if b then 1 else 0

/-- The minuend bit plus twice the outgoing borrow equals the subtrahend bit plus the incoming
borrow and the difference bit. -/
private theorem sub_bit_balance (a b c : Bool) :
    subBit a+2*subBit (((!a) && b) ^^ ((!(a ^^ b)) && c)) =
      subBit b+subBit c+subBit ((a ^^ b) ^^ c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Appending a Boolean node preserves earlier graph values and evaluates the new node at the
last coordinate. -/
private theorem sub_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Extending a subtraction prefix by one stage preserves every earlier coordinate value. -/
private theorem sub_prefix_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(7*i+1)) :
    booleanDAGValue (booleanWordSubPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordSubPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordSubPrefix,Nat.mul_succ,Nat.add_assoc,
    sub_snoc_value,hj]
  split_ifs <;> first | rfl | omega

/-- Every original input coordinate retains its value in a subtraction prefix. -/
private theorem sub_prefix_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w) :
    booleanDAGValue (booleanWordSubPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ := by
  induction i with
  | zero => simp (disch := omega) [booleanWordSubPrefix,sub_snoc_value,booleanDAGValue,hj]
  | succ i ih =>
    rw [sub_prefix_old w i hi x j (by omega)]
    exact ih (by omega)

/-- The borrow bit after the first i stages of the subtraction graph. -/
private def subBorrow (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) : Bool :=
  booleanDAGValue (booleanWordSubPrefix w i hi) x ⟨2*w+7*i,by omega⟩

/-- The specified difference bit among the first i stages of the subtraction graph. -/
private def subDiff (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) (j : Fin i) : Bool :=
  booleanDAGValue (booleanWordSubPrefix w i hi) x ⟨2*w+7*j.val+2,by omega⟩

/-- The initial subtraction borrow bit is false. -/
private theorem sub_carry_zero (w : ℕ) (x : Reg (2*w)) : subBorrow w 0 (by omega) x = false := by
  simp [subBorrow,booleanWordSubPrefix,sub_snoc_value,booleanNodeValue]

/-- Extending a subtraction prefix preserves the previously computed difference bits. -/
private theorem sub_sum_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) (j : Fin i) :
    subDiff w (i+1) hi x j.castSucc = subDiff w i (by omega) x j := by
  have hj := j.isLt
  simpa only [subDiff,Fin.val_castSucc] using!
    sub_prefix_old w i hi x (2*w+7*j.val+2) (by omega)

/-- The next difference bit is the XOR of the two input bits and the incoming borrow. -/
private theorem sub_sum_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    subDiff w (i+1) hi x (Fin.last i) =
      ((x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩) ^^ subBorrow w i (by omega) x) := by
  simp (disch := omega) [subDiff,subBorrow,booleanWordSubPrefix,Nat.mul_succ,
    Nat.add_assoc,sub_snoc_value,booleanNodeValue,sub_prefix_input]

/-- The next borrow is the XOR of the negated-minuend conjunction with the subtrahend and the
equality-of-input-bits conjunction with the incoming borrow. -/
private theorem sub_carry_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    subBorrow w (i+1) hi x =
      (((!x ⟨i,by omega⟩) && x ⟨w+i,by omega⟩) ^^
        ((!(x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩)) && subBorrow w i (by omega) x)) := by
  simp (disch := omega) [subBorrow,booleanWordSubPrefix,Nat.mul_succ,Nat.add_assoc,
    sub_snoc_value,booleanNodeValue,sub_prefix_input]
  split_ifs <;> first | rfl | omega

/-- Across the first i positions, the minuend value plus the outgoing borrow weighted by 2^i
equals the subtrahend value plus the computed difference value. -/
private theorem sub_partial_balance (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    (∑ j : Fin i, subBit (x ⟨j.val,by have := j.isLt; omega⟩)*2^j.val) +
      subBit (subBorrow w i hi x)*2^i =
    (∑ j : Fin i, subBit (x ⟨w+j.val,by have := j.isLt; omega⟩)*2^j.val) +
      (∑ j : Fin i, subBit (subDiff w i hi x j)*2^j.val) := by
  induction i with
  | zero => simp [sub_carry_zero,subBit]
  | succ i ih =>
    have hp : i ≤ w := by omega
    have hprev := ih hp
    have hbit := sub_bit_balance (x ⟨i,by omega⟩) (x ⟨w+i,by omega⟩)
      (subBorrow w i hp x)
    have hweighted := congrArg (fun z : ℕ => z*2^i) hbit
    simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,
      sub_sum_old,pow_succ]
    rw [sub_sum_new,sub_carry_new]
    (try dsimp only at hweighted)
    nlinarith only [hprev,hweighted]

/-- The first half of the combined word input recovers each bit of the left word. -/
private theorem sub_input_left (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨i.val,by have := i.isLt; omega⟩ = a i := by
  simp [booleanWordAdderInput,i.isLt]

/-- The second half of the combined word input recovers each bit of the right word. -/
private theorem sub_input_right (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨w+i.val,by have := i.isLt; omega⟩ = b i := by
  have hn : ¬w+i.val < w := by omega
  simp [booleanWordAdderInput,hn]

/-- The full-word minuend plus the final borrow weighted by 2^w equals the subtrahend plus the
w-bit difference value. -/
private theorem sub_full_balance (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue w a +
      subBit (subBorrow w w (Nat.le_refl w) (booleanWordAdderInput w a b))*2^w =
    booleanWordLSBValue w b +
      booleanWordLSBValue w (subDiff w w (Nat.le_refl w) (booleanWordAdderInput w a b)) := by
  have h := sub_partial_balance w w (Nat.le_refl w) (booleanWordAdderInput w a b)
  simpa only [sub_input_left,sub_input_right,boolean_word_lsb_value,subBit] using! h

/-- Extending the conditional-selection prefix preserves all previously available graph values. -/
private theorem cond_extend_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(7*w+1+3*i)) :
    booleanDAGValue (booleanWordCondSubPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordCondSubPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordCondSubPrefix,Nat.mul_succ,Nat.add_assoc,
    sub_snoc_value]
  split_ifs <;> first | rfl | omega

/-- Every conditional-selection prefix preserves the values of the completed subtraction graph. -/
private theorem cond_prefix_base (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(7*w+1)) :
    booleanDAGValue (booleanWordCondSubPrefix w i hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordSubPrefix w w (Nat.le_refl w)) x ⟨j,hj⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [cond_extend_old w i hi x j (by omega)]
    exact ih (by omega)

/-- Each selected conditional-result bit is the original minuend bit if the final borrow is true
and the difference bit otherwise. -/
private theorem cond_prefix_bit (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) (j : Fin i) :
    booleanDAGValue (booleanWordCondSubPrefix w i hi) x
      ⟨2*w+(7*w+1+3*j.val)+2,by have := j.isLt; omega⟩ =
      if subBorrow w w (Nat.le_refl w) x then x ⟨j.val,by have := j.isLt; omega⟩
      else subDiff w w (Nat.le_refl w) x ⟨j.val,by have := j.isLt; omega⟩ := by
  induction i with
  | zero => exact Fin.elim0 j
  | succ i ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp (disch := omega) [booleanWordCondSubPrefix,Nat.mul_succ,Nat.add_assoc,
        sub_snoc_value,booleanNodeValue,cond_prefix_base,sub_prefix_input]
      split_ifs <;> try omega
      all_goals
        change (subDiff w w (Nat.le_refl w) x ⟨i,by omega⟩ ^^
          ((x ⟨i,by omega⟩ ^^ subDiff w w (Nat.le_refl w) x ⟨i,by omega⟩) &&
            subBorrow w w (Nat.le_refl w) x)) = _
        cases hc : subBorrow w w (Nat.le_refl w) x <;>
          cases ha : x ⟨i,by omega⟩ <;>
          cases hd : subDiff w w (Nat.le_refl w) x ⟨i,by omega⟩ <;> simp_all
    · rw [cond_extend_old w i hi x _ (by have := k.isLt; simp only [Fin.val_castSucc]; omega)]
      exact ih (by omega) k

/-- Each low output bit of conditional subtraction chooses the minuend on borrow and the
computed difference otherwise. -/
private theorem cond_result_bit (w : ℕ) (a b : Reg w) (j : Fin w) :
    booleanWordCondSubResult w a b j.castSucc =
      if subBorrow w w (Nat.le_refl w) (booleanWordAdderInput w a b) then a j
      else subDiff w w (Nat.le_refl w) (booleanWordAdderInput w a b) j := by
  simp only [booleanWordCondSubResult,booleanWordCondSubSelect,Fin.val_castSucc,dif_pos j.isLt]
  have hj : 2*w+(7*w+1+3*j.val)+2 < 2*w+(7*w+1+3*w) := by
    have := j.isLt
    omega
  rw [booleanWordCondSubDAG,sub_snoc_value,dif_pos hj]
  simpa only [sub_input_left] using! cond_prefix_bit w w (Nat.le_refl w)
    (booleanWordAdderInput w a b) j

/-- The final output flag of conditional subtraction is the negation of the final borrow bit. -/
private theorem cond_result_flag (w : ℕ) (a b : Reg w) :
    booleanWordCondSubResult w a b (Fin.last w) =
      !(subBorrow w w (Nat.le_refl w) (booleanWordAdderInput w a b)) := by
  simp (disch := omega) [booleanWordCondSubResult,booleanWordCondSubSelect,
    booleanWordCondSubDAG,sub_snoc_value,booleanNodeValue,cond_prefix_base,subBorrow]
  intro h
  omega

/-- The output flag tests whether b ≤ a, and the low output word represents a - b when this
holds and a otherwise. -/
theorem boolean_word_cond_sub_value (w : ℕ) (a b : Reg w) :
    let r := booleanWordCondSubResult w a b
    r (Fin.last w) = decide (booleanWordLSBValue w b ≤ booleanWordLSBValue w a) ∧
      booleanWordLSBValue w (fun j => r j.castSucc) =
        if booleanWordLSBValue w b ≤ booleanWordLSBValue w a then
          booleanWordLSBValue w a - booleanWordLSBValue w b
        else booleanWordLSBValue w a := by
  have hbal := sub_full_balance w a b
  have hlt : booleanWordLSBValue w
      (subDiff w w (Nat.le_refl w) (booleanWordAdderInput w a b)) < 2^w :=
    (bitVecEquiv w (fun j => subDiff w w (Nat.le_refl w)
      (booleanWordAdderInput w a b) (Fin.rev j))).isLt
  cases hc : subBorrow w w (Nat.le_refl w) (booleanWordAdderInput w a b) with
  | false =>
    simp only [hc,subBit,Bool.false_eq_true,if_false,zero_mul,add_zero] at hbal
    have hle : booleanWordLSBValue w b ≤ booleanWordLSBValue w a := by omega
    have hr : (fun j => booleanWordCondSubResult w a b j.castSucc) =
        subDiff w w (Nat.le_refl w) (booleanWordAdderInput w a b) := by
      funext j
      simpa only [hc,Bool.false_eq_true,if_false] using! cond_result_bit w a b j
    (try dsimp only)
    constructor
    · simp [cond_result_flag,hc,hle]
    · rw [hr,if_pos hle]
      omega
  | true =>
    simp only [hc,subBit,if_true,one_mul] at hbal
    have hnot : ¬booleanWordLSBValue w b ≤ booleanWordLSBValue w a := by omega
    have hr : (fun j => booleanWordCondSubResult w a b j.castSucc) = a := by
      funext j
      simpa only [hc,if_true] using! cond_result_bit w a b j
    (try dsimp only)
    constructor
    · simp [cond_result_flag,hc,hnot]
    · rw [hr,if_neg hnot]

/-- If 0 < b and a < 2b in unsigned value, conditional subtraction yields a remainder below b
and reconstructs a as the flag times b plus that remainder. -/
theorem boolean_word_cond_sub_step (w : ℕ) (a b : Reg w)
    (hb : 0 < booleanWordLSBValue w b)
    (ha : booleanWordLSBValue w a < 2*booleanWordLSBValue w b) :
    let r := booleanWordCondSubResult w a b
    booleanWordLSBValue w (fun j => r j.castSucc) < booleanWordLSBValue w b ∧
      booleanWordLSBValue w a =
        (if r (Fin.last w) then 1 else 0)*booleanWordLSBValue w b +
          booleanWordLSBValue w (fun j => r j.castSucc) := by
  obtain ⟨hf,hv⟩ := boolean_word_cond_sub_value w a b
  (try dsimp only at hf hv ⊢)
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  rw [hn] at ha hf hv ⊢
  rw [hf,hv]
  by_cases h : n+1 ≤ booleanWordLSBValue w a
  · simp [h]
    omega
  · simp [h]
    omega

/-- The conditional-subtraction compilation is legal, has at most 301w + 61 gates and no
queries, and uses 13w + 3 register bits, with gate count equal to list length. -/
theorem boolean_word_cond_sub_resources (w : ℕ) :
    let gs := booleanDAGSteps (booleanWordCondSubDAG w) (booleanWordCondSubSelect w)
    reflectionLegal gs ∧ gs.length ≤ 301*w+61 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      2*w+(7*w+1+3*w+1)+(w+1) = 13*w+3 := by
  obtain ⟨hl,hn,hq,hg⟩ := boolean_dag_resources
    (booleanWordCondSubDAG w) (booleanWordCondSubSelect w)
  exact ⟨hl,by omega,hq,hg,by omega⟩

/-- The compiled conditional subtraction XORs its result and flag into a basis output register,
preserving the inputs and restoring clean work bits. -/
theorem boolean_word_cond_sub_basis (w : ℕ) (a b : Reg w) (y : Reg (w+1)) :
    Run (1 : Matrix (Reg (2*w+(7*w+1+3*w+1)+(w+1)))
      (Reg (2*w+(7*w+1+3*w+1)+(w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordCondSubDAG w) (booleanWordCondSubSelect w)))
      (Ket (booleanDAGInput (2*w) (7*w+1+3*w+1) (w+1) (booleanWordAdderInput w a b) y)) =
      Ket (booleanDAGInput (2*w) (7*w+1+3*w+1) (w+1) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordCondSubResult w a b j)) := boolean_dag_basis _ _ _ _

/-- The compiled conditional subtraction coherently XORs its result and flag into the output of
an arbitrary embedded input-output state, restoring clean work bits. -/
theorem boolean_word_cond_sub_coherent (w : ℕ) (ψ : QState (Reg (2*w) × Reg (w+1))) :
    Run (1 : Matrix (Reg (2*w+(7*w+1+3*w+1)+(w+1)))
      (Reg (2*w+(7*w+1+3*w+1)+(w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordCondSubDAG w) (booleanWordCondSubSelect w)))
      (booleanDAGEmbed (2*w) (7*w+1+3*w+1) (w+1) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w) (7*w+1+3*w+1) (w+1) xy.1
        (fun j => xy.2 j ^^ booleanWordCondSubResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j)) := by
  have hx (x : Reg (2*w)) : booleanWordAdderInput w
      (booleanWordAdderLeft w x) (booleanWordAdderRight w x) = x := by
    funext j
    by_cases hj : j.val < w
    · simp [booleanWordAdderInput,booleanWordAdderLeft,hj]
    · have hle : w ≤ j.val := by omega
      simp [booleanWordAdderInput,booleanWordAdderRight,hj,Nat.add_sub_of_le hle]
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordCondSubResult,hx]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
