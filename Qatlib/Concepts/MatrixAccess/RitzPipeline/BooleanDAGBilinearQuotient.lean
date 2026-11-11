/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGBilinearQuotientData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDot
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDivision

/-!
# Correctness of a signed bilinear quotient circuit

This module verifies `booleanWordBilinearQuotientProgram`, which evaluates a three-dimensional
integer bilinear form and divides its scaled value by a scaled square. It proves the signed-word
padding, shifting, dot-product, and multiplication identities needed to compose the Boolean
graph.

The resulting basis-state and coherent implementations use reversible computation as in
[NielsenChuang2010], with explicit node, gate, and register-size bounds.

## Main statements

* `boolean_word_bilinear_quotient_value`: identifies the result with the specified integer
  quotient.
* `boolean_word_bilinear_quotient_resources`: proves polynomial resource bounds and zero
  queries.
* `boolean_word_bilinear_quotient_coherent`: gives the coherent output XOR action.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Decodes a word with w magnitude bits and one sign bit as an integer. -/
private def bqDecode (w : ℕ) (a : Reg (w+1)) : ℤ :=
  booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w))

/-- The unsigned magnitude of a signed word shifted left by s positions is its original
magnitude multiplied by 2^s. -/
private theorem bq_shift_nat (w s : ℕ) (a : Reg (w+1)) :
    booleanWordLSBValue (w+s) (fun j => booleanSignedWordShift w s false a j.castSucc) =
      booleanWordLSBValue w (fun j => a j.castSucc) * 2^s := by
  rw [boolean_word_lsb_value]
  let f : Fin (s+w) → ℕ := fun j =>
    if hj : j.val < s then 0 else
      (if a (Fin.castSucc ⟨j.val-s,by have := j.isLt; omega⟩) then 1 else 0) * 2^j.val
  have hs : (∑ j : Fin (w+s),
      (if booleanSignedWordShift w s false a j.castSucc then 1 else 0) * 2^j.val) = ∑ j, f j := by
    apply Fintype.sum_equiv (finCongr (Nat.add_comm w s))
    intro j
    by_cases hj : j.val < s <;> simp [booleanSignedWordShift,f,finCongr_apply,hj,j.isLt]
  rw [hs,Fin.sum_univ_add]
  have hz : (∑ j : Fin s, f (Fin.castAdd w j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [f,j.isLt]
  rw [hz,zero_add,boolean_word_lsb_value,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hn : ¬s+j.val < s := by omega
  change (if hj : s+j.val < s then 0 else
    (if a (Fin.castSucc ⟨s+j.val-s,by have := j.isLt; omega⟩) then 1 else 0) * 2^(s+j.val)) = _
  rw [dif_neg hn]
  have he : (⟨s+j.val-s,by have := j.isLt; omega⟩ : Fin w) = j := by
    apply Fin.ext
    change s+j.val-s = j.val
    omega
  rw [he,pow_add]
  ring

/-- Shifting a signed word left by the specified number of positions multiplies its integer
value by the corresponding power of two. -/
theorem boolean_signed_word_shift_value (w shift : ℕ) (a : Reg (w+1)) :
    booleanWordSignedValue (w+shift)
      (fun j => booleanSignedWordShift w shift false a j.castSucc)
      (booleanSignedWordShift w shift false a (Fin.last (w+shift))) =
      (2 : ℤ)^shift * booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w)) := by
  have hs : booleanSignedWordShift w shift false a (Fin.last (w+shift)) = a (Fin.last w) := by
    have hn : ¬w+shift < shift := by omega
    simp [booleanSignedWordShift,hn]
  simp only [booleanWordSignedValue,hs,bq_shift_nat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  split_ifs <;> ring

/-- Padding a signed word to a larger magnitude width with false bits preserves its decoded
integer value. -/
private theorem bq_pad_to_value (w v : ℕ) (hw : w ≤ v) (a : Reg (w+1)) :
    bqDecode v (booleanSignedWordPadTo w v hw false a) = bqDecode w a := by
  rcases Nat.exists_eq_add_of_le hw with ⟨e,rfl⟩
  have he : booleanSignedWordPadTo w (w+e) (by omega) false a =
      booleanSignedWordPad w e false a := by
    funext j
    dsimp only [booleanSignedWordPadTo,booleanSignedWordPad]
    split_ifs <;> first | rfl | omega
  rw [he]
  exact boolean_signed_word_pad_value w e a

/-- Mapping signed-pair wire selections to Boolean values produces the standard signed
multiplication input layout. -/
private theorem bq_pair_map {α : Type*} (w : ℕ) (a b : Fin (w+1) → α) (f : α → Bool) :
    (fun j => f (booleanSignedPairSelect w a b j)) =
      booleanWordSignedMulInput w (fun j => f (a j.castSucc)) (fun j => f (b j.castSucc))
        (f (a (Fin.last w))) (f (b (Fin.last w))) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*w+1 < w := by omega
    simp [booleanSignedPairSelect,booleanWordSignedMulInput,hn]
  · rw [booleanWordSignedMulInput,Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun t => ?_) k
    · have hn : ¬2*w < w := by omega
      simp [booleanSignedPairSelect,hn]
    · rw [Fin.snoc_castSucc]
      by_cases ht : t.val < w
      · simp [booleanSignedPairSelect,booleanWordAdderInput,ht]
      · simp [booleanSignedPairSelect,booleanWordAdderInput,ht,t.isLt]

/-- The left magnitude view of a constructed signed multiplication input is the original left
word. -/
private theorem bq_pair_left (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedMulLeft w (booleanWordSignedMulInput w a b sa sb) = a := by
  unfold booleanWordSignedMulLeft
  simp only [booleanWordSignedMulInput,Fin.snoc_castSucc]
  funext j
  simp [booleanWordAdderLeft,booleanWordAdderInput,j.isLt]

/-- The right magnitude view of a constructed signed multiplication input is the original right
word. -/
private theorem bq_pair_right (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedMulRight w (booleanWordSignedMulInput w a b sa sb) = b := by
  unfold booleanWordSignedMulRight
  simp only [booleanWordSignedMulInput,Fin.snoc_castSucc]
  funext j
  have hn : ¬w+j.val < w := by omega
  simp [booleanWordAdderRight,booleanWordAdderInput,hn]

/-- Selecting the ith pair from the triple layout recovers the corresponding signed-pair
selection. -/
private theorem bq_triple_slot {α : Type*} (w : ℕ) (a b : Fin 3 → Fin (w+1) → α)
    (i : Fin 3) (j : Fin (2*w+2)) :
    booleanSignedTripleSelect w a b (booleanWordSignedDotPair w i j) = booleanSignedPairSelect w (a i) (b i) j := by
  fin_cases i
  all_goals
    have hj := j.isLt
    simp only [booleanSignedTripleSelect,booleanWordSignedDotPair,Fin.val_mk]
    split_ifs <;> first | omega | simp

/-- A selected output of an appended word program evaluates as that program on the selected
values of the preceding graph. -/
private theorem bq_append_value {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin o) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x ((booleanDAGAppendWord g r h).output j) =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) (h.output j) :=
  boolean_dag_splice_value _ _ _ _ _

/-- The designated zero wire of an appended word program evaluates as that program's zero wire
on the selected input values. -/
private theorem bq_append_zero {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (booleanDAGAppendWord g r h).zero =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) h.zero :=
  boolean_dag_splice_value _ _ _ _ _

/-- Appending a word program preserves the values at every existing graph coordinate. -/
private theorem bq_append_old {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin (M+K)) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (Fin.castLE (by dsimp [booleanDAGAppendWord]; omega) j) =
      booleanDAGValue g x j := boolean_dag_splice_prefix _ _ _ _ _

/-- Appending the signed dot-product program produces a designated zero wire whose value is
false. -/
private theorem bq_dot_zero {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (r : Fin (3*(2*w+2)) → Fin (M+K)) (x : Reg M) :
    booleanDAGValue (booleanDAGAppendWord g r (booleanWordSignedDotProgram w)).graph x
      (booleanDAGAppendWord g r (booleanWordSignedDotProgram w)).zero = false := by
  rw [bq_append_zero]
  exact boolean_word_signed_dot_zero _ _

/-- The decoded output of an appended signed dot-product program equals the sum of the three
products of the selected signed values. -/
private theorem bq_dot_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin 3 → Fin (w+1) → Fin (M+K)) (x : Reg M) :
    let p :=
        booleanDAGAppendWord g (booleanSignedTripleSelect w a b) (booleanWordSignedDotProgram w)
    bqDecode (2*w+2) (fun j => booleanDAGValue p.graph x (p.output j)) =
      ∑ i : Fin 3, bqDecode w (fun j => booleanDAGValue g x (a i j)) *
        bqDecode w (fun j => booleanDAGValue g x (b i j)) := by
  (try dsimp only)
  have he : (fun j => booleanDAGValue
      (booleanDAGAppendWord g (booleanSignedTripleSelect w a b) (booleanWordSignedDotProgram w)).graph x
      ((booleanDAGAppendWord g (booleanSignedTripleSelect w a b) (booleanWordSignedDotProgram w)).output j)) =
      booleanWordSignedDotResult w (fun t => booleanDAGValue g x (booleanSignedTripleSelect w a b t)) := by
    funext j
    exact bq_append_value _ _ _ _ _
  rw [he]
  change booleanWordSignedDotValue w _ = _
  rw [boolean_word_signed_dot_value]
  apply Finset.sum_congr rfl
  intro i _
  have hv : booleanWordSignedDotView w (fun t => booleanDAGValue g x (booleanSignedTripleSelect w a b t)) i =
      booleanWordSignedMulInput w (fun j => booleanDAGValue g x (a i j.castSucc))
        (fun j => booleanDAGValue g x (b i j.castSucc))
        (booleanDAGValue g x (a i (Fin.last w))) (booleanDAGValue g x (b i (Fin.last w))) := by
    funext j
    change booleanDAGValue g x
        (booleanSignedTripleSelect w a b (booleanWordSignedDotPair w i j)) = _
    rw [bq_triple_slot]
    exact congrFun (bq_pair_map w (a i) (b i) (booleanDAGValue g x)) j
  rw [hv]
  (try dsimp only)
  rw [bq_pair_left,bq_pair_right]
  simp only [booleanWordSignedMulInput,Fin.snoc_castSucc,Fin.snoc_last]
  rfl

/-- Evaluation of a Boolean graph preserves every original input coordinate. -/
private theorem bq_input_value {m n : ℕ} (g : BooleanDAG m n) (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m n) j)) = x j
    simpa only [booleanDAGValue,Fin.lastCases_castSucc] using! ih

/-- A raw bilinear input wire evaluates to the corresponding original input bit, regardless of
the graph appended to it. -/
private theorem bq_raw_value {w n : ℕ} (g : BooleanDAG (16*(w+1)) n)
    (x : Reg (16*(w+1))) (slot : Fin 16) (j : Fin (w+1)) :
    booleanDAGValue g x (booleanWordBilinearRaw w n slot j) =
      x (booleanWordBilinearRaw w 0 slot j) :=
  bq_input_value g x (booleanWordBilinearRaw w 0 slot j)

/-- The total input width 16(w+1) of the bilinear quotient construction. -/
private abbrev bqM (w : ℕ) := 16*(w+1)
/-- The magnitude width 2w + 2 used for the three column dot products. -/
private abbrev bqQ (w : ℕ) := 2*w+2
/-- The signed three-term dot-product program at magnitude width w. -/
private abbrev bqDot (w : ℕ) := booleanWordSignedDotProgram w
/-- The first graph stage, computing the dot product for matrix column zero. -/
private abbrev bqP0 (w : ℕ) := booleanDAGAppendWord (.nil : BooleanDAG (bqM w) 0)
  (booleanWordBilinearColumnInput w 0 0) (bqDot w)
/-- The graph stage obtained by appending the dot product for matrix column one. -/
private abbrev bqP1 (w : ℕ) := booleanDAGAppendWord (bqP0 w).graph
  (booleanWordBilinearColumnInput w (bqP0 w).nodes 1) (bqDot w)
/-- The graph stage obtained by appending the dot product for matrix column two. -/
private abbrev bqP2 (w : ℕ) := booleanDAGAppendWord (bqP1 w).graph
  (booleanWordBilinearColumnInput w (bqP1 w).nodes 2) (bqDot w)
/-- The combined program computing all three matrix-column dot products. -/
private abbrev bqCols (w : ℕ) := booleanWordBilinearColumns w
/-- Selects the signed words representing the three computed column dot products. -/
private abbrev bqLeft (w : ℕ) : Fin 3 → Fin (bqQ w+1) → Fin (bqM w+(bqCols w).nodes) := fun i j =>
  (bqCols w).output ⟨i.val*(2*w+3)+j.val,by have hi := i.isLt; have hj := j.isLt; dsimp only [bqQ] at hj; nlinarith⟩
/-- Selects the three right-vector input words, padded to the column-result width. -/
private abbrev bqRight (w : ℕ) : Fin 3 → Fin (bqQ w+1) → Fin (bqM w+(bqCols w).nodes) := fun i =>
  booleanSignedWordPadTo w (bqQ w) (by dsimp only [bqQ]; omega) (bqCols w).zero
    (booleanWordBilinearRaw w (bqCols w).nodes ⟨12+i.val,by have := i.isLt; omega⟩)
/-- The Boolean word program evaluating the bilinear form. -/
private abbrev bqBil (w : ℕ) := booleanWordBilinearProgram w
/-- Selects the signed input word in slot 15 after the bilinear program. -/
private abbrev bqRawK (w : ℕ) := booleanWordBilinearRaw w (bqBil w).nodes 15
/-- Appends signed multiplication of the slot-15 input word by itself to the bilinear program. -/
private abbrev bqSquare (w : ℕ) := booleanDAGAppendWord (bqBil w).graph
  (booleanSignedPairSelect w (bqRawK w) (bqRawK w)) (booleanWordSignedMulProgram w)
/-- Selects the earlier bilinear-result wires within the graph extended by the squaring program. -/
private abbrev bqBilS (w : ℕ) : Fin (2*bqQ w+3) → Fin (bqM w+(bqSquare w).nodes) := fun j =>
  Fin.castLE (by change bqM w+(bqBil w).nodes ≤ bqM w+((bqBil w).nodes+(booleanWordSignedMulProgram w).nodes); omega)
    ((bqBil w).output j)
/-- The common magnitude width used to prepare the quotient numerator and denominator. -/
private abbrev bqV (w b d : ℕ) := booleanWordBilinearQuotientWidth w b d
/-- Selects the bilinear result shifted left by b positions and padded to the quotient magnitude
width. -/
private abbrev bqNum (w b d : ℕ) : Fin (bqV w b d+1) → Fin (bqM w+(bqSquare w).nodes) :=
  booleanSignedWordPadTo (2*bqQ w+2+b) (bqV w b d)
    (by dsimp only [bqQ,bqV,booleanWordBilinearQuotientWidth]; omega) (bqSquare w).zero
    (booleanSignedWordShift (2*bqQ w+2) b (bqSquare w).zero (bqBilS w))
/-- Selects the squared slot-15 value shifted left by d positions and padded to the quotient
magnitude width. -/
private abbrev bqDen (w b d : ℕ) : Fin (bqV w b d+1) → Fin (bqM w+(bqSquare w).nodes) :=
  booleanSignedWordPadTo (2*w+d) (bqV w b d)
    (by dsimp only [bqV,booleanWordBilinearQuotientWidth]; omega) (bqSquare w).zero
    (booleanSignedWordShift (2*w) d (bqSquare w).zero (bqSquare w).output)
/-- Selects the numerator magnitude, denominator magnitude, and numerator sign for the signed
division program. -/
private abbrev bqDivInputs (w b d : ℕ) : Fin (2*bqV w b d+1) → Fin (bqM w+(bqSquare w).nodes) := fun j =>
  if hj : j.val < bqV w b d then bqNum w b d (Fin.castSucc ⟨j.val,hj⟩)
  else if hk : j.val < 2*bqV w b d then bqDen w b d (Fin.castSucc ⟨j.val-bqV w b d,by omega⟩)
  else bqNum w b d (Fin.last (bqV w b d))
/-- The graph obtained by appending signed division to the bilinear and squaring stages. -/
private abbrev bqFinal (w b d : ℕ) := booleanDAGAppendWord (bqSquare w).graph
  (bqDivInputs w b d) (booleanWordSignedDivProgram (bqV w b d))

/-- The integer dot product of the left vector with the specified matrix column. -/
private def bqColumn (w : ℕ) (x : Reg (bqM w)) (j : Fin 3) : ℤ :=
  ∑ i : Fin 3, booleanWordBilinearInputValue w x ⟨i.val,by have := i.isLt; omega⟩ *
    booleanWordBilinearInputValue w x (booleanWordBilinearMatrixSlot i j)

/-- The decoded output of the first column program equals the integer dot product for column
zero. -/
private theorem bq_col0_value (w : ℕ) (x : Reg (bqM w)) :
    bqDecode (bqQ w) (fun j => booleanDAGValue (bqP0 w).graph x ((bqP0 w).output j)) = bqColumn w x 0 := by
  have h := bq_dot_value (.nil : BooleanDAG (bqM w) 0) w
    (fun i => booleanWordBilinearRaw w 0 ⟨i.val,by have := i.isLt; omega⟩)
    (fun i => booleanWordBilinearRaw w 0 (booleanWordBilinearMatrixSlot i 0)) x
  simpa only [bqDecode,bq_raw_value,booleanWordBilinearInputValue] using! h

/-- The decoded output of the second column program equals the integer dot product for column
one. -/
private theorem bq_col1_value (w : ℕ) (x : Reg (bqM w)) :
    bqDecode (bqQ w) (fun j => booleanDAGValue (bqP1 w).graph x ((bqP1 w).output j)) = bqColumn w x 1 := by
  have h := bq_dot_value (bqP0 w).graph w
    (fun i => booleanWordBilinearRaw w (bqP0 w).nodes ⟨i.val,by have := i.isLt; omega⟩)
    (fun i => booleanWordBilinearRaw w (bqP0 w).nodes (booleanWordBilinearMatrixSlot i 1)) x
  simpa only [bqDecode,bq_raw_value,booleanWordBilinearInputValue] using! h

/-- The decoded output of the third column program equals the integer dot product for column
two. -/
private theorem bq_col2_value (w : ℕ) (x : Reg (bqM w)) :
    bqDecode (bqQ w) (fun j => booleanDAGValue (bqP2 w).graph x ((bqP2 w).output j)) = bqColumn w x 2 := by
  have h := bq_dot_value (bqP1 w).graph w
    (fun i => booleanWordBilinearRaw w (bqP1 w).nodes ⟨i.val,by have := i.isLt; omega⟩)
    (fun i => booleanWordBilinearRaw w (bqP1 w).nodes (booleanWordBilinearMatrixSlot i 2)) x
  simpa only [bqDecode,bq_raw_value,booleanWordBilinearInputValue] using! h

/-- Within the combined column program, the selected column-zero word equals the original
first-stage output word. -/
private theorem bq_col0_word (w : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqCols w).graph x (bqLeft w 0 j)) =
      (fun j => booleanDAGValue (bqP0 w).graph x ((bqP0 w).output j)) := by
  funext j
  simp only [bqLeft,bqCols,booleanWordBilinearColumns,Fin.val_zero,zero_mul,zero_add,dif_pos j.isLt]
  exact (bq_append_old (bqP1 w).graph (booleanWordBilinearColumnInput w (bqP1 w).nodes 2) (bqDot w) x
    (Fin.castLE (by change bqM w+(bqP0 w).nodes ≤ bqM w+((bqP0 w).nodes+(bqDot w).nodes); omega)
      ((bqP0 w).output j))).trans
      (bq_append_old (bqP0 w).graph (booleanWordBilinearColumnInput w (bqP0 w).nodes 1) (bqDot w) x ((bqP0 w).output j))

/-- Within the combined column program, the selected column-one word equals the original
second-stage output word. -/
private theorem bq_col1_word (w : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqCols w).graph x (bqLeft w 1 j)) =
      (fun j => booleanDAGValue (bqP1 w).graph x ((bqP1 w).output j)) := by
  funext j
  have hn : ¬2*w+3+j.val < 2*w+3 := by omega
  have hp : 2*w+3+j.val < 2*(2*w+3) := by have := j.isLt; dsimp only [bqQ] at this; omega
  simp only [bqLeft,bqCols,booleanWordBilinearColumns,Fin.val_one,one_mul,dif_neg hn,dif_pos hp,
    Nat.add_sub_cancel_left]
  exact bq_append_old (bqP1 w).graph (booleanWordBilinearColumnInput w (bqP1 w).nodes 2)
      (bqDot w) x ((bqP1 w).output j)

/-- Within the combined column program, the selected column-two word equals the original
third-stage output word. -/
private theorem bq_col2_word (w : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqCols w).graph x (bqLeft w 2 j)) =
      (fun j => booleanDAGValue (bqP2 w).graph x ((bqP2 w).output j)) := by
  funext j
  have hn : ¬2*(2*w+3)+j.val < 2*w+3 := by omega
  have hp : ¬2*(2*w+3)+j.val < 2*(2*w+3) := by omega
  simp only [bqLeft,bqCols,booleanWordBilinearColumns]
  change booleanDAGValue (bqP2 w).graph x
    (if h : 2*(2*w+3)+j.val < 2*w+3 then _ else
      if h' : 2*(2*w+3)+j.val < 2*(2*w+3) then _ else _) = _
  simp only [dif_neg hn,dif_neg hp]
  norm_num

/-- Each selected column word in the combined program decodes to its corresponding integer
column dot product. -/
private theorem bq_column_value (w : ℕ) (x : Reg (bqM w)) (i : Fin 3) :
    bqDecode (bqQ w) (fun j => booleanDAGValue (bqCols w).graph x (bqLeft w i j)) = bqColumn w x i := by
  fin_cases i
  · exact (congrArg (bqDecode (bqQ w)) (bq_col0_word w x)).trans (bq_col0_value w x)
  · exact (congrArg (bqDecode (bqQ w)) (bq_col1_word w x)).trans (bq_col1_value w x)
  · exact (congrArg (bqDecode (bqQ w)) (bq_col2_word w x)).trans (bq_col2_value w x)

/-- The designated zero wire of the combined column program evaluates to false. -/
private theorem bq_cols_zero (w : ℕ) (x : Reg (bqM w)) :
    booleanDAGValue (bqCols w).graph x (bqCols w).zero = false :=
  bq_dot_zero _ _ _ _

/-- Evaluating wire selections commutes with signed-word padding when the padding wire evaluates
to false. -/
private theorem bq_pad_map {α : Type*} (w v : ℕ) (hw : w ≤ v) (z : α)
    (a : Fin (w+1) → α) (f : α → Bool) (hz : f z = false) :
    (fun j => f (booleanSignedWordPadTo w v hw z a j)) =
      booleanSignedWordPadTo w v hw false (fun j => f (a j)) := by
  funext j
  dsimp only [booleanSignedWordPadTo,booleanSignedWordPad]
  split_ifs <;> first | rfl | exact hz

/-- Evaluating wire selections commutes with signed-word shifting when the inserted zero wire
evaluates to false. -/
private theorem bq_shift_map {α : Type*} (w s : ℕ) (z : α)
    (a : Fin (w+1) → α) (f : α → Bool) (hz : f z = false) :
    (fun j => f (booleanSignedWordShift w s z a j)) =
      booleanSignedWordShift w s false (fun j => f (a j)) := by
  funext j
  dsimp only [booleanSignedWordShift]
  split_ifs <;> first | rfl | exact hz

/-- Each padded right-vector word decodes to the signed input value in slot 12+i. -/
private theorem bq_right_value (w : ℕ) (x : Reg (bqM w)) (i : Fin 3) :
    bqDecode (bqQ w) (fun j => booleanDAGValue (bqCols w).graph x (bqRight w i j)) =
      booleanWordBilinearInputValue w x ⟨12+i.val,by have := i.isLt; omega⟩ := by
  rw [bq_pad_map _ _ _ _ _ _ (bq_cols_zero w x),bq_pad_to_value]
  simp only [bqDecode,bq_raw_value,booleanWordBilinearInputValue]

/-- The signed output of the bilinear program decodes to `booleanWordBilinearForm`. -/
private theorem bq_bilinear_value (w : ℕ) (x : Reg (bqM w)) :
    bqDecode (2*bqQ w+2) (fun j => booleanDAGValue (bqBil w).graph x ((bqBil w).output j)) =
      booleanWordBilinearForm w x := by
  have h := bq_dot_value (bqCols w).graph (bqQ w) (bqLeft w) (bqRight w) x
  (try dsimp only at h)
  simpa only [bq_column_value,bq_right_value,bqColumn,booleanWordBilinearForm] using! h

/-- An appended signed multiplication program has a false zero wire, decodes to the product of
its selected inputs, and has output sign equal to the XOR of their signs. -/
private theorem bq_mul_semantics {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin (w+1) → Fin (M+K)) (x : Reg M) :
    let p := booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedMulProgram w)
    booleanDAGValue p.graph x p.zero = false ∧
      bqDecode (2*w) (fun j => booleanDAGValue p.graph x (p.output j)) =
        bqDecode w (fun j => booleanDAGValue g x (a j)) * bqDecode w (fun j => booleanDAGValue g x (b j)) ∧
      booleanDAGValue p.graph x (p.output (Fin.last (2*w))) =
        (booleanDAGValue g x (a (Fin.last w)) ^^ booleanDAGValue g x (b (Fin.last w))) := by
  (try dsimp only)
  have he : (fun j => booleanDAGValue
      (booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedMulProgram w)).graph x
      ((booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedMulProgram w)).output j)) =
      booleanWordSignedMulResult w (fun j => booleanDAGValue g x (a j.castSucc))
        (fun j => booleanDAGValue g x (b j.castSucc))
        (booleanDAGValue g x (a (Fin.last w))) (booleanDAGValue g x (b (Fin.last w))) := by
    funext j
    rw [bq_append_value,bq_pair_map]
    rfl
  refine ⟨?_,?_,?_⟩
  · rw [bq_append_zero,bq_pair_map]
    exact (boolean_word_signed_mul_magnitude _ _ _ _ _).1
  · rw [he]
    exact boolean_word_signed_mul_value _ _ _ _ _
  · change (fun j => booleanDAGValue
      (booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedMulProgram w)).graph x
      ((booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedMulProgram w)).output j))
        (Fin.last (2*w)) = _
    rw [he]
    exact (boolean_word_signed_mul_magnitude _ _ _ _ _).2.1

/-- The appended squaring program has a false zero wire and false output sign, and its output
decodes to the square of the signed input in slot 15. -/
private theorem bq_square_semantics (w : ℕ) (x : Reg (bqM w)) :
    booleanDAGValue (bqSquare w).graph x (bqSquare w).zero = false ∧
      bqDecode (2*w) (fun j => booleanDAGValue (bqSquare w).graph x ((bqSquare w).output j)) =
        booleanWordBilinearInputValue w x 15 * booleanWordBilinearInputValue w x 15 ∧
      booleanDAGValue (bqSquare w).graph x ((bqSquare w).output (Fin.last (2*w))) = false := by
  have h := bq_mul_semantics (bqBil w).graph w (bqRawK w) (bqRawK w) x
  simpa only [bqRawK,bqDecode,bq_raw_value,booleanWordBilinearInputValue,Bool.xor_self] using! h

/-- The bilinear-result wires retain their values after appending the squaring program. -/
private theorem bq_bil_square_word (w : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqSquare w).graph x (bqBilS w j)) =
      (fun j => booleanDAGValue (bqBil w).graph x ((bqBil w).output j)) := by
  funext j
  exact bq_append_old (bqBil w).graph (booleanSignedPairSelect w (bqRawK w) (bqRawK w))
    (booleanWordSignedMulProgram w) x ((bqBil w).output j)

/-- The selected numerator word equals the bilinear output shifted by b positions and padded
with false bits to the common width. -/
private theorem bq_num_word (w b d : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqSquare w).graph x (bqNum w b d j)) =
      booleanSignedWordPadTo (2*bqQ w+2+b) (bqV w b d)
        (by dsimp only [bqQ,bqV,booleanWordBilinearQuotientWidth]; omega) false
        (booleanSignedWordShift (2*bqQ w+2) b false
          (fun j => booleanDAGValue (bqBil w).graph x ((bqBil w).output j))) := by
  rw [bq_pad_map _ _ _ _ _ _ (bq_square_semantics w x).1,
    bq_shift_map _ _ _ _ _ (bq_square_semantics w x).1,bq_bil_square_word]

/-- The selected denominator word equals the square output shifted by d positions and padded
with false bits to the common width. -/
private theorem bq_den_word (w b d : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j)) =
      booleanSignedWordPadTo (2*w+d) (bqV w b d)
        (by dsimp only [bqV,booleanWordBilinearQuotientWidth]; omega) false
        (booleanSignedWordShift (2*w) d false
          (fun j => booleanDAGValue (bqSquare w).graph x ((bqSquare w).output j))) := by
  rw [bq_pad_map _ _ _ _ _ _ (bq_square_semantics w x).1,
    bq_shift_map _ _ _ _ _ (bq_square_semantics w x).1]

/-- The prepared numerator decodes to 2^b times the integer bilinear form. -/
private theorem bq_num_value (w b d : ℕ) (x : Reg (bqM w)) :
    bqDecode (bqV w b d) (fun j => booleanDAGValue (bqSquare w).graph x (bqNum w b d j)) =
      (2 : ℤ)^b*booleanWordBilinearForm w x := by
  rw [bq_num_word,bq_pad_to_value]
  have h := boolean_signed_word_shift_value (2*bqQ w+2) b
    (fun j => booleanDAGValue (bqBil w).graph x ((bqBil w).output j))
  exact h.trans (congrArg (fun z : ℤ => (2 : ℤ)^b*z) (bq_bilinear_value w x))

/-- The prepared denominator decodes to 2^d times the square of the signed input in slot 15. -/
private theorem bq_den_value (w b d : ℕ) (x : Reg (bqM w)) :
    bqDecode (bqV w b d) (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j)) =
      (2 : ℤ)^d*(booleanWordBilinearInputValue w x 15*booleanWordBilinearInputValue w x 15) := by
  rw [bq_den_word,bq_pad_to_value]
  have h := boolean_signed_word_shift_value (2*w) d
    (fun j => booleanDAGValue (bqSquare w).graph x ((bqSquare w).output j))
  exact h.trans (congrArg (fun z : ℤ => (2 : ℤ)^d*z) (bq_square_semantics w x).2.1)

/-- Padding a signed word preserves its final sign entry. -/
private theorem bq_pad_sign {α : Type*} (w v : ℕ) (hw : w ≤ v) (z : α)
    (a : Fin (w+1) → α) :
    booleanSignedWordPadTo w v hw z a (Fin.last v) = a (Fin.last w) := by
  dsimp only [booleanSignedWordPadTo,booleanSignedWordPad]
  simp only [Fin.val_last]
  split_ifs <;> first | rfl | omega

/-- Shifting a signed word preserves its final sign entry. -/
private theorem bq_shift_sign {α : Type*} (w s : ℕ) (z : α) (a : Fin (w+1) → α) :
    booleanSignedWordShift w s z a (Fin.last (w+s)) = a (Fin.last w) := by
  dsimp only [booleanSignedWordShift]
  simp only [Fin.val_last]
  split_ifs <;> first | rfl | omega

/-- The prepared denominator has a false sign bit. -/
private theorem bq_den_sign (w b d : ℕ) (x : Reg (bqM w)) :
    booleanDAGValue (bqSquare w).graph x (bqDen w b d (Fin.last (bqV w b d))) = false := by
  change (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j)) (Fin.last (bqV w b d)) = _
  rw [bq_den_word,bq_pad_sign,bq_shift_sign]
  exact (bq_square_semantics w x).2.2

/-- The selected division wires evaluate to the standard input layout for the prepared
numerator, denominator, and numerator sign. -/
private theorem bq_div_inputs (w b d : ℕ) (x : Reg (bqM w)) :
    (fun j => booleanDAGValue (bqSquare w).graph x (bqDivInputs w b d j)) =
      booleanWordSignedDivInput (bqV w b d)
        (fun j => booleanDAGValue (bqSquare w).graph x (bqNum w b d j.castSucc))
        (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j.castSucc))
        (booleanDAGValue (bqSquare w).graph x (bqNum w b d (Fin.last (bqV w b d)))) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*bqV w b d < bqV w b d := by omega
    simp only [bqDivInputs,Fin.val_last,dif_neg hn,dif_neg (Nat.lt_irrefl _),
      booleanWordSignedDivInput,Fin.snoc_last]
  · rw [booleanWordSignedDivInput,Fin.snoc_castSucc]
    by_cases hk : k.val < bqV w b d
    · simp only [bqDivInputs,Fin.val_castSucc,booleanWordAdderInput,dif_pos hk]
    · simp only [bqDivInputs,Fin.val_castSucc,booleanWordAdderInput,dif_neg hk,dif_pos k.isLt]

/-- The bilinear quotient output word equals the signed division result for the prepared
numerator and denominator. -/
private theorem bq_result_word (w b d : ℕ) (x : Reg (bqM w)) :
    booleanWordBilinearQuotientResult w b d x =
      booleanWordSignedDivResult (bqV w b d)
        (fun j => booleanDAGValue (bqSquare w).graph x (bqNum w b d j.castSucc))
        (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j.castSucc))
        (booleanDAGValue (bqSquare w).graph x (bqNum w b d (Fin.last (bqV w b d)))) := by
  funext j
  change booleanDAGValue (bqFinal w b d).graph x ((bqFinal w b d).output j) = _
  rw [bq_append_value,bq_div_inputs]
  rfl

/-- The designated zero wire of the complete bilinear quotient program evaluates to false. -/
theorem boolean_word_bilinear_quotient_zero (w b d : ℕ) (x : Reg (16*(w+1))) :
    let p := booleanWordBilinearQuotientProgram w b d
    booleanDAGValue p.graph x p.zero = false := by
  exact (bq_append_old (bqSquare w).graph (bqDivInputs w b d)
    (booleanWordSignedDivProgram (bqV w b d)) x (bqSquare w).zero).trans (bq_square_semantics w x).1

/-- The decoded result equals the integer quotient of 2^b times the bilinear form by 2^d times
the square of the slot-15 input value. -/
theorem boolean_word_bilinear_quotient_value (w b d : ℕ) (x : Reg (16*(w+1))) :
    let K := booleanWordBilinearInputValue w x 15
    booleanWordBilinearQuotientValue w b d x =
      ((2 : ℤ)^b*booleanWordBilinearForm w x) / ((2 : ℤ)^d*(K*K)) := by
  (try dsimp only)
  dsimp only [booleanWordBilinearQuotientValue]
  rw [bq_result_word]
  change booleanWordSignedDivValue (bqV w b d) _ _ _ = _
  rw [boolean_word_signed_div_value]
  change bqDecode (bqV w b d) (fun j => booleanDAGValue (bqSquare w).graph x (bqNum w b d j)) /
    (booleanWordLSBValue (bqV w b d)
      (fun j => booleanDAGValue (bqSquare w).graph x (bqDen w b d j.castSucc)) : ℤ) = _
  rw [bq_num_value]
  have hd := bq_den_value w b d x
  dsimp only [bqDecode,booleanWordSignedValue] at hd
  simp only [bq_den_sign,Bool.false_eq_true,ite_false] at hd
  rw [hd]

/-- The bilinear quotient program and its legal local compilation satisfy explicit quadratic
bounds on nodes, gates, and total register width, with no queries and gate count equal to
list length. -/
theorem boolean_word_bilinear_quotient_resources (w b d : ℕ) :
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordBilinearQuotientProgram w b d
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 20*V^2+17*V+242*w^2+900*w+642 ∧ reflectionLegal gs ∧
      gs.length ≤ 600*V^2+511*V+7260*w^2+27000*w+19263 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      16*(w+1)+p.nodes+(V+3) ≤ 20*V^2+18*V+242*w^2+916*w+661 := by
  let V := booleanWordBilinearQuotientWidth w b d
  let p := booleanWordBilinearQuotientProgram w b d
  have h0 := (boolean_word_signed_dot_resources w).1
  have h1 := (boolean_word_signed_dot_resources (2*w+2)).1
  have hs := (boolean_word_signed_mul_resources w).1
  have hd := (boolean_word_signed_div_resources V).1
  have hn : p.nodes ≤ 20*V^2+17*V+242*w^2+900*w+642 := by
    change 0+(booleanWordSignedDotProgram w).nodes+(booleanWordSignedDotProgram w).nodes+
      (booleanWordSignedDotProgram w).nodes+(booleanWordSignedDotProgram (2*w+2)).nodes+
      (booleanWordSignedMulProgram w).nodes+(booleanWordSignedDivProgram V).nodes ≤ _
    nlinarith
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,?_,hq,hc,?_⟩
  · change (booleanDAGSteps p.graph p.output).length ≤ _
    nlinarith
  · change 16*(w+1)+p.nodes+(V+3) ≤ 20*V^2+18*V+242*w^2+916*w+661
    omega

/-- The compiled bilinear quotient program XORs its result into a basis output register,
preserves the input, and restores the work bits to false. -/
theorem boolean_word_bilinear_quotient_basis (w b d : ℕ) (x : Reg (16*(w+1)))
    (y : Reg (booleanWordBilinearQuotientWidth w b d+3)) :
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordBilinearQuotientProgram w b d
    Run (1 : Matrix (Reg (16*(w+1)+p.nodes+(V+3))) (Reg (16*(w+1)+p.nodes+(V+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput (16*(w+1)) p.nodes (V+3) x y)) =
      Ket (booleanDAGInput (16*(w+1)) p.nodes (V+3) x
        (fun j => y j ^^ booleanWordBilinearQuotientResult w b d x j)) :=
  boolean_dag_basis _ _ _ _

/-- The compiled bilinear quotient program coherently XORs its result into the output of any
embedded input-output state while restoring the work bits. -/
theorem boolean_word_bilinear_quotient_coherent (w b d : ℕ)
    (ψ : QState (Reg (16*(w+1)) × Reg (booleanWordBilinearQuotientWidth w b d+3))) :
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordBilinearQuotientProgram w b d
    Run (1 : Matrix (Reg (16*(w+1)+p.nodes+(V+3))) (Reg (16*(w+1)+p.nodes+(V+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed (16*(w+1)) p.nodes (V+3) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (16*(w+1)) p.nodes (V+3) xy.1
        (fun j => xy.2 j ^^ booleanWordBilinearQuotientResult w b d xy.1 j)) :=
  boolean_dag_coherent _ _ _

/-- Packing sixteen signed words and then selecting a raw slot bit recovers the corresponding
original bit. -/
private theorem bq_input_slot (w : ℕ) (a : Fin 16 → Reg (w+1)) (slot : Fin 16) (j : Fin (w+1)) :
    booleanWordBilinearInput w a (booleanWordBilinearRaw w 0 slot j) = a slot j := by
  have hd : (slot.val*(w+1)+j.val)/(w+1) = slot.val := by
    rw [Nat.add_comm (slot.val*(w+1)) j.val,Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt j.isLt,zero_add]
  have hm : (slot.val*(w+1)+j.val)%(w+1) = j.val := by
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  dsimp only [booleanWordBilinearInput,booleanWordBilinearRaw,Fin.val_mk]
  simp only [hd,hm]

/-- Decoding a slot of the packed bilinear input gives the signed value of the word packed into
that slot. -/
theorem boolean_word_bilinear_input_decode (w : ℕ) (a : Fin 16 → Reg (w+1)) (slot : Fin 16) :
    booleanWordBilinearInputValue w (booleanWordBilinearInput w a) slot =
      booleanWordSignedValue w (fun j => a slot j.castSucc) (a slot (Fin.last w)) := by
  simp only [booleanWordBilinearInputValue,bq_input_slot]

end Qatlib.Concepts.MatrixAccess.RitzPipeline
