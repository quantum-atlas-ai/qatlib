/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDotData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAddition

/-!
# Three-term signed dot products by Boolean DAGs

`boolean_word_signed_dot_value` verifies a three-term dot product formed from three signed
multiplications and two signed additions. Padding inserts zero magnitude bits while preserving
each sign and integer value.

The module proves the distinguished zero-wire property, polynomial resource bounds, and the
compiled circuit action on basis states and arbitrary embedded states. The circuit background is
described in [NielsenChuang2010].

## Main statements

* `boolean_signed_word_pad_value`: value preservation under magnitude padding.
* `boolean_word_signed_dot_value`: sum of the three signed products.
* `boolean_word_signed_dot_resources`: polynomial circuit bounds.
* `boolean_word_signed_dot_basis`, `boolean_word_signed_dot_coherent`: circuit action.

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
set_option autoImplicit false

/-- Decode a word whose last bit is a negative flag and whose preceding bits form a
little-endian magnitude. -/
private def dotDecode (w : ℕ) (a : Reg (w+1)) : ℤ :=
  booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w))

/-- Padding the magnitude of a sign-magnitude word with false high bits preserves its decoded
integer value. -/
theorem boolean_signed_word_pad_value (w extra : ℕ) (a : Reg (w+1)) :
    booleanWordSignedValue (w+extra)
      (fun j => booleanSignedWordPad w extra false a j.castSucc)
      (booleanSignedWordPad w extra false a (Fin.last (w+extra))) =
      booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w)) := by
  have hs : booleanSignedWordPad w extra false a (Fin.last (w+extra)) = a (Fin.last w) := by
    simp (disch := omega) [booleanSignedWordPad]
  have hm : booleanWordLSBValue (w+extra)
      (fun j => booleanSignedWordPad w extra false a j.castSucc) =
      booleanWordLSBValue w (fun j => a j.castSucc) := by
    rw [boolean_word_lsb_value,Fin.sum_univ_add,boolean_word_lsb_value]
    have hhead (j : Fin w) :
        booleanSignedWordPad w extra false a ((Fin.castAdd extra j).castSucc) = a j.castSucc := by
      simp [booleanSignedWordPad,j.isLt]
    have htail (j : Fin extra) :
        booleanSignedWordPad w extra false a ((Fin.natAdd w j).castSucc) = false := by
      simp (disch := omega) [booleanSignedWordPad]
    simp only [hhead,htail,Bool.false_eq_true,ite_false,Fin.val_castAdd,zero_mul,Finset.sum_const_zero,add_zero]
  simp only [booleanWordSignedValue,hs,hm]

/-- Applying a Boolean-valued map to a signed-pair source layout gives the corresponding packed
signed-multiplication input. -/
private theorem dot_pair_map {α : Type*} (w : ℕ) (a b : Fin (w+1) → α) (f : α → Bool) :
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

/-- Each output of an appended word graph evaluates as that graph on the values supplied by its
source map. -/
private theorem dot_append_value {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin o) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x ((booleanDAGAppendWord g r h).output j) =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) (h.output j) :=
  boolean_dag_splice_value _ _ _ _ _

/-- The distinguished wire of an appended word graph evaluates as its distinguished wire on the
values supplied by the source map. -/
private theorem dot_append_zero {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (booleanDAGAppendWord g r h).zero =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) h.zero :=
  boolean_dag_splice_value _ _ _ _ _

/-- Appending a word-valued graph preserves all pre-existing wire values. -/
private theorem dot_append_old {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin (M+K)) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (Fin.castLE (by dsimp [booleanDAGAppendWord]; omega) j) =
      booleanDAGValue g x j := boolean_dag_splice_prefix _ _ _ _ _

/-- Appending a signed adder to two selected signed words produces the corresponding
signed-addition result word. -/
private theorem dot_add_word {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin (w+1) → Fin (M+K)) (x : Reg M) :
    let p := booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedAddProgram w)
    (fun j => booleanDAGValue p.graph x (p.output j)) =
      booleanWordSignedAddResult w (fun j => booleanDAGValue g x (a j.castSucc))
        (fun j => booleanDAGValue g x (b j.castSucc))
        (booleanDAGValue g x (a (Fin.last w))) (booleanDAGValue g x (b (Fin.last w))) := by
  funext j
  rw [dot_append_value,dot_pair_map]
  rfl

/-- The decoded output of an appended signed adder is the sum of the decoded selected operand
words. -/
private theorem dot_add_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin (w+1) → Fin (M+K)) (x : Reg M) :
    let p := booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedAddProgram w)
    dotDecode (w+1) (fun j => booleanDAGValue p.graph x (p.output j)) =
      dotDecode w (fun j => booleanDAGValue g x (a j)) +
        dotDecode w (fun j => booleanDAGValue g x (b j)) := by
  (try dsimp only)
  rw [dot_add_word]
  exact boolean_word_signed_add_value _ _ _ _ _

/-- The distinguished zero wire of an appended signed adder evaluates to false. -/
private theorem dot_add_zero {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin (w+1) → Fin (M+K)) (x : Reg M) :
    let p := booleanDAGAppendWord g (booleanSignedPairSelect w a b) (booleanWordSignedAddProgram w)
    booleanDAGValue p.graph x p.zero = false := by
  (try dsimp only)
  rw [dot_append_zero,dot_pair_map]
  exact (boolean_word_signed_add_magnitude _ _ _ _ _).1

/-- Packing the two magnitude views and two sign bits reconstructs the original
signed-multiplication input. -/
private theorem dot_input_views (w : ℕ) (x : Reg (2*w+2)) :
    booleanWordSignedMulInput w (booleanWordSignedMulLeft w x) (booleanWordSignedMulRight w x)
      (x ((Fin.last (2*w)).castSucc)) (x (Fin.last (2*w+1))) = x := by
  have hraw : booleanWordAdderInput w (booleanWordAdderLeft w (fun j => x j.castSucc.castSucc))
      (booleanWordAdderRight w (fun j => x j.castSucc.castSucc)) = fun j => x j.castSucc.castSucc := by
    funext j
    by_cases hj : j.val < w
    · simp [booleanWordAdderInput,booleanWordAdderLeft,hj]
    · have hle : w ≤ j.val := by omega
      simp [booleanWordAdderInput,booleanWordAdderRight,hj,Nat.add_sub_of_le hle]
  dsimp only [booleanWordSignedMulInput,booleanWordSignedMulLeft,booleanWordSignedMulRight]
  rw [hraw]
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]

/-- The decoded output of an appended signed multiplier equals the product of the two signed
values supplied by its source map. -/
private theorem dot_mul_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (r : Fin (2*w+2) → Fin (M+K)) (x : Reg M) :
    let p := booleanDAGAppendWord g r (booleanWordSignedMulProgram w)
    let v := fun t => booleanDAGValue g x (r t)
    dotDecode (2*w) (fun j => booleanDAGValue p.graph x (p.output j)) =
      booleanWordSignedValue w (booleanWordSignedMulLeft w v) (v ((Fin.last (2*w)).castSucc)) *
        booleanWordSignedValue w (booleanWordSignedMulRight w v) (v (Fin.last (2*w+1))) := by
  (try dsimp only)
  have he : (fun j => booleanDAGValue (booleanDAGAppendWord g r (booleanWordSignedMulProgram w)).graph x
      ((booleanDAGAppendWord g r (booleanWordSignedMulProgram w)).output j)) =
      booleanWordSignedMulResult w
        (booleanWordSignedMulLeft w (fun t => booleanDAGValue g x (r t)))
        (booleanWordSignedMulRight w (fun t => booleanDAGValue g x (r t)))
        (booleanDAGValue g x (r ((Fin.last (2*w)).castSucc)))
        (booleanDAGValue g x (r (Fin.last (2*w+1)))) := by
    funext j
    rw [dot_append_value]
    simp only [booleanWordSignedMulResult,dot_input_views]
  rw [he]
  exact boolean_word_signed_mul_value _ _ _ _ _

/-- Every original input wire retains its value in a Boolean graph. -/
private theorem dot_raw_value {m n : ℕ} (g : BooleanDAG m n) (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m n) j)) = x j
    simpa only [booleanDAGValue,Fin.lastCases_castSucc] using! ih

/-- The input width for three pairs of width `w` magnitudes and their sign bits. -/
private abbrev dotM (w : ℕ) := 3*(2*w+2)
/-- The signed-multiplication program used for each term of the dot product. -/
private abbrev dotMul (w : ℕ) := booleanWordSignedMulProgram w
/-- Select one of the three raw signed operand-pair blocks in a graph with `K` nodes. -/
private abbrev dotRaw (w : ℕ) (K : ℕ) (i : Fin 3) : Fin (2*w+2) → Fin (dotM w+K) :=
  fun j => Fin.castLE (by dsimp only [dotM]; omega) (booleanWordSignedDotPair w i j)
/-- Append the signed multiplier for the first dot-product term to the empty graph. -/
private abbrev dotP0 (w : ℕ) :=
    booleanDAGAppendWord (.nil : BooleanDAG (dotM w) 0) (dotRaw w 0 0) (dotMul w)
/-- Append the signed multiplier for the second dot-product term after the first multiplier. -/
private abbrev dotP1 (w : ℕ) :=
    booleanDAGAppendWord (dotP0 w).graph (dotRaw w (dotP0 w).nodes 1) (dotMul w)
/-- Append the signed multiplier for the third dot-product term after the first two multipliers. -/
private abbrev dotP2 (w : ℕ) :=
    booleanDAGAppendWord (dotP1 w).graph (dotRaw w (dotP1 w).nodes 2) (dotMul w)
/-- Select the first signed product word in the graph after all three multipliers. -/
private abbrev dotFirst (w : ℕ) : Fin (2*w+1) → Fin (dotM w+(dotP2 w).nodes) := fun j =>
  Fin.castLE (by change dotM w+(dotP0 w).nodes ≤ dotM w+((dotP0 w).nodes+(dotMul w).nodes+(dotMul w).nodes); omega)
    ((dotP0 w).output j)
/-- Select the second signed product word in the graph after all three multipliers. -/
private abbrev dotSecond (w : ℕ) : Fin (2*w+1) → Fin (dotM w+(dotP2 w).nodes) := fun j =>
  Fin.castLE (by change dotM w+(dotP1 w).nodes ≤ dotM w+((dotP1 w).nodes+(dotMul w).nodes); omega)
    ((dotP1 w).output j)
/-- Append a signed adder to sum the first two product words. -/
private abbrev dotSum (w : ℕ) := booleanDAGAppendWord (dotP2 w).graph
  (booleanSignedPairSelect (2*w) (dotFirst w) (dotSecond w)) (booleanWordSignedAddProgram (2*w))
/-- Select the third product word in the graph after the first signed addition. -/
private abbrev dotThird (w : ℕ) : Fin (2*w+1) → Fin (dotM w+(dotSum w).nodes) := fun j =>
  Fin.castLE (by change dotM w+(dotP2 w).nodes ≤ dotM w+((dotP2 w).nodes+(booleanWordSignedAddProgram (2*w)).nodes); omega)
    ((dotP2 w).output j)
/-- Pad the third product magnitude by one zero bit, preserving its sign, to match the first
partial sum's width. -/
private abbrev dotPadThird (w : ℕ) := booleanSignedWordPad (2*w) 1 (dotSum w).zero (dotThird w)
/-- Append the final signed adder to combine the first partial sum with the padded third
product. -/
private abbrev dotFinal (w : ℕ) := booleanDAGAppendWord (dotSum w).graph
  (booleanSignedPairSelect (2*w+1) (dotSum w).output (dotPadThird w)) (booleanWordSignedAddProgram (2*w+1))

/-- The integer product of the two signed operands in input block `i` of the three-term dot
product. -/
private def dotTerm (w : ℕ) (x : Reg (dotM w)) (i : Fin 3) : ℤ :=
  let v := booleanWordSignedDotView w x i
  booleanWordSignedValue w (booleanWordSignedMulLeft w v) (v ((Fin.last (2*w)).castSucc)) *
    booleanWordSignedValue w (booleanWordSignedMulRight w v) (v (Fin.last (2*w+1)))

/-- The decoded first multiplier output equals the first signed dot-product term. -/
private theorem dot_product0 (w : ℕ) (x : Reg (dotM w)) :
    dotDecode (2*w) (fun j => booleanDAGValue (dotP0 w).graph x ((dotP0 w).output j)) = dotTerm w x 0 := by
  have h := dot_mul_value (.nil : BooleanDAG (dotM w) 0) w (dotRaw w 0 0) x
  (try dsimp only at h)
  simp only [dotRaw,dot_raw_value] at h
  exact h

/-- The decoded second multiplier output equals the second signed dot-product term. -/
private theorem dot_product1 (w : ℕ) (x : Reg (dotM w)) :
    dotDecode (2*w) (fun j => booleanDAGValue (dotP1 w).graph x ((dotP1 w).output j)) = dotTerm w x 1 := by
  have h := dot_mul_value (dotP0 w).graph w (dotRaw w (dotP0 w).nodes 1) x
  (try dsimp only at h)
  simp only [dotRaw,dot_raw_value] at h
  exact h

/-- The decoded third multiplier output equals the third signed dot-product term. -/
private theorem dot_product2 (w : ℕ) (x : Reg (dotM w)) :
    dotDecode (2*w) (fun j => booleanDAGValue (dotP2 w).graph x ((dotP2 w).output j)) = dotTerm w x 2 := by
  have h := dot_mul_value (dotP1 w).graph w (dotRaw w (dotP1 w).nodes 2) x
  (try dsimp only at h)
  simp only [dotRaw,dot_raw_value] at h
  exact h

/-- The first product word retains its evaluated bits after appending the second and third
multipliers. -/
private theorem dot_first_word (w : ℕ) (x : Reg (dotM w)) :
    (fun j => booleanDAGValue (dotP2 w).graph x (dotFirst w j)) =
      (fun j => booleanDAGValue (dotP0 w).graph x ((dotP0 w).output j)) := by
  funext j
  exact (dot_append_old (dotP1 w).graph (dotRaw w (dotP1 w).nodes 2) (dotMul w) x
    (Fin.castLE (by change dotM w+(dotP0 w).nodes ≤ dotM w+((dotP0 w).nodes+(dotMul w).nodes); omega)
      ((dotP0 w).output j))).trans
      (dot_append_old (dotP0 w).graph (dotRaw w (dotP0 w).nodes 1) (dotMul w) x ((dotP0 w).output j))

/-- The second product word retains its evaluated bits after appending the third multiplier. -/
private theorem dot_second_word (w : ℕ) (x : Reg (dotM w)) :
    (fun j => booleanDAGValue (dotP2 w).graph x (dotSecond w j)) =
      (fun j => booleanDAGValue (dotP1 w).graph x ((dotP1 w).output j)) := by
  funext j
  exact dot_append_old (dotP1 w).graph (dotRaw w (dotP1 w).nodes 2) (dotMul w) x
      ((dotP1 w).output j)

/-- The third product word retains its evaluated bits after appending the first signed adder. -/
private theorem dot_third_word (w : ℕ) (x : Reg (dotM w)) :
    (fun j => booleanDAGValue (dotSum w).graph x (dotThird w j)) =
      (fun j => booleanDAGValue (dotP2 w).graph x ((dotP2 w).output j)) := by
  funext j
  exact dot_append_old (dotP2 w).graph (booleanSignedPairSelect (2*w) (dotFirst w) (dotSecond w))
    (booleanWordSignedAddProgram (2*w)) x ((dotP2 w).output j)

/-- The distinguished zero wire of the first partial-sum graph evaluates to false. -/
private theorem dot_sum_zero (w : ℕ) (x : Reg (dotM w)) :
    booleanDAGValue (dotSum w).graph x (dotSum w).zero = false := dot_add_zero _ _ _ _ _

/-- The decoded first partial sum equals the sum of the first two signed dot-product terms. -/
private theorem dot_sum_value (w : ℕ) (x : Reg (dotM w)) :
    dotDecode (2*w+1) (fun j => booleanDAGValue (dotSum w).graph x ((dotSum w).output j)) =
      dotTerm w x 0+dotTerm w x 1 := by
  rw [dot_add_value,dot_first_word,dot_second_word,dot_product0,dot_product1]

/-- The padded third product word decodes to the third signed dot-product term. -/
private theorem dot_pad_third_value (w : ℕ) (x : Reg (dotM w)) :
    dotDecode (2*w+1) (fun j => booleanDAGValue (dotSum w).graph x (dotPadThird w j)) = dotTerm w x 2 := by
  have he : (fun j => booleanDAGValue (dotSum w).graph x (dotPadThird w j)) =
      booleanSignedWordPad (2*w) 1 false (fun j => booleanDAGValue (dotSum w).graph x (dotThird w j)) := by
    funext j
    dsimp only [dotPadThird,booleanSignedWordPad]
    split_ifs <;> first | rfl | exact dot_sum_zero w x
  rw [he]
  have h :=
      boolean_signed_word_pad_value (2*w) 1
      (fun j => booleanDAGValue (dotSum w).graph x (dotThird w j))
  exact h.trans ((congrArg (dotDecode (2*w)) (dot_third_word w x)).trans (dot_product2 w x))

/-- The distinguished zero wire of the complete three-term signed dot-product graph evaluates to
false. -/
theorem boolean_word_signed_dot_zero (w : ℕ) (x : Reg (3*(2*w+2))) :
    let p := booleanWordSignedDotProgram w
    booleanDAGValue p.graph x p.zero = false := dot_add_zero _ _ _ _ _

/-- The decoded signed dot-product output equals the sum of the three products of the signed
input operand pairs. -/
theorem boolean_word_signed_dot_value (w : ℕ) (x : Reg (3*(2*w+2))) :
    booleanWordSignedDotValue w x =
      ∑ i : Fin 3,
        let v := booleanWordSignedDotView w x i
        booleanWordSignedValue w (booleanWordSignedMulLeft w v) (v ((Fin.last (2*w)).castSucc)) *
          booleanWordSignedValue w (booleanWordSignedMulRight w v) (v (Fin.last (2*w+1))) := by
  change dotDecode ((2*w+1)+1) (fun j => booleanDAGValue (dotFinal w).graph x ((dotFinal w).output j)) =
    ∑ i : Fin 3, dotTerm w x i
  rw [dot_add_value,dot_sum_value,dot_pad_third_value,Fin.sum_univ_three]

/-- The three-term signed dot-product circuit is legal with at most `33*w^2+127*w+61` nodes,
`990*w^2+3812*w+1833` compiled gates, and `33*w^2+135*w+70` total wires. It uses zero oracle
queries, and its gate count equals its reflection-step count. -/
theorem boolean_word_signed_dot_resources (w : ℕ) :
    let p := booleanWordSignedDotProgram w
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 33*w^2+127*w+61 ∧ reflectionLegal gs ∧
      gs.length ≤ 990*w^2+3812*w+1833 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      3*(2*w+2)+p.nodes+(2*w+3) ≤ 33*w^2+135*w+70 := by
  let p := booleanWordSignedDotProgram w
  have hm := (boolean_word_signed_mul_resources w).1
  have ha := (boolean_word_signed_add_resources (2*w)).1
  have hb := (boolean_word_signed_add_resources (2*w+1)).1
  have hn : p.nodes ≤ 33*w^2+127*w+61 := by
    change 0+(booleanWordSignedMulProgram w).nodes+(booleanWordSignedMulProgram w).nodes+
      (booleanWordSignedMulProgram w).nodes+(booleanWordSignedAddProgram (2*w)).nodes+
      (booleanWordSignedAddProgram (2*w+1)).nodes ≤ _
    nlinarith
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,?_,hq,hc,?_⟩
  · change (booleanDAGSteps p.graph p.output).length ≤ _
    nlinarith
  · change 3*(2*w+2)+p.nodes+(2*w+3) ≤ _
    omega

/-- On a basis state with initialized workspace, the compiled signed dot-product circuit XORs
its result into the target and restores the workspace. -/
theorem boolean_word_signed_dot_basis (w : ℕ) (x : Reg (3*(2*w+2))) (y : Reg (2*w+3)) :
    let p := booleanWordSignedDotProgram w
    Run (1 : Matrix (Reg (3*(2*w+2)+p.nodes+(2*w+3))) (Reg (3*(2*w+2)+p.nodes+(2*w+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput (3*(2*w+2)) p.nodes (2*w+3) x y)) =
      Ket (booleanDAGInput (3*(2*w+2)) p.nodes (2*w+3) x
        (fun j => y j ^^ booleanWordSignedDotResult w x j)) :=
  boolean_dag_basis _ _ _ _

/-- On an arbitrary embedded state, the compiled signed dot-product circuit coherently XORs each
result into its target and restores the workspace. -/
theorem boolean_word_signed_dot_coherent (w : ℕ) (ψ : QState (Reg (3*(2*w+2)) × Reg (2*w+3))) :
    let p := booleanWordSignedDotProgram w
    Run (1 : Matrix (Reg (3*(2*w+2)+p.nodes+(2*w+3))) (Reg (3*(2*w+2)+p.nodes+(2*w+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed (3*(2*w+2)) p.nodes (2*w+3) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (3*(2*w+2)) p.nodes (2*w+3) xy.1
        (fun j => xy.2 j ^^ booleanWordSignedDotResult w xy.1 j)) :=
  boolean_dag_coherent _ _ _

end Qatlib.Concepts.MatrixAccess.RitzPipeline
