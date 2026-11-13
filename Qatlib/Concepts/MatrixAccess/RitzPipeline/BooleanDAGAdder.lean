/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdderData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAG
import Mathlib.Data.Fin.Rev

/-!
# Correctness of a reversible word adder

This module proves that `booleanWordAdderResult` represents the exact sum of two unsigned words,
including the final carry bit. It establishes bitwise carry invariants and verifies the
basis-state and coherent action of the local gate implementation.

The compilation uses the reversible arithmetic framework discussed in [NielsenChuang2010], with
a gate bound linear in the input width.

## Main statements

* `boolean_word_adder_value`: identifies the output value with the sum of the inputs.
* `boolean_word_adder_resources`: gives legality, a 151w + 31 gate bound, and zero queries.
* `boolean_word_adder_coherent`: proves coherent addition into the output register by XOR.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators

/-- Converts a Boolean bit to the natural number zero or one. -/
private def adderBit (b : Bool) : ℕ := if b then 1 else 0

/-- The sum of three input bits equals the sum bit plus twice the carry bit of a full adder. -/
private theorem adder_bit_balance (a b c : Bool) :
    adderBit a+adderBit b+adderBit c =
      adderBit ((a ^^ b) ^^ c)+2*adderBit ((a && b) ^^ ((a ^^ b) && c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The value of a word with its least significant bit first is the sum of its bits weighted by
powers of two. -/
theorem boolean_word_lsb_value (w : ℕ) (a : Reg w) :
    booleanWordLSBValue w a = ∑ i : Fin w, (if a i then 1 else 0)*(2:ℕ)^i.val := by
  rw [booleanWordLSBValue,bitVecEquiv_val_msb]
  calc
    _ = ∑ i : Fin w,
        (boolEquivFin2 (a (Fin.rev (Fin.rev i)))).val *
          2^(w-1-(Fin.rev i).val) :=
      (Equiv.sum_comp (Fin.revPerm (n:=w)) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := i.isLt
      have hexp : w-1-(Fin.rev i).val = i.val := by
        change w-1-(w-(i.val+1)) = i.val
        omega
      simp only [Fin.rev_rev,hexp]
      cases ha : a i <;> simp [boolEquivFin2]

/-- Appending a Boolean node preserves earlier coordinates and evaluates the new node at the
final coordinate. -/
private theorem adder_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Extending the adder prefix by one bit preserves all previously available values. -/
private theorem adder_prefix_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(5*i+1)) :
    booleanDAGValue (booleanWordAdderPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordAdderPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordAdderPrefix,Nat.mul_succ,Nat.add_assoc,
    adder_snoc_value,hj]
  split_ifs <;> first | rfl | omega

/-- The input coordinates of an adder prefix retain the original input bits. -/
private theorem adder_prefix_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w) :
    booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ := by
  induction i with
  | zero => simp (disch := omega) [booleanWordAdderPrefix,adder_snoc_value,booleanDAGValue,hj]
  | succ i ih =>
    rw [adder_prefix_old w i hi x j (by omega)]
    exact ih (by omega)

/-- The carry bit stored after the first i stages of the word adder. -/
private def adderCarry (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) : Bool :=
  booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨2*w+5*i,by omega⟩

/-- The specified sum bit among the first i stages of the word adder. -/
private def adderSum (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) (j : Fin i) : Bool :=
  booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨2*w+5*j.val+2,by omega⟩

/-- The initial carry bit of the word adder is false. -/
private theorem adder_carry_zero (w : ℕ) (x : Reg (2*w)) : adderCarry w 0 (by omega) x = false := by
  simp [adderCarry,booleanWordAdderPrefix,adder_snoc_value,booleanNodeValue]

/-- Extending the adder prefix preserves each previously computed sum bit. -/
private theorem adder_sum_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) (j : Fin i) :
    adderSum w (i+1) hi x j.castSucc = adderSum w i (by omega) x j := by
  have hj := j.isLt
  simpa only [adderSum,Fin.val_castSucc] using!
    adder_prefix_old w i hi x (2*w+5*j.val+2) (by omega)

/-- The next sum bit is the XOR of the two input bits and the preceding carry. -/
private theorem adder_sum_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    adderSum w (i+1) hi x (Fin.last i) =
      ((x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩) ^^ adderCarry w i (by omega) x) := by
  simp (disch := omega) [adderSum,adderCarry,booleanWordAdderPrefix,Nat.mul_succ,
    Nat.add_assoc,adder_snoc_value,booleanNodeValue,adder_prefix_input]

/-- The next carry is the XOR of the input conjunction and the conjunction of the input XOR with
the preceding carry. -/
private theorem adder_carry_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    adderCarry w (i+1) hi x =
      ((x ⟨i,by omega⟩ && x ⟨w+i,by omega⟩) ^^
        ((x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩) && adderCarry w i (by omega) x)) := by
  simp (disch := omega) [adderCarry,booleanWordAdderPrefix,Nat.mul_succ,Nat.add_assoc,
    adder_snoc_value,booleanNodeValue,adder_prefix_input]
  split_ifs <;> first | rfl | omega

/-- For the first i bits, the two input values sum to the computed sum-bit value plus the carry
weighted by 2^i. -/
private theorem adder_partial_balance (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) :
    (∑ j : Fin i, adderBit (x ⟨j.val,by have := j.isLt; omega⟩)*2^j.val) +
      (∑ j : Fin i, adderBit (x ⟨w+j.val,by have := j.isLt; omega⟩)*2^j.val) =
    (∑ j : Fin i, adderBit (adderSum w i hi x j)*2^j.val) +
      adderBit (adderCarry w i hi x)*2^i := by
  induction i with
  | zero => simp [adder_carry_zero,adderBit]
  | succ i ih =>
    have hp : i ≤ w := by omega
    have hprev := ih hp
    have hbit := adder_bit_balance (x ⟨i,by omega⟩) (x ⟨w+i,by omega⟩)
      (adderCarry w i hp x)
    have hweighted := congrArg (fun z : ℕ => z*2^i) hbit
    simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,
      adder_sum_old,pow_succ]
    rw [adder_sum_new,adder_carry_new]

    nlinarith only [hprev,hweighted]

/-- The first half of `booleanWordAdderInput` recovers the left word bit by bit. -/
private theorem adder_input_left (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨i.val,by have := i.isLt; omega⟩ = a i := by
  simp [booleanWordAdderInput,i.isLt]

/-- The second half of `booleanWordAdderInput` recovers the right word bit by bit. -/
private theorem adder_input_right (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨w+i.val,by have := i.isLt; omega⟩ = b i := by
  have hn : ¬w+i.val < w := by omega
  simp [booleanWordAdderInput,hn]

/-- Each of the first w output bits is the corresponding sum bit of the completed adder prefix. -/
private theorem adder_result_sum (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderResult w a b i.castSucc =
      adderSum w w (Nat.le_refl w) (booleanWordAdderInput w a b) i := by
  simp [booleanWordAdderResult,booleanWordAdderDAG,booleanWordAdderSelect,adderSum,i.isLt]

/-- The last output bit is the final carry of the completed adder prefix. -/
private theorem adder_result_carry (w : ℕ) (a b : Reg w) :
    booleanWordAdderResult w a b (Fin.last w) =
      adderCarry w w (Nat.le_refl w) (booleanWordAdderInput w a b) := by
  simp [booleanWordAdderResult,booleanWordAdderDAG,booleanWordAdderSelect,adderCarry]

/-- The w+1-bit adder result represents the sum of the unsigned values of its two w-bit inputs. -/
theorem boolean_word_adder_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (w+1) (booleanWordAdderResult w a b) =
      booleanWordLSBValue w a + booleanWordLSBValue w b := by
  rw [boolean_word_lsb_value,boolean_word_lsb_value,boolean_word_lsb_value,
    Fin.sum_univ_castSucc]
  have hv := adder_partial_balance w w (Nat.le_refl w) (booleanWordAdderInput w a b)
  simp only [adder_input_left,adder_input_right] at hv
  simpa only [Fin.val_castSucc,Fin.val_last,adder_result_sum,adder_result_carry,adderBit] using!
      hv.symm

/-- The compiled adder XORs its w+1-bit result into a basis output register while preserving the
inputs and restoring clean work bits. -/
theorem boolean_word_adder_basis (w : ℕ) (a b : Reg w) (y : Reg (w+1)) :
    Run (1 : Matrix (Reg ((2*w)+(5*w+1)+(w+1)))
      (Reg ((2*w)+(5*w+1)+(w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)))
      (Ket (booleanDAGInput (2*w) (5*w+1) (w+1) (booleanWordAdderInput w a b) y)) =
      Ket (booleanDAGInput (2*w) (5*w+1) (w+1) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordAdderResult w a b j)) := by
  simpa only [booleanDAGOutput,booleanWordAdderResult] using!
    boolean_dag_basis (booleanWordAdderDAG w) (booleanWordAdderSelect w)
      (booleanWordAdderInput w a b) y

/-- The compiled word adder is legal, contains at most 151w + 31 gates, uses no queries, and has
gate count equal to its gate-list length. -/
theorem boolean_word_adder_resources (w : ℕ) :
    reflectionLegal (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)) ∧
    (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)).length ≤ 151*w+31 ∧
    QueryCount (reflectionCompile
      (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w))) = 0 ∧
    GateCount (reflectionCompile
      (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w))) =
      (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)).length := by
  have h := boolean_dag_resources (booleanWordAdderDAG w) (booleanWordAdderSelect w)
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2⟩
  have hl := h.2.1
  omega

/-- Splitting a combined adder input into its left and right words and joining them again
recovers the combined input. -/
private theorem adder_input_views (w : ℕ) (x : Reg (2*w)) :
    booleanWordAdderInput w (booleanWordAdderLeft w x) (booleanWordAdderRight w x) = x := by
  funext i
  by_cases hi : i.val < w
  · simp [booleanWordAdderInput,booleanWordAdderLeft,hi]
  · have hle : w ≤ i.val := by omega
    simp [booleanWordAdderInput,booleanWordAdderRight,hi,Nat.add_sub_of_le hle]

/-- The compiled adder coherently XORs the sum word into the output register of an arbitrary
embedded input-output state. -/
theorem boolean_word_adder_coherent (w : ℕ) (ψ : QState (Reg (2*w) × Reg (w+1))) :
    Run (1 : Matrix (Reg ((2*w)+(5*w+1)+(w+1)))
      (Reg ((2*w)+(5*w+1)+(w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordAdderDAG w) (booleanWordAdderSelect w)))
      (booleanDAGEmbed (2*w) (5*w+1) (w+1) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w) (5*w+1) (w+1) xy.1
        (fun j => xy.2 j ^^ booleanWordAdderResult w
          (booleanWordAdderLeft w xy.1) (booleanWordAdderRight w xy.1) j)) := by
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordAdderResult,adder_input_views]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
