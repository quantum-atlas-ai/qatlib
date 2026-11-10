/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdderData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAG
import Mathlib.Data.Fin.Rev
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators

private def adderBit (b : Bool) : ℕ := if b then 1 else 0

private theorem adder_bit_balance (a b c : Bool) :
    adderBit a+adderBit b+adderBit c =
      adderBit ((a ^^ b) ^^ c)+2*adderBit ((a && b) ^^ ((a ^^ b) && c)) := by
  cases a <;> cases b <;> cases c <;> decide

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

private theorem adder_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

private theorem adder_prefix_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w+(5*i+1)) :
    booleanDAGValue (booleanWordAdderPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordAdderPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordAdderPrefix,Nat.mul_succ,Nat.add_assoc,
    adder_snoc_value,hj]
  split_ifs <;> first | rfl | omega

private theorem adder_prefix_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w))
    (j : ℕ) (hj : j < 2*w) :
    booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ := by
  induction i with
  | zero => simp (disch := omega) [booleanWordAdderPrefix,adder_snoc_value,booleanDAGValue,hj]
  | succ i ih =>
    rw [adder_prefix_old w i hi x j (by omega)]
    exact ih (by omega)

private def adderCarry (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) : Bool :=
  booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨2*w+5*i,by omega⟩

private def adderSum (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w)) (j : Fin i) : Bool :=
  booleanDAGValue (booleanWordAdderPrefix w i hi) x ⟨2*w+5*j.val+2,by omega⟩

private theorem adder_carry_zero (w : ℕ) (x : Reg (2*w)) : adderCarry w 0 (by omega) x = false := by
  simp [adderCarry,booleanWordAdderPrefix,adder_snoc_value,booleanNodeValue]

private theorem adder_sum_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) (j : Fin i) :
    adderSum w (i+1) hi x j.castSucc = adderSum w i (by omega) x j := by
  have hj := j.isLt
  simpa only [adderSum,Fin.val_castSucc] using!
    adder_prefix_old w i hi x (2*w+5*j.val+2) (by omega)

private theorem adder_sum_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    adderSum w (i+1) hi x (Fin.last i) =
      ((x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩) ^^ adderCarry w i (by omega) x) := by
  simp (disch := omega) [adderSum,adderCarry,booleanWordAdderPrefix,Nat.mul_succ,
    Nat.add_assoc,adder_snoc_value,booleanNodeValue,adder_prefix_input]

private theorem adder_carry_new (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w)) :
    adderCarry w (i+1) hi x =
      ((x ⟨i,by omega⟩ && x ⟨w+i,by omega⟩) ^^
        ((x ⟨i,by omega⟩ ^^ x ⟨w+i,by omega⟩) && adderCarry w i (by omega) x)) := by
  simp (disch := omega) [adderCarry,booleanWordAdderPrefix,Nat.mul_succ,Nat.add_assoc,
    adder_snoc_value,booleanNodeValue,adder_prefix_input]
  split_ifs <;> first | rfl | omega

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

private theorem adder_input_left (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨i.val,by have := i.isLt; omega⟩ = a i := by
  simp [booleanWordAdderInput,i.isLt]

private theorem adder_input_right (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderInput w a b ⟨w+i.val,by have := i.isLt; omega⟩ = b i := by
  have hn : ¬w+i.val < w := by omega
  simp [booleanWordAdderInput,hn]

private theorem adder_result_sum (w : ℕ) (a b : Reg w) (i : Fin w) :
    booleanWordAdderResult w a b i.castSucc =
      adderSum w w (Nat.le_refl w) (booleanWordAdderInput w a b) i := by
  simp [booleanWordAdderResult,booleanWordAdderDAG,booleanWordAdderSelect,adderSum,i.isLt]

private theorem adder_result_carry (w : ℕ) (a b : Reg w) :
    booleanWordAdderResult w a b (Fin.last w) =
      adderCarry w w (Nat.le_refl w) (booleanWordAdderInput w a b) := by
  simp [booleanWordAdderResult,booleanWordAdderDAG,booleanWordAdderSelect,adderCarry]

theorem boolean_word_adder_value (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (w+1) (booleanWordAdderResult w a b) =
      booleanWordLSBValue w a + booleanWordLSBValue w b := by
  rw [boolean_word_lsb_value,boolean_word_lsb_value,boolean_word_lsb_value,
    Fin.sum_univ_castSucc]
  have hv := adder_partial_balance w w (Nat.le_refl w) (booleanWordAdderInput w a b)
  simp only [adder_input_left,adder_input_right] at hv
  simpa only [Fin.val_castSucc,Fin.val_last,adder_result_sum,adder_result_carry,adderBit] using!
      hv.symm

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

private theorem adder_input_views (w : ℕ) (x : Reg (2*w)) :
    booleanWordAdderInput w (booleanWordAdderLeft w x) (booleanWordAdderRight w x) = x := by
  funext i
  by_cases hi : i.val < w
  · simp [booleanWordAdderInput,booleanWordAdderLeft,hi]
  · have hle : w ≤ i.val := by omega
    simp [booleanWordAdderInput,booleanWordAdderRight,hi,Nat.add_sub_of_le hle]

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
