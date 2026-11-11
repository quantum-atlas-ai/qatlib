/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDivisionData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider

/-!
# Sign-magnitude division by Boolean DAGs

`boolean_word_signed_div_value` proves that the circuit divides a signed numerator by an
unsigned denominator according to Lean integer division. For a negative numerator and a positive
denominator, a nonzero remainder increments the quotient magnitude before negation.

`boolean_word_signed_div_magnitude` records the correction formula, the preserved input sign,
and a magnitude bound. Resource bounds and reversible circuit semantics apply to every input,
including a zero denominator. The circuit background is described in [NielsenChuang2010].

## Main statements

* `boolean_word_signed_div_magnitude`: output sign, corrected magnitude, and bound.
* `boolean_word_signed_div_value`: correctness for integer division.
* `boolean_word_signed_div_resources`: polynomial circuit resource bounds.
* `boolean_word_signed_div_basis`, `boolean_word_signed_div_coherent`: circuit action.

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

/-- The node count of the unsigned division graph embedded in the signed-divider input layout. -/
private abbrev sdN0 (w : ℕ) := 0+((booleanWordDivProgram w).nodes+w)
/-- Embed the two unsigned magnitude words before the final numerator sign input. -/
private abbrev sdRaw (w : ℕ) : Fin (2*w) → Fin (2*w+1+0) := fun j => j.castSucc
/-- Embed the unsigned divider in a graph whose inputs also include a numerator sign bit. -/
private abbrev sdG0 (w : ℕ) : BooleanDAG (2*w+1) (sdN0 w) :=
  booleanDAGSplice .nil (sdRaw w) (booleanWordDivDAG w)
/-- Select one unsigned quotient bit in the embedded divider graph. -/
private abbrev sdQ (w : ℕ) (j : Fin w) : Fin (2*w+1+sdN0 w) :=
  booleanSpliceSource (sdRaw w) (booleanWordDivSelect w ⟨j.val,by have := j.isLt; omega⟩)
/-- Select one unsigned remainder bit in the embedded divider graph. -/
private abbrev sdR (w : ℕ) (j : Fin (2*w)) : Fin (2*w+1+sdN0 w) :=
  booleanSpliceSource (sdRaw w) (booleanWordDivSelect w ⟨w+j.val,by have := j.isLt; omega⟩)
/-- Select the unsigned divider's distinguished zero wire in the embedded graph. -/
private abbrev sdZero (w : ℕ) : Fin (2*w+1+sdN0 w) :=
  booleanSpliceSource (sdRaw w) (Fin.castLE (by omega) (booleanWordDivProgram w).zero)
/-- Select the divisor nonzero flag in the embedded unsigned-divider graph. -/
private abbrev sdDNZ (w : ℕ) : Fin (2*w+1+sdN0 w) :=
  booleanSpliceSource (sdRaw w) (Fin.castLE (by omega) (booleanWordDivProgram w).nonzero)
/-- Route a zero word and the remainder word into the remainder nonzero-test graph. -/
private abbrev sdRemMap (w : ℕ) : Fin (2*(2*w)) → Fin (2*w+1+sdN0 w) := fun j =>
  if hj : j.val < 2*w then sdZero w else sdR w ⟨j.val-2*w,by have := j.isLt; omega⟩
/-- Append a nonzero test of the unsigned remainder to the embedded divider. -/
private abbrev sdG1 (w : ℕ) : BooleanDAG (2*w+1) (sdN0 w+(3*(2*w)+1)) :=
  booleanDAGSplice (sdG0 w) (sdRemMap w) (booleanWordNonzeroPrefix (2*w) (2*w) (Nat.le_refl _))
/-- Select the final flag of the remainder nonzero-test graph. -/
private abbrev sdRNZ (w : ℕ) : Fin (2*w+1+(sdN0 w+(3*(2*w)+1))) :=
  booleanSpliceSource (sdRemMap w)
    (⟨2*(2*w)+3*(2*w),by omega⟩ : Fin (2*(2*w)+(3*(2*w)+1)))
/-- Append a guard requiring both a nonzero remainder and a nonzero divisor. -/
private abbrev sdG2 (w : ℕ) : BooleanDAG (2*w+1) (sdN0 w+(3*(2*w)+1)+1) :=
  (sdG1 w).snoc (.conj (sdRNZ w) (Fin.castLE (by omega) (sdDNZ w)))
/-- Append the conjunction of the remainder-and-divisor guard with the negative-numerator flag. -/
private abbrev sdG3 (w : ℕ) : BooleanDAG (2*w+1) (sdN0 w+(3*(2*w)+1)+1+1) :=
  (sdG2 w).snoc (.conj ⟨2*w+1+(sdN0 w+(3*(2*w)+1)),by omega⟩ ⟨2*w,by omega⟩)
/-- The node count after the remainder test and the two rounding-guard conjunctions. -/
private abbrev sdN3 (w : ℕ) := sdN0 w+(3*(2*w)+1)+1+1
/-- Select the original zero wire after the rounding-guard nodes have been appended. -/
private abbrev sdZ (w : ℕ) : Fin (2*w+1+sdN3 w) :=
    Fin.castLE (by dsimp only [sdN3]; omega) (sdZero w)
/-- Select the bit controlling the quotient-magnitude rounding increment. -/
private abbrev sdC (w : ℕ) : Fin (2*w+1+sdN3 w) :=
  ⟨2*w+1+(sdN0 w+(3*(2*w)+1))+1,by dsimp only [sdN3]; omega⟩
/-- Select the unsigned quotient padded by a false high bit as the final adder's left operand. -/
private abbrev sdLeft (w : ℕ) : Fin (w+1) → Fin (2*w+1+sdN3 w) := fun j =>
  if hj : j.val < w then Fin.castLE (by dsimp only [sdN3]; omega) (sdQ w ⟨j.val,hj⟩) else sdZ w
/-- Select the rounding-increment bit in the low position and zero wires elsewhere as the final
adder's right operand. -/
private abbrev sdRight (w : ℕ) : Fin (w+1) → Fin (2*w+1+sdN3 w) := fun j =>
  if j.val = 0 then sdC w else sdZ w

/-- Appending one Boolean node preserves earlier wire values and evaluates the new final wire
using that node on the previous graph values. -/
private theorem sd_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Appending one Boolean node preserves the values of all earlier wires. -/
private theorem sd_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [sd_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

/-- Every original input wire of a Boolean graph evaluates to the corresponding input bit. -/
private theorem sd_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [sd_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

/-- The right view of a packed unsigned operand pair recovers the second word. -/
private theorem sd_right_input (w : ℕ) (a b : Reg w) :
    booleanWordAdderRight w (booleanWordAdderInput w a b) = b := by
  funext j
  have hnot : ¬w+j.val < w := by omega
  simp [booleanWordAdderRight,booleanWordAdderInput,hnot]

/-- Each mapped wire of the embedded unsigned divider has the same value as in the original
unsigned-divider graph. -/
private theorem sd_clause0_source (w : ℕ) (a b : Reg w) (s : Bool)
    (j : Fin (2*w+((booleanWordDivProgram w).nodes+w))) :
    booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s)
      (booleanSpliceSource (sdRaw w) j) =
      booleanDAGValue (booleanWordDivDAG w) (booleanWordAdderInput w a b) j := by
  have h := boolean_dag_splice_value (.nil : BooleanDAG (2*w+1) 0) (sdRaw w)
    (booleanWordDivDAG w) (booleanWordSignedDivInput w a b s) j
  have he : (fun j => booleanDAGValue (.nil : BooleanDAG (2*w+1) 0)
      (booleanWordSignedDivInput w a b s) (sdRaw w j)) = booleanWordAdderInput w a b := by
    funext k
    simp [sdRaw,booleanDAGValue,booleanWordSignedDivInput]
  rw [he] at h
  exact h

/-- The embedded divider's quotient wires evaluate to the unsigned quotient word. -/
private theorem sd_clause0_q (w : ℕ) (a b : Reg w) (s : Bool) (j : Fin w) :
    booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s) (sdQ w j) =
      booleanWordDivQuotient w a b j := sd_clause0_source _ _ _ _ _

/-- The embedded divider's remainder wires evaluate to the unsigned remainder word. -/
private theorem sd_clause0_r (w : ℕ) (a b : Reg w) (s : Bool) (j : Fin (2*w)) :
    booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s) (sdR w j) =
      booleanWordDivRemainder w a b j := sd_clause0_source _ _ _ _ _

/-- Appending the unsigned quotient mask preserves all wires of the division state graph. -/
private theorem sd_unsigned_old (w : ℕ) (a b : Reg w)
    (j : Fin (2*w+(booleanWordDivProgram w).nodes)) :
    booleanDAGValue (booleanWordDivDAG w) (booleanWordAdderInput w a b)
      (Fin.castLE (by omega) j) =
      booleanDAGValue (booleanWordDivProgram w).graph (booleanWordAdderInput w a b) j :=
  boolean_dag_splice_prefix _ _ _ _ j

/-- The distinguished zero wire of the embedded unsigned divider evaluates to false. -/
private theorem sd_clause0_zero (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s) (sdZero w) = false := by
  rw [sd_clause0_source,sd_unsigned_old]
  exact (boolean_word_div_prefix w w (Nat.le_refl w) (booleanWordAdderInput w a b)).1

/-- The embedded divisor nonzero flag detects positivity of the divisor's unsigned value. -/
private theorem sd_clause0_nonzero (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s) (sdDNZ w) =
      decide (0 < booleanWordLSBValue w b) := by
  rw [sd_clause0_source,sd_unsigned_old]
  have h := (boolean_word_div_prefix w w (Nat.le_refl w) (booleanWordAdderInput w a b)).2.1
  simpa only [sd_right_input] using! h

/-- The remainder-test source map evaluates to a zero word paired with the unsigned remainder
word. -/
private theorem sd_rem_inputs (w : ℕ) (a b : Reg w) (s : Bool) :
    (fun j => booleanDAGValue (sdG0 w) (booleanWordSignedDivInput w a b s) (sdRemMap w j)) =
      booleanWordAdderInput (2*w) (fun _ => false) (booleanWordDivRemainder w a b) := by
  funext j
  by_cases hj : j.val < 2*w
  · simp only [sdRemMap,booleanWordAdderInput,dif_pos hj,sd_clause0_zero]
  · simp only [sdRemMap,booleanWordAdderInput,dif_neg hj,sd_clause0_r]

/-- The remainder nonzero-test flag detects positivity of the natural remainder of the input
values. -/
private theorem sd_rem_nonzero (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG1 w) (booleanWordSignedDivInput w a b s) (sdRNZ w) =
      decide (0 < booleanWordLSBValue w a % booleanWordLSBValue w b) := by
  have h := boolean_dag_splice_value (sdG0 w) (sdRemMap w)
    (booleanWordNonzeroPrefix (2*w) (2*w) (Nat.le_refl _))
    (booleanWordSignedDivInput w a b s)
    (⟨2*(2*w)+3*(2*w),by omega⟩ : Fin (2*(2*w)+(3*(2*w)+1)))
  rw [sd_rem_inputs] at h
  have hn := (boolean_word_div_prefix (2*w) 0 (by omega)
    (booleanWordAdderInput (2*w) (fun _ => false) (booleanWordDivRemainder w a b))).2.1
  simp only [booleanWordDivPrefix,booleanWordDivStart,sd_right_input] at hn
  exact h.trans (hn.trans (congrArg (fun n : ℕ => decide (0 < n)) (boolean_word_div_value w a b).2))

/-- Appending the remainder nonzero test preserves every wire of the embedded unsigned divider. -/
private theorem sd_clause1_old (w : ℕ) (x : Reg (2*w+1)) (j : Fin (2*w+1+sdN0 w)) :
    booleanDAGValue (sdG1 w) x (Fin.castLE (by omega) j) = booleanDAGValue (sdG0 w) x j :=
  boolean_dag_splice_prefix _ _ _ _ j

/-- Appending the two rounding-guard conjunctions preserves all wires of the graph after the
remainder test. -/
private theorem sd_clause3_clause1_old (w : ℕ) (x : Reg (2*w+1))
    (j : Fin (2*w+1+(sdN0 w+(3*(2*w)+1)))) :
    booleanDAGValue (sdG3 w) x (Fin.castLE (by omega) j) = booleanDAGValue (sdG1 w) x j := by
  exact (sd_snoc_old (sdG2 w) _ x (Fin.castLE (by omega) j)).trans (sd_snoc_old (sdG1 w) _ x j)

/-- The graph containing all rounding guards preserves every wire of the embedded unsigned
divider. -/
private theorem sd_clause3_old (w : ℕ) (x : Reg (2*w+1)) (j : Fin (2*w+1+sdN0 w)) :
    booleanDAGValue (sdG3 w) x (Fin.castLE (by omega) j) = booleanDAGValue (sdG0 w) x j :=
  (sd_clause3_clause1_old w x (Fin.castLE (by omega) j)).trans (sd_clause1_old w x j)

/-- The first rounding guard is true exactly when both the natural remainder and the unsigned
divisor are positive. -/
private theorem sd_guard_value (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG2 w) (booleanWordSignedDivInput w a b s)
      ⟨2*w+1+(sdN0 w+(3*(2*w)+1)),by omega⟩ =
      (decide (0 < booleanWordLSBValue w a % booleanWordLSBValue w b) &&
        decide (0 < booleanWordLSBValue w b)) := by
  have hn : ¬2*w+1+(sdN0 w+(3*(2*w)+1)) < 2*w+1+(sdN0 w+(3*(2*w)+1)) := by omega
  rw [sdG2,sd_snoc_value,dif_neg hn]
  change (booleanDAGValue (sdG1 w) (booleanWordSignedDivInput w a b s) (sdRNZ w) &&
    booleanDAGValue (sdG1 w) (booleanWordSignedDivInput w a b s)
      (Fin.castLE (by omega) (sdDNZ w))) = _
  rw [sd_rem_nonzero,sd_clause1_old,sd_clause0_nonzero]

/-- The rounding-increment bit is the conjunction of positive remainder, positive divisor, and
the negative-numerator flag. -/
private theorem sd_c_value (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG3 w) (booleanWordSignedDivInput w a b s) (sdC w) =
      ((decide (0 < booleanWordLSBValue w a % booleanWordLSBValue w b) &&
        decide (0 < booleanWordLSBValue w b)) && s) := by
  have hn : ¬2*w+1+(sdN0 w+(3*(2*w)+1))+1 <
      2*w+1+(sdN0 w+(3*(2*w)+1)+1) := by omega
  rw [sdC,sdG3,sd_snoc_value,dif_neg hn]
  change (booleanDAGValue (sdG2 w) (booleanWordSignedDivInput w a b s)
      ⟨2*w+1+(sdN0 w+(3*(2*w)+1)),by omega⟩ &&
    booleanDAGValue (sdG2 w) (booleanWordSignedDivInput w a b s) ⟨2*w,by omega⟩) = _
  rw [sd_guard_value]
  have hs : booleanDAGValue (sdG2 w) (booleanWordSignedDivInput w a b s) ⟨2*w,by omega⟩ = s := by
    have h := sd_input_value (sdG2 w) (booleanWordSignedDivInput w a b s) (Fin.last (2*w))
    simpa only [booleanWordSignedDivInput,Fin.snoc_last] using! h
  rw [hs]

/-- The distinguished zero wire remains false after appending the rounding guards. -/
private theorem sd_z_value (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanDAGValue (sdG3 w) (booleanWordSignedDivInput w a b s) (sdZ w) = false :=
  (sd_clause3_old w (booleanWordSignedDivInput w a b s) (sdZero w)).trans (sd_clause0_zero w a b s)

/-- The final adder's left operand evaluates to the unsigned quotient with a false most
significant bit appended. -/
private theorem sd_left_word (w : ℕ) (a b : Reg w) (s : Bool) :
    (fun j => booleanDAGValue (sdG3 w) (booleanWordSignedDivInput w a b s) (sdLeft w j)) =
      Fin.snoc (booleanWordDivQuotient w a b) false := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [sdLeft,Fin.val_last,dif_neg (Nat.lt_irrefl w),Fin.snoc_last]
    exact sd_z_value w a b s
  · simp only [sdLeft,Fin.val_castSucc,dif_pos k.isLt,Fin.snoc_castSucc]
    exact (sd_clause3_old w (booleanWordSignedDivInput w a b s) (sdQ w k)).trans
        (sd_clause0_q w a b s k)

/-- The final adder's right operand has the guarded rounding-increment bit in its least
significant position and false bits elsewhere. -/
private theorem sd_right_word (w : ℕ) (a b : Reg w) (s : Bool) :
    (fun j => booleanDAGValue (sdG3 w) (booleanWordSignedDivInput w a b s) (sdRight w j)) =
      Fin.cons ((decide (0 < booleanWordLSBValue w a % booleanWordLSBValue w b) &&
        decide (0 < booleanWordLSBValue w b)) && s) (fun _ => false) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [sdRight,Fin.val_zero,Fin.cons_zero]
    exact sd_c_value w a b s
  · simp only [sdRight,Fin.val_succ,Nat.succ_ne_zero,if_false,Fin.cons_succ]
    exact sd_z_value w a b s

/-- Appending a false most significant bit preserves the unsigned word value. -/
private theorem sd_pad_value (w : ℕ) (a : Reg w) :
    booleanWordLSBValue (w+1) (Fin.snoc a false) = booleanWordLSBValue w a := by
  simp [boolean_word_lsb_value,Fin.sum_univ_castSucc]

/-- A word whose only potentially true bit is its least significant bit has value one or zero
according to that bit. -/
private theorem sd_unit_value (w : ℕ) (bit : Bool) :
    booleanWordLSBValue (w+1) (Fin.cons bit (fun _ => false)) = (if bit then 1 else 0) := by
  simp [boolean_word_lsb_value,Fin.sum_univ_succ]

/-- The signed-divider magnitude is the selected output of the final adder applied to the padded
unsigned quotient and guarded increment. -/
private theorem sd_magnitude_word (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanWordSignedDivMagnitude w a b s = fun j =>
      booleanDAGValue (booleanDAGAppendAdder (sdG3 w) (w+1) (sdLeft w) (sdRight w))
        (booleanWordSignedDivInput w a b s) (booleanDAGAppendAdderSelect (w+1) (sdLeft w) (sdRight w) j) := by
  funext j
  simp only [booleanWordSignedDivMagnitude,booleanWordSignedDivResult,booleanWordSignedDivProgram,
    Fin.val_castSucc,dif_pos j.isLt]

/-- The quotient magnitude is the unsigned quotient plus one exactly for a negative numerator, a
positive divisor, and a nonzero remainder. -/
private theorem sd_magnitude_value (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanWordLSBValue (w+2) (booleanWordSignedDivMagnitude w a b s) =
      booleanWordLSBValue w a / booleanWordLSBValue w b +
        (if s = true ∧ 0 < booleanWordLSBValue w b ∧
          booleanWordLSBValue w a % booleanWordLSBValue w b ≠ 0 then 1 else 0) := by
  rw [sd_magnitude_word,boolean_dag_append_adder_value,sd_left_word,sd_right_word,
    sd_pad_value,sd_unit_value,(boolean_word_div_value w a b).1]
  have hc : (((decide (0 < booleanWordLSBValue w a % booleanWordLSBValue w b) &&
      decide (0 < booleanWordLSBValue w b)) && s) = true) ↔
      (s = true ∧ 0 < booleanWordLSBValue w b ∧
        booleanWordLSBValue w a % booleanWordLSBValue w b ≠ 0) := by
    simp only [Bool.and_eq_true,decide_eq_true_eq,Nat.pos_iff_ne_zero]
    tauto
  simp only [hc]

/-- The signed-divider output sign equals the input negative flag. -/
private theorem sd_sign_value (w : ℕ) (a b : Reg w) (s : Bool) :
    booleanWordSignedDivSign w a b s = s := by
  have ho : (booleanWordSignedDivProgram w).output (Fin.last (w+2)) =
      Fin.castLE (by omega) (Fin.last (2*w)) := by
    simp only [booleanWordSignedDivProgram,Fin.val_last,dif_neg (Nat.lt_irrefl (w+2))]
    apply Fin.ext
    rfl
  rw [booleanWordSignedDivSign,booleanWordSignedDivResult,ho,sd_input_value]
  simp [booleanWordSignedDivInput]

/-- The natural quotient plus the guarded negative-rounding increment is at most the numerator
magnitude. -/
private theorem sd_magnitude_bound (A B : ℕ) (s : Bool) :
    A/B+(if s = true ∧ 0 < B ∧ A%B ≠ 0 then 1 else 0) ≤ A := by
  have hq : A/B ≤ A := Nat.div_le_self A B
  split_ifs with hc
  · have hR : 0 < A%B := Nat.pos_of_ne_zero hc.2.2
    have hbalance := Nat.mod_add_div A B
    have hm : A/B ≤ B*(A/B) := Nat.le_mul_of_pos_left _ hc.2.1
    omega
  · omega

/-- The signed divider preserves the negative flag and increments the unsigned quotient
magnitude exactly for a negative numerator with positive divisor and nonzero remainder. The
resulting magnitude is at most the numerator magnitude. -/
theorem boolean_word_signed_div_magnitude (w : ℕ) (a b : Reg w) (negative : Bool) :
    booleanWordSignedDivSign w a b negative = negative ∧
      booleanWordLSBValue (w+2) (booleanWordSignedDivMagnitude w a b negative) =
        booleanWordLSBValue w a / booleanWordLSBValue w b +
          (if negative = true ∧ 0 < booleanWordLSBValue w b ∧
              booleanWordLSBValue w a % booleanWordLSBValue w b ≠ 0 then 1 else 0) ∧
      booleanWordLSBValue (w+2) (booleanWordSignedDivMagnitude w a b negative) ≤
        booleanWordLSBValue w a := by
  refine ⟨sd_sign_value w a b negative,sd_magnitude_value w a b negative,?_⟩
  rw [sd_magnitude_value]
  exact sd_magnitude_bound _ _ _

/-- For a positive natural divisor, negating the quotient rounded upward for a nonzero remainder
gives the integer quotient of the negated numerator. -/
private theorem sd_negative_value (A B : ℕ) (hb : 0 < B) :
    -((A/B+(if A%B ≠ 0 then 1 else 0) : ℕ) : ℤ) = -(A : ℤ)/(B : ℤ) := by
  have hbZ : (0 : ℤ) < B := by exact_mod_cast hb
  have he : ((A%B : ℕ) : ℤ)+(B : ℤ)*((A/B : ℕ) : ℤ) = (A : ℤ) := by
    exact_mod_cast Nat.mod_add_div A B
  have hr : ((A%B : ℕ) : ℤ) < (B : ℤ) := by exact_mod_cast Nat.mod_lt A hb
  by_cases hz : A%B = 0
  · have hinv : (0 : ℤ)+(B : ℤ)*(-((A/B : ℕ) : ℤ)) = -(A : ℤ) ∧
        (0 : ℤ) ≤ 0 ∧ (0 : ℤ) < B := by
      simp only [hz,Nat.cast_zero,zero_add] at he
      exact ⟨by nlinarith only [he],le_refl _,hbZ⟩
    have h := (Int.ediv_emod_unique hbZ).mpr hinv
    simpa [hz] using! h.1.symm
  · have hpos : (0 : ℤ) < ((A%B : ℕ) : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hinv : ((B : ℤ)-((A%B : ℕ) : ℤ))+(B : ℤ)*(-(((A/B : ℕ) : ℤ)+1)) = -(A : ℤ) ∧
        0 ≤ (B : ℤ)-((A%B : ℕ) : ℤ) ∧ (B : ℤ)-((A%B : ℕ) : ℤ) < B := by
      exact ⟨by nlinarith only [he],by omega,by omega⟩
    have h := (Int.ediv_emod_unique hbZ).mpr hinv
    simpa [hz] using! h.1.symm

/-- The signed-divider output equals Lean integer division of the signed numerator by the
unsigned denominator, including when the denominator is zero. -/
theorem boolean_word_signed_div_value (w : ℕ) (a b : Reg w) (negative : Bool) :
    booleanWordSignedDivValue w a b negative =
      booleanWordSignedValue w a negative / (booleanWordLSBValue w b : ℤ) := by
  obtain ⟨hs,hm,_⟩ := boolean_word_signed_div_magnitude w a b negative
  dsimp only [booleanWordSignedDivValue,booleanWordSignedValue]
  rw [hs,hm]
  cases negative with
  | false => simp [Int.natCast_ediv]
  | true =>
    by_cases hb : booleanWordLSBValue w b = 0
    · simp [hb]
    · have hpos : 0 < booleanWordLSBValue w b := Nat.pos_of_ne_zero hb
      simpa [hpos] using! sd_negative_value (booleanWordLSBValue w a) (booleanWordLSBValue w b) hpos

/-- The signed divider is legal with at most `20*w^2+17*w+10` nodes, `600*w^2+511*w+303`
compiled gates, and `20*w^2+20*w+14` total wires. It uses zero oracle queries, and its gate
count equals its reflection-step count. -/
theorem boolean_word_signed_div_resources (w : ℕ) :
    let p := booleanWordSignedDivProgram w
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 20*w^2+17*w+10 ∧ reflectionLegal gs ∧
      gs.length ≤ 600*w^2+511*w+303 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (2*w+1)+p.nodes+(w+3) ≤ 20*w^2+20*w+14 := by
  let p := booleanWordSignedDivProgram w
  have hn : p.nodes ≤ 20*w^2+17*w+10 := by
    have h := (boolean_word_div_resources w).1
    change 0+((booleanWordDivProgram w).nodes+w)+(3*(2*w)+1)+1+1+(5*(w+1)+1) ≤ _
    nlinarith
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  exact ⟨hn,hl,by nlinarith,hq,hc,by nlinarith⟩

/-- On a basis state with initialized workspace, the compiled signed divider XORs its
sign-magnitude result into the target and restores the workspace. -/
theorem boolean_word_signed_div_basis (w : ℕ) (a b : Reg w) (negative : Bool) (y : Reg (w+3)) :
    let p := booleanWordSignedDivProgram w
    Run (1 : Matrix (Reg ((2*w+1)+p.nodes+(w+3))) (Reg ((2*w+1)+p.nodes+(w+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput (2*w+1) p.nodes (w+3) (booleanWordSignedDivInput w a b negative) y)) =
      Ket (booleanDAGInput (2*w+1) p.nodes (w+3) (booleanWordSignedDivInput w a b negative)
        (fun j => y j ^^ booleanWordSignedDivResult w a b negative j)) :=
  boolean_dag_basis _ _ _ _

/-- Packing the two magnitude views and the sign bit reconstructs the original signed-division
input. -/
private theorem sd_input_views (w : ℕ) (x : Reg (2*w+1)) :
    booleanWordSignedDivInput w (booleanWordSignedDivLeft w x) (booleanWordSignedDivRight w x)
      (x (Fin.last (2*w))) = x := by
  have hraw : booleanWordAdderInput w (booleanWordAdderLeft w (fun j => x j.castSucc))
      (booleanWordAdderRight w (fun j => x j.castSucc)) = fun j => x j.castSucc := by
    funext j
    by_cases hj : j.val < w
    · simp [booleanWordAdderInput,booleanWordAdderLeft,hj]
    · have hle : w ≤ j.val := by omega
      simp [booleanWordAdderInput,booleanWordAdderRight,hj,Nat.add_sub_of_le hle]
  dsimp only [booleanWordSignedDivInput,booleanWordSignedDivLeft,booleanWordSignedDivRight]
  rw [hraw]
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- On an arbitrary embedded state, the compiled signed divider coherently XORs each
sign-magnitude quotient into its target and restores the workspace. -/
theorem boolean_word_signed_div_coherent (w : ℕ) (ψ : QState (Reg (2*w+1) × Reg (w+3))) :
    let p := booleanWordSignedDivProgram w
    Run (1 : Matrix (Reg ((2*w+1)+p.nodes+(w+3))) (Reg ((2*w+1)+p.nodes+(w+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed (2*w+1) p.nodes (w+3) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w+1) p.nodes (w+3) xy.1
        (fun j => xy.2 j ^^ booleanWordSignedDivResult w
          (booleanWordSignedDivLeft w xy.1) (booleanWordSignedDivRight w xy.1)
          (xy.1 (Fin.last (2*w))) j)) := by
  (try dsimp only)
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordSignedDivResult,sd_input_views]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
