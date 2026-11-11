/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAdditionData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedMultiplication
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGConditionalSubtract

/-!
# Sign-magnitude addition by Boolean DAGs

`boolean_word_mux_value` verifies word selection by a Boolean control. The signed adder combines
unsigned addition, conditional subtraction in both operand orders, and multiplexing to select a
magnitude.

`boolean_word_signed_add_value` proves exact integer addition for sign-magnitude inputs. The
module also characterizes the output sign and magnitude, establishes linear resource bounds, and
proves the compiled reversible circuit semantics. The circuit background is described in
[NielsenChuang2010].

## Main statements

* `boolean_word_mux_value`: correctness of the word multiplexer.
* `boolean_word_signed_add_magnitude`: zero-wire, sign, and magnitude properties.
* `boolean_word_signed_add_value`: exact signed addition.
* `boolean_word_signed_add_resources`: node, gate, and register bounds.

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

/-- Appending one Boolean node preserves earlier wire values and evaluates the new final wire
using that node on the previous graph values. -/
private theorem sa_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Appending one Boolean node preserves the values of all earlier wires. -/
private theorem sa_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [sa_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

/-- Every original input wire of a Boolean graph evaluates to the corresponding input bit. -/
private theorem sa_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [sa_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

/-- The expression `b ^^ ((a ^^ b) && c)` selects `a` when `c` is true and `b` otherwise. -/
private theorem mux_bool (a b c : Bool) : (b ^^ ((a ^^ b) && c)) = if c then a else b := by
  cases a <;> cases b <;> cases c <;> decide

/-- Extending a multiplexer prefix by one stage preserves every wire of the previous prefix. -/
private theorem mux_prefix_old (w i : ℕ) (hi : i+1 ≤ w) (x : Reg (2*w+1))
    (j : ℕ) (hj : j < 2*w+1+3*i) :
    booleanDAGValue (booleanWordMuxPrefix w (i+1) hi) x ⟨j,by omega⟩ =
      booleanDAGValue (booleanWordMuxPrefix w i (by omega)) x ⟨j,hj⟩ := by
  simp (disch := omega) [booleanWordMuxPrefix,Nat.mul_succ,Nat.add_assoc,sa_snoc_value]
  split_ifs <;> first | rfl | omega

/-- Every input wire retains its value throughout a multiplexer prefix. -/
private theorem mux_prefix_input (w i : ℕ) (hi : i ≤ w) (x : Reg (2*w+1))
    (j : ℕ) (hj : j < 2*w+1) :
    booleanDAGValue (booleanWordMuxPrefix w i hi) x ⟨j,by omega⟩ = x ⟨j,hj⟩ :=
  sa_input_value _ x ⟨j,hj⟩

/-- Each computed multiplexer-prefix bit selects the corresponding first or second input bit
according to the final control input. -/
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

/-- The word multiplexer returns `a` when `selectA` is true and `b` otherwise. -/
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

/-- The node count after initializing the zero wire and appending the unsigned magnitude adder. -/
private abbrev saNA (w : ℕ) := 1+(5*w+1)
/-- The number of nodes in one width `w` conditional-subtraction graph. -/
private abbrev saNC (w : ℕ) := 7*w+1+3*w+1
/-- The node count after appending the forward conditional subtraction. -/
private abbrev saNF (w : ℕ) := saNA w+saNC w
/-- The node count after appending both operand orders of conditional subtraction. -/
private abbrev saNR (w : ℕ) := saNF w+saNC w
/-- The node count after appending the three sign-selection nodes. -/
private abbrev saNS (w : ℕ) := saNR w+1+1+1
/-- The node count after appending the magnitude-difference multiplexer. -/
private abbrev saND (w : ℕ) := saNS w+3*w
/-- The final node count after appending the sum-versus-difference multiplexer. -/
private abbrev saNT (w : ℕ) := saND w+3*(w+1)
/-- The initial signed-addition graph containing a single false constant. -/
private abbrev saG0 (w : ℕ) : BooleanDAG (2*w+2) 1 := .snoc .nil (.constant false)
/-- Embed the two raw magnitude words into the initial signed-addition graph. -/
private abbrev saRaw0 (w : ℕ) : Fin (2*w) → Fin (2*w+2+1) :=
  fun j => ⟨j.val,by have := j.isLt; omega⟩
/-- Append the unsigned magnitude adder to the initial zero-wire graph. -/
private abbrev saGA (w : ℕ) : BooleanDAG (2*w+2) (saNA w) :=
  booleanDAGSplice (saG0 w) (saRaw0 w) (booleanWordAdderDAG w)
/-- Select a sum or carry bit from the unsigned magnitude adder. -/
private abbrev saSum (w : ℕ) (j : Fin (w+1)) : Fin (2*w+2+saNA w) :=
  booleanSpliceSource (saRaw0 w) (booleanWordAdderSelect w j)
/-- Embed the two raw magnitude words into the graph after unsigned addition. -/
private abbrev saRawA (w : ℕ) : Fin (2*w) → Fin (2*w+2+saNA w) :=
  fun j => ⟨j.val,by have := j.isLt; omega⟩
/-- Append conditional subtraction of the second magnitude from the first. -/
private abbrev saGF (w : ℕ) : BooleanDAG (2*w+2) (saNF w) :=
  booleanDAGSplice (saGA w) (saRawA w) (booleanWordCondSubDAG w)
/-- Select a result or comparison bit from the forward conditional subtraction. -/
private abbrev saF (w : ℕ) (j : Fin (w+1)) : Fin (2*w+2+saNF w) :=
  booleanSpliceSource (saRawA w) (booleanWordCondSubSelect w j)
/-- Route the two raw magnitude words in reverse order for conditional subtraction. -/
private abbrev saReverse (w : ℕ) : Fin (2*w) → Fin (2*w+2+saNF w) := fun j =>
  if hj : j.val < w then ⟨w+j.val,by omega⟩ else ⟨j.val-w,by have := j.isLt; omega⟩
/-- Append conditional subtraction of the first magnitude from the second. -/
private abbrev saGR (w : ℕ) : BooleanDAG (2*w+2) (saNR w) :=
  booleanDAGSplice (saGF w) (saReverse w) (booleanWordCondSubDAG w)
/-- Select a result or comparison bit from the reverse conditional subtraction. -/
private abbrev saR (w : ℕ) (j : Fin (w+1)) : Fin (2*w+2+saNR w) :=
  booleanSpliceSource (saReverse w) (booleanWordCondSubSelect w j)
/-- Select the forward conditional-subtraction comparison flag in the graph after both
subtractions. -/
private abbrev saFlag (w : ℕ) : Fin (2*w+2+saNR w) :=
  Fin.castLE (by dsimp only [saNR]; omega) (saF w (Fin.last w))
/-- Append the XOR of the two input sign bits to the signed-addition graph. -/
private abbrev saG1 (w : ℕ) : BooleanDAG (2*w+2) (saNR w+1) :=
  (saGR w).snoc (.xor ⟨2*w,by omega⟩ ⟨2*w+1,by omega⟩)
/-- Append the conjunction of sign disagreement with the forward magnitude-comparison flag. -/
private abbrev saG2 (w : ℕ) : BooleanDAG (2*w+2) (saNR w+1+1) :=
  (saG1 w).snoc (.conj ⟨2*w+2+saNR w,by omega⟩ (Fin.castLE (by omega) (saFlag w)))
/-- Append the output sign-selection bit to the signed-addition graph. -/
private abbrev saG3 (w : ℕ) : BooleanDAG (2*w+2) (saNS w) :=
  (saG2 w).snoc (.xor ⟨2*w+1,by omega⟩ ⟨2*w+2+saNR w+1,by omega⟩)
/-- Route the two conditional-subtraction magnitude outputs and their comparison flag into a
word multiplexer. -/
private abbrev saDiffMap (w : ℕ) : Fin (2*w+1) → Fin (2*w+2+saNS w) := fun j =>
  if hj : j.val < w then
    Fin.castLE (by dsimp only [saNS,saNR]; omega) (saF w (Fin.castSucc ⟨j.val,hj⟩))
  else if hk : j.val < 2*w then
    Fin.castLE (by dsimp only [saNS]; omega) (saR w (Fin.castSucc ⟨j.val-w,by omega⟩))
  else Fin.castLE (by dsimp only [saNS,saNR]; omega) (saF w (Fin.last w))
/-- Append the multiplexer selecting the nonnegative magnitude difference. -/
private abbrev saGD (w : ℕ) : BooleanDAG (2*w+2) (saND w) :=
  booleanDAGSplice (saG3 w) (saDiffMap w) (booleanWordMuxDAG w)
/-- Select one magnitude bit from the difference multiplexer. -/
private abbrev saDiff (w : ℕ) (j : Fin w) : Fin (2*w+2+saND w) :=
  booleanSpliceSource (saDiffMap w) (booleanWordMuxSelect w j)
/-- Select the original false constant in the graph after difference selection. -/
private abbrev saZeroD (w : ℕ) : Fin (2*w+2+saND w) :=
  ⟨2*w+2,by dsimp only [saND,saNS,saNR,saNF,saNA,saNC]; omega⟩
/-- Route the padded magnitude difference, unsigned sum, and sign-disagreement bit into the
final multiplexer. -/
private abbrev saFinalMap (w : ℕ) : Fin (2*(w+1)+1) → Fin (2*w+2+saND w) := fun j =>
  if hj : j.val < w+1 then
    if hk : j.val < w then saDiff w ⟨j.val,hk⟩ else saZeroD w
  else if hk : j.val < 2*(w+1) then
    Fin.castLE (by dsimp only [saND,saNS,saNR,saNF]; omega) (saSum w ⟨j.val-(w+1),by omega⟩)
  else ⟨2*w+2+saNR w,by dsimp only [saND,saNS]; omega⟩
/-- Append the final multiplexer choosing between the magnitude difference and the unsigned sum. -/
private abbrev saGT (w : ℕ) : BooleanDAG (2*w+2) (saNT w) :=
  booleanDAGSplice (saGD w) (saFinalMap w) (booleanWordMuxDAG (w+1))
/-- Select a final magnitude output bit from the sum-versus-difference multiplexer. -/
private abbrev saMag (w : ℕ) (j : Fin (w+1)) : Fin (2*w+2+saNT w) :=
  booleanSpliceSource (saFinalMap w) (booleanWordMuxSelect (w+1) j)

/-- Appending forward conditional subtraction preserves every wire of the unsigned-adder graph. -/
private theorem sa_FA (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNA w)) :
    booleanDAGValue (saGF w) x (Fin.castLE (by dsimp only [saNF]; omega) j) =
      booleanDAGValue (saGA w) x j := boolean_dag_splice_prefix _ _ _ _ j

/-- Appending reverse conditional subtraction preserves every wire of the forward-subtraction
graph. -/
private theorem sa_RF (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNF w)) :
    booleanDAGValue (saGR w) x (Fin.castLE (by dsimp only [saNR]; omega) j) =
      booleanDAGValue (saGF w) x j := boolean_dag_splice_prefix _ _ _ _ j

/-- The completed sign-selection graph preserves every wire of the graph containing the sign
XOR. -/
private theorem sa_S1 (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+(saNR w+1))) :
    booleanDAGValue (saG3 w) x (Fin.castLE (by dsimp only [saNS]; omega) j) =
      booleanDAGValue (saG1 w) x j :=
  (sa_snoc_old (saG2 w) _ x (Fin.castLE (by omega) j)).trans (sa_snoc_old (saG1 w) _ x j)

/-- Appending the sign-selection nodes preserves all wires of the graph after reverse
subtraction. -/
private theorem sa_SR (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNR w)) :
    booleanDAGValue (saG3 w) x (Fin.castLE (by dsimp only [saNS]; omega) j) =
      booleanDAGValue (saGR w) x j :=
  (sa_S1 w x (Fin.castLE (by omega) j)).trans (sa_snoc_old (saGR w) _ x j)

/-- The completed sign-selection graph preserves all wires of the forward-subtraction graph. -/
private theorem sa_SF (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNF w)) :
    booleanDAGValue (saG3 w) x (Fin.castLE (by dsimp only [saNS,saNR]; omega) j) =
      booleanDAGValue (saGF w) x j :=
  (sa_SR w x (Fin.castLE (by dsimp only [saNR]; omega) j)).trans (sa_RF w x j)

/-- The completed sign-selection graph preserves all wires of the unsigned-adder graph. -/
private theorem sa_SA (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNA w)) :
    booleanDAGValue (saG3 w) x (Fin.castLE (by dsimp only [saNS,saNR,saNF]; omega) j) =
      booleanDAGValue (saGA w) x j :=
  (sa_SF w x (Fin.castLE (by dsimp only [saNF]; omega) j)).trans (sa_FA w x j)

/-- Appending the difference multiplexer preserves all wires of the sign-selection graph. -/
private theorem sa_DS (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNS w)) :
    booleanDAGValue (saGD w) x (Fin.castLE (by dsimp only [saND]; omega) j) =
      booleanDAGValue (saG3 w) x j := boolean_dag_splice_prefix _ _ _ _ j

/-- The difference-selection graph preserves all wires of the unsigned-adder graph. -/
private theorem sa_DA (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNA w)) :
    booleanDAGValue (saGD w) x (Fin.castLE (by dsimp only [saND,saNS,saNR,saNF]; omega) j) =
      booleanDAGValue (saGA w) x j :=
  (sa_DS w x (Fin.castLE (by dsimp only [saNS,saNR,saNF]; omega) j)).trans (sa_SA w x j)

/-- Appending the final magnitude multiplexer preserves all wires of the difference-selection
graph. -/
private theorem sa_TD (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saND w)) :
    booleanDAGValue (saGT w) x (Fin.castLE (by dsimp only [saNT]; omega) j) =
      booleanDAGValue (saGD w) x j := boolean_dag_splice_prefix _ _ _ _ j

/-- The final signed-addition graph preserves all wires of the sign-selection graph. -/
private theorem sa_TS (w : ℕ) (x : Reg (2*w+2)) (j : Fin (2*w+2+saNS w)) :
    booleanDAGValue (saGT w) x (Fin.castLE (by dsimp only [saNT,saND]; omega) j) =
      booleanDAGValue (saG3 w) x j :=
  (sa_TD w x (Fin.castLE (by dsimp only [saND]; omega) j)).trans (sa_DS w x j)

/-- The distinguished zero wire evaluates to false after difference selection. -/
private theorem sa_zero_D (w : ℕ) (x : Reg (2*w+2)) :
    booleanDAGValue (saGD w) x (saZeroD w) = false := by
  have hA : booleanDAGValue (saGA w) x
      (Fin.castLE (by dsimp only [saNA]; omega) (Fin.last (2*w+2))) = false := by
    rw [boolean_dag_splice_prefix]
    simp [saG0,sa_snoc_value,booleanNodeValue]
  exact (sa_DA w x (Fin.castLE (by dsimp only [saNA]; omega) (Fin.last (2*w+2)))).trans hA

/-- The raw magnitude input wires evaluate to the packed unsigned operand pair, independently of
the sign bits. -/
private theorem sa_raw_value {w n : ℕ} (g : BooleanDAG (2*w+2) n) (a b : Reg w) (sa sb : Bool)
    (j : Fin (2*w)) :
    booleanDAGValue g (booleanWordSignedAddInput w a b sa sb) ⟨j.val,by have := j.isLt; omega⟩ =
      booleanWordAdderInput w a b j := by
  have h := sa_input_value g (booleanWordSignedAddInput w a b sa sb) j.castSucc.castSucc
  simpa only [booleanWordSignedAddInput,booleanWordSignedMulInput,Fin.snoc_castSucc] using! h

/-- The unsigned-adder output wires evaluate to the unsigned sum word of the two input
magnitudes. -/
private theorem sa_sum_value (w : ℕ) (a b : Reg w) (sa sb : Bool) (j : Fin (w+1)) :
    booleanDAGValue (saGA w) (booleanWordSignedAddInput w a b sa sb) (saSum w j) =
      booleanWordAdderResult w a b j := by
  have h := boolean_dag_splice_value (saG0 w) (saRaw0 w) (booleanWordAdderDAG w)
    (booleanWordSignedAddInput w a b sa sb) (booleanWordAdderSelect w j)
  have he : (fun k => booleanDAGValue (saG0 w) (booleanWordSignedAddInput w a b sa sb) (saRaw0 w k)) =
      booleanWordAdderInput w a b := by
    funext k
    exact sa_raw_value _ _ _ _ _ k
  rw [he] at h
  exact h

/-- The forward-subtraction output wires evaluate to conditional subtraction of `b` from `a`. -/
private theorem sa_forward_value (w : ℕ) (a b : Reg w) (sa sb : Bool) (j : Fin (w+1)) :
    booleanDAGValue (saGF w) (booleanWordSignedAddInput w a b sa sb) (saF w j) =
      booleanWordCondSubResult w a b j := by
  have h := boolean_dag_splice_value (saGA w) (saRawA w) (booleanWordCondSubDAG w)
    (booleanWordSignedAddInput w a b sa sb) (booleanWordCondSubSelect w j)
  have he : (fun k => booleanDAGValue (saGA w) (booleanWordSignedAddInput w a b sa sb) (saRawA w k)) =
      booleanWordAdderInput w a b := by
    funext k
    exact sa_raw_value _ _ _ _ _ k
  rw [he] at h
  exact h

/-- The reversed source map evaluates to the packed unsigned operand pair in the order `b`, `a`. -/
private theorem sa_reverse_inputs (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    (fun k => booleanDAGValue (saGF w) (booleanWordSignedAddInput w a b sa sb) (saReverse w k)) =
      booleanWordAdderInput w b a := by
  funext j
  by_cases hj : j.val < w
  · simp only [saReverse,booleanWordAdderInput,dif_pos hj]
    have h := sa_raw_value (saGF w) a b sa sb (⟨w+j.val,by omega⟩ : Fin (2*w))
    have hnot : ¬w+j.val < w := by omega
    simpa only [booleanWordAdderInput,dif_neg hnot,Nat.add_sub_cancel_left] using! h
  · simp only [saReverse,booleanWordAdderInput,dif_neg hj]
    have hk : j.val-w < w := by have := j.isLt; omega
    have h := sa_raw_value (saGF w) a b sa sb (⟨j.val-w,by omega⟩ : Fin (2*w))
    simpa only [booleanWordAdderInput,dif_pos hk] using! h

/-- The reverse-subtraction output wires evaluate to conditional subtraction of `a` from `b`. -/
private theorem sa_reverse_value (w : ℕ) (a b : Reg w) (sa sb : Bool) (j : Fin (w+1)) :
    booleanDAGValue (saGR w) (booleanWordSignedAddInput w a b sa sb) (saR w j) =
      booleanWordCondSubResult w b a j := by
  have h := boolean_dag_splice_value (saGF w) (saReverse w) (booleanWordCondSubDAG w)
    (booleanWordSignedAddInput w a b sa sb) (booleanWordCondSubSelect w j)
  rw [sa_reverse_inputs] at h
  exact h

/-- The first sign input wire retains the supplied first sign bit in any graph of the
signed-addition input width. -/
private theorem sa_sign_a {w n : ℕ} (g : BooleanDAG (2*w+2) n) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue g (booleanWordSignedAddInput w a b sa sb) ⟨2*w,by omega⟩ = sa := by
  have h := sa_input_value g (booleanWordSignedAddInput w a b sa sb) (Fin.last (2*w)).castSucc
  simpa only [booleanWordSignedAddInput,booleanWordSignedMulInput,Fin.snoc_castSucc,Fin.snoc_last] using! h

/-- The second sign input wire retains the supplied second sign bit in any graph of the
signed-addition input width. -/
private theorem sa_sign_b {w n : ℕ} (g : BooleanDAG (2*w+2) n) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue g (booleanWordSignedAddInput w a b sa sb) ⟨2*w+1,by omega⟩ = sb := by
  have h := sa_input_value g (booleanWordSignedAddInput w a b sa sb) (Fin.last (2*w+1))
  simpa only [booleanWordSignedAddInput,booleanWordSignedMulInput,Fin.snoc_last] using! h

/-- The appended sign-disagreement wire evaluates to the XOR of the input signs. -/
private theorem sa_xor_value (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue (saG1 w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w,by omega⟩ = (sa ^^ sb) := by
  have hn : ¬2*w+2+saNR w < 2*w+2+saNR w := by omega
  rw [saG1,sa_snoc_value,dif_neg hn]
  change (booleanDAGValue (saGR w) (booleanWordSignedAddInput w a b sa sb) ⟨2*w,by omega⟩ ^^
    booleanDAGValue (saGR w) (booleanWordSignedAddInput w a b sa sb) ⟨2*w+1,by omega⟩) = _
  rw [sa_sign_a,sa_sign_b]

/-- The sign-choice guard is the conjunction of sign disagreement and the forward-subtraction
comparison flag. -/
private theorem sa_choose_value (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue (saG2 w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w+1,by omega⟩ =
      ((sa ^^ sb) && booleanWordCondSubResult w a b (Fin.last w)) := by
  have hn : ¬2*w+2+saNR w+1 < 2*w+2+(saNR w+1) := by omega
  rw [saG2,sa_snoc_value,dif_neg hn]
  change (booleanDAGValue (saG1 w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w,by omega⟩ &&
    booleanDAGValue (saG1 w) (booleanWordSignedAddInput w a b sa sb)
      (Fin.castLE (by omega) (saFlag w))) = _
  rw [sa_xor_value,sa_snoc_old,sa_RF,sa_forward_value]

/-- The sign-selection graph chooses the sign of the operand with larger magnitude, choosing the
first operand on ties. -/
private theorem sa_sign_S (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue (saG3 w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w+2,by dsimp only [saNS]; omega⟩ =
      if booleanWordLSBValue w b ≤ booleanWordLSBValue w a then sa else sb := by
  have hn : ¬2*w+2+saNR w+2 < 2*w+2+(saNR w+1+1) := by omega
  rw [saG3,sa_snoc_value,dif_neg hn]
  change (booleanDAGValue (saG2 w) (booleanWordSignedAddInput w a b sa sb) ⟨2*w+1,by omega⟩ ^^
    booleanDAGValue (saG2 w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w+1,by omega⟩) = _
  rw [sa_sign_b,sa_choose_value,mux_bool,(boolean_word_cond_sub_value w a b).1]
  by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a <;> simp [h]

/-- The sign-disagreement wire still evaluates to the input-sign XOR after appending the
difference multiplexer. -/
private theorem sa_xor_D (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanDAGValue (saGD w) (booleanWordSignedAddInput w a b sa sb)
      ⟨2*w+2+saNR w,by dsimp only [saND,saNS]; omega⟩ = (sa ^^ sb) := by
  have h := sa_DS w (booleanWordSignedAddInput w a b sa sb)
    (Fin.castLE (by dsimp only [saNS]; omega)
      (⟨2*w+2+saNR w,by omega⟩ : Fin (2*w+2+(saNR w+1))))
  exact h.trans
      ((sa_S1 w (booleanWordSignedAddInput w a b sa sb) _).trans (sa_xor_value w a b sa sb))

/-- The difference-multiplexer source map evaluates to the two subtraction magnitude words and
the forward comparison flag. -/
private theorem sa_diff_inputs (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    (fun j => booleanDAGValue (saG3 w) (booleanWordSignedAddInput w a b sa sb) (saDiffMap w j)) =
      booleanWordMuxInput w (fun j => booleanWordCondSubResult w a b j.castSucc)
        (fun j => booleanWordCondSubResult w b a j.castSucc)
        (booleanWordCondSubResult w a b (Fin.last w)) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*w < w := by omega
    simp only [saDiffMap,Fin.val_last,dif_neg hn,dif_neg (Nat.lt_irrefl (2*w)),
      booleanWordMuxInput,Fin.snoc_last]
    exact (sa_SF w (booleanWordSignedAddInput w a b sa sb) (saF w (Fin.last w))).trans
      (sa_forward_value w a b sa sb (Fin.last w))
  · rw [booleanWordMuxInput,Fin.snoc_castSucc]
    by_cases hk : k.val < w
    · simp only [saDiffMap,Fin.val_castSucc,booleanWordAdderInput,dif_pos hk]
      exact (sa_SF w (booleanWordSignedAddInput w a b sa sb) (saF w (Fin.castSucc ⟨k.val,hk⟩))).trans
        (sa_forward_value w a b sa sb (Fin.castSucc ⟨k.val,hk⟩))
    · simp only [saDiffMap,Fin.val_castSucc,booleanWordAdderInput,dif_neg hk,dif_pos k.isLt]
      exact (sa_SR w (booleanWordSignedAddInput w a b sa sb)
        (saR w (Fin.castSucc ⟨k.val-w,by have := k.isLt; omega⟩))).trans
        (sa_reverse_value w a b sa sb (Fin.castSucc ⟨k.val-w,by have := k.isLt; omega⟩))

/-- Evaluate the selected magnitude-difference wires in the difference-selection graph. -/
private def saDiffWord (w : ℕ) (a b : Reg w) (sa sb : Bool) : Reg w := fun j =>
  booleanDAGValue (saGD w) (booleanWordSignedAddInput w a b sa sb) (saDiff w j)

/-- The selected difference word is the multiplexer result for the two conditional-subtraction
magnitudes and the forward comparison flag. -/
private theorem sa_diff_word (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    saDiffWord w a b sa sb =
      booleanWordMuxResult w (fun j => booleanWordCondSubResult w a b j.castSucc)
        (fun j => booleanWordCondSubResult w b a j.castSucc)
        (booleanWordCondSubResult w a b (Fin.last w)) := by
  funext j
  have h := boolean_dag_splice_value (saG3 w) (saDiffMap w) (booleanWordMuxDAG w)
    (booleanWordSignedAddInput w a b sa sb) (booleanWordMuxSelect w j)
  rw [sa_diff_inputs] at h
  exact h

/-- The unsigned value of a multiplexer result is the value of its first word when the control
is true, and of its second word otherwise. -/
private theorem sa_mux_numeric (w : ℕ) (a b : Reg w) (c : Bool) :
    booleanWordLSBValue w (booleanWordMuxResult w a b c) =
      if c then booleanWordLSBValue w a else booleanWordLSBValue w b := by
  rw [boolean_word_mux_value]
  cases c <;> rfl

/-- The selected difference word represents the larger input magnitude minus the smaller input
magnitude. -/
private theorem sa_diff_numeric (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordLSBValue w (saDiffWord w a b sa sb) =
      if booleanWordLSBValue w b ≤ booleanWordLSBValue w a then
        booleanWordLSBValue w a - booleanWordLSBValue w b
      else booleanWordLSBValue w b - booleanWordLSBValue w a := by
  rw [sa_diff_word,sa_mux_numeric,(boolean_word_cond_sub_value w a b).1,
    (boolean_word_cond_sub_value w a b).2,(boolean_word_cond_sub_value w b a).2]
  by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a
  · simp [h]
  · have hrev : booleanWordLSBValue w a ≤ booleanWordLSBValue w b := by omega
    simp [h,hrev]

/-- The final multiplexer receives the zero-padded magnitude difference, the unsigned sum, and
the XOR of the input signs. -/
private theorem sa_final_inputs (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    (fun j => booleanDAGValue (saGD w) (booleanWordSignedAddInput w a b sa sb) (saFinalMap w j)) =
      booleanWordMuxInput (w+1) (Fin.snoc (saDiffWord w a b sa sb) false)
        (booleanWordAdderResult w a b) (sa ^^ sb) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*(w+1) < w+1 := by omega
    simp only [saFinalMap,Fin.val_last,dif_neg hn,dif_neg (Nat.lt_irrefl (2*(w+1))),
      booleanWordMuxInput,Fin.snoc_last]
    exact sa_xor_D w a b sa sb
  · rw [booleanWordMuxInput,Fin.snoc_castSucc]
    by_cases hk : k.val < w+1
    · simp only [saFinalMap,Fin.val_castSucc,booleanWordAdderInput,dif_pos hk]
      have hbit (t : Fin (w+1)) :
          booleanDAGValue (saGD w) (booleanWordSignedAddInput w a b sa sb)
            (if ht : t.val < w then saDiff w ⟨t.val,ht⟩ else saZeroD w) =
            (Fin.snoc (saDiffWord w a b sa sb) false : Reg (w+1)) t := by
        refine Fin.lastCases ?_ (fun r => ?_) t
        · simp only [Fin.val_last,dif_neg (Nat.lt_irrefl w),Fin.snoc_last]
          exact sa_zero_D w _
        · simp only [Fin.val_castSucc,dif_pos r.isLt,Fin.snoc_castSucc,saDiffWord]
      exact hbit ⟨k.val,hk⟩
    · simp only [saFinalMap,Fin.val_castSucc,booleanWordAdderInput,dif_neg hk,dif_pos k.isLt]
      exact (sa_DA w (booleanWordSignedAddInput w a b sa sb)
        (saSum w ⟨k.val-(w+1),by have := k.isLt; omega⟩)).trans
        (sa_sum_value w a b sa sb ⟨k.val-(w+1),by have := k.isLt; omega⟩)

/-- The final magnitude word selects the padded difference for unequal signs and the unsigned
sum for equal signs. -/
private theorem sa_magnitude_word (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedAddMagnitude w a b sa sb =
      booleanWordMuxResult (w+1) (Fin.snoc (saDiffWord w a b sa sb) false)
        (booleanWordAdderResult w a b) (sa ^^ sb) := by
  funext j
  simp only [booleanWordSignedAddMagnitude,booleanWordSignedAddResult,booleanWordSignedAddProgram,
    Fin.val_castSucc,dif_pos j.isLt]
  have h := boolean_dag_splice_value (saGD w) (saFinalMap w) (booleanWordMuxDAG (w+1))
    (booleanWordSignedAddInput w a b sa sb) (booleanWordMuxSelect (w+1) j)
  rw [sa_final_inputs] at h
  exact h

/-- Appending a false most significant bit preserves the unsigned value of a word. -/
private theorem sa_pad_value (w : ℕ) (a : Reg w) :
    booleanWordLSBValue (w+1) (Fin.snoc a false) = booleanWordLSBValue w a := by
  simp [boolean_word_lsb_value,Fin.sum_univ_castSucc]

/-- The result magnitude equals the sum of input magnitudes for equal signs and their absolute
difference for unequal signs. -/
private theorem sa_magnitude_value (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordLSBValue (w+1) (booleanWordSignedAddMagnitude w a b sa sb) =
      if sa=sb then booleanWordLSBValue w a+booleanWordLSBValue w b else
      if booleanWordLSBValue w b ≤ booleanWordLSBValue w a then
        booleanWordLSBValue w a-booleanWordLSBValue w b
      else booleanWordLSBValue w b-booleanWordLSBValue w a := by
  rw [sa_magnitude_word,sa_mux_numeric,sa_pad_value,boolean_word_adder_value,sa_diff_numeric]
  cases sa <;> cases sb <;> simp

/-- The signed-addition result uses the sign of the operand with larger magnitude, choosing the
first operand on ties. -/
private theorem sa_sign_value (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedAddSign w a b sa sb =
      if booleanWordLSBValue w b ≤ booleanWordLSBValue w a then sa else sb := by
  simp only [booleanWordSignedAddSign,booleanWordSignedAddResult,booleanWordSignedAddProgram,
    Fin.val_last,dif_neg (Nat.lt_irrefl (w+1))]
  exact (sa_TS w (booleanWordSignedAddInput w a b sa sb)
    (⟨2*w+2+saNR w+2,by dsimp only [saNS]; omega⟩ : Fin (2*w+2+saNS w))).trans
    (sa_sign_S w a b sa sb)

/-- The signed adder has a false zero wire and chooses the sign of the operand with larger
magnitude, with ties favoring the first. Its magnitude is the sum for equal signs and the
absolute difference otherwise, and is at most the sum of input magnitudes. -/
theorem boolean_word_signed_add_magnitude (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) :
    let A := booleanWordLSBValue w a
    let B := booleanWordLSBValue w b
    let p := booleanWordSignedAddProgram w
    booleanDAGValue p.graph (booleanWordSignedAddInput w a b negativeA negativeB) p.zero = false ∧
      booleanWordSignedAddSign w a b negativeA negativeB =
        (if B ≤ A then negativeA else negativeB) ∧
      booleanWordLSBValue (w+1) (booleanWordSignedAddMagnitude w a b negativeA negativeB) =
        (if negativeA = negativeB then A+B else if B ≤ A then A-B else B-A) ∧
      booleanWordLSBValue (w+1) (booleanWordSignedAddMagnitude w a b negativeA negativeB) ≤ A+B := by
  (try dsimp only)
  refine ⟨?_,sa_sign_value w a b negativeA negativeB,sa_magnitude_value w a b negativeA negativeB,?_⟩
  · exact (sa_TD w (booleanWordSignedAddInput w a b negativeA negativeB) (saZeroD w)).trans
      (sa_zero_D w _)
  · rw [sa_magnitude_value]
    split_ifs <;> omega

/-- The integer decoded from the signed-addition output equals the sum of the integers decoded
from its two sign-magnitude inputs. -/
theorem boolean_word_signed_add_value (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) :
    booleanWordSignedAddValue w a b negativeA negativeB =
      booleanWordSignedValue w a negativeA + booleanWordSignedValue w b negativeB := by
  dsimp only [booleanWordSignedAddValue,booleanWordSignedValue]
  rw [sa_sign_value,sa_magnitude_value]
  cases negativeA <;> cases negativeB <;>
    by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a <;>
    simp [h] <;> omega

/-- The signed adder has `31*w+12` nodes and is legal, with at most `931*w+362` compiled gates,
zero oracle queries, and `34*w+16` total wires. Its gate count equals its reflection-step
count. -/
theorem boolean_word_signed_add_resources (w : ℕ) :
    let p := booleanWordSignedAddProgram w
    let gs := booleanDAGSteps p.graph p.output
    p.nodes = 31*w+12 ∧ reflectionLegal gs ∧
      gs.length ≤ 931*w+362 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (2*w+2)+p.nodes+(w+2) = 34*w+16 := by
  let p := booleanWordSignedAddProgram w
  have hn : p.nodes = 31*w+12 := by
    change (1+(5*w+1)+(7*w+1+3*w+1)+(7*w+1+3*w+1)+1+1+1+3*w+3*(w+1)) = _
    omega
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,?_,hq,hc,?_⟩
  · change (booleanDAGSteps p.graph p.output).length ≤ _
    omega
  change (2*w+2)+p.nodes+(w+2) = _
  omega

/-- On a basis state with initialized workspace, the compiled signed adder XORs its
sign-magnitude result into the target and restores the workspace. -/
theorem boolean_word_signed_add_basis (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool)
    (y : Reg (w+2)) :
    let p := booleanWordSignedAddProgram w
    Run (1 : Matrix (Reg ((2*w+2)+p.nodes+(w+2))) (Reg ((2*w+2)+p.nodes+(w+2))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput (2*w+2) p.nodes (w+2)
        (booleanWordSignedAddInput w a b negativeA negativeB) y)) =
      Ket (booleanDAGInput (2*w+2) p.nodes (w+2)
        (booleanWordSignedAddInput w a b negativeA negativeB)
        (fun j => y j ^^ booleanWordSignedAddResult w a b negativeA negativeB j)) :=
  boolean_dag_basis _ _ _ _

/-- Packing the two magnitude views and the two sign bits reconstructs the signed arithmetic
input register. -/
private theorem sa_input_views (w : ℕ) (x : Reg (2*w+2)) :
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

/-- On an arbitrary embedded state, the compiled signed adder coherently XORs each
sign-magnitude sum into its target and restores the workspace. -/
theorem boolean_word_signed_add_coherent (w : ℕ) (ψ : QState (Reg (2*w+2) × Reg (w+2))) :
    let p := booleanWordSignedAddProgram w
    Run (1 : Matrix (Reg ((2*w+2)+p.nodes+(w+2))) (Reg ((2*w+2)+p.nodes+(w+2))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed (2*w+2) p.nodes (w+2) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w+2) p.nodes (w+2) xy.1
        (fun j => xy.2 j ^^ booleanWordSignedAddResult w
          (booleanWordSignedMulLeft w xy.1) (booleanWordSignedMulRight w xy.1)
          (xy.1 ((Fin.last (2*w)).castSucc)) (xy.1 (Fin.last (2*w+1))) j)) := by
  (try dsimp only)
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordSignedAddResult,booleanWordSignedAddInput,sa_input_views]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
