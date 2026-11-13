/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGCoarseBranchData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGBilinearQuotient
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider

/-!
# Correctness of the coarse frequency branch circuit

This module verifies `booleanWordCoarseProgram`, which selects a special entry-dependent
quotient when the frequency word is zero and otherwise returns the bilinear quotient. It proves
the zero-frequency flag and the mask-and-divisor formula for the special branch.

The Boolean graph is compiled into a reversible circuit as in [NielsenChuang2010], with explicit
resource bounds and coherent output XOR semantics.

## Main statements

* `boolean_zero_detail_value`: gives the integer quotient for the special branch.
* `boolean_word_coarse_value`: proves the frequency-dependent result.
* `boolean_word_coarse_resources`: bounds nodes, local gates, and total register width.
* `boolean_word_coarse_coherent`: proves the action on arbitrary embedded states.

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

/-- Decodes a word with w magnitude bits and one sign bit as an integer. -/
private def cbDecode (w : ℕ) (a : Reg (w+1)) : ℤ :=
  booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w))

/-- Appending a Boolean node preserves earlier values and places the new node's value at the
final coordinate. -/
private theorem cb_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Appending one Boolean node leaves all previously available graph coordinates unchanged. -/
private theorem cb_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [cb_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

/-- Every original input coordinate retains its value under Boolean graph evaluation. -/
private theorem cb_input_value {m n : ℕ} (g : BooleanDAG m n) (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m n) j)) = x j
    simpa only [booleanDAGValue,Fin.lastCases_castSucc] using! ih

/-- A selected output of an appended word program evaluates as that program applied to the
selected preceding graph values. -/
private theorem cb_append_value {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin o) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x ((booleanDAGAppendWord g r h).output j) =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) (h.output j) :=
  boolean_dag_splice_value _ _ _ _ _

/-- The designated zero coordinate of an appended program evaluates as its zero coordinate on
the selected preceding graph values. -/
private theorem cb_append_zero {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (booleanDAGAppendWord g r h).zero =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) h.zero :=
  boolean_dag_splice_value _ _ _ _ _

/-- Appending a word program preserves every existing graph-coordinate value. -/
private theorem cb_append_old {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin (M+K)) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (Fin.castLE (by dsimp [booleanDAGAppendWord]; omega) j) =
      booleanDAGValue g x j := boolean_dag_splice_prefix _ _ _ _ _

/-- The XOR-and-conjunction expression for the special-branch mask equals matching two bit pairs
and requiring the first pair to be nonzero. -/
private theorem zd_mask_bool (a b c d : Bool) :
    (((! (a ^^ c)) && (! (b ^^ d))) && ((a ^^ b) ^^ (a && b))) =
      (((a == c) && (b == d)) && (a || b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The empty Boolean graph evaluates each input coordinate to the original input bit. -/
private theorem cb_nil_value {m : ℕ} (x : Reg m) (j : Fin m) :
    booleanDAGValue (.nil : BooleanDAG m 0) x j = x j := rfl
/-- Extends a four-bit entry register by a final false bit. -/
private def zdInput (e : Reg 4) : Reg 5 := fun j => if h : j.val < 4 then e ⟨j.val,h⟩ else false

/-- Appending false with `Fin.snoc` gives the explicit five-bit entry layout `zdInput`. -/
private theorem zd_input_eq (e : Reg 4) : Fin.snoc e false = zdInput e := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change (Fin.snoc e false : Reg 5) (Fin.last 4) = false
    simp only [Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    simp only [zdInput,Fin.val_castSucc,dif_pos k.isLt]

/-- Coordinate 13 of the entry-flag graph evaluates to `booleanZeroDetailMask`. -/
private theorem zd_mask (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨13,by omega⟩ = booleanZeroDetailMask e := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]
  simpa only [booleanZeroDetailMask,Bool.xor_assoc] using! (zd_mask_bool (e 0) (e 1) (e 2) (e 3))

/-- Coordinate 11 of the entry-flag graph is the conjunction of the first two entry bits. -/
private theorem zd_row11 (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨11,by omega⟩ = (e 0 && e 1) := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

/-- Coordinate 14 of the entry-flag graph is the negation of the conjunction of the first two
entry bits. -/
private theorem zd_not11 (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨14,by omega⟩ = !(e 0 && e 1) := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

/-- Coordinate 15 of the entry-flag graph evaluates to true. -/
private theorem zd_one (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨15,by omega⟩ = true := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

/-- Coordinate four of the entry-flag graph evaluates to false when the input is the four entry
bits followed by false. -/
private theorem zd_false (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨4,by omega⟩ = false := by
  exact (cb_input_value booleanZeroDetailFlags (Fin.snoc e false) (Fin.last 4)).trans
      (by simp only [Fin.snoc_last])

/-- Selects a V-bit numerator with the mask wire at bit b and the supplied false-input wire
elsewhere. -/
private abbrev zdNum (V b : ℕ) : Fin V → Fin 16 :=
    fun j => if j.val=b then ⟨13,by omega⟩ else ⟨4,by omega⟩
/-- Selects the V-bit divisor word using the row-conjunction, its negation, a true wire, and the
supplied false-input wire. -/
private abbrev zdDen (V : ℕ) : Fin V → Fin 16 := fun j =>
  if j.val=2 then ⟨14,by omega⟩ else if j.val=3 then ⟨15,by omega⟩
  else if j.val=4 then ⟨11,by omega⟩ else ⟨4,by omega⟩
/-- Selects the numerator, divisor, and false sign wire for the special-branch signed division. -/
private abbrev zdInputs (V b : ℕ) : Fin (2*V+1) → Fin 16 := fun j =>
  if hj : j.val < V then zdNum V b ⟨j.val,hj⟩
  else if hk : j.val < 2*V then zdDen V ⟨j.val-V,by omega⟩ else ⟨4,by omega⟩

/-- The selected special-branch numerator has its mask bit at position b and false at every
other position. -/
private theorem zd_num_word (V b : ℕ) (e : Reg 4) :
    (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdNum V b j)) =
      (fun j => if j.val=b then booleanZeroDetailMask e else false) := by
  funext j
  by_cases h : j.val=b
  · simp only [zdNum,if_pos h]
    exact zd_mask e
  · simp only [zdNum,if_neg h]
    exact zd_false e

/-- For b < V, a word with a single possibly true bit at position b has value 2^b when that bit
is true and zero otherwise. -/
private theorem zd_num_nat (V b : ℕ) (hb : b < V) (bit : Bool) :
    booleanWordLSBValue V (fun j => if j.val=b then bit else false) = if bit then 2^b else 0 := by
  have he (j : Fin V) : (j.val=b) ↔ j=⟨b,hb⟩ := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  cases bit <;> simp [boolean_word_lsb_value,he]

/-- Copies the available low bits of a word into a target width and fills any additional high
bits with false. -/
private def zdExtend (k V : ℕ) (a : Reg k) : Reg V := fun j =>
  if hj : j.val < k then a ⟨j.val,hj⟩ else false

/-- Extending an unsigned word to a width at least as large by false high bits preserves its
value. -/
private theorem zd_extend_value (k V : ℕ) (hk : k ≤ V) (a : Reg k) :
    booleanWordLSBValue V (zdExtend k V a) = booleanWordLSBValue k a := by
  rcases Nat.exists_eq_add_of_le hk with ⟨r,rfl⟩
  rw [boolean_word_lsb_value,Fin.sum_univ_add,boolean_word_lsb_value]
  have hhead (j : Fin k) : zdExtend k (k+r) a (Fin.castAdd r j) = a j := by
    simp [zdExtend,j.isLt]
  have htail (j : Fin r) : zdExtend k (k+r) a (Fin.natAdd k j) = false := by
    have hn : ¬k+j.val < k := by omega
    simp [zdExtend,hn]
  simp only [hhead,htail,Fin.val_castAdd,Bool.false_eq_true,ite_false,zero_mul,Finset.sum_const_zero,add_zero]
/-- The five-bit divisor word representing 24 when r is true and 12 when r is false. -/
private def zdDen5 (r : Bool) : Reg 5 := fun j =>
  if j.val=2 then !r else if j.val=3 then true else if j.val=4 then r else false

/-- The selected divisor word equals the five-bit divisor layout extended with false high bits. -/
private theorem zd_den_word (V : ℕ) (e : Reg 4) :
    (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) =
      zdExtend 5 V (zdDen5 (e 0 && e 1)) := by
  have hv : (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) =
      (fun j => if j.val=2 then !(e 0 && e 1) else if j.val=3 then true
        else if j.val=4 then (e 0 && e 1) else false) := by
    funext j
    by_cases h2 : j.val=2
    · simp only [zdDen,if_pos h2]
      exact zd_not11 e
    · by_cases h3 : j.val=3
      · simp only [zdDen,if_neg h2,if_pos h3]
        exact zd_one e
      · by_cases h4 : j.val=4
        · simp only [zdDen,if_neg h2,if_neg h3,if_pos h4]
          exact zd_row11 e
        · simp only [zdDen,if_neg h2,if_neg h3,if_neg h4]
          exact zd_false e
  rw [hv]
  funext j
  dsimp only [zdExtend,zdDen5]
  split_ifs <;> first | rfl | omega

/-- For V ≥ 5, the selected divisor word has unsigned value `booleanZeroDetailDivisor e`. -/
private theorem zd_den_nat (V : ℕ) (hV : 5 ≤ V) (e : Reg 4) :
    booleanWordLSBValue V (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) =
      booleanZeroDetailDivisor e := by
  rw [zd_den_word,zd_extend_value 5 V hV]
  unfold booleanZeroDetailDivisor
  cases h :
      e 0 && e 1 <;> norm_num [zdDen5,boolean_word_lsb_value,Fin.sum_univ_succ,Fin.sum_univ_zero,h]

/-- Evaluating the special-branch division selections gives the signed division input formed
from the selected numerator and divisor with false sign. -/
private theorem zd_inputs_value (V b : ℕ) (e : Reg 4) :
    (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdInputs V b j)) =
      booleanWordSignedDivInput V
        (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdNum V b j))
        (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) false := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*V < V := by omega
    simp only [zdInputs,Fin.val_last,dif_neg hn,dif_neg (Nat.lt_irrefl _),
      booleanWordSignedDivInput,Fin.snoc_last]
    exact zd_false e
  · rw [booleanWordSignedDivInput,Fin.snoc_castSucc]
    by_cases hk : k.val < V
    · simp only [zdInputs,Fin.val_castSucc,booleanWordAdderInput,dif_pos hk]
    · simp only [zdInputs,Fin.val_castSucc,booleanWordAdderInput,dif_neg hk,dif_pos k.isLt]

/-- The special-branch result word equals the signed division result for its selected numerator
and divisor, with a false numerator sign. -/
private theorem zd_result_word (V b : ℕ) (hb : b < V) (hV : 5 ≤ V) (e : Reg 4) :
    booleanZeroDetailResult V b hb hV e = booleanWordSignedDivResult V
      (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdNum V b j))
      (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) false := by
  funext j
  change booleanDAGValue (booleanDAGAppendWord booleanZeroDetailFlags (zdInputs V b)
    (booleanWordSignedDivProgram V)).graph (Fin.snoc e false)
    ((booleanDAGAppendWord booleanZeroDetailFlags (zdInputs V b) (booleanWordSignedDivProgram V)).output j) = _
  rw [cb_append_value,zd_inputs_value]
  rfl

/-- For b < V and V ≥ 5, the special-branch value is the integer quotient of the masked power
2^b by the entry-dependent divisor. -/
theorem boolean_zero_detail_value (V b : ℕ) (hb : b < V) (hV : 5 ≤ V) (e : Reg 4) :
    booleanZeroDetailValue V b hb hV e =
      (if booleanZeroDetailMask e then (2 : ℤ)^b else 0) / (booleanZeroDetailDivisor e : ℤ) := by
  dsimp only [booleanZeroDetailValue]
  rw [zd_result_word]
  change booleanWordSignedDivValue V _ _ false = _
  rw [boolean_word_signed_div_value]
  simp only [booleanWordSignedValue,Bool.false_eq_true,ite_false]
  rw [zd_num_word,zd_num_nat V b hb,zd_den_nat V hV]
  by_cases h : booleanZeroDetailMask e <;> simp [h]

/-- The full coarse-branch input width, including coefficients, frequency bits, and four entry
bits. -/
private abbrev cbM (n w : ℕ) := booleanWordCoarseInputWidth n w
/-- The magnitude width used by the bilinear quotient and special branch. -/
private abbrev cbV (w b d : ℕ) := booleanWordBilinearQuotientWidth w b d
/-- The bilinear quotient program used for the nonzero-frequency branch. -/
private abbrev cbOld (w b d : ℕ) := booleanWordBilinearQuotientProgram w b d
/-- Selects the coefficient bits from the beginning of the coarse-branch input register. -/
private abbrev cbRaw (n w : ℕ) : Fin (16*(w+1)) → Fin (cbM n w+0) :=
  fun j => ⟨j.val,by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
/-- The initial coarse-branch graph stage evaluating the bilinear quotient on the coefficient
inputs. -/
private abbrev cbP (n w b d : ℕ) :=
    booleanDAGAppendWord (.nil : BooleanDAG (cbM n w) 0) (cbRaw n w) (cbOld w b d)
/-- Selects zero bits and frequency bits as the inputs of the frequency nonzero test. -/
private abbrev cbNZI (n w b d : ℕ) : Fin (2*(2*n)) → Fin (cbM n w+(cbP n w b d).nodes) := fun j =>
  if hj : j.val < 2*n then (cbP n w b d).zero else
    ⟨16*(w+1)+(j.val-2*n),by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
/-- The node count after appending the frequency nonzero-test graph. -/
private abbrev cbNNZ (n w b d : ℕ) := (cbP n w b d).nodes+(3*(2*n)+1)
/-- The graph formed by appending the frequency nonzero test to the bilinear quotient stage. -/
private abbrev cbGNZ (n w b d : ℕ) := booleanDAGSplice (cbP n w b d).graph (cbNZI n w b d)
  (booleanWordNonzeroPrefix (2*n) (2*n) (Nat.le_refl _))
/-- The wire holding the result of the frequency nonzero test. -/
private abbrev cbNZ (n w b d : ℕ) : Fin (cbM n w+cbNNZ n w b d) :=
  booleanSpliceSource (cbNZI n w b d) (⟨2*(2*n)+3*(2*n),by omega⟩ : Fin (2*(2*n)+(3*(2*n)+1)))
/-- The graph obtained by negating the frequency nonzero flag to produce a zero-frequency flag. -/
private abbrev cbGC (n w b d : ℕ) := (cbGNZ n w b d).snoc (.neg (cbNZ n w b d))
/-- The node count after adding the zero-frequency flag. -/
private abbrev cbNC (n w b d : ℕ) := cbNNZ n w b d+1
/-- The earlier designated zero wire included into the graph containing the zero-frequency flag. -/
private abbrev cbZeroC (n w b d : ℕ) : Fin (cbM n w+cbNC n w b d) :=
  Fin.castLE (by (try dsimp only [cbNC,cbNNZ]); omega) (cbP n w b d).zero
/-- The wire holding the zero-frequency flag before appending the special-branch program. -/
private abbrev cbFlagC (n w b d : ℕ) : Fin (cbM n w+cbNC n w b d) :=
  ⟨cbM n w+cbNNZ n w b d,by dsimp only [cbNC]; omega⟩
/-- Selects the four entry bits and the designated zero wire as inputs to the special-branch
program. -/
private abbrev cbZI (n w b d : ℕ) : Fin 5 → Fin (cbM n w+cbNC n w b d) := fun j =>
  if hj : j.val < 4 then ⟨16*(w+1)+2*n+j.val,by dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
  else cbZeroC n w b d
/-- The special-branch division program at the common quotient width and numerator shift b. -/
private abbrev cbDetail (w b d : ℕ) := booleanZeroDetailProgram (cbV w b d) b
  (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
  (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
/-- The graph stage obtained by appending the special-branch program after the frequency test. -/
private abbrev cbZ (n w b d : ℕ) :=
    booleanDAGAppendWord (cbGC n w b d) (cbZI n w b d) (cbDetail w b d)
/-- Selects the retained bilinear quotient output within the graph containing the special-branch
result. -/
private abbrev cbOldZ (n w b d : ℕ) : Fin (cbV w b d+3) → Fin (cbM n w+(cbZ n w b d).nodes) := fun j =>
  Fin.castLE (by
    change cbM n w+(cbP n w b d).nodes ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes)
    dsimp only [cbNC,cbNNZ]
    omega) ((cbP n w b d).output j)
/-- The zero-frequency flag wire included into the graph containing the special-branch result. -/
private abbrev cbFlagZ (n w b d : ℕ) : Fin (cbM n w+(cbZ n w b d).nodes) :=
  Fin.castLE (by change cbM n w+cbNC n w b d ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes); omega)
    (cbFlagC n w b d)
/-- Selects the special-branch result, bilinear quotient result, and zero-frequency flag as
multiplexer inputs. -/
private abbrev cbMI (n w b d : ℕ) : Fin (2*(cbV w b d+3)+1) → Fin (cbM n w+(cbZ n w b d).nodes) := fun j =>
  if hj : j.val < cbV w b d+3 then (cbZ n w b d).output ⟨j.val,hj⟩
  else if hk : j.val < 2*(cbV w b d+3) then cbOldZ n w b d ⟨j.val-(cbV w b d+3),by omega⟩
  else cbFlagZ n w b d
/-- The graph obtained by appending the output multiplexer to the two branch computations. -/
private abbrev cbGT (n w b d : ℕ) := booleanDAGSplice (cbZ n w b d).graph (cbMI n w b d)
  (booleanWordMuxDAG (cbV w b d+3))

/-- The initial coefficient-wire selections evaluate to `booleanWordCoarseCoefficients`. -/
private theorem cb_initial_inputs (n w : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (.nil : BooleanDAG (cbM n w) 0) x (cbRaw n w j)) = booleanWordCoarseCoefficients n w x := rfl

/-- The first graph stage produces the bilinear quotient result for the coefficient portion of
the coarse input. -/
private theorem cb_old_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbP n w b d).graph x ((cbP n w b d).output j)) =
      booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x) := by
  funext j
  rw [cb_append_value,cb_initial_inputs]
  rfl

/-- The designated zero wire of the first bilinear quotient stage evaluates to false. -/
private theorem cb_old_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbP n w b d).graph x (cbP n w b d).zero = false := by
  rw [cb_append_zero,cb_initial_inputs]
  exact boolean_word_bilinear_quotient_zero _ _ _ _

/-- Appending the frequency test and its negation preserves every coordinate of the initial
bilinear quotient graph. -/
private theorem cb_C_old (n w b d : ℕ) (x : Reg (cbM n w)) (j : Fin (cbM n w+(cbP n w b d).nodes)) :
    booleanDAGValue (cbGC n w b d) x
      (Fin.castLE (by omega) j) = booleanDAGValue (cbP n w b d).graph x j := by
  exact (cb_snoc_old (cbGNZ n w b d) _ x
    (Fin.castLE (by omega) j)).trans
    (boolean_dag_splice_prefix _ _ _ _ _)

/-- The retained designated zero wire remains false after constructing the zero-frequency flag. -/
private theorem cb_C_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbGC n w b d) x (cbZeroC n w b d) = false :=
  (cb_C_old n w b d x (cbP n w b d).zero).trans (cb_old_zero n w b d x)

/-- The right input word selected for the frequency nonzero test is the frequency portion of the
coarse input. -/
private theorem cb_nz_right (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanWordAdderRight (2*n) (fun j => booleanDAGValue (cbP n w b d).graph x (cbNZI n w b d j)) =
      booleanWordCoarseFrequency n w x := by
  funext j
  have hn : ¬2*n+j.val < 2*n := by omega
  simp only [booleanWordAdderRight,cbNZI,dif_neg hn,Nat.add_sub_cancel_left]
  exact cb_input_value (cbP n w b d).graph x
    ⟨16*(w+1)+j.val,by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩

/-- The computed frequency flag is true exactly when the unsigned frequency word has value zero. -/
private theorem cb_C_flag (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbGC n w b d) x (cbFlagC n w b d) =
      decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0) := by
  rw [cb_snoc_value]
  have hn : ¬cbM n w+cbNNZ n w b d < cbM n w+cbNNZ n w b d := by omega
  rw [dif_neg hn]
  change (!(booleanDAGValue (cbGNZ n w b d) x (cbNZ n w b d))) = _
  rw [boolean_dag_splice_value]
  have h := (boolean_word_div_prefix (2*n) 0 (by omega)
    (fun j => booleanDAGValue (cbP n w b d).graph x (cbNZI n w b d j))).2.1
  dsimp only [booleanWordDivPrefix,booleanWordDivStart] at h
  rw [cb_nz_right] at h
  rw [h]
  by_cases hz : booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0
  · simp [hz]
  · have hp : 0 < booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) := by omega
    simp [hz,hp]

/-- The inputs selected for the special-branch program are the four entry bits followed by
false. -/
private theorem cb_Z_inputs (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbGC n w b d) x (cbZI n w b d j)) =
      Fin.snoc (booleanWordCoarseEntry n w x) false := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [cbZI,Fin.val_last,dif_neg (Nat.lt_irrefl 4),Fin.snoc_last]
    exact cb_C_zero n w b d x
  · simp only [cbZI,Fin.val_castSucc,dif_pos k.isLt,Fin.snoc_castSucc]
    exact cb_input_value (cbGC n w b d) x
      ⟨16*(w+1)+2*n+k.val,by have := k.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩

/-- The appended special-branch program produces `booleanZeroDetailResult` for the entry portion
of the coarse input. -/
private theorem cb_Z_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbZ n w b d).graph x ((cbZ n w b d).output j)) =
      booleanZeroDetailResult (cbV w b d) b
        (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
        (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega) (booleanWordCoarseEntry n w x) := by
  funext j
  rw [cb_append_value,cb_Z_inputs]
  rfl

/-- The designated zero wire remains false after appending the special-branch program. -/
private theorem cb_Z_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbZ n w b d).graph x (cbZ n w b d).zero = false := by
  rw [cb_append_zero,cb_Z_inputs]
  exact (cb_input_value (cbDetail w b d).graph (Fin.snoc (booleanWordCoarseEntry n w x) false) (Fin.last 4)).trans
    (by simp only [Fin.snoc_last])

/-- Appending the special-branch program preserves all values in the graph containing the
zero-frequency flag. -/
private theorem cb_Z_C (n w b d : ℕ) (x : Reg (cbM n w)) (j : Fin (cbM n w+cbNC n w b d)) :
    booleanDAGValue (cbZ n w b d).graph x
      (Fin.castLE (by change cbM n w+cbNC n w b d ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes); omega) j) =
        booleanDAGValue (cbGC n w b d) x j := cb_append_old _ _ _ _ _

/-- The bilinear quotient output retains its values after the special-branch program is
appended. -/
private theorem cb_Z_old_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbZ n w b d).graph x (cbOldZ n w b d j)) =
      booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x) := by
  trans (fun j => booleanDAGValue (cbP n w b d).graph x ((cbP n w b d).output j))
  · funext j
    exact (cb_Z_C n w b d x
      (Fin.castLE (by (try dsimp only [cbNC,cbNNZ]); omega) ((cbP n w b d).output j))).trans
      (cb_C_old n w b d x ((cbP n w b d).output j))
  · exact cb_old_word n w b d x

/-- The retained flag after the special-branch program is true exactly when the frequency word
has value zero. -/
private theorem cb_Z_flag (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbZ n w b d).graph x (cbFlagZ n w b d) =
      decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0) :=
  (cb_Z_C n w b d x (cbFlagC n w b d)).trans (cb_C_flag n w b d x)

/-- The selected multiplexer inputs evaluate to the special-branch word, bilinear quotient word,
and zero-frequency decision bit. -/
private theorem cb_mux_inputs (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbZ n w b d).graph x (cbMI n w b d j)) =
      booleanWordMuxInput (cbV w b d+3)
        (booleanZeroDetailResult (cbV w b d) b
          (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
          (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega) (booleanWordCoarseEntry n w x))
        (booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x))
        (decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x)=0)) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*(cbV w b d+3) < cbV w b d+3 := by omega
    simp only [cbMI,Fin.val_last,dif_neg hn,dif_neg (Nat.lt_irrefl _),booleanWordMuxInput,Fin.snoc_last]
    exact cb_Z_flag n w b d x
  · rw [booleanWordMuxInput,Fin.snoc_castSucc]
    by_cases hk : k.val < cbV w b d+3
    · simp only [cbMI,Fin.val_castSucc,booleanWordAdderInput,dif_pos hk]
      exact congrFun (cb_Z_word n w b d x) ⟨k.val,hk⟩
    · simp only [cbMI,Fin.val_castSucc,booleanWordAdderInput,dif_neg hk,dif_pos k.isLt]
      exact congrFun (cb_Z_old_word n w b d x) ⟨k.val-(cbV w b d+3),by have := k.isLt; omega⟩

/-- The coarse result word is the multiplexer output selecting between the special-branch and
bilinear quotient words according to the zero-frequency decision. -/
private theorem cb_result_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanWordCoarseResult n w b d x =
      booleanWordMuxResult (cbV w b d+3)
        (booleanZeroDetailResult (cbV w b d) b
          (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
          (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega) (booleanWordCoarseEntry n w x))
        (booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x))
        (decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x)=0)) := by
  funext j
  change booleanDAGValue (cbGT n w b d) x
    (booleanSpliceSource (cbMI n w b d) (booleanWordMuxSelect (cbV w b d+3) j)) = _
  rw [boolean_dag_splice_value,cb_mux_inputs]
  rfl

/-- The coarse-program flag is true exactly when the unsigned frequency word has value zero. -/
theorem boolean_word_coarse_flag (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    booleanWordCoarseFlag n w b d x =
      decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0) := by
  have he : booleanWordCoarseFlagSelect n w b d =
      Fin.castLE (by
        change cbM n w+(cbZ n w b d).nodes ≤ cbM n w+((cbZ n w b d).nodes+3*(cbV w b d+3))
        omega) (cbFlagZ n w b d) := by
    apply Fin.ext
    dsimp only [booleanWordCoarseFlagSelect,cbFlagZ,cbFlagC,cbNNZ,cbP,booleanDAGAppendWord,Fin.val_castLE,cbM,cbOld]
    omega
  rw [booleanWordCoarseFlag,he]
  exact (boolean_dag_splice_prefix (cbZ n w b d).graph (cbMI n w b d)
    (booleanWordMuxDAG (cbV w b d+3)) x (cbFlagZ n w b d)).trans (cb_Z_flag n w b d x)

/-- The designated zero wire of the complete coarse-branch program evaluates to false. -/
theorem boolean_word_coarse_zero (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    let p := booleanWordCoarseProgram n w b d
    booleanDAGValue p.graph x p.zero = false := by
  exact (boolean_dag_splice_prefix (cbZ n w b d).graph (cbMI n w b d)
    (booleanWordMuxDAG (cbV w b d+3)) x (cbZ n w b d).zero).trans (cb_Z_zero n w b d x)

/-- The decoded coarse result is the entry-dependent masked quotient when the frequency word is
zero, and the bilinear quotient value otherwise. -/
theorem boolean_word_coarse_value (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    booleanWordCoarseValue n w b d x =
      if booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0 then
        (if booleanZeroDetailMask (booleanWordCoarseEntry n w x) then (2 : ℤ)^b else 0) /
          (booleanZeroDetailDivisor (booleanWordCoarseEntry n w x) : ℤ)
      else booleanWordBilinearQuotientValue w b d (booleanWordCoarseCoefficients n w x) := by
  change cbDecode (cbV w b d+2) (booleanWordCoarseResult n w b d x) = _
  rw [cb_result_word,boolean_word_mux_value]
  by_cases hz : booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x)=0
  · simp only [hz,decide_true,ite_true]
    exact boolean_zero_detail_value _ _ _ _ _
  · simp only [hz,decide_false,ite_false]
    simp only [cbDecode,booleanWordBilinearQuotientValue,cbV,Bool.false_eq_true,ite_false]

/-- The coarse-branch program and its legal local compilation satisfy explicit bounds quadratic
in the arithmetic widths and linear in n, with no queries and gate count equal to list
length. -/
theorem boolean_word_coarse_resources (n w b d : ℕ) :
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordCoarseProgram n w b d
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 40*V^2+37*V+242*w^2+900*w+6*n+674 ∧ reflectionLegal gs ∧
      gs.length ≤ 1200*V^2+1111*V+7260*w^2+27000*w+180*n+20223 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      booleanWordCoarseInputWidth n w+p.nodes+(V+3) ≤ 40*V^2+38*V+242*w^2+916*w+8*n+697 := by
  let V := booleanWordBilinearQuotientWidth w b d
  let p := booleanWordCoarseProgram n w b d
  have ho := (boolean_word_bilinear_quotient_resources w b d).1
  have hd := (boolean_word_signed_div_resources V).1
  change (booleanWordBilinearQuotientProgram w b d).nodes ≤ 20*V^2+17*V+242*w^2+900*w+642 at ho
  have hn : p.nodes ≤ 40*V^2+37*V+242*w^2+900*w+6*n+674 := by
    change 0+(booleanWordBilinearQuotientProgram w b d).nodes+(3*(2*n)+1)+1+
      (11+(booleanWordSignedDivProgram V).nodes)+3*(V+3) ≤ _
    omega
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,?_,hq,hc,?_⟩
  · change (booleanDAGSteps p.graph p.output).length ≤
      1200*V^2+1111*V+7260*w^2+27000*w+180*n+20223
    omega
  · change (16*(w+1)+2*n+4)+p.nodes+(V+3) ≤
      40*V^2+38*V+242*w^2+916*w+8*n+697
    omega

/-- The compiled coarse-branch program XORs its result into a basis output register while
preserving the input and restoring clean work bits. -/
theorem boolean_word_coarse_basis (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w))
    (y : Reg (booleanWordBilinearQuotientWidth w b d+3)) :
    let M := booleanWordCoarseInputWidth n w
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordCoarseProgram n w b d
    Run (1 : Matrix (Reg (M+p.nodes+(V+3))) (Reg (M+p.nodes+(V+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput M p.nodes (V+3) x y)) =
      Ket (booleanDAGInput M p.nodes (V+3) x (fun j => y j ^^ booleanWordCoarseResult n w b d x j)) :=
  boolean_dag_basis _ _ _ _

/-- The compiled coarse-branch program coherently XORs its result into the output of an
arbitrary embedded input-output state, restoring the work bits. -/
theorem boolean_word_coarse_coherent (n w b d : ℕ)
    (ψ : QState (Reg (booleanWordCoarseInputWidth n w) × Reg (booleanWordBilinearQuotientWidth w b d+3))) :
    let M := booleanWordCoarseInputWidth n w
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordCoarseProgram n w b d
    Run (1 : Matrix (Reg (M+p.nodes+(V+3))) (Reg (M+p.nodes+(V+3))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed M p.nodes (V+3) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput M p.nodes (V+3) xy.1
        (fun j => xy.2 j ^^ booleanWordCoarseResult n w b d xy.1 j)) :=
  boolean_dag_coherent _ _ _

end Qatlib.Concepts.MatrixAccess.RitzPipeline
