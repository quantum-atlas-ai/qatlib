/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGCoarseBranchData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGBilinearQuotient
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Classical BigOperators
set_option warningAsError false
set_option autoImplicit false

private def cbDecode (w : ℕ) (a : Reg (w+1)) : ℤ :=
  booleanWordSignedValue w (fun j => a j.castSucc) (a (Fin.last w))

private theorem cb_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

private theorem cb_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [cb_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

private theorem cb_input_value {m n : ℕ} (g : BooleanDAG m n) (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    change booleanDAGValue (g.snoc node) x
        (Fin.castSucc (Fin.castLE (Nat.le_add_right m n) j)) = x j
    simpa only [booleanDAGValue,Fin.lastCases_castSucc] using! ih

private theorem cb_append_value {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin o) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x ((booleanDAGAppendWord g r h).output j) =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) (h.output j) :=
  boolean_dag_splice_value _ _ _ _ _

private theorem cb_append_zero {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (booleanDAGAppendWord g r h).zero =
      booleanDAGValue h.graph (fun t => booleanDAGValue g x (r t)) h.zero :=
  boolean_dag_splice_value _ _ _ _ _

private theorem cb_append_old {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) (x : Reg M) (j : Fin (M+K)) :
    booleanDAGValue (booleanDAGAppendWord g r h).graph x (Fin.castLE (by dsimp [booleanDAGAppendWord]; omega) j) =
      booleanDAGValue g x j := boolean_dag_splice_prefix _ _ _ _ _

private theorem zd_mask_bool (a b c d : Bool) :
    (((! (a ^^ c)) && (! (b ^^ d))) && ((a ^^ b) ^^ (a && b))) =
      (((a == c) && (b == d)) && (a || b)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem cb_nil_value {m : ℕ} (x : Reg m) (j : Fin m) :
    booleanDAGValue (.nil : BooleanDAG m 0) x j = x j := rfl
private def zdInput (e : Reg 4) : Reg 5 := fun j => if h : j.val < 4 then e ⟨j.val,h⟩ else false

private theorem zd_input_eq (e : Reg 4) : Fin.snoc e false = zdInput e := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change (Fin.snoc e false : Reg 5) (Fin.last 4) = false
    simp only [Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    simp only [zdInput,Fin.val_castSucc,dif_pos k.isLt]

private theorem zd_mask (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨13,by omega⟩ = booleanZeroDetailMask e := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]
  simpa only [booleanZeroDetailMask,Bool.xor_assoc] using! (zd_mask_bool (e 0) (e 1) (e 2) (e 3))

private theorem zd_row11 (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨11,by omega⟩ = (e 0 && e 1) := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

private theorem zd_not11 (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨14,by omega⟩ = !(e 0 && e 1) := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

private theorem zd_one (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨15,by omega⟩ = true := by
  rw [zd_input_eq]
  norm_num [booleanZeroDetailFlags,cb_snoc_value,booleanNodeValue,cb_nil_value,zdInput]

private theorem zd_false (e : Reg 4) :
    booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) ⟨4,by omega⟩ = false := by
  exact (cb_input_value booleanZeroDetailFlags (Fin.snoc e false) (Fin.last 4)).trans
      (by simp only [Fin.snoc_last])

private abbrev zdNum (V b : ℕ) : Fin V → Fin 16 :=
    fun j => if j.val=b then ⟨13,by omega⟩ else ⟨4,by omega⟩
private abbrev zdDen (V : ℕ) : Fin V → Fin 16 := fun j =>
  if j.val=2 then ⟨14,by omega⟩ else if j.val=3 then ⟨15,by omega⟩
  else if j.val=4 then ⟨11,by omega⟩ else ⟨4,by omega⟩
private abbrev zdInputs (V b : ℕ) : Fin (2*V+1) → Fin 16 := fun j =>
  if hj : j.val < V then zdNum V b ⟨j.val,hj⟩
  else if hk : j.val < 2*V then zdDen V ⟨j.val-V,by omega⟩ else ⟨4,by omega⟩

private theorem zd_num_word (V b : ℕ) (e : Reg 4) :
    (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdNum V b j)) =
      (fun j => if j.val=b then booleanZeroDetailMask e else false) := by
  funext j
  by_cases h : j.val=b
  · simp only [zdNum,if_pos h]
    exact zd_mask e
  · simp only [zdNum,if_neg h]
    exact zd_false e

private theorem zd_num_nat (V b : ℕ) (hb : b < V) (bit : Bool) :
    booleanWordLSBValue V (fun j => if j.val=b then bit else false) = if bit then 2^b else 0 := by
  have he (j : Fin V) : (j.val=b) ↔ j=⟨b,hb⟩ := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact congrArg Fin.val h
  cases bit <;> simp [boolean_word_lsb_value,he]

private def zdExtend (k V : ℕ) (a : Reg k) : Reg V := fun j =>
  if hj : j.val < k then a ⟨j.val,hj⟩ else false

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
private def zdDen5 (r : Bool) : Reg 5 := fun j =>
  if j.val=2 then !r else if j.val=3 then true else if j.val=4 then r else false

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

private theorem zd_den_nat (V : ℕ) (hV : 5 ≤ V) (e : Reg 4) :
    booleanWordLSBValue V (fun j => booleanDAGValue booleanZeroDetailFlags (Fin.snoc e false) (zdDen V j)) =
      booleanZeroDetailDivisor e := by
  rw [zd_den_word,zd_extend_value 5 V hV]
  unfold booleanZeroDetailDivisor
  cases h :
      e 0 && e 1 <;> norm_num [zdDen5,boolean_word_lsb_value,Fin.sum_univ_succ,Fin.sum_univ_zero,h]

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

private abbrev cbM (n w : ℕ) := booleanWordCoarseInputWidth n w
private abbrev cbV (w b d : ℕ) := booleanWordBilinearQuotientWidth w b d
private abbrev cbOld (w b d : ℕ) := booleanWordBilinearQuotientProgram w b d
private abbrev cbRaw (n w : ℕ) : Fin (16*(w+1)) → Fin (cbM n w+0) :=
  fun j => ⟨j.val,by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
private abbrev cbP (n w b d : ℕ) :=
    booleanDAGAppendWord (.nil : BooleanDAG (cbM n w) 0) (cbRaw n w) (cbOld w b d)
private abbrev cbNZI (n w b d : ℕ) : Fin (2*(2*n)) → Fin (cbM n w+(cbP n w b d).nodes) := fun j =>
  if hj : j.val < 2*n then (cbP n w b d).zero else
    ⟨16*(w+1)+(j.val-2*n),by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
private abbrev cbNNZ (n w b d : ℕ) := (cbP n w b d).nodes+(3*(2*n)+1)
private abbrev cbGNZ (n w b d : ℕ) := booleanDAGSplice (cbP n w b d).graph (cbNZI n w b d)
  (booleanWordNonzeroPrefix (2*n) (2*n) (Nat.le_refl _))
private abbrev cbNZ (n w b d : ℕ) : Fin (cbM n w+cbNNZ n w b d) :=
  booleanSpliceSource (cbNZI n w b d) (⟨2*(2*n)+3*(2*n),by omega⟩ : Fin (2*(2*n)+(3*(2*n)+1)))
private abbrev cbGC (n w b d : ℕ) := (cbGNZ n w b d).snoc (.neg (cbNZ n w b d))
private abbrev cbNC (n w b d : ℕ) := cbNNZ n w b d+1
private abbrev cbZeroC (n w b d : ℕ) : Fin (cbM n w+cbNC n w b d) :=
  Fin.castLE (by (try dsimp only [cbNC,cbNNZ]); omega) (cbP n w b d).zero
private abbrev cbFlagC (n w b d : ℕ) : Fin (cbM n w+cbNC n w b d) :=
  ⟨cbM n w+cbNNZ n w b d,by dsimp only [cbNC]; omega⟩
private abbrev cbZI (n w b d : ℕ) : Fin 5 → Fin (cbM n w+cbNC n w b d) := fun j =>
  if hj : j.val < 4 then ⟨16*(w+1)+2*n+j.val,by dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩
  else cbZeroC n w b d
private abbrev cbDetail (w b d : ℕ) := booleanZeroDetailProgram (cbV w b d) b
  (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
  (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
private abbrev cbZ (n w b d : ℕ) :=
    booleanDAGAppendWord (cbGC n w b d) (cbZI n w b d) (cbDetail w b d)
private abbrev cbOldZ (n w b d : ℕ) : Fin (cbV w b d+3) → Fin (cbM n w+(cbZ n w b d).nodes) := fun j =>
  Fin.castLE (by
    change cbM n w+(cbP n w b d).nodes ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes)
    dsimp only [cbNC,cbNNZ]
    omega) ((cbP n w b d).output j)
private abbrev cbFlagZ (n w b d : ℕ) : Fin (cbM n w+(cbZ n w b d).nodes) :=
  Fin.castLE (by change cbM n w+cbNC n w b d ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes); omega)
    (cbFlagC n w b d)
private abbrev cbMI (n w b d : ℕ) : Fin (2*(cbV w b d+3)+1) → Fin (cbM n w+(cbZ n w b d).nodes) := fun j =>
  if hj : j.val < cbV w b d+3 then (cbZ n w b d).output ⟨j.val,hj⟩
  else if hk : j.val < 2*(cbV w b d+3) then cbOldZ n w b d ⟨j.val-(cbV w b d+3),by omega⟩
  else cbFlagZ n w b d
private abbrev cbGT (n w b d : ℕ) := booleanDAGSplice (cbZ n w b d).graph (cbMI n w b d)
  (booleanWordMuxDAG (cbV w b d+3))

private theorem cb_initial_inputs (n w : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (.nil : BooleanDAG (cbM n w) 0) x (cbRaw n w j)) = booleanWordCoarseCoefficients n w x := rfl

private theorem cb_old_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbP n w b d).graph x ((cbP n w b d).output j)) =
      booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x) := by
  funext j
  rw [cb_append_value,cb_initial_inputs]
  rfl

private theorem cb_old_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbP n w b d).graph x (cbP n w b d).zero = false := by
  rw [cb_append_zero,cb_initial_inputs]
  exact boolean_word_bilinear_quotient_zero _ _ _ _

private theorem cb_C_old (n w b d : ℕ) (x : Reg (cbM n w)) (j : Fin (cbM n w+(cbP n w b d).nodes)) :
    booleanDAGValue (cbGC n w b d) x
      (Fin.castLE (by omega) j) = booleanDAGValue (cbP n w b d).graph x j := by
  exact (cb_snoc_old (cbGNZ n w b d) _ x
    (Fin.castLE (by omega) j)).trans
    (boolean_dag_splice_prefix _ _ _ _ _)

private theorem cb_C_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbGC n w b d) x (cbZeroC n w b d) = false :=
  (cb_C_old n w b d x (cbP n w b d).zero).trans (cb_old_zero n w b d x)

private theorem cb_nz_right (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanWordAdderRight (2*n) (fun j => booleanDAGValue (cbP n w b d).graph x (cbNZI n w b d j)) =
      booleanWordCoarseFrequency n w x := by
  funext j
  have hn : ¬2*n+j.val < 2*n := by omega
  simp only [booleanWordAdderRight,cbNZI,dif_neg hn,Nat.add_sub_cancel_left]
  exact cb_input_value (cbP n w b d).graph x
    ⟨16*(w+1)+j.val,by have := j.isLt; dsimp only [cbM,booleanWordCoarseInputWidth]; omega⟩

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

private theorem cb_Z_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbZ n w b d).graph x ((cbZ n w b d).output j)) =
      booleanZeroDetailResult (cbV w b d) b
        (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega)
        (by dsimp only [cbV,booleanWordBilinearQuotientWidth]; omega) (booleanWordCoarseEntry n w x) := by
  funext j
  rw [cb_append_value,cb_Z_inputs]
  rfl

private theorem cb_Z_zero (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbZ n w b d).graph x (cbZ n w b d).zero = false := by
  rw [cb_append_zero,cb_Z_inputs]
  exact (cb_input_value (cbDetail w b d).graph (Fin.snoc (booleanWordCoarseEntry n w x) false) (Fin.last 4)).trans
    (by simp only [Fin.snoc_last])

private theorem cb_Z_C (n w b d : ℕ) (x : Reg (cbM n w)) (j : Fin (cbM n w+cbNC n w b d)) :
    booleanDAGValue (cbZ n w b d).graph x
      (Fin.castLE (by change cbM n w+cbNC n w b d ≤ cbM n w+(cbNC n w b d+(cbDetail w b d).nodes); omega) j) =
        booleanDAGValue (cbGC n w b d) x j := cb_append_old _ _ _ _ _

private theorem cb_Z_old_word (n w b d : ℕ) (x : Reg (cbM n w)) :
    (fun j => booleanDAGValue (cbZ n w b d).graph x (cbOldZ n w b d j)) =
      booleanWordBilinearQuotientResult w b d (booleanWordCoarseCoefficients n w x) := by
  trans (fun j => booleanDAGValue (cbP n w b d).graph x ((cbP n w b d).output j))
  · funext j
    exact (cb_Z_C n w b d x
      (Fin.castLE (by (try dsimp only [cbNC,cbNNZ]); omega) ((cbP n w b d).output j))).trans
      (cb_C_old n w b d x ((cbP n w b d).output j))
  · exact cb_old_word n w b d x

private theorem cb_Z_flag (n w b d : ℕ) (x : Reg (cbM n w)) :
    booleanDAGValue (cbZ n w b d).graph x (cbFlagZ n w b d) =
      decide (booleanWordLSBValue (2*n) (booleanWordCoarseFrequency n w x) = 0) :=
  (cb_Z_C n w b d x (cbFlagC n w b d)).trans (cb_C_flag n w b d x)

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

theorem boolean_word_coarse_zero (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    let p := booleanWordCoarseProgram n w b d
    booleanDAGValue p.graph x p.zero = false := by
  exact (boolean_dag_splice_prefix (cbZ n w b d).graph (cbMI n w b d)
    (booleanWordMuxDAG (cbV w b d+3)) x (cbZ n w b d).zero).trans (cb_Z_zero n w b d x)

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
