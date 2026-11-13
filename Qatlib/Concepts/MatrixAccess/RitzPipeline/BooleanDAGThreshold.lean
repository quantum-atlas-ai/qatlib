/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGThresholdData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGCoarseBranch

/-!
# Threshold-word encoding and circuit correctness

`boolean_word_threshold_offset_value` proves that the offset graph adds `32*2^b` to the signed
coarse value. `boolean_word_threshold_value` identifies the selected width `b+6` bit-vector with
the absolute value of that shifted integer modulo `2^(b+6)`.

The module also proves low-word truncation, the zero-wire property, polynomial resource bounds,
and reversible basis-state and coherent semantics. The circuit background is described in
[NielsenChuang2010].

## Main statements

* `boolean_word_low_value`: truncation of a little-endian word is reduction modulo a power of
  two.
* `boolean_word_threshold_offset_value`, `boolean_word_threshold_value`: integer and bit-vector
  interpretations.
* `boolean_word_threshold_resources`: circuit resource bounds.
* `boolean_word_threshold_basis`, `boolean_word_threshold_coherent`: circuit action.

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
attribute [local irreducible] booleanWordCoarseProgram booleanWordSignedAddProgram

/-- Restricting a little-endian word to its low `m` bits gives its unsigned value modulo `2^m`. -/
theorem boolean_word_low_value (W m : ℕ) (hm : m ≤ W) (a : Reg W) :
    booleanWordLSBValue m (booleanWordLow W m hm a) = booleanWordLSBValue W a % 2^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  let low := booleanWordLSBValue m (booleanWordLow (m+k) m hm a)
  let high := booleanWordLSBValue k (fun j => a (Fin.natAdd m j))
  have hlt : low < 2^m := (bitVecEquiv m (fun j => booleanWordLow (m+k) m hm a (Fin.rev j))).isLt
  have hs : booleanWordLSBValue (m+k) a = low + 2^m*high := by
    rw [boolean_word_lsb_value,Fin.sum_univ_add]
    change _ = booleanWordLSBValue m (booleanWordLow (m+k) m hm a)+
      2^m*booleanWordLSBValue k (fun j => a (Fin.natAdd m j))
    rw [boolean_word_lsb_value,boolean_word_lsb_value,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_natAdd,pow_add]
    ring
  change low = _
  simp only [hs,Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hlt]

/-- Applying a Boolean-valued map to signed-pair sources gives the corresponding packed
signed-addition input. -/
private theorem th_pair_map {α : Type*} (w : ℕ) (a b : Fin (w+1) → α) (f : α → Bool) :
    (fun j => f (booleanSignedPairSelect w a b j)) =
      booleanWordSignedAddInput w (fun j => f (a j.castSucc)) (fun j => f (b j.castSucc))
        (f (a (Fin.last w))) (f (b (Fin.last w))) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*w+1 < w := by omega
    simp [booleanSignedPairSelect,booleanWordSignedAddInput,booleanWordSignedMulInput,hn]
  · rw [booleanWordSignedAddInput,booleanWordSignedMulInput,Fin.snoc_castSucc]
    refine Fin.lastCases ?_ (fun t => ?_) k
    · have hn : ¬2*w < w := by omega
      simp [booleanSignedPairSelect,hn]
    · rw [Fin.snoc_castSucc]
      by_cases ht : t.val < w
      · simp [booleanSignedPairSelect,booleanWordAdderInput,ht]
      · simp [booleanSignedPairSelect,booleanWordAdderInput,ht,t.isLt]

/-- The input width of the coarse-value graph used by the threshold construction. -/
private abbrev thM (n w : ℕ) := booleanWordCoarseInputWidth n w
/-- The bilinear quotient width determining the intermediate threshold word sizes. -/
private abbrev thV (w b d : ℕ) := booleanWordBilinearQuotientWidth w b d
/-- The coarse-value program used as the initial threshold graph. -/
private abbrev thP (n w b d : ℕ) := booleanWordCoarseProgram n w b d
/-- Append a true constant to the coarse-value graph for constructing the positive offset word. -/
private abbrev thG (n w b d : ℕ) := (thP n w b d).graph.snoc (.constant true)
/-- Select the coarse-value output wires after appending the true constant. -/
private abbrev thOld (n w b d : ℕ) : Fin (thV w b d+3) → Fin (thM n w+((thP n w b d).nodes+1)) :=
  fun j => Fin.castSucc ((thP n w b d).output j)
/-- Select the original distinguished zero wire after appending the true constant. -/
private abbrev thZero (n w b d : ℕ) : Fin (thM n w+((thP n w b d).nodes+1)) :=
  Fin.castSucc (thP n w b d).zero
/-- Select the newly appended true constant wire. -/
private abbrev thOne (n w b d : ℕ) : Fin (thM n w+((thP n w b d).nodes+1)) :=
  ⟨thM n w+(thP n w b d).nodes,by omega⟩
/-- Select the true wire at position `b+5` and the zero wire at all other positions of the
signed offset word. -/
private abbrev thOffset (n w b d : ℕ) : Fin (thV w b d+3) → Fin (thM n w+((thP n w b d).nodes+1)) :=
  fun j => if j.val=b+5 then thOne n w b d else thZero n w b d

/-- The transported coarse-value output wires retain their evaluated result bits after the true
constant is appended. -/
private theorem th_old (n w b d : ℕ) (x : Reg (thM n w)) (j : Fin (thV w b d+3)) :
    booleanDAGValue (thG n w b d) x (thOld n w b d j) = booleanWordCoarseResult n w b d x j := by
  simp only [thOld,booleanDAGValue,Fin.lastCases_castSucc]
  rfl

/-- The transported distinguished zero wire evaluates to false. -/
private theorem th_zero (n w b d : ℕ) (x : Reg (thM n w)) :
    booleanDAGValue (thG n w b d) x (thZero n w b d) = false := by
  simp only [thZero,booleanDAGValue,Fin.lastCases_castSucc]
  exact boolean_word_coarse_zero n w b d x

/-- The appended constant wire evaluates to true. -/
private theorem th_one (n w b d : ℕ) (x : Reg (thM n w)) :
    booleanDAGValue (thG n w b d) x (thOne n w b d) = true := by
  change Fin.lastCases true (booleanDAGValue (thP n w b d).graph x)
    (Fin.last (thM n w+(thP n w b d).nodes)) = true
  exact Fin.lastCases_last

/-- The offset source at position `j` evaluates to true exactly when `j.val = b+5`. -/
private theorem th_offset (n w b d : ℕ) (x : Reg (thM n w)) (j : Fin (thV w b d+3)) :
    booleanDAGValue (thG n w b d) x (thOffset n w b d j) = decide (j.val=b+5) := by
  by_cases hj : j.val=b+5 <;> simp only [thOffset,hj,ite_true,ite_false,th_one,th_zero,decide_true,decide_false]

/-- The offset result is the signed sum of the coarse result and a positive word with its sole
true magnitude bit at position `b+5`. -/
private theorem th_result (n w b d : ℕ) (x : Reg (thM n w)) :
    booleanWordThresholdOffsetResult n w b d x =
      booleanWordSignedAddResult (thV w b d+2)
        (fun j => booleanWordCoarseResult n w b d x j.castSucc)
        (fun j => decide (j.val=b+5))
        (booleanWordCoarseResult n w b d x (Fin.last (thV w b d+2))) false := by
  have hi : (fun j => booleanDAGValue (thG n w b d) x
      (booleanSignedPairSelect (thV w b d+2) (thOld n w b d) (thOffset n w b d) j)) =
      booleanWordSignedAddInput (thV w b d+2)
        (fun j => booleanWordCoarseResult n w b d x j.castSucc) (fun j => decide (j.val=b+5))
        (booleanWordCoarseResult n w b d x (Fin.last (thV w b d+2))) false := by
    rw [th_pair_map]
    simp only [th_old,th_offset,Fin.val_castSucc,Fin.val_last]
    have hn : thV w b d+2 ≠ b+5 := by dsimp only [thV,booleanWordBilinearQuotientWidth]; omega
    simp only [hn,decide_false]
  have hr : booleanWordThresholdOffsetResult n w b d x = fun j =>
      booleanDAGValue (booleanWordSignedAddProgram (thV w b d+2)).graph
        (fun t => booleanDAGValue (thG n w b d) x
          (booleanSignedPairSelect (thV w b d+2) (thOld n w b d) (thOffset n w b d) t))
        ((booleanWordSignedAddProgram (thV w b d+2)).output j) := by
    funext j
    exact boolean_dag_splice_value (thG n w b d)
      (booleanSignedPairSelect (thV w b d+2) (thOld n w b d) (thOffset n w b d))
      (booleanWordSignedAddProgram (thV w b d+2)).graph x
      ((booleanWordSignedAddProgram (thV w b d+2)).output j)
  rw [hr,hi]
  rfl

/-- The unsigned value of the offset magnitude word is `2^(b+5)`. -/
private theorem th_offset_lsb (w b d : ℕ) :
    booleanWordLSBValue (thV w b d+2) (fun j => decide (j.val=b+5)) = 2^(b+5) := by
  rw [boolean_word_lsb_value]
  let t : Fin (thV w b d+2) := ⟨b+5,by dsimp only [thV,booleanWordBilinearQuotientWidth]; omega⟩
  rw [Finset.sum_eq_single t]
  · simp only [t,decide_true,ite_true,one_mul]
  · intro j _ hj
    have hn : j.val ≠ b+5 := by intro h; apply hj; exact Fin.ext h
    simp only [hn,decide_false,Bool.false_eq_true,ite_false,zero_mul]
  · simp

/-- The decoded threshold-offset output equals the coarse integer value plus `32*2^b`. -/
theorem boolean_word_threshold_offset_value (n w b d : ℕ)
    (x : Reg (booleanWordCoarseInputWidth n w)) :
    booleanWordThresholdOffsetValue n w b d x = booleanWordCoarseValue n w b d x + 32*(2:ℤ)^b := by
  simp only [booleanWordThresholdOffsetValue,th_result]
  change booleanWordSignedAddValue (thV w b d+2) _ _ _ false = _
  rw [boolean_word_signed_add_value]
  change booleanWordCoarseValue n w b d x + booleanWordSignedValue (thV w b d+2) _ false = _
  simp only [booleanWordSignedValue,Bool.false_eq_true,ite_false,th_offset_lsb,Nat.cast_pow,Nat.cast_ofNat]
  rw [pow_add]
  norm_num
  ring

/-- The natural absolute value of a decoded sign-magnitude integer is the unsigned value of its
magnitude word. -/
private theorem th_magnitude_natAbs (W : ℕ) (a : Reg W) (s : Bool) :
    (booleanWordSignedValue W a s).natAbs = booleanWordLSBValue W a := by
  cases s <;> simp [booleanWordSignedValue]

/-- The threshold output bit-vector has value equal to the natural absolute value of the coarse
value plus `32*2^b`, reduced modulo `2^(b+6)`. -/
theorem boolean_word_threshold_value (n w b d : ℕ)
    (x : Reg (booleanWordCoarseInputWidth n w)) :
    (bitVecEquiv (b+6) (booleanWordThresholdResult n w b d x)).val =
      (booleanWordCoarseValue n w b d x + 32*(2:ℤ)^b).natAbs % 2^(b+6) := by
  let V := thV w b d
  let a : Reg (V+3) := fun j => booleanWordThresholdOffsetResult n w b d x j.castSucc
  have hm : b+6 ≤ V+3 := by dsimp only [V,thV,booleanWordBilinearQuotientWidth]; omega
  have hbits : (fun j => booleanWordThresholdResult n w b d x (Fin.rev j)) =
      booleanWordLow (V+3) (b+6) hm a := by
    funext j
    simp only [booleanWordThresholdResult,booleanWordThresholdProgram,Fin.rev_rev,booleanWordLow]
    rfl
  have he : (bitVecEquiv (b+6) (booleanWordThresholdResult n w b d x)).val =
      booleanWordLSBValue (b+6) (booleanWordLow (V+3) (b+6) hm a) := by
    rw [booleanWordLSBValue,← hbits]
    simp only [Fin.rev_rev]
  rw [he,boolean_word_low_value]
  have ha : booleanWordLSBValue (V+3) a = (booleanWordThresholdOffsetValue n w b d x).natAbs :=
    (th_magnitude_natAbs (V+3) a (booleanWordThresholdOffsetResult n w b d x (Fin.last (V+3)))).symm
  rw [ha,boolean_word_threshold_offset_value]

/-- The threshold program's distinguished zero wire evaluates to false. -/
theorem boolean_word_threshold_zero (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    let p := booleanWordThresholdProgram n w b d
    booleanDAGValue p.graph x p.zero = false := by
  (try dsimp only)
  have hi : (fun j => booleanDAGValue (thG n w b d) x
      (booleanSignedPairSelect (thV w b d+2) (thOld n w b d) (thOffset n w b d) j)) =
      booleanWordSignedAddInput (thV w b d+2)
        (fun j => booleanDAGValue (thG n w b d) x (thOld n w b d j.castSucc))
        (fun j => booleanDAGValue (thG n w b d) x (thOffset n w b d j.castSucc))
        (booleanDAGValue (thG n w b d) x (thOld n w b d (Fin.last (thV w b d+2))))
        (booleanDAGValue (thG n w b d) x (thOffset n w b d (Fin.last (thV w b d+2)))) :=
    th_pair_map _ _ _ _
  have hz : booleanDAGValue (booleanWordThresholdProgram n w b d).graph x
      (booleanWordThresholdProgram n w b d).zero =
      booleanDAGValue (booleanWordSignedAddProgram (thV w b d+2)).graph
        (fun j => booleanDAGValue (thG n w b d) x
          (booleanSignedPairSelect (thV w b d+2) (thOld n w b d) (thOffset n w b d) j))
        (booleanWordSignedAddProgram (thV w b d+2)).zero :=
    boolean_dag_splice_value _ _ _ _ _
  rw [hz,hi]
  exact (boolean_word_signed_add_magnitude _ _ _ _ _).1

/-- The threshold circuit is legal and satisfies the stated polynomial bounds on its node, step,
and total wire counts in terms of the bilinear quotient width and input parameters. It uses
zero oracle queries, and its compiled gate count equals its reflection-step count. -/
theorem boolean_word_threshold_resources (n w b d : ℕ) :
    let V := booleanWordBilinearQuotientWidth w b d
    let p := booleanWordThresholdProgram n w b d
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 40*V^2+68*V+242*w^2+900*w+6*n+749 ∧ reflectionLegal gs ∧
      gs.length ≤ 1200*V^2+2040*V+7260*w^2+27000*w+180*n+b+22476 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      booleanWordCoarseInputWidth n w+p.nodes+(b+6) ≤
        40*V^2+68*V+242*w^2+916*w+8*n+b+775 := by
  let V := booleanWordBilinearQuotientWidth w b d
  let p := booleanWordThresholdProgram n w b d
  have hc := (boolean_word_coarse_resources n w b d).1
  have ha := (boolean_word_signed_add_resources (V+2)).1
  have hn : p.nodes ≤ 40*V^2+68*V+242*w^2+900*w+6*n+749 := by
    change (booleanWordCoarseProgram n w b d).nodes+1+(booleanWordSignedAddProgram (V+2)).nodes ≤ _
    change (booleanWordCoarseProgram n w b d).nodes ≤ 40*V^2+37*V+242*w^2+900*w+6*n+674 at hc
    omega
  obtain ⟨hl,hg,hq,hgates⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,?_,hq,hgates,?_⟩
  · change (booleanDAGSteps p.graph p.output).length ≤
      1200*V^2+2040*V+7260*w^2+27000*w+180*n+b+22476
    omega
  · change (16*(w+1)+2*n+4)+p.nodes+(b+6) ≤
      40*V^2+68*V+242*w^2+916*w+8*n+b+775
    omega

/-- On a basis state with initialized workspace, the compiled threshold circuit XORs its width
`b+6` result into the target and restores the workspace. -/
theorem boolean_word_threshold_basis (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w))
    (y : Reg (b+6)) :
    let M := booleanWordCoarseInputWidth n w
    let p := booleanWordThresholdProgram n w b d
    Run (1 : Matrix (Reg (M+p.nodes+(b+6))) (Reg (M+p.nodes+(b+6))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput M p.nodes (b+6) x y)) =
      Ket (booleanDAGInput M p.nodes (b+6) x (fun j => y j ^^ booleanWordThresholdResult n w b d x j)) :=
  boolean_dag_basis _ _ _ _

/-- On an arbitrary embedded state, the compiled threshold circuit coherently XORs each
threshold result into its target and restores the workspace. -/
theorem boolean_word_threshold_coherent (n w b d : ℕ)
    (ψ : QState (Reg (booleanWordCoarseInputWidth n w) × Reg (b+6))) :
    let M := booleanWordCoarseInputWidth n w
    let p := booleanWordThresholdProgram n w b d
    Run (1 : Matrix (Reg (M+p.nodes+(b+6))) (Reg (M+p.nodes+(b+6))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed M p.nodes (b+6) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput M p.nodes (b+6) xy.1
        (fun j => xy.2 j ^^ booleanWordThresholdResult n w b d xy.1 j)) :=
  boolean_dag_coherent _ _ _

end Qatlib.Concepts.MatrixAccess.RitzPipeline
