/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedMultiplicationData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplier

/-!
# Sign-magnitude multiplication by Boolean DAGs

`boolean_word_signed_mul_value` verifies exact multiplication of two sign-magnitude integers.
The magnitude is the unsigned product, and the output sign is the XOR of the two input sign
bits.

The module also proves the zero-wire property, polynomial resource bounds, and the action of the
compiled reversible circuit on basis states and arbitrary embedded states. The circuit
background is described in [NielsenChuang2010].

## Main statements

* `boolean_word_signed_mul_magnitude`: zero-wire, magnitude, and sign properties.
* `boolean_word_signed_mul_value`: exact signed multiplication.
* `boolean_word_signed_mul_resources`: polynomial circuit resource bounds.
* `boolean_word_signed_mul_basis`, `boolean_word_signed_mul_coherent`: circuit action.

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

/-- The node count of the unsigned multiplier embedded in the signed-multiplication graph. -/
private abbrev smN0 (w : ℕ) := 0+(booleanWordMulProgram w).nodes
/-- Embed the two unsigned magnitude words before the two sign inputs. -/
private abbrev smRaw (w : ℕ) : Fin (2*w) → Fin (2*w+2+0) := fun j => j.castSucc.castSucc
/-- Embed the unsigned multiplier in the input layout containing two magnitude words and two
sign bits. -/
private abbrev smG0 (w : ℕ) : BooleanDAG (2*w+2) (smN0 w) :=
  booleanDAGSplice .nil (smRaw w) (booleanWordMulProgram w).graph

/-- Appending one Boolean node preserves earlier wire values and evaluates the new final wire
using that node on the previous graph values. -/
private theorem sm_snoc_value {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+(n+1))) :
    booleanDAGValue (g.snoc node) x j =
      if hj : j.val < m+n then booleanDAGValue g x ⟨j.val,hj⟩
      else booleanNodeValue node (booleanDAGValue g x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [booleanDAGValue]
  · simp [booleanDAGValue]

/-- Appending one Boolean node preserves the values of all earlier wires. -/
private theorem sm_snoc_old {m n : ℕ} (g : BooleanDAG m n)
    (node : BooleanNode (m+n)) (x : Reg m) (j : Fin (m+n)) :
    booleanDAGValue (g.snoc node) x (Fin.castLE (by omega) j) = booleanDAGValue g x j := by
  rw [sm_snoc_value]
  simp only [Fin.val_castLE,dif_pos j.isLt]

/-- Every original input wire of a Boolean graph evaluates to the corresponding input bit. -/
private theorem sm_input_value {m n : ℕ} (g : BooleanDAG m n)
    (x : Reg m) (j : Fin m) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc n g node ih =>
    rw [sm_snoc_value]
    have hj : j.val < m+n := by have := j.isLt; omega
    simpa only [Fin.val_castLE,dif_pos hj] using! ih

/-- The signed multiplier preserves the evaluated values of mapped wires from the underlying
unsigned multiplier. -/
private theorem sm_old_value (w : ℕ) (a b : Reg w) (sa sb : Bool)
    (j : Fin (2*w+(booleanWordMulProgram w).nodes)) :
    booleanDAGValue (booleanWordSignedMulProgram w).graph (booleanWordSignedMulInput w a b sa sb)
      (Fin.castLE (by dsimp only [booleanWordSignedMulProgram]; omega)
        (booleanSpliceSource (smRaw w) j)) =
      booleanDAGValue (booleanWordMulProgram w).graph (booleanWordAdderInput w a b) j := by
  have h := boolean_dag_splice_value (.nil : BooleanDAG (2*w+2) 0) (smRaw w)
    (booleanWordMulProgram w).graph (booleanWordSignedMulInput w a b sa sb) j
  have he : (fun k => booleanDAGValue (.nil : BooleanDAG (2*w+2) 0)
      (booleanWordSignedMulInput w a b sa sb) (smRaw w k)) = booleanWordAdderInput w a b := by
    funext k
    simp [smRaw,booleanDAGValue,booleanWordSignedMulInput]
  rw [he] at h
  exact (sm_snoc_old (smG0 w) _ (booleanWordSignedMulInput w a b sa sb)
    (booleanSpliceSource (smRaw w) j)).trans h

/-- The signed multiplication magnitude word equals the unsigned multiplication result word. -/
private theorem sm_magnitude_word (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedMulMagnitude w a b sa sb = booleanWordMulResult w a b := by
  funext j
  simp only [booleanWordSignedMulMagnitude,booleanWordSignedMulResult,booleanWordSignedMulProgram,
    Fin.val_castSucc,dif_pos j.isLt]
  exact sm_old_value w a b sa sb (booleanWordMulSelect w j)

/-- The signed multiplication output sign is the XOR of the two input sign bits. -/
private theorem sm_sign_value (w : ℕ) (a b : Reg w) (sa sb : Bool) :
    booleanWordSignedMulSign w a b sa sb = (sa ^^ sb) := by
  have hn : ¬2*w+2+smN0 w < 2*w+2+smN0 w := by omega
  simp only [booleanWordSignedMulSign,booleanWordSignedMulResult,booleanWordSignedMulProgram,
    Fin.val_last,dif_neg (Nat.lt_irrefl (2*w))]
  rw [sm_snoc_value,dif_neg hn]
  change (booleanDAGValue (smG0 w) (booleanWordSignedMulInput w a b sa sb) ⟨2*w,by omega⟩ ^^
      booleanDAGValue (smG0 w) (booleanWordSignedMulInput w a b sa sb) ⟨2*w+1,by omega⟩) = _
  have ha : booleanDAGValue (smG0 w) (booleanWordSignedMulInput w a b sa sb) ⟨2*w,by omega⟩ = sa := by
    have h :=
        sm_input_value (smG0 w) (booleanWordSignedMulInput w a b sa sb) (Fin.last (2*w)).castSucc
    simpa only [booleanWordSignedMulInput,Fin.snoc_castSucc,Fin.snoc_last] using! h
  have hb : booleanDAGValue (smG0 w) (booleanWordSignedMulInput w a b sa sb) ⟨2*w+1,by omega⟩ = sb := by
    have h := sm_input_value (smG0 w) (booleanWordSignedMulInput w a b sa sb) (Fin.last (2*w+1))
    simpa only [booleanWordSignedMulInput,Fin.snoc_last] using! h
  rw [ha,hb]

/-- The signed multiplier has a false zero wire, output sign equal to the XOR of the input
signs, and magnitude equal to the product of the input magnitudes. -/
theorem boolean_word_signed_mul_magnitude (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) :
    let p := booleanWordSignedMulProgram w
    booleanDAGValue p.graph (booleanWordSignedMulInput w a b negativeA negativeB) p.zero = false ∧
      booleanWordSignedMulSign w a b negativeA negativeB = (negativeA ^^ negativeB) ∧
      booleanWordLSBValue (2*w) (booleanWordSignedMulMagnitude w a b negativeA negativeB) =
        booleanWordLSBValue w a * booleanWordLSBValue w b := by
  refine ⟨?_,sm_sign_value w a b negativeA negativeB,?_⟩
  · exact (sm_old_value w a b negativeA negativeB (booleanWordMulProgram w).zero).trans
      (boolean_word_mul_prefix w w (Nat.le_refl w) (booleanWordAdderInput w a b)).1
  · rw [sm_magnitude_word,boolean_word_mul_value]

/-- The integer decoded from the signed multiplication output equals the product of the two
input sign-magnitude integers. -/
theorem boolean_word_signed_mul_value (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) :
    booleanWordSignedMulValue w a b negativeA negativeB =
      booleanWordSignedValue w a negativeA * booleanWordSignedValue w b negativeB := by
  obtain ⟨_,hs,hm⟩ := boolean_word_signed_mul_magnitude w a b negativeA negativeB
  dsimp only [booleanWordSignedMulValue,booleanWordSignedValue]
  rw [hs,hm]
  cases negativeA <;> cases negativeB <;> simp

/-- The signed multiplier is legal with at most `11*w^2+w+2` nodes, `330*w^2+32*w+61` compiled
gates, and `11*w^2+5*w+5` total wires. It uses zero oracle queries, and its gate count
equals its reflection-step count. -/
theorem boolean_word_signed_mul_resources (w : ℕ) :
    let p := booleanWordSignedMulProgram w
    let gs := booleanDAGSteps p.graph p.output
    p.nodes ≤ 11*w^2+w+2 ∧ reflectionLegal gs ∧
      gs.length ≤ 330*w^2+32*w+61 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      (2*w+2)+p.nodes+(2*w+1) ≤ 11*w^2+5*w+5 := by
  let p := booleanWordSignedMulProgram w
  have hn : p.nodes ≤ 11*w^2+w+2 := by
    have h := (boolean_word_mul_resources w).1
    change 0+(booleanWordMulProgram w).nodes+1 ≤ _
    omega
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources p.graph p.output
  refine ⟨hn,hl,by nlinarith,hq,hc,?_⟩
  change (2*w+2)+p.nodes+(2*w+1) ≤ 11*w^2+5*w+5
  omega

/-- On a basis state with initialized workspace, the compiled signed multiplier XORs its
sign-magnitude product into the target and restores the workspace. -/
theorem boolean_word_signed_mul_basis (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool)
    (y : Reg (2*w+1)) :
    let p := booleanWordSignedMulProgram w
    Run (1 : Matrix (Reg ((2*w+2)+p.nodes+(2*w+1))) (Reg ((2*w+2)+p.nodes+(2*w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (Ket (booleanDAGInput (2*w+2) p.nodes (2*w+1)
        (booleanWordSignedMulInput w a b negativeA negativeB) y)) =
      Ket (booleanDAGInput (2*w+2) p.nodes (2*w+1)
        (booleanWordSignedMulInput w a b negativeA negativeB)
        (fun j => y j ^^ booleanWordSignedMulResult w a b negativeA negativeB j)) :=
  boolean_dag_basis _ _ _ _

/-- Packing the two magnitude views and two sign bits reconstructs the original
signed-multiplication input. -/
private theorem sm_input_views (w : ℕ) (x : Reg (2*w+2)) :
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

/-- On an arbitrary embedded state, the compiled signed multiplier coherently XORs each
sign-magnitude product into its target and restores the workspace. -/
theorem boolean_word_signed_mul_coherent (w : ℕ) (ψ : QState (Reg (2*w+2) × Reg (2*w+1))) :
    let p := booleanWordSignedMulProgram w
    Run (1 : Matrix (Reg ((2*w+2)+p.nodes+(2*w+1))) (Reg ((2*w+2)+p.nodes+(2*w+1))) ℂ)
      (reflectionCompile (booleanDAGSteps p.graph p.output))
      (booleanDAGEmbed (2*w+2) p.nodes (2*w+1) ψ) =
      ∑ xy, ψ xy • Ket (booleanDAGInput (2*w+2) p.nodes (2*w+1) xy.1
        (fun j => xy.2 j ^^ booleanWordSignedMulResult w
          (booleanWordSignedMulLeft w xy.1) (booleanWordSignedMulRight w xy.1)
          (xy.1 ((Fin.last (2*w)).castSucc)) (xy.1 (Fin.last (2*w+1))) j)) := by
  (try dsimp only)
  rw [boolean_dag_coherent]
  apply Finset.sum_congr rfl
  intro xy _
  simp only [booleanWordSignedMulResult,sm_input_views]
  rfl

end Qatlib.Concepts.MatrixAccess.RitzPipeline
