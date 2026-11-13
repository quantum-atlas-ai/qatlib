/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.GetD
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationAux
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationConstr

/-!
# Programs implementing adaptive purification

Relabeling, block-diagonal evaluation, and gate-prepending operations assemble purification
programs from adaptive computation trees. `sourceAdaptive_purify_program` constructs a legal
program that exactly produces the recorded pure output using at most twice the adaptive
oracle-call count.

The construction implements the deferred-measurement principle through unitary extensions and
explicit registers, as described in [Watrous2018].

## Main statements

* `sourceRelabelWord_matrix`: compatibility of word evaluation with relabeling.
* `sourceProgramPrependOp_matrix`: evaluation of an added oracle layer.
* `sourceAdaptive_purify_program`: exact purification with a query bound.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
noncomputable section

/-- Multiplying composable basis frames gives the basis frame of the composed index maps. -/
theorem sourceBasisFrame_mul {S T U : Type} [DecidableEq S] [Fintype T] [DecidableEq T]
    (f : T → S) (g : U → T) :
    sourceBasisFrame f*sourceBasisFrame g=sourceBasisFrame (f ∘ g) := by
  ext s u
  simp only [Matrix.mul_apply,sourceBasisFrame,Function.comp_apply]
  rw [Finset.sum_eq_single (g u)]
  · by_cases h : s=f (g u) <;> simp [h]
  · intro t _ ht
    simp [ht]
  · simp
end
noncomputable section

/-- Relabeling a matrix intertwines its action with the basis frame of the relabeling
equivalence. -/
theorem sourceRelabelGate_mul_basisFrame {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) :
    relabelGate e M*sourceBasisFrame ⇑e=sourceBasisFrame ⇑e*M := by
  ext j i
  have hl : (∑ y : J,M (e.symm j) (e.symm y)*(if y=e i then (1:ℂ) else 0))=M (e.symm j) i := by
    rw [Finset.sum_eq_single (e i)]
    · simp
    · intro y _ hy
      simp [hy]
    · simp
  have hr : (∑ a : I,(if j=e a then (1:ℂ) else 0)*M a i)=M (e.symm j) i := by
    rw [Finset.sum_eq_single (e.symm j)]
    · rw [if_pos (Equiv.apply_symm_apply e j).symm,one_mul]
    · intro a _ ha
      have hne : j≠e a := fun hh => ha (((congrArg e.symm hh).trans
        (Equiv.symm_apply_apply e a)).symm)
      rw [if_neg hne,zero_mul]
    · simp
  simp only [Matrix.mul_apply,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
    sourceBasisFrame]
  rw [hl,hr]
end
noncomputable section

/-- Relabeling a permutation matrix gives the permutation matrix of a map intertwined by the
equivalence. -/
theorem sourceRelabelGate_permMatrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (σ : I → I) (τ : J → J)
    (h : ∀ i, e (σ i)=τ (e i)) :
    relabelGate e (permMatrix σ)=permMatrix τ := by
  ext j j'
  simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,permMatrix,Matrix.of_apply]
  by_cases hj : j=τ j'
  · rw [if_pos hj]
    have hh : e.symm j=σ (e.symm j') := by
      have h1 := h (e.symm j')
      rw [Equiv.apply_symm_apply] at h1
      have h2 : e (σ (e.symm j'))=j := h1.trans hj.symm
      exact ((congrArg e.symm h2).symm).trans (Equiv.symm_apply_apply e (σ (e.symm j')))
    rw [if_pos hh]
  · rw [if_neg hj]
    have hh : e.symm j≠σ (e.symm j') := fun he => hj (by
      have h1 := h (e.symm j')
      rw [← he,Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h1
      exact h1)
    rw [if_neg hh]
end
noncomputable section

/-- Applying a relabeled matrix is equivalent to transporting the input to the original indices,
multiplying, and transporting the output back. -/
theorem sourceRelabelGate_mulVec {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) (φ : J → ℂ) :
    relabelGate e M *ᵥ φ=fun j => (M *ᵥ fun i => φ (e i)) (e.symm j) := by
  funext j
  simp only [Matrix.mulVec,dotProduct,relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e (fun b => M (e.symm j) (e.symm b)*φ b)]
  apply Finset.sum_congr rfl
  intro i _
  simp
end
noncomputable section

/-- Relabeling a finite product of matrices equals the product of their relabelings. -/
theorem sourceRelabelGate_list_prod {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (l : List (Matrix I I ℂ)) :
    relabelGate e l.prod=(l.map (relabelGate e)).prod := by
  induction l with
  | nil => simp [sourceRelabelGate_one]
  | cons a l ih => simp [List.prod_cons,sourceRelabelGate_mul,ih]
end
noncomputable section

/-- The source word obtained by relabeling every known gate while leaving oracle-call flags
unchanged. -/
def sourceRelabelWord {I J : Type} [DecidableEq I] [DecidableEq J] (e : I ≃ J) :
    SourceWord I → SourceWord J :=
  List.map (Sum.map (relabelGate e) id)
end
noncomputable section

/-- Relabeling a source word preserves its oracle-call count. -/
theorem sourceRelabelWord_calls {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (w : SourceWord I) :
    sourceWordCalls (sourceRelabelWord e w)=sourceWordCalls w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s with
    | inl U => simpa [sourceRelabelWord,sourceWordCalls] using! ih
    | inr b => simp [sourceRelabelWord,sourceWordCalls] at ih ⊢; omega
end
noncomputable section

/-- Relabeling a legal source word preserves legality. -/
theorem sourceRelabelWord_legal {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (w : SourceWord I)
    (hw : sourceWordLegal w) : sourceWordLegal (sourceRelabelWord e w) := by
  intro s hs
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
  have hh := hw t ht
  cases t with
  | inl U => exact sourceRelabelGate_unitary e U hh
  | inr b => trivial
end
noncomputable section

/-- Evaluating a relabeled word with the relabeled oracle gives the relabeling of the original
word matrix. -/
theorem sourceRelabelWord_matrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (O : Matrix I I ℂ) (w : SourceWord I) :
    sourceWordMatrix (relabelGate e O) (sourceRelabelWord e w)=
      relabelGate e (sourceWordMatrix O w) := by
  simp only [sourceWordMatrix,sourceRelabelWord,List.map_map,← List.map_reverse,
    sourceRelabelGate_list_prod]
  congr 1
  congr 1
  funext s
  cases s with
  | inl U => rfl
  | inr b => cases b <;> simp [sourceRelabelGate_conjTranspose]
end
noncomputable section

/-- The purification program obtained by relabeling its initial matrix and both known matrices
of each layer. -/
def sourceRelabelProgram {I J : Type} [DecidableEq I] [DecidableEq J] (e : I ≃ J)
    (P : SourcePurificationProgram I) : SourcePurificationProgram J :=
  ⟨relabelGate e P.start,P.layers.map (fun p => (relabelGate e p.1,relabelGate e p.2))⟩
end
noncomputable section

/-- Taking the word of a relabeled purification program agrees with relabeling its word. -/
theorem sourceRelabelProgram_word {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (P : SourcePurificationProgram I) :
    sourcePurificationProgramWord (sourceRelabelProgram e P)=
      sourceRelabelWord e (sourcePurificationProgramWord P) := by
  have key : ∀ layers : List (Matrix I I ℂ × Matrix I I ℂ),
      (layers.map (fun p => (relabelGate e p.1,relabelGate e p.2))).flatMap
        sourcePurificationLayerWord=
      (layers.flatMap sourcePurificationLayerWord).map (Sum.map (relabelGate e) id) := by
    intro layers
    induction layers with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons,List.flatMap_cons,List.map_append,ih]
      rw [show sourcePurificationLayerWord (relabelGate e p.1,relabelGate e p.2)=
        (sourcePurificationLayerWord p).map (Sum.map (relabelGate e) id) from by
        simp [sourcePurificationLayerWord,List.map_cons,List.map_nil,Sum.map_inl,Sum.map_inr]]
  simp only [sourceRelabelProgram,sourcePurificationProgramWord,sourceRelabelWord,
    List.map_cons,Sum.map_inl,key]
end
noncomputable section

/-- Relabeling a legal purification program preserves legality. -/
theorem sourceRelabelProgram_legal {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (P : SourcePurificationProgram I)
    (hP : sourcePurificationProgramLegal P) :
    sourcePurificationProgramLegal (sourceRelabelProgram e P) := by
  refine ⟨sourceRelabelGate_unitary e P.start hP.1,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨sourceRelabelGate_unitary e q.1 (hP.2 q hq).1,
    sourceRelabelGate_unitary e q.2 (hP.2 q hq).2⟩
end
noncomputable section

/-- Relabeling a purification program preserves the oracle-call count of its word. -/
theorem sourceRelabelProgram_calls {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (P : SourcePurificationProgram I) :
    sourceWordCalls (sourcePurificationProgramWord (sourceRelabelProgram e P))=
      sourceWordCalls (sourcePurificationProgramWord P) := by
  rw [sourceRelabelProgram_word,sourceRelabelWord_calls]
end
noncomputable section

/-- The purification program that applies `U` before the original program by replacing its
initial matrix with `P.start*U`. -/
def sourceProgramPrependGate {S : Type} [Fintype S] (U : Matrix S S ℂ)
    (P : SourcePurificationProgram S) : SourcePurificationProgram S :=
  ⟨P.start*U,P.layers⟩
end
noncomputable section

/-- Prepending a known gate right-multiplies the original program matrix by that gate. -/
theorem sourceProgramPrependGate_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (U : Matrix S S ℂ) (P : SourcePurificationProgram S) :
    sourceWordMatrix O (sourcePurificationProgramWord (sourceProgramPrependGate U P))=
      sourceWordMatrix O (sourcePurificationProgramWord P)*U := by
  simp [sourcePurificationProgramWord_matrix,sourceProgramPrependGate,Matrix.mul_assoc]
end
noncomputable section

/-- Prepending a known gate preserves the program's oracle-call count. -/
theorem sourceProgramPrependGate_calls {S : Type} [Fintype S] (U : Matrix S S ℂ)
    (P : SourcePurificationProgram S) :
    sourceWordCalls (sourcePurificationProgramWord (sourceProgramPrependGate U P))=
      sourceWordCalls (sourcePurificationProgramWord P) := by
  simp [sourcePurificationProgramWord_calls,sourceProgramPrependGate]
end
noncomputable section

/-- Prepending a unitary known gate to a legal purification program preserves legality. -/
theorem sourceProgramPrependGate_legal {S : Type} [Fintype S] [DecidableEq S]
    (U : Matrix S S ℂ) (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (P : SourcePurificationProgram S) (hP : sourcePurificationProgramLegal P) :
    sourcePurificationProgramLegal (sourceProgramPrependGate U P) :=
  ⟨mul_mem hP.1 hU,hP.2⟩
end
noncomputable section

/-- The purification program that prepends the operation with matrix `V*Oᴴ*U*O*S0` to the
original program. -/
def sourceProgramPrependOp {S : Type} [Fintype S] (S0 U V : Matrix S S ℂ)
    (P : SourcePurificationProgram S) : SourcePurificationProgram S :=
  ⟨S0,(U,P.start*V)::P.layers⟩
end
noncomputable section

/-- Prepending an oracle operation right-multiplies the original program matrix by
`V*Oᴴ*U*O*S0`. -/
theorem sourceProgramPrependOp_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (S0 U V : Matrix S S ℂ) (P : SourcePurificationProgram S) :
    sourceWordMatrix O (sourcePurificationProgramWord (sourceProgramPrependOp S0 U V P))=
      sourceWordMatrix O (sourcePurificationProgramWord P)*(V*Oᴴ*U*O*S0) := by
  rw [sourcePurificationProgramWord_matrix,sourcePurificationProgramWord_matrix]
  simp only [sourceProgramPrependOp,List.map_cons,List.reverse_cons,List.prod_append,
    List.prod_cons,List.prod_nil,mul_one]
  simp [sourcePurificationLayerMatrix,Matrix.mul_assoc]
end
noncomputable section

/-- Prepending an oracle operation adds exactly two oracle calls. -/
theorem sourceProgramPrependOp_calls {S : Type} [Fintype S] (S0 U V : Matrix S S ℂ)
    (P : SourcePurificationProgram S) :
    sourceWordCalls (sourcePurificationProgramWord (sourceProgramPrependOp S0 U V P))=
      2+sourceWordCalls (sourcePurificationProgramWord P) := by
  rw [sourcePurificationProgramWord_calls,sourcePurificationProgramWord_calls]
  simp [sourceProgramPrependOp]
  omega
end
noncomputable section

/-- Prepending an oracle operation with unitary known matrices to a legal purification program
preserves legality. -/
theorem sourceProgramPrependOp_legal {S : Type} [Fintype S] [DecidableEq S]
    (S0 U V : Matrix S S ℂ) (hS0 : S0 ∈ Matrix.unitaryGroup S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) (hV : V ∈ Matrix.unitaryGroup S ℂ)
    (P : SourcePurificationProgram S) (hP : sourcePurificationProgramLegal P) :
    sourcePurificationProgramLegal (sourceProgramPrependOp S0 U V P) := by
  refine ⟨hS0,?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl|hp
  · exact ⟨hU,mul_mem hP.1 hV⟩
  · exact hP.2 p hp
end
noncomputable section

/-- A maximum fold is at most `B` when its initial value and every list element are at most `B`. -/
theorem sourceFoldl_max_le (l : List ℕ) (a B : ℕ) (ha : a≤B) (h : ∀ x ∈ l, x≤B) :
    l.foldl max a≤B := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    rw [List.foldl_cons]
    have hb := h b (List.mem_cons.mpr (Or.inl rfl))
    exact ih _ (by omega) (fun x hx => h x (List.mem_cons_of_mem b hx))
end
noncomputable section

/-- Taking the first `i` elements of `List.ofFn f` restricts `f` to `Fin i`. -/
theorem sourceOfFn_take {α : Type} {m : ℕ} (f : Fin m → α) (i : ℕ) (hi : i≤m) :
    (List.ofFn f).take i=List.ofFn (fun j : Fin i => f (Fin.castLE hi j)) := by
  apply List.ext_getElem
  · simp [List.length_take,List.length_ofFn,Nat.min_eq_left hi]
  · intro j h1 h2
    rw [List.getElem_take,List.getElem_ofFn,List.getElem_ofFn]
    congr 1
end
noncomputable section

/-- The sum of lengths of the lists before index `i` equals the corresponding finite sum of
their lengths. -/
theorem sourceTake_ofFn_lengths_sum {α : Type} {m : ℕ} (f : Fin m → List α) (i : Fin m) :
    (((List.ofFn f).take i.val).map List.length).sum=
      ∑ j : Fin i.val,(f (Fin.castLE (Nat.le_of_lt i.isLt) j)).length := by
  rw [sourceOfFn_take f i.val (Nat.le_of_lt i.isLt),List.map_ofFn,List.sum_ofFn]
  rfl
end
noncomputable section

/-- Lookup in a flattened list at a block's cumulative offset plus an internal index agrees with
lookup in that block. -/
theorem sourceFlatten_getD {α : Type} (d : α) : ∀ (ls : List (List α)) (i : ℕ)
    (hi : i<ls.length) (j : ℕ) (_hj : j<(ls[i]'hi).length),
    ls.flatten.getD (((ls.take i).map List.length).sum+j) d=(ls[i]'hi).getD j d := by
  intro ls
  induction ls with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi j hj
    cases i with
    | zero =>
      simp only [List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add,
        List.flatten_cons,List.getElem_cons_zero] at hj ⊢
      exact List.getD_append _ _ _ _ hj
    | succ i =>
      have hi' : i<l.length := by
        simp only [List.length_cons] at hi
        omega
      have hj' : j<(l[i]'hi').length := by
        have hh := hj
        rw [List.getElem_cons_succ] at hh
        exact hh
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons,
        List.getElem_cons_succ] at ⊢
      rw [Nat.add_assoc,List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact ih i hi' j hj'
end
noncomputable section

/-- A block-diagonal matrix acts independently on the state slice of each block. -/
theorem sourceBlockDiagonal'_mulVec {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (M : ∀ i,Matrix (S i) (S i) ℂ) (ψ : (Σ i,S i) → ℂ) :
    Matrix.blockDiagonal' M *ᵥ ψ=fun p => (M p.1 *ᵥ fun y => ψ ⟨p.1,y⟩) p.2 := by
  funext ⟨i,y⟩
  simp only [Matrix.mulVec,dotProduct]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro i' _ hi'
    apply Finset.sum_eq_zero
    intro y' _
    rw [Matrix.blockDiagonal'_apply_ne M y y' hi'.symm,zero_mul]
  · simp
end
noncomputable section

/-- The block-diagonal matrix of permutation matrices is the permutation matrix acting within
each block. -/
theorem sourceBlockDiagonal'_permMatrix {I : Type} [DecidableEq I]
    {S : I → Type} [∀ i,DecidableEq (S i)] (σ : ∀ i,S i → S i) :
    Matrix.blockDiagonal' (fun i => permMatrix (σ i))=
      permMatrix (fun p : Σ i,S i => ⟨p.1,σ p.1 p.2⟩) := by
  ext ⟨i,a⟩ ⟨i',b⟩
  by_cases h : i=i'
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq,permMatrix,Matrix.of_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    symm
    simp only [permMatrix,Matrix.of_apply]
    rw [if_neg (fun hh => h (congrArg Sigma.fst hh))]
end
noncomputable section

/-- The purification value-negation gate is unitary. -/
theorem sourcePurifyFlipGate_unitary {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ} :
    sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L) ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary_of_injective (Equiv.injective _)
end
noncomputable section

/-- The purification address-swap gate is unitary. -/
theorem sourcePurifySwapGate_unitary {H : Type} [Fintype H] [DecidableEq H] {n q r L : ℕ} :
    sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L) ∈ Matrix.unitaryGroup _ ℂ :=
  permMatrix_unitary_of_injective (Equiv.injective _)
end
noncomputable section

/-- On states supported at spare address `n`, the layer formed from two swap gates, the adjoint
oracle, and the oracle acts as a single lifted oracle. -/
theorem sourcePurifySwapGate_layer {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X)
    (st : QState (Fin L × SourceSpace n q H r × Fin (n+1)))
    (hclean : ∀ (l : Fin L) (s : SourceSpace n q H r) (w : Fin (n+1)),
      w≠(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) → st (l,s,w)=0) :
    (sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)*
      (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ*
      sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)*
      sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L)) *ᵥ st=
    sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L) *ᵥ st :=
  sourcePurify_swapLayer input x st hclean
end
noncomputable section

/-- Conjugating the lifted oracle by the purification flip gate gives the adjoint oracle. -/
theorem sourcePurifyFlipGate_conj {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r L : ℕ}
    (input : X → Fin n → Fin (q+1)) (x : X) :
    sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)*
      sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L)*
      sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=L)=
    (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=L))ᴴ :=
  sourcePurifyFlip_conj input x
end
noncomputable section

/-- Every legal adaptive computation has a legal purification program using at most twice as
many oracle calls and exactly reproducing its recorded pure output from the initialized
input embedding. -/
theorem sourceAdaptive_purify_program {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) :
    ∀ (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    ∀ (hL : 0<max 1 (sourceAdaptiveLeaves T)),
    ∃ P : SourcePurificationProgram
        (Fin (max 1 (sourceAdaptiveLeaves T)) × SourceSpace n q H r × Fin (n+1)),
      sourcePurificationProgramLegal P ∧
      sourceWordCalls (sourcePurificationProgramWord P)≤2*sourceAdaptiveCalls T ∧
      ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
        sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves T))) (sourcePurificationProgramWord P) *ᵥ
          (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves T)) hL *ᵥ ψ)=
        sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves T)) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) T ψ := by
  haveI : Nonempty (SourceSpace n q H r) :=
    ⟨⟨⟨⟨0,Nat.succ_pos n⟩,⟨0,Nat.succ_pos q⟩⟩,⟨⟨true,Classical.arbitrary H⟩,⟨0,hr⟩⟩⟩⟩
  intro T
  induction T with
  | finish =>
    intro _hT hL
    refine ⟨⟨1,[]⟩,⟨(Matrix.unitaryGroup _ ℂ).one_mem,fun p hp => by simp at hp⟩,?_,?_⟩
    · rw [sourcePurificationProgramWord_calls]
      simp
    · intro x ψ
      rw [sourcePurificationProgramWord_matrix]
      simp only [List.map_nil,List.reverse_nil,List.prod_nil,Matrix.one_mul,Matrix.one_mulVec]
      funext ⟨i,s,w⟩
      rw [sourcePurifyIn_apply,sourcePurifyOut_apply]
      (try dsimp only)
      have hi : i=(⟨0,hL⟩ : Fin (max 1 (sourceAdaptiveLeaves SourceAdaptive.finish))) := by
        apply Fin.ext
        have hh : i.val<1 := i.isLt
        show i.val=0
        omega
      have hiv : i.val=0 := by
        rw [hi]
      by_cases hw : w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
      · rw [if_pos ⟨hi,hw⟩,if_pos hw]
        simp [sourceAdaptivePure,sourceAdaptiveBranches]
      · rw [if_neg (fun hh => hw hh.2),if_neg hw]
  | known U next ih =>
    intro hT hL
    have hL' : 0<max 1 (sourceAdaptiveLeaves next) := hL
    obtain ⟨P,hPleg,hPcalls,hPtrans⟩ := ih hT.2 hL'
    show ∃ P : SourcePurificationProgram
        (Fin (max 1 (sourceAdaptiveLeaves next)) × SourceSpace n q H r × Fin (n+1)),
      sourcePurificationProgramLegal P ∧
      sourceWordCalls (sourcePurificationProgramWord P)≤2*sourceAdaptiveCalls next ∧
      ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
        sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves next))) (sourcePurificationProgramWord P) *ᵥ
          (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
        sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) next (U *ᵥ ψ)
    refine ⟨sourceProgramPrependGate
      (sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) U) P,?_,?_,?_⟩
    · exact sourceProgramPrependGate_legal _ (sourcePurifyGate_unitary U hT.1) P hPleg
    · rw [sourceProgramPrependGate_calls]
      exact hPcalls
    · intro x ψ
      rw [sourceProgramPrependGate_matrix,← Matrix.mulVec_mulVec]
      have hgate : sourcePurifyGate (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) U *ᵥ
          (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
        sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ
          (U *ᵥ ψ) := by
        have hh := congrArg (fun M : Matrix _ _ ℂ => M*ᵥψ) (sourcePurifyGate_mul_in U hL')
        simpa only [Matrix.mulVec_mulVec] using! hh
      rw [hgate,hPtrans x (U *ᵥ ψ)]
  | query adj next ih =>
    intro hT hL
    have hL' : 0<max 1 (sourceAdaptiveLeaves next) := hL
    obtain ⟨P,hPleg,hPcalls,hPtrans⟩ := ih hT hL'
    cases adj with
    | false =>
      show ∃ P : SourcePurificationProgram
          (Fin (max 1 (sourceAdaptiveLeaves next)) × SourceSpace n q H r × Fin (n+1)),
        sourcePurificationProgramLegal P ∧
        sourceWordCalls (sourcePurificationProgramWord P)≤2*(1+sourceAdaptiveCalls next) ∧
        ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
          sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next))) (sourcePurificationProgramWord P) *ᵥ
            (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
          sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) *ᵥ
            sourceAdaptivePure (sourceAlphabetOracle input x) next
              (sourceAlphabetOracle input x *ᵥ ψ)
      refine ⟨sourceProgramPrependOp 1
        (sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))
        (sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))
        P,?_,?_,?_⟩
      · exact sourceProgramPrependOp_legal _ _ _
          (Matrix.unitaryGroup _ ℂ).one_mem sourcePurifySwapGate_unitary
          sourcePurifySwapGate_unitary P hPleg
      · rw [sourceProgramPrependOp_calls]
        omega
      · intro x ψ
        rw [sourceProgramPrependOp_matrix,mul_one,← Matrix.mulVec_mulVec]
        have hclean : ∀ (l : Fin (max 1 (sourceAdaptiveLeaves next)))
            (s : SourceSpace n q H r) (w : Fin (n+1)),
            w≠(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) →
            (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)
              (l,s,w)=0 := by
          intro l s w hw
          rw [sourcePurifyIn_apply]
          exact if_neg (fun hh => hw hh.2)
        rw [sourcePurifySwapGate_layer input x _ hclean]
        have hor : sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves next)) *ᵥ
            (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
          sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ
            (sourceAlphabetOracle input x *ᵥ ψ) := by
          have hh := congrArg (fun M : Matrix _ _ ℂ => M*ᵥψ)
            (sourcePurifyOracle_mul_in input x hL')
          simpa only [Matrix.mulVec_mulVec] using! hh
        rw [hor,hPtrans x (sourceAlphabetOracle input x *ᵥ ψ)]
    | true =>
      show ∃ P : SourcePurificationProgram
          (Fin (max 1 (sourceAdaptiveLeaves next)) × SourceSpace n q H r × Fin (n+1)),
        sourcePurificationProgramLegal P ∧
        sourceWordCalls (sourcePurificationProgramWord P)≤2*(1+sourceAdaptiveCalls next) ∧
        ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
          sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next))) (sourcePurificationProgramWord P) *ᵥ
            (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
          sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) *ᵥ
            sourceAdaptivePure (sourceAlphabetOracle input x) next
              ((sourceAlphabetOracle input x)ᴴ *ᵥ ψ)
      refine ⟨sourceProgramPrependOp
        (sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))
        (sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))
        (sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next))*
          sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))
        P,?_,?_,?_⟩
      · exact sourceProgramPrependOp_legal _ _ _ sourcePurifyFlipGate_unitary
          sourcePurifySwapGate_unitary
          (mul_mem sourcePurifyFlipGate_unitary sourcePurifySwapGate_unitary) P hPleg
      · rw [sourceProgramPrependOp_calls]
        omega
      · intro x ψ
        rw [sourceProgramPrependOp_matrix,← Matrix.mulVec_mulVec]
        have hOsm : sourceAlphabetOracle (W:=(Bool × H) × Fin r) input x ∈
            Matrix.unitaryGroup _ ℂ := by
          rw [sourceAlphabetOracle_eq_permMatrix]
          exact permMatrix_unitary_of_injective (Equiv.injective _)
        have hOlog : sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves next)) ∈ Matrix.unitaryGroup
              (Fin (max 1 (sourceAdaptiveLeaves next)) × SourceSpace n q H r × Fin (n+1)) ℂ :=
          sourcePurifyOracle_unitary input x
        have hadj : (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves next)))ᴴ*
            sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL'=
          sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL'*
            (sourceAlphabetOracle input x)ᴴ :=
          sourceFrame_adjoint _ _ _ hOlog hOsm (sourcePurifyOracle_mul_in input x hL')
        have hcleanflip : ∀ (l : Fin (max 1 (sourceAdaptiveLeaves next)))
            (s : SourceSpace n q H r) (w : Fin (n+1)),
            w≠(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) →
            (sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next)) *ᵥ
              (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ))
              (l,s,w)=0 := by
          intro l s w hw
          rw [sourcePurifyFlipGate,sourcePermMatrix_equiv_mulVec,sourcePurifyIn_apply]
          exact if_neg (fun hh => hw hh.2)
        have hstep : ((sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next))*
            sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))*
            (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next)))ᴴ*
            sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next))*
            sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=max 1 (sourceAdaptiveLeaves next))*
            sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves next))) *ᵥ
            (sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ ψ)=
          sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)) hL' *ᵥ
            ((sourceAlphabetOracle input x)ᴴ *ᵥ ψ) := by
          have hag : (sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
                (L:=max 1 (sourceAdaptiveLeaves next))*
              sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next)))*
              (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
                (L:=max 1 (sourceAdaptiveLeaves next)))ᴴ*
              sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves next))*
              sourcePurifyOracle (n:=n) (q:=q) input x (r:=r) (L:=max 1 (sourceAdaptiveLeaves next))*
              sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
                (L:=max 1 (sourceAdaptiveLeaves next))=
            sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
                (L:=max 1 (sourceAdaptiveLeaves next))*
              (sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r)
                  (L:=max 1 (sourceAdaptiveLeaves next))*
                (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
                  (L:=max 1 (sourceAdaptiveLeaves next)))ᴴ*
                sourcePurifySwapGate (H:=H) (n:=n) (q:=q) (r:=r)
                  (L:=max 1 (sourceAdaptiveLeaves next))*
                sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
                  (L:=max 1 (sourceAdaptiveLeaves next)))*
              sourcePurifyFlipGate (H:=H) (n:=n) (q:=q) (r:=r)
                (L:=max 1 (sourceAdaptiveLeaves next)) := by
            simp only [Matrix.mul_assoc]
          rw [hag,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
            sourcePurifySwapGate_layer input x _ hcleanflip]
          rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,sourcePurifyFlipGate_conj]
          have hh := congrArg (fun M : Matrix _ _ ℂ => M*ᵥψ) hadj
          simpa only [Matrix.mulVec_mulVec] using! hh
        rw [hstep,hPtrans x ((sourceAlphabetOracle input x)ᴴ *ᵥ ψ)]
  | instrument m K next ih =>
    intro hT hL
    have hL' : 0<max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum) := hL
    show ∃ P : SourcePurificationProgram
        (Fin (max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) ×
          SourceSpace n q H r × Fin (n+1)),
      sourcePurificationProgramLegal P ∧
      sourceWordCalls (sourcePurificationProgramWord P)≤
        2*(List.ofFn (fun i => sourceAdaptiveCalls (next i))).foldl max 0 ∧
      ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
        sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)))
          (sourcePurificationProgramWord P) *ᵥ
          (sourcePurifyIn (n:=n) (q:=q) (r:=r)
            (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) hL' *ᵥ ψ)=
        sourcePurifyOut (n:=n) (q:=q) (r:=r)
          (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) (SourceAdaptive.instrument m K next) ψ
    have hm : 0<m := sourceInstrument_outcome_positive K hT.1
    have hpos : ∀ i, 0<sourceAdaptiveLeaves (next i) :=
      fun i => sourceAdaptive_leaves_positive _ (hT.2 i)
    have hLfi : ∀ i, max 1 (sourceAdaptiveLeaves (next i))=sourceAdaptiveLeaves (next i) :=
      fun i => Nat.max_eq_right (hpos i)
    have hsum1 : 1≤∑ i, sourceAdaptiveLeaves (next i) :=
      le_trans (hpos ⟨0,hm⟩) (Finset.single_le_sum
        (f := fun i : Fin m => sourceAdaptiveLeaves (next i))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
    have hLL : max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)=
        ∑ i, max 1 (sourceAdaptiveLeaves (next i)) := by
      rw [List.sum_ofFn,max_eq_right hsum1]
      exact Finset.sum_congr rfl fun i _ => (hLfi i).symm
    set e_leaf_inv : (Σ i, Fin (max 1 (sourceAdaptiveLeaves (next i)))) ≃
        Fin (max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) :=
      finSigmaFinEquiv.trans (finCongr hLL.symm) with heli
    have heli_val : ∀ (i : Fin m) (j : Fin (max 1 (sourceAdaptiveLeaves (next i)))),
        (e_leaf_inv ⟨i,j⟩).val=
          ∑ i' : Fin i.val,max 1 (sourceAdaptiveLeaves (next (Fin.castLE (Nat.le_of_lt i.isLt) i')))+
            j.val := by
      intro i j
      rw [heli,Equiv.trans_apply]
      have hc : ∀ k : (i : Fin m) × Fin (max 1 (sourceAdaptiveLeaves (next i))),
          (finCongr hLL.symm (finSigmaFinEquiv k)).val=(finSigmaFinEquiv k).val :=
        fun k => rfl
      rw [hc ⟨i,j⟩,finSigmaFinEquiv_apply]
    set e_instr : (Fin (max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) ×
        SourceSpace n q H r × Fin (n+1)) ≃
        (Σ i, Fin (max 1 (sourceAdaptiveLeaves (next i))) × SourceSpace n q H r × Fin (n+1)) :=
      { toFun := fun y => ⟨(e_leaf_inv.symm y.1).1,(⟨(e_leaf_inv.symm y.1).2,y.2.1,y.2.2⟩)⟩,
        invFun := fun p => (e_leaf_inv ⟨p.1,p.2.1⟩,p.2.2.1,p.2.2.2),
        left_inv := fun y => by
          obtain ⟨g,s,w⟩ := y
          show (e_leaf_inv ⟨(e_leaf_inv.symm g).1,(e_leaf_inv.symm g).2⟩,s,w)=(g,s,w)
          rw [Sigma.eta]
          have hh := Equiv.symm_apply_apply e_leaf_inv.symm g
          rw [Equiv.symm_symm] at hh
          rw [hh]
        right_inv := fun p => by
          obtain ⟨i,j,s,w⟩ := p
          show (⟨(e_leaf_inv.symm (e_leaf_inv ⟨i,j⟩)).1,
              ⟨(e_leaf_inv.symm (e_leaf_inv ⟨i,j⟩)).2,s,w⟩⟩ :
            (Σ i', Fin (max 1 (sourceAdaptiveLeaves (next i'))) × SourceSpace n q H r ×
              Fin (n+1)))=⟨i,j,s,w⟩
          rw [Equiv.symm_apply_apply e_leaf_inv ⟨i,j⟩] } with hei
    set c_a : Fin m × SourceSpace n q H r →
        Fin (max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) ×
          SourceSpace n q H r × Fin (n+1) :=
      fun p => (e_leaf_inv ⟨p.1,⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩,p.2,
        ⟨n,Nat.lt_succ_self n⟩) with hca
    have hca_inj : Function.Injective c_a := by
      rintro ⟨i,s⟩ ⟨i',s'⟩ h
      have h1 : e_leaf_inv ⟨i,⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩=
          e_leaf_inv ⟨i',⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩⟩ :=
        congrArg (fun y => y.1) h
      have hi : i=i' := congrArg Sigma.fst (e_leaf_inv.injective h1)
      have hs : s=s' := congrArg (fun y => y.2.1) h
      exact Prod.ext hi hs
    set F_a : Matrix (Fin (max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) ×
        SourceSpace n q H r × Fin (n+1)) (Fin m × SourceSpace n q H r) ℂ :=
      sourceBasisFrame c_a with hFa
    have hFa_iso : F_aᴴ*F_a=1 := sourceBasisFrame_isometry _ hca_inj
    have hKm : (sourceInstrumentMatrix K)ᴴ*sourceInstrumentMatrix K=1 :=
      sourceInstrumentMatrix_isometry K hT.1
    obtain ⟨G_K,hGKu,hGK⟩ := sourcePublic_isometry_transport _ _
      (sourcePurifyIn_isometry hL') (sourceComposeFrames_isometry _ _ hFa_iso hKm)
    choose P hP using fun i => ih i (hT.2 i) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    set Lmax := (List.ofFn (fun i => (P i).layers.length)).foldl max 0 with hLmaxdef
    set block := sourcePurificationBlockProgram (fun i => P i) Lmax with hblockdef
    refine ⟨sourceProgramPrependGate G_K (sourceRelabelProgram e_instr.symm block),?_,?_,?_⟩
    · exact sourceProgramPrependGate_legal G_K hGKu _
        (sourceRelabelProgram_legal _ _
          (sourcePurificationBlockProgram_legal _ (fun i => (hP i).1) Lmax))
    · rw [sourceProgramPrependGate_calls,sourceRelabelProgram_calls,
        sourcePurificationProgramWord_calls]
      have hblen : block.layers.length=Lmax := by
        rw [hblockdef]
        simp [sourcePurificationBlockProgram]
      rw [hblen]
      have hpc : ∀ i, (P i).layers.length≤sourceAdaptiveCalls (next i) := by
        intro i
        have hh := (hP i).2.1
        rw [sourcePurificationProgramWord_calls] at hh
        omega
      have hfold : (List.ofFn (fun i => (P i).layers.length)).foldl max 0≤
          (List.ofFn (fun i => sourceAdaptiveCalls (next i))).foldl max 0 := by
        refine sourceFoldl_max_le _ 0 _ (Nat.zero_le _) ?_
        intro x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact le_trans (hpc i) (sourceList_mem_le_foldl_max _ 0 _
          (List.mem_ofFn.mpr ⟨i,rfl⟩ : sourceAdaptiveCalls (next i)∈
            List.ofFn (fun i => sourceAdaptiveCalls (next i))))
      exact Nat.mul_le_mul_left 2 hfold
    · intro x ψ
      have hOSig : (Matrix.blockDiagonal' (fun i => sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
          (L:=max 1 (sourceAdaptiveLeaves (next i)))))=
        permMatrix (fun p : (Σ i, Fin (max 1 (sourceAdaptiveLeaves (next i))) ×
            SourceSpace n q H r × Fin (n+1)) =>
          ⟨p.1,sourcePurifyLift (sourceSmallShift (r:=r) input x) p.2⟩) := by
        simp only [sourcePurifyOracle]
        exact sourceBlockDiagonal'_permMatrix
          (σ := fun i => ⇑(sourcePurifyLift (sourceSmallShift (r:=r) input x)))
      have hconj : relabelGate e_instr.symm
          (Matrix.blockDiagonal' (fun i => sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves (next i)))))=
        sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
          (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) := by
        rw [hOSig]
        apply sourceRelabelGate_permMatrix
        rintro ⟨i,j,s,w⟩
        rfl
      have hmat : sourceWordMatrix
          (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)))
          (sourcePurificationProgramWord
            (sourceProgramPrependGate G_K (sourceRelabelProgram e_instr.symm block)))=
        relabelGate e_instr.symm (Matrix.blockDiagonal' (fun i =>
          sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves (next i))))
            (sourcePurificationProgramWord (P i))))*G_K := by
        rw [sourceProgramPrependGate_matrix]
        congr 1
        rw [sourceRelabelProgram_word,← hconj,sourceRelabelWord_matrix,hblockdef,
          sourcePurificationBlockProgram_matrix]
        apply congrArg (relabelGate e_instr.symm)
        ext ⟨i,a⟩ ⟨i',b⟩
        by_cases hii : i=i'
        · subst hii
          simp only [Matrix.blockDiagonal'_apply_eq]
          rw [sourcePurificationPad_matrix _ (sourcePurifyOracle_unitary input x) _ _
            (sourceList_mem_le_foldl_max _ 0 _
              (List.mem_ofFn.mpr ⟨i,rfl⟩ : (P i).layers.length∈
                List.ofFn (fun i => (P i).layers.length)))]
        · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hii,Matrix.blockDiagonal'_apply_ne _ _ _ hii]
      rw [hmat,← Matrix.mulVec_mulVec]
      have hGv : G_K *ᵥ (sourcePurifyIn (n:=n) (q:=q) (r:=r)
          (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) hL' *ᵥ ψ)=
        F_a *ᵥ (sourceInstrumentMatrix K *ᵥ ψ) := by
        have hh := congrArg (fun M : Matrix _ _ ℂ => M*ᵥψ) hGK
        simpa only [Matrix.mulVec_mulVec] using! hh
      rw [hGv,sourceRelabelGate_mulVec]
      simp only [Equiv.symm_symm]
      have hFa_apply : ∀ (i : Fin m) (j : Fin (max 1 (sourceAdaptiveLeaves (next i))))
          (s : SourceSpace n q H r) (w : Fin (n+1))
          (χ : Fin m × SourceSpace n q H r → ℂ),
        (F_a *ᵥ χ) (e_leaf_inv ⟨i,j⟩,s,w)=
          if j=(⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ :
              Fin (max 1 (sourceAdaptiveLeaves (next i))))∧
            w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
          then χ (i,s) else 0 := by
        intro i j s w χ
        rw [hFa]
        simp only [sourceBasisFrame,Matrix.mulVec,dotProduct]
        by_cases hj : j=(⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ :
          Fin (max 1 (sourceAdaptiveLeaves (next i))))
        · subst hj
          by_cases hw : w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
          · subst hw
            rw [if_pos ⟨rfl,rfl⟩]
            rw [Finset.sum_eq_single (i,s)]
            · rw [if_pos rfl,one_mul]
            · intro ⟨i',s'⟩ _ hne
              rw [if_neg (show (e_leaf_inv ⟨i,⟨0,_⟩⟩,s,⟨n,Nat.lt_succ_self n⟩)≠c_a (i',s') from
                fun hh => hne (Prod.ext (congrArg Sigma.fst (e_leaf_inv.injective
                  (congrArg (fun y => y.1) hh))).symm (congrArg (fun y => y.2.1) hh).symm)),zero_mul]
            · simp
          · rw [if_neg (fun hh => hw hh.2)]
            apply Finset.sum_eq_zero
            intro ⟨i',s'⟩ _
            rw [if_neg (show (e_leaf_inv ⟨i,⟨0,_⟩⟩,s,w)≠c_a (i',s') from fun hh =>
              hw (congrArg (fun y => y.2.2) hh)),zero_mul]
        · rw [if_neg (fun hh => hj hh.1)]
          apply Finset.sum_eq_zero
          intro ⟨i',s'⟩ _
          rw [if_neg (show (e_leaf_inv ⟨i,j⟩,s,w)≠c_a (i',s') from fun hh => hj (by
            have h1 := e_leaf_inv.injective (congrArg (fun y => y.1) hh)
            have hi : i=i' := congrArg Sigma.fst h1
            subst hi
            have h2 := (Sigma.mk.inj_iff.mp h1).2
            exact heq_iff_eq.mp h2)),zero_mul]
      have hB : (Matrix.blockDiagonal' (fun i => sourceWordMatrix
            (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
              (L:=max 1 (sourceAdaptiveLeaves (next i))))
            (sourcePurificationProgramWord (P i))) *ᵥ
          fun p : (Σ i, Fin (max 1 (sourceAdaptiveLeaves (next i))) ×
              SourceSpace n q H r × Fin (n+1)) =>
            (F_a *ᵥ (sourceInstrumentMatrix K *ᵥ ψ)) (e_instr.symm p))=
        fun p => (sourcePurifyOut (n:=n) (q:=q) (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves (next p.1))) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) (next p.1) (K p.1 *ᵥ ψ)) p.2 := by
        rw [sourceBlockDiagonal'_mulVec]
        funext ⟨i,y⟩
        show (sourceWordMatrix (sourcePurifyOracle (n:=n) (q:=q) input x (r:=r)
            (L:=max 1 (sourceAdaptiveLeaves (next i))))
            (sourcePurificationProgramWord (P i)) *ᵥ
            (fun y' => (F_a *ᵥ (sourceInstrumentMatrix K *ᵥ ψ)) (e_instr.symm ⟨i,y'⟩))) y=
          (sourcePurifyOut (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves (next i))) *ᵥ
            sourceAdaptivePure (sourceAlphabetOracle input x) (next i) (K i *ᵥ ψ)) y
        have hθ : (fun y' => (F_a *ᵥ (sourceInstrumentMatrix K *ᵥ ψ)) (e_instr.symm ⟨i,y'⟩))=
            sourcePurifyIn (n:=n) (q:=q) (r:=r) (L:=max 1 (sourceAdaptiveLeaves (next i)))
              (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) *ᵥ (K i *ᵥ ψ) := by
          funext ⟨j,s,w⟩
          show (F_a *ᵥ (sourceInstrumentMatrix K *ᵥ ψ)) (e_leaf_inv ⟨i,j⟩,s,w)=_
          rw [hFa_apply,sourcePurifyIn_apply]
          show (if j=(⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ :
                Fin (max 1 (sourceAdaptiveLeaves (next i))))∧
              w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) then
              (sourceInstrumentMatrix K *ᵥ ψ) (i,s) else 0)=
            if j=(⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ :
                Fin (max 1 (sourceAdaptiveLeaves (next i))))∧
              w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1)) then (K i *ᵥ ψ) s else 0
          by_cases hcond : j=(⟨0,lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩ :
              Fin (max 1 (sourceAdaptiveLeaves (next i))))∧
            w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
          · rw [if_pos hcond,if_pos hcond]
            simp [sourceInstrumentMatrix,Matrix.mulVec,dotProduct]
          · rw [if_neg hcond,if_neg hcond]
        rw [hθ]
        exact congrFun ((hP i).2.2 x (K i *ᵥ ψ)) y
      rw [hB]
      funext ⟨g,s,w⟩
      show (sourcePurifyOut (n:=n) (q:=q) (r:=r)
          (L:=max 1 (sourceAdaptiveLeaves (next (e_leaf_inv.symm g).1))) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) (next (e_leaf_inv.symm g).1)
            (K (e_leaf_inv.symm g).1 *ᵥ ψ)) ((e_leaf_inv.symm g).2,s,w)=
        (sourcePurifyOut (n:=n) (q:=q) (r:=r)
          (L:=max 1 ((List.ofFn fun i => sourceAdaptiveLeaves (next i)).sum)) *ᵥ
          sourceAdaptivePure (sourceAlphabetOracle input x) (SourceAdaptive.instrument m K next) ψ)
          (g,s,w)
      simp only [sourcePurifyOut_apply]
      by_cases hw : w=(⟨n,Nat.lt_succ_self n⟩ : Fin (n+1))
      · subst hw
        rw [if_pos rfl,if_pos rfl]
        have hgl : (e_leaf_inv ⟨(e_leaf_inv.symm g).1,(e_leaf_inv.symm g).2⟩)=g := by
          have hh := Equiv.symm_apply_apply e_leaf_inv.symm g
          rw [Equiv.symm_symm] at hh
          rw [Sigma.eta]
          exact hh
        have hgval : g.val=
            (((List.ofFn fun i => sourceAdaptiveBranches (sourceAlphabetOracle input x)
              (next i) (K i *ᵥ ψ)).take (e_leaf_inv.symm g).1.val).map List.length).sum+
            (e_leaf_inv.symm g).2.val := by
          have h2 : g.val=(e_leaf_inv ⟨(e_leaf_inv.symm g).1,(e_leaf_inv.symm g).2⟩).val :=
            congrArg Fin.val hgl.symm
          rw [h2,heli_val]
          congr 1
          rw [sourceTake_ofFn_lengths_sum]
          apply Finset.sum_congr rfl
          intro i' _
          rw [hLfi,sourceAdaptive_branches_length]
        have hjlt : (e_leaf_inv.symm g).2.val<((List.ofFn fun i => sourceAdaptiveBranches
            (sourceAlphabetOracle input x) (next i) (K i *ᵥ ψ))[(e_leaf_inv.symm g).1.val]'
            (by rw [List.length_ofFn]; exact (e_leaf_inv.symm g).1.isLt)).length := by
          rw [List.getElem_ofFn,sourceAdaptive_branches_length,Fin.eta]
          exact lt_of_lt_of_eq (e_leaf_inv.symm g).2.isLt (hLfi _)
        show sourceAdaptivePure (sourceAlphabetOracle input x) (next (e_leaf_inv.symm g).1)
            (K (e_leaf_inv.symm g).1 *ᵥ ψ) ((e_leaf_inv.symm g).2,s)=
          ((List.ofFn fun i => sourceAdaptiveBranches (sourceAlphabetOracle input x) (next i)
            (K i *ᵥ ψ)).flatten.getD g.val 0) s
        rw [hgval,sourceFlatten_getD 0 _ _ _ _ hjlt,List.getElem_ofFn]
        simp only [sourceAdaptivePure,Fin.eta]
      · rw [if_neg hw,if_neg hw]
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
