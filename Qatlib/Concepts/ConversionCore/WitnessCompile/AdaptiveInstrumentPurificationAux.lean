/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetPhaseWordAssemblyQuan
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.GetD

/-!
# Auxiliary constructions for adaptive purification

This module develops recorded branch operators, their completeness identities, and isometric
embeddings for legal adaptive computations. `sourceAdaptivePureMatrix` packages the recorded
output as an isometry, using the finite-dimensional instrument framework described in
[Watrous2018].

`SourcePurificationProgram` represents a known initial gate followed by layers containing a
forward and an adjoint oracle call. Padding and block-diagonal constructions support the
recursive purification compiler.

## Main statements

* `sourceAdaptive_operators_complete`: completeness of adaptive branch operators.
* `sourceAdaptivePureMatrix_isometry`: isometry of the recorded output matrix.
* `sourceAdaptive_zero_query_compiler`: compilation of computations with no oracle calls.
* `sourcePurificationBlockProgram_matrix`: evaluation of block-diagonal programs.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
noncomputable section

/-- The inner product is additive over a finite sum in its second argument. -/
theorem sourceInner_sum_right {H I : Type} [Fintype H] [Fintype I]
    (ψ : QState H) (φ : I → QState H) : Qatlib.Foundations.PureStateMath.Inner ψ (∑ i,φ i)=∑ i,Qatlib.Foundations.PureStateMath.Inner ψ (φ i) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Finset.sum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
end
noncomputable section

/-- A complete family of Kraus matrices preserves the total squared norm when summed over its
outcomes. -/
theorem sourceInstrument_mass {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (K : Fin m → Matrix H H ℂ) (hK : (∑ i,(K i)ᴴ*K i)=1) (ψ : QState H) :
    (∑ i, ‖toEuclidean_fromVec (K i*ᵥψ)‖^2)=‖toEuclidean_fromVec ψ‖^2 := by
  have hi (i : Fin m) : Qatlib.Foundations.PureStateMath.Inner (K i*ᵥψ) (K i*ᵥψ)=Qatlib.Foundations.PureStateMath.Inner ψ (((K i)ᴴ*K i)*ᵥψ) := by
    simp only [Qatlib.Foundations.PureStateMath.Inner,Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec]
  have hv : (∑ i,((K i)ᴴ*K i)*ᵥψ)=(∑ i,(K i)ᴴ*K i)*ᵥψ := by
    ext p
    simp only [Finset.sum_apply,Matrix.mulVec,dotProduct,Matrix.sum_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  simp_rw [norm_toEuclidean_sq_eq_re_inner,hi]
  rw [← Complex.re_sum,← sourceInner_sum_right ψ, hv,hK,Matrix.one_mulVec]
end
noncomputable section

/-- A complete instrument on a nonempty state space has at least one outcome. -/
theorem sourceInstrument_outcome_positive {H : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    {m : ℕ} (K : Fin m → Matrix H H ℂ) (hK : (∑ i,(K i)ᴴ*K i)=1) : 0<m := by
  by_contra hm
  have he : m=0 := by omega
  subst m
  have hp := congrFun (congrFun hK (Classical.arbitrary H)) (Classical.arbitrary H)
  simp at hp
end
noncomputable section

/-- A legal adaptive computation on a nonempty state space has a positive number of leaves. -/
theorem sourceAdaptive_leaves_positive {H : Type} [Fintype H] [DecidableEq H] [Nonempty H]
    (T : SourceAdaptive H) (hT : sourceAdaptiveLegal T) : 0<sourceAdaptiveLeaves T := by
  induction T with
  | finish => simp [sourceAdaptiveLeaves]
  | known U next ih => exact ih hT.2
  | query adj next ih => exact ih hT
  | instrument m K next ih =>
    have hm := sourceInstrument_outcome_positive K hT.1
    let j : Fin m := ⟨0,hm⟩
    have hj := ih j (hT.2 j)
    have hs : sourceAdaptiveLeaves (next j) ≤ ∑ i,sourceAdaptiveLeaves (next i) :=
      Finset.single_le_sum (f := fun i : Fin m => sourceAdaptiveLeaves (next i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simpa only [sourceAdaptiveLeaves,List.sum_ofFn] using! hj.trans_le hs
end
noncomputable section

/-- The branch-state list has length equal to the number of leaves of the adaptive computation. -/
theorem sourceAdaptive_branches_length {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) :
    (sourceAdaptiveBranches O T ψ).length=sourceAdaptiveLeaves T := by
  induction T generalizing ψ with
  | finish => simp [sourceAdaptiveBranches,sourceAdaptiveLeaves]
  | known U next ih => exact ih _
  | query adj next ih => exact ih _
  | instrument m K next ih =>
    simp only [sourceAdaptiveBranches,sourceAdaptiveLeaves,List.length_flatten,List.map_ofFn]
    apply congrArg List.sum
    congr 1
    funext i
    exact ih i _
end
noncomputable section

/-- For a unitary oracle and a legal adaptive computation, the sum of squared branch norms
equals the squared input norm. -/
theorem sourceAdaptive_branches_mass {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (hO : O ∈ Matrix.unitaryGroup H ℂ)
    (T : SourceAdaptive H) (hT : sourceAdaptiveLegal T) (ψ : QState H) :
    ((sourceAdaptiveBranches O T ψ).map (fun φ => ‖toEuclidean_fromVec φ‖^2)).sum=
      ‖toEuclidean_fromVec ψ‖^2 := by
  induction T generalizing ψ with
  | finish => simp [sourceAdaptiveBranches]
  | known U next ih =>
    rw [sourceAdaptiveBranches,ih hT.2]
    simpa only [ApplyGate] using!
        congrArg (fun t : ℝ => t^2) (norm_applyGate_of_mem_unitaryGroup hT.1 ψ)
  | query adj next ih =>
    rw [sourceAdaptiveBranches,ih hT]
    have hu : (if adj then Oᴴ else O) ∈ Matrix.unitaryGroup H ℂ := by
      cases adj
      · exact hO
      · simpa only [ite_true,Matrix.star_eq_conjTranspose] using! Unitary.star_mem hO
    simpa only [ApplyGate] using!
        congrArg (fun t : ℝ => t^2) (norm_applyGate_of_mem_unitaryGroup hu ψ)
  | instrument m K next ih =>
    simp only [sourceAdaptiveBranches,List.map_flatten,List.sum_flatten,List.map_ofFn,
      Function.comp_def,List.sum_ofFn]
    simp_rw [ih _ (hT.2 _)]
    exact sourceInstrument_mass K hT.1 ψ
end
noncomputable section

/-- Summing a function over a list padded to length `L` with a default of zero contribution
equals the mapped list sum. -/
theorem sourceList_sum_getD {A B : Type} [AddCommMonoid B]
    (l : List A) (d : A) (g : A → B) (hg : g d=0) (L : ℕ) (hL : l.length≤L) :
    (∑ i : Fin L,g (l.getD i.val d))=(l.map g).sum := by
  induction l generalizing L with
  | nil => simp [hg]
  | cons a l ih =>
    cases L with
    | zero => simp at hL
    | succ L =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ,
        List.map_cons,List.sum_cons]
      rw [ih L (by simpa using! hL)]
end
noncomputable section

/-- The adaptive density matrix is the sum over record labels of the outer products of the
recorded pure-output slices. -/
theorem sourceAdaptive_density_pure {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) (p t : H) :
    sourceAdaptiveDensity O T ψ p t=
      ∑ i : Fin (max 1 (sourceAdaptiveLeaves T)),sourceAdaptivePure O T ψ (i,p)*star (sourceAdaptivePure O T ψ (i,t)) := by
  symm
  exact sourceList_sum_getD (sourceAdaptiveBranches O T ψ) (0 : QState H)
    (fun φ => φ p*star (φ t)) (by simp) _ (by rw [sourceAdaptive_branches_length]; exact le_max_right _ _)
end
noncomputable section

/-- Recorded adaptive purification preserves the squared norm for legal computations and unitary
oracles. -/
theorem sourceAdaptive_pure_mass {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (hO : O ∈ Matrix.unitaryGroup H ℂ)
    (T : SourceAdaptive H) (hT : sourceAdaptiveLegal T) (ψ : QState H) :
    ‖toEuclidean_fromVec (sourceAdaptivePure O T ψ)‖^2=‖toEuclidean_fromVec ψ‖^2 := by
  rw [norm_toEuclidean_fromVec_sq,Fintype.sum_prod_type]
  change (∑ i : Fin (max 1 (sourceAdaptiveLeaves T)),
    ∑ p : H, ‖((sourceAdaptiveBranches O T ψ).getD i.val 0) p‖^2)=_
  simp_rw [← norm_toEuclidean_fromVec_sq]
  rw [sourceList_sum_getD (sourceAdaptiveBranches O T ψ) (0 : QState H)
    (fun φ => ‖toEuclidean_fromVec φ‖^2) (by (try dsimp only); rw [norm_toEuclidean_fromVec_sq]; simp) _
    (by rw [sourceAdaptive_branches_length]; exact le_max_right _ _)]
  exact sourceAdaptive_branches_mass O hO T hT ψ
end
noncomputable section
/-- The encoding that packs a record label and old workspace index into the new workspace index
while preserving the other registers. -/
def sourceTreeCode {H : Type} (n q old records new : ℕ) (h : records*old≤new) :
    Fin records × SourceSpace n q H old → SourceSpace n q H new :=
  fun p => (p.2.1,(p.2.2.1,⟨p.1.val*old+p.2.2.2.val,by
    have hp : (p.1.val+1)*old≤records*old := Nat.mul_le_mul_right old p.1.isLt
    simp only [Nat.add_mul,Nat.one_mul] at hp
    omega⟩))
end
noncomputable section

/-- The tree-record encoding is injective when the new workspace can contain every record and
old workspace pair. -/
theorem sourceTreeCode_injective {H : Type} (n q old records new : ℕ) (h : records*old≤new) :
    Function.Injective (sourceTreeCode (H := H) n q old records new h) := by
  intro a b he
  have ha := congrArg (fun p => p.1) he
  have hb := congrArg (fun p => p.2.1) he
  have hc := congrArg (fun p => p.2.2.val) he
  dsimp only [sourceTreeCode] at ha hb hc
  have ho : 0<old := by have ha := a.2.2.2.isLt; omega
  have hget (i : ℕ) (j : Fin old) : (i*old+j.val)/old=i := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ ho,Nat.div_eq_of_lt j.isLt,zero_add]
  have hdiv := congrArg (fun z => z/old) hc
  (try dsimp only at hdiv)
  rw [hget,hget] at hdiv
  have hrec : a.1=b.1 := Fin.ext hdiv
  have hold : a.2.2.2=b.2.2.2 := by
    apply Fin.ext
    rw [hrec] at hc
    exact Nat.add_left_cancel hc
  exact Prod.ext hrec (Prod.ext ha (Prod.ext hb hold))
end
noncomputable section

/-- The tree frame equals the basis frame of the tree-record encoding under the workspace size
bound. -/
theorem sourceTreeFrame_eq_basis {H : Type} [DecidableEq H]
    (n q old records new : ℕ) (h : records*old≤new) :
    sourceTreeFrame (H := H) n q old records new=sourceBasisFrame (sourceTreeCode n q old records new h) := by
  ext p t
  simp only [sourceTreeFrame,Matrix.of_apply,sourceBasisFrame,sourceTreeCode,Prod.ext_iff,Fin.ext_iff]
end
noncomputable section

/-- The tree frame is an isometry when `records*old ≤ new`. -/
theorem sourceTreeFrame_isometry {H : Type} [Fintype H] [DecidableEq H]
    (n q old records new : ℕ) (h : records*old≤new) :
    (sourceTreeFrame (H := H) n q old records new)ᴴ*sourceTreeFrame (H := H) n q old records new=1 := by
  rw [sourceTreeFrame_eq_basis (H := H) n q old records new h]
  exact sourceBasisFrame_isometry _ (sourceTreeCode_injective (H := H) n q old records new h)
end
noncomputable section
/-- The list of branch operators obtained by composing known gates, oracle calls, and Kraus
operators along each adaptive branch. -/
def sourceAdaptiveOperators {H : Type} [Fintype H] [DecidableEq H] (O : Matrix H H ℂ) :
    SourceAdaptive H → List (Matrix H H ℂ)
  | .finish => [1]
  | .known U next => (sourceAdaptiveOperators O next).map (fun A => A*U)
  | .query adj next => (sourceAdaptiveOperators O next).map (fun A => A*(if adj then Oᴴ else O))
  | .instrument _ K next => (List.ofFn (fun i => (sourceAdaptiveOperators O (next i)).map (fun A => A*K i))).flatten
end
noncomputable section

/-- The branch-state list is obtained by applying the adaptive branch operators to the input
state. -/
theorem sourceAdaptive_branches_operators {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) :
    sourceAdaptiveBranches O T ψ=(sourceAdaptiveOperators O T).map (fun A => A*ᵥψ) := by
  induction T generalizing ψ with
  | finish => simp [sourceAdaptiveBranches,sourceAdaptiveOperators]
  | known U next ih => simp [sourceAdaptiveBranches,sourceAdaptiveOperators,ih,Matrix.mulVec_mulVec]
  | query adj next ih => simp [sourceAdaptiveBranches,sourceAdaptiveOperators,ih,Matrix.mulVec_mulVec]
  | instrument m K next ih =>
    simp [sourceAdaptiveBranches,sourceAdaptiveOperators,List.map_flatten,List.map_ofFn,List.map_map,Function.comp_def,ih,Matrix.mulVec_mulVec]
end
noncomputable section

/-- The adaptive branch-operator list has length equal to the number of leaves. -/
theorem sourceAdaptive_operators_length {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) : (sourceAdaptiveOperators O T).length=sourceAdaptiveLeaves T := by
  have hh := sourceAdaptive_branches_length O T (0 : QState H)
  rw [sourceAdaptive_branches_operators,List.length_map] at hh
  exact hh
end
noncomputable section
/-- The sum of `Aᴴ*A` over the matrices in the given list. -/
def sourceKrausTotal {H : Type} [Fintype H] [DecidableEq H] (l : List (Matrix H H ℂ)) : Matrix H H ℂ :=
  (l.map (fun A => Aᴴ*A)).sum
end
noncomputable section

/-- Right-composing each matrix in a Kraus list by `U` conjugates its Kraus total by `U`. -/
theorem sourceKrausTotal_comp {H : Type} [Fintype H] [DecidableEq H]
    (l : List (Matrix H H ℂ)) (U : Matrix H H ℂ) :
    sourceKrausTotal (l.map (fun A => A*U))=Uᴴ*sourceKrausTotal l*U := by
  induction l with
  | nil => simp [sourceKrausTotal]
  | cons A l ih =>
    simp only [List.map_cons,sourceKrausTotal,List.sum_cons,Matrix.conjTranspose_mul,
      Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc] at ih ⊢
    rw [ih]
end
noncomputable section

/-- For a legal adaptive computation with a unitary oracle, the adaptive branch operators have
Kraus total equal to the identity. -/
theorem sourceAdaptive_operators_complete {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (hO : O ∈ Matrix.unitaryGroup H ℂ)
    (T : SourceAdaptive H) (hT : sourceAdaptiveLegal T) : sourceKrausTotal (sourceAdaptiveOperators O T)=1 := by
  induction T with
  | finish => simp [sourceAdaptiveOperators,sourceKrausTotal]
  | known U next ih =>
    rw [sourceAdaptiveOperators,sourceKrausTotal_comp,ih hT.2,Matrix.mul_one]
    simpa only [Matrix.star_eq_conjTranspose] using! hT.1.1
  | query adj next ih =>
    rw [sourceAdaptiveOperators,sourceKrausTotal_comp,ih hT,Matrix.mul_one]
    have hu : (if adj then Oᴴ else O) ∈ Matrix.unitaryGroup H ℂ := by
      cases adj
      · exact hO
      · simpa only [ite_true,Matrix.star_eq_conjTranspose] using! Unitary.star_mem hO
    simpa only [Matrix.star_eq_conjTranspose] using! hu.1
  | instrument m K next ih =>
    simp only [sourceAdaptiveOperators,sourceKrausTotal,List.map_flatten,List.map_ofFn,
      List.sum_flatten,List.sum_ofFn]
    change (∑ i,sourceKrausTotal ((sourceAdaptiveOperators O (next i)).map (fun A => A*K i)))=1
    simp_rw [sourceKrausTotal_comp,ih _ (hT.2 _),Matrix.mul_one]
    exact hT.1
end
noncomputable section
/-- The matrix whose record slices are the adaptive branch operators, padded with zero matrices
when necessary. -/
def sourceAdaptivePureMatrix {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) : Matrix (Fin (max 1 (sourceAdaptiveLeaves T)) × H) H ℂ :=
  fun p t => ((sourceAdaptiveOperators O T).getD p.1.val 0) p.2 t
end
noncomputable section

/-- Applying the adaptive pure matrix to an input produces the recorded adaptive pure output. -/
theorem sourceAdaptivePureMatrix_apply {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (ψ : QState H) :
    sourceAdaptivePureMatrix O T *ᵥψ=sourceAdaptivePure O T ψ := by
  ext p
  simp only [sourceAdaptivePure,sourceAdaptive_branches_operators]
  have hg := List.getD_map (l := sourceAdaptiveOperators O T) (d := (0 : Matrix H H ℂ))
    (n := p.1.val) (fun A => A*ᵥψ)
  simp only [Matrix.zero_mulVec] at hg
  rw [hg]
  rfl
end
noncomputable section

/-- Evaluating a finite list sum of matrices at an entry equals summing the entries of the list. -/
theorem sourceMatrixList_sum_apply {H : Type} (l : List (Matrix H H ℂ)) (p t : H) :
    l.sum p t=(l.map (fun A => A p t)).sum := by
  induction l with
  | nil => rfl
  | cons A l ih => simp only [List.sum_cons,List.map_cons,Matrix.add_apply,ih]
end
noncomputable section

/-- The adaptive pure matrix is an isometry for a legal computation and a unitary oracle. -/
theorem sourceAdaptivePureMatrix_isometry {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (hO : O ∈ Matrix.unitaryGroup H ℂ)
    (T : SourceAdaptive H) (hT : sourceAdaptiveLegal T) :
    (sourceAdaptivePureMatrix O T)ᴴ*sourceAdaptivePureMatrix O T=1 := by
  have ht := sourceAdaptive_operators_complete O hO T hT
  ext p t
  have he := sourceList_sum_getD (sourceAdaptiveOperators O T) (0 : Matrix H H ℂ)
    (fun A => (Aᴴ*A) p t) (by simp) (max 1 (sourceAdaptiveLeaves T))
    (by rw [sourceAdaptive_operators_length]; exact le_max_right _ _)
  simp only [sourceAdaptivePureMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type]
  change (∑ i : Fin (max 1 (sourceAdaptiveLeaves T)),
    (((sourceAdaptiveOperators O T).getD i.val 0)ᴴ*((sourceAdaptiveOperators O T).getD i.val 0)) p t)=(1 : Matrix H H ℂ) p t
  (try dsimp only at he)
  rw [he]
  have hh := congrFun (congrFun ht p) t
  simpa only [sourceKrausTotal,sourceMatrixList_sum_apply,List.map_map,Function.comp_def] using! hh
end
noncomputable section
/-- The matrix that stacks the Kraus operators in an outcome register. -/
def sourceInstrumentMatrix {H : Type} {m : ℕ} (K : Fin m → Matrix H H ℂ) :
    Matrix (Fin m × H) H ℂ := fun p t => K p.1 p.2 t
end
noncomputable section

/-- Stacking a complete Kraus family gives an isometry. -/
theorem sourceInstrumentMatrix_isometry {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (K : Fin m → Matrix H H ℂ) (hK : (∑ i,(K i)ᴴ*K i)=1) :
    (sourceInstrumentMatrix K)ᴴ*sourceInstrumentMatrix K=1 := by
  ext p t
  simp only [sourceInstrumentMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type]
  have he := congrFun (congrFun hK p) t
  simpa only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply] using! he
end
noncomputable section

/-- Two isometries with the same source and target dimensions are related by a unitary acting on
their target. -/
theorem sourcePublic_isometry_transport {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (F A : Matrix S T ℂ) (hF : Fᴴ*F=1) (hA : Aᴴ*A=1) :
    ∃ G : Matrix S S ℂ, G ∈ Matrix.unitaryGroup S ℂ ∧ G*F=A :=
  gram_equal_actual_unitary_transport S T F A (hF.trans hA.symm)
end
noncomputable section
/-- A purification program consisting of a known initial matrix and a list of pairs of known
matrices. -/
structure SourcePurificationProgram (S : Type) where
  start : Matrix S S ℂ
  layers : List (Matrix S S ℂ × Matrix S S ℂ)
end
noncomputable section
/-- The four-instruction word consisting of a forward oracle call, the first known matrix, an
adjoint oracle call, and the second known matrix. -/
def sourcePurificationLayerWord {S : Type} (p : Matrix S S ℂ × Matrix S S ℂ) : SourceWord S :=
  [.inr false,.inl p.1,.inr true,.inl p.2]
end
noncomputable section
/-- The source word consisting of the initial known matrix followed by the words of all
purification layers. -/
def sourcePurificationProgramWord {S : Type} (P : SourcePurificationProgram S) : SourceWord S :=
  .inl P.start::P.layers.flatMap sourcePurificationLayerWord
end
noncomputable section
/-- Legality of a purification program requires its initial matrix and both known matrices in
every layer to be unitary. -/
def sourcePurificationProgramLegal {S : Type} [Fintype S] [DecidableEq S] (P : SourcePurificationProgram S) : Prop :=
  P.start ∈ Matrix.unitaryGroup S ℂ ∧ ∀ p ∈ P.layers, p.1 ∈ Matrix.unitaryGroup S ℂ ∧ p.2 ∈ Matrix.unitaryGroup S ℂ
end
noncomputable section
/-- The matrix `p.2*Oᴴ*p.1*O` implementing a purification layer. -/
def sourcePurificationLayerMatrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (p : Matrix S S ℂ × Matrix S S ℂ) : Matrix S S ℂ := p.2*Oᴴ*p.1*O
end
noncomputable section

/-- A purification layer uses exactly two oracle calls. -/
theorem sourcePurificationLayerWord_calls {S : Type} (p : Matrix S S ℂ × Matrix S S ℂ) :
    sourceWordCalls (sourcePurificationLayerWord p)=2 := by simp [sourcePurificationLayerWord,sourceWordCalls]
end
noncomputable section

/-- The word of a purification layer evaluates to its layer matrix. -/
theorem sourcePurificationLayerWord_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (p : Matrix S S ℂ × Matrix S S ℂ) :
    sourceWordMatrix O (sourcePurificationLayerWord p)=sourcePurificationLayerMatrix O p := by
  simp [sourcePurificationLayerWord,sourcePurificationLayerMatrix,sourceWordMatrix,Matrix.mul_assoc]
end
noncomputable section

/-- The matrix of a concatenation of instruction words is the product of their matrices in
reverse list order. -/
theorem sourceWordMatrix_flatMap {A S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (l : List A) (f : A → SourceWord S) :
    sourceWordMatrix O (l.flatMap f)=(l.map (fun a => sourceWordMatrix O (f a))).reverse.prod := by
  induction l with
  | nil => simp [sourceWordMatrix]
  | cons a l ih => simp [List.flatMap_cons,sourceWordMatrix_append,ih]
end
noncomputable section

/-- A purification program evaluates to the reverse-ordered product of its layer matrices
multiplied by its initial matrix. -/
theorem sourcePurificationProgramWord_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (P : SourcePurificationProgram S) :
    sourceWordMatrix O (sourcePurificationProgramWord P)=
      (P.layers.map (sourcePurificationLayerMatrix O)).reverse.prod*P.start := by
  rw [show sourcePurificationProgramWord P=[Sum.inl P.start]++P.layers.flatMap sourcePurificationLayerWord from rfl,
    sourceWordMatrix_append,sourceWordMatrix_flatMap]
  simp_rw [sourcePurificationLayerWord_matrix]
  simp only [sourceWordMatrix,List.map_cons,List.map_nil,
    List.reverse_singleton,List.prod_cons,List.prod_nil,Matrix.mul_one]
end
noncomputable section

/-- A purification program word uses twice as many oracle calls as it has layers. -/
theorem sourcePurificationProgramWord_calls {S : Type} (P : SourcePurificationProgram S) :
    sourceWordCalls (sourcePurificationProgramWord P)=2*P.layers.length := by
  have he (l : List (Matrix S S ℂ × Matrix S S ℂ)) : sourceWordCalls (l.flatMap sourcePurificationLayerWord)=2*l.length := by
    induction l with
    | nil => simp [sourceWordCalls]
    | cons p l ih =>
      simp only [List.flatMap_cons,sourceWordCalls_append,sourcePurificationLayerWord_calls,
        List.length_cons,ih]
      omega
  simpa only [sourcePurificationProgramWord,sourceWordCalls,List.countP_cons,ite_false,zero_add] using! he P.layers
end
noncomputable section

/-- The word of a legal purification program is legal. -/
theorem sourcePurificationProgramWord_legal {S : Type} [Fintype S] [DecidableEq S]
    (P : SourcePurificationProgram S) (hP : sourcePurificationProgramLegal P) :
    sourceWordLegal (sourcePurificationProgramWord P) := by
  intro s hs
  rcases List.mem_cons.mp hs with he|hs
  · subst s
    exact hP.1
  · obtain ⟨p,hp,hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_cons.mp hs with rfl|hs
    · trivial
    rcases List.mem_cons.mp hs with rfl|hs
    · exact (hP.2 p hp).1
    rcases List.mem_cons.mp hs with rfl|hs
    · trivial
    rcases List.mem_cons.mp hs with rfl|hs
    · exact (hP.2 p hp).2
    · simp at hs
end
noncomputable section

/-- For a unitary oracle, the purification layer with both known matrices equal to identity
evaluates to identity. -/
theorem sourcePurificationLayer_identity {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (hO : O ∈ Matrix.unitaryGroup S ℂ) : sourcePurificationLayerMatrix O (1,1)=1 := by
  simp only [sourcePurificationLayerMatrix,Matrix.one_mul,Matrix.mul_one]
  simpa only [Matrix.star_eq_conjTranspose] using! hO.1
end
noncomputable section

/-- Reading a list with default `d` at every index below `L` produces that list followed by
`L-l.length` copies of `d`, when `l.length ≤ L`. -/
theorem sourceList_pad_getD {A : Type} (l : List A) (d : A) (L : ℕ) (hL : l.length≤L) :
    List.ofFn (fun i : Fin L => l.getD i.val d)=l++List.replicate (L-l.length) d := by
  induction l generalizing L with
  | nil => simp [List.ofFn_const]
  | cons a l ih =>
    cases L with
    | zero => simp at hL
    | succ L =>
      rw [List.ofFn_succ]
      simp only [Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ,List.length_cons,
        Nat.succ_sub_succ_eq_sub,List.cons_append]
      rw [ih L (by simpa using! hL)]
end
noncomputable section
/-- The purification program with exactly `L` layers obtained by indexed lookup, using identity
pairs beyond the original layer list. -/
def sourcePurificationPad {S : Type} [DecidableEq S] (P : SourcePurificationProgram S) (L : ℕ) : SourcePurificationProgram S :=
  ⟨P.start,List.ofFn (fun i : Fin L => P.layers.getD i.val (1,1))⟩
end
noncomputable section

/-- Padding a purification program to at least its original length preserves its matrix for a
unitary oracle. -/
theorem sourcePurificationPad_matrix {S : Type} [Fintype S] [DecidableEq S]
    (O : Matrix S S ℂ) (hO : O ∈ Matrix.unitaryGroup S ℂ) (P : SourcePurificationProgram S)
    (L : ℕ) (hL : P.layers.length≤L) :
    sourceWordMatrix O (sourcePurificationProgramWord (sourcePurificationPad P L))=
      sourceWordMatrix O (sourcePurificationProgramWord P) := by
  rw [sourcePurificationProgramWord_matrix,sourcePurificationProgramWord_matrix]
  simp only [sourcePurificationPad,sourceList_pad_getD _ _ L hL,List.map_append,List.map_replicate,
    List.reverse_append,List.prod_append,List.reverse_replicate,sourcePurificationLayer_identity O hO,
    List.prod_replicate,one_pow,Matrix.one_mul]
end
noncomputable section

/-- The initial value of a maximum fold is at most the fold result. -/
theorem sourceList_le_foldl_max (l : List ℕ) (a : ℕ) : a≤l.foldl max a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact (le_max_left a b).trans (ih (max a b))
end
noncomputable section

/-- Every element of a list of natural numbers is at most the result of folding maximum over the
list. -/
theorem sourceList_mem_le_foldl_max (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x≤l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons b l ih =>
    rcases List.mem_cons.mp hx with rfl|hx
    · exact (le_max_right a x).trans (sourceList_le_foldl_max l (max a x))
    · exact ih (max a b) hx
end
noncomputable section

/-- The call count of any continuation of an instrument is at most the call count of the
complete instrument node. -/
theorem sourceAdaptiveCalls_instrument_ge {H : Type} {m : ℕ}
    (K : Fin m → Matrix H H ℂ) (next : Fin m → SourceAdaptive H) (i : Fin m) :
    sourceAdaptiveCalls (next i)≤sourceAdaptiveCalls (.instrument m K next) :=
  sourceList_mem_le_foldl_max _ 0 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
end
noncomputable section

/-- The branch operators of a zero-call adaptive computation are independent of the oracle and
equal those for the identity oracle. -/
theorem sourceAdaptiveOperators_zeroCalls {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (hT : sourceAdaptiveCalls T=0) :
    sourceAdaptiveOperators O T=sourceAdaptiveOperators 1 T := by
  induction T with
  | finish => rfl
  | known U next ih => simp only [sourceAdaptiveOperators,ih hT]
  | query adj next ih => simp [sourceAdaptiveCalls] at hT
  | instrument m K next ih =>
    have hz (i : Fin m) : sourceAdaptiveCalls (next i)=0 := by
      have hh := sourceAdaptiveCalls_instrument_ge K next i
      rw [hT] at hh
      exact Nat.le_zero.mp hh
    simp only [sourceAdaptiveOperators,ih _ (hz _)]
end
noncomputable section

/-- The recorded pure output of a zero-call adaptive computation is independent of the oracle. -/
theorem sourceAdaptivePure_zeroCalls {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (T : SourceAdaptive H) (hT : sourceAdaptiveCalls T=0) (ψ : QState H) :
    sourceAdaptivePure O T ψ=sourceAdaptivePure 1 T ψ := by
  have he : sourceAdaptivePureMatrix O T=sourceAdaptivePureMatrix 1 T := by
    ext p t
    change ((sourceAdaptiveOperators O T).getD p.1.val 0) p.2 t=
      ((sourceAdaptiveOperators 1 T).getD p.1.val 0) p.2 t
    rw [sourceAdaptiveOperators_zeroCalls O T hT]
  calc
    _ = sourceAdaptivePureMatrix O T*ᵥψ := (sourceAdaptivePureMatrix_apply O T ψ).symm
    _ = sourceAdaptivePureMatrix 1 T*ᵥψ := congrArg (fun A => A*ᵥψ) he
    _ = _ := sourceAdaptivePureMatrix_apply 1 T ψ
end
noncomputable section
/-- The basis frame that adjoins the zero record to an input state. -/
def sourceRootFrame {H : Type} [DecidableEq H] (L : ℕ) (hL : 0<L) : Matrix (Fin L × H) H ℂ :=
  sourceBasisFrame (fun p => ((⟨0,hL⟩ : Fin L),p))
end
noncomputable section

/-- The zero-record root frame is an isometry. -/
theorem sourceRootFrame_isometry {H : Type} [Fintype H] [DecidableEq H] (L : ℕ) (hL : 0<L) :
    (sourceRootFrame (H := H) L hL)ᴴ*sourceRootFrame (H := H) L hL=1 := by
  apply sourceBasisFrame_isometry
  intro p t he
  exact congrArg Prod.snd he
end
noncomputable section

/-- Applying the root frame tensors the input with the zero basis record. -/
theorem sourceRootFrame_apply {H : Type} [Fintype H] [DecidableEq H]
    (L : ℕ) (hL : 0<L) (ψ : QState H) :
    sourceRootFrame L hL*ᵥψ=TensorState (Ket (⟨0,hL⟩ : Fin L)) ψ := by
  ext p
  rcases p with ⟨i,p⟩
  simp only [sourceRootFrame,sourceBasisFrame,Matrix.mulVec,dotProduct,Prod.mk.injEq,TensorState,Ket]
  by_cases he : i=(⟨0,hL⟩ : Fin L) <;> simp [he]
end
noncomputable section

/-- The product of two composable isometries is an isometry. -/
theorem sourceComposeFrames_isometry {S T U : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    (F : Matrix S T ℂ) (A : Matrix T U ℂ) (hF : Fᴴ*F=1) (hA : Aᴴ*A=1) :
    (F*A)ᴴ*(F*A)=1 := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Fᴴ F A,hF,Matrix.one_mul]
  exact hA
end
noncomputable section

/-- A legal zero-call adaptive computation is exactly simulated by a single unitary on the
workspace enlarged to hold its branch records. -/
theorem sourceAdaptive_zero_query_compiler {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q r : ℕ} (_hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (T : SourceAdaptive (SourceSpace n q H r))
    (hT : sourceAdaptiveLegal T) (hCalls : sourceAdaptiveCalls T=0) :
    let L := max 1 (sourceAdaptiveLeaves T)
    ∃ G : Matrix (SourceSpace n q H (L*r)) (SourceSpace n q H (L*r)) ℂ,
      G ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ x (ψ : QState (SourceSpace n q H r)),
      G*ᵥ(sourceTreeFrame n q r L (L*r)*ᵥTensorState (Ket (⟨0,by dsimp [L]; omega⟩ : Fin L)) ψ)=
      sourceTreeFrame n q r L (L*r)*ᵥsourceAdaptivePure (sourceAlphabetOracle input x) T ψ := by
  (try dsimp only)
  let L := max 1 (sourceAdaptiveLeaves T)
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0 : ℕ)<1) (le_max_left _ _)
  let F := sourceTreeFrame (H := H) n q r L (L*r)
  have hF : Fᴴ*F=1 := sourceTreeFrame_isometry n q r L (L*r) le_rfl
  let B := sourceRootFrame (H := SourceSpace n q H r) L hL
  let A := sourceAdaptivePureMatrix (1 : Matrix (SourceSpace n q H r) _ ℂ) T
  have hB : Bᴴ*B=1 := sourceRootFrame_isometry L hL
  have hA : Aᴴ*A=1 := sourceAdaptivePureMatrix_isometry 1 (Matrix.unitaryGroup _ ℂ).one_mem T hT
  obtain ⟨G,hG,he⟩ := sourcePublic_isometry_transport (F*B) (F*A)
    (sourceComposeFrames_isometry F B hF hB) (sourceComposeFrames_isometry F A hF hA)
  refine ⟨G,hG,?_⟩
  intro x ψ
  have hh := congrArg (fun M : Matrix (SourceSpace n q H (L*r)) (SourceSpace n q H r) ℂ => M*ᵥψ) he
  simp only [B,A,← Matrix.mulVec_mulVec,sourceRootFrame_apply] at hh
  rw [sourceAdaptivePure_zeroCalls (sourceAlphabetOracle input x) T hCalls]
  exact hh.trans (congrArg (fun v => F*ᵥv)
    (sourceAdaptivePureMatrix_apply (1 : Matrix (SourceSpace n q H r) _ ℂ) T ψ))
end
noncomputable section

/-- Relabeling a gate commutes with conjugate transpose. -/
theorem sourceRelabelGate_conjTranspose {S T : Type} [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (U : Matrix S S ℂ) : (relabelGate e U)ᴴ=relabelGate e Uᴴ := by
  ext p t
  rfl
end
noncomputable section

/-- Relabeling gates preserves matrix multiplication. -/
theorem sourceRelabelGate_mul {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T) (U V : Matrix S S ℂ) :
    relabelGate e (U*V)=relabelGate e U*relabelGate e V := by
  ext p t
  simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.mul_apply]
  exact (e.symm.sum_comp (fun s => U (e.symm p) s*V s (e.symm t))).symm
end
noncomputable section

/-- Relabeling the identity gate gives the identity gate. -/
theorem sourceRelabelGate_one {S T : Type} [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) : relabelGate e (1 : Matrix S S ℂ)=1 := by
  ext p t
  simp [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.one_apply,e.symm.injective.eq_iff]
end
noncomputable section

/-- Relabeling a unitary gate gives a unitary gate. -/
theorem sourceRelabelGate_unitary {S T : Type} [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] (e : S ≃ T) (U : Matrix S S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) : relabelGate e U ∈ Matrix.unitaryGroup T ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,sourceRelabelGate_conjTranspose,
    ← sourceRelabelGate_mul,show Uᴴ*U=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hU.1,
    sourceRelabelGate_one]
end
noncomputable section

/-- Indexed layer lookup in a legal purification program returns two unitary matrices, including
when the default identity pair is used. -/
theorem sourcePurification_getD_legal {S : Type} [Fintype S] [DecidableEq S]
    (P : SourcePurificationProgram S) (hP : sourcePurificationProgramLegal P) (j : ℕ) :
    (P.layers.getD j (1,1)).1 ∈ Matrix.unitaryGroup S ℂ ∧
      (P.layers.getD j (1,1)).2 ∈ Matrix.unitaryGroup S ℂ := by
  by_cases he : j<P.layers.length
  · exact hP.2 _ (by rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem he)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨(Matrix.unitaryGroup _ ℂ).one_mem,(Matrix.unitaryGroup _ ℂ).one_mem⟩
end
noncomputable section

/-- Taking `L` layers with default identity pairs preserves purification-program legality. -/
theorem sourcePurificationPad_legal {S : Type} [Fintype S] [DecidableEq S]
    (P : SourcePurificationProgram S) (hP : sourcePurificationProgramLegal P) (L : ℕ) :
    sourcePurificationProgramLegal (sourcePurificationPad P L) := by
  refine ⟨hP.1,?_⟩
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact sourcePurification_getD_legal P hP j.val
end
noncomputable section

/-- A block-diagonal matrix with unitary diagonal blocks is unitary. -/
theorem sourceBlockDiagonal_unitary {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (U : ∀ i,Matrix (S i) (S i) ℂ) (hU : ∀ i,U i ∈ Matrix.unitaryGroup (S i) ℂ) :
    Matrix.blockDiagonal' U ∈ Matrix.unitaryGroup (Sigma S) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have he : (fun i => (U i)ᴴ*U i)=(1 : ∀ i,Matrix (S i) (S i) ℂ) := by
    funext i
    simpa only [Matrix.star_eq_conjTranspose] using! (hU i).1
  rw [he,Matrix.blockDiagonal'_one]
end
noncomputable section
/-- The purification program formed by combining initial matrices and indexed layers
block-diagonally across a family of programs. -/
def sourcePurificationBlockProgram {I : Type} [DecidableEq I]
    {S : I → Type} [∀ i,DecidableEq (S i)] (P : ∀ i,SourcePurificationProgram (S i)) (L : ℕ) :
    SourcePurificationProgram (Sigma S) :=
  ⟨Matrix.blockDiagonal' (fun i => (P i).start),List.ofFn (fun j : Fin L =>
    (Matrix.blockDiagonal' (fun i => ((P i).layers.getD j.val (1,1)).1),
     Matrix.blockDiagonal' (fun i => ((P i).layers.getD j.val (1,1)).2)))⟩
end
noncomputable section

/-- The block-diagonal purification program is legal when each component program is legal. -/
theorem sourcePurificationBlockProgram_legal {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (P : ∀ i,SourcePurificationProgram (S i)) (hP : ∀ i,sourcePurificationProgramLegal (P i)) (L : ℕ) :
    sourcePurificationProgramLegal (sourcePurificationBlockProgram P L) := by
  refine ⟨sourceBlockDiagonal_unitary _ (fun i => (hP i).1),?_⟩
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨sourceBlockDiagonal_unitary _ (fun i => (sourcePurification_getD_legal (P i) (hP i) j.val).1),
    sourceBlockDiagonal_unitary _ (fun i => (sourcePurification_getD_legal (P i) (hP i) j.val).2)⟩
end
noncomputable section

/-- A purification layer with block-diagonal oracle and known matrices evaluates blockwise. -/
theorem sourcePurificationLayer_block {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (O : ∀ i,Matrix (S i) (S i) ℂ) (p : ∀ i,Matrix (S i) (S i) ℂ × Matrix (S i) (S i) ℂ) :
    sourcePurificationLayerMatrix (Matrix.blockDiagonal' O)
      (Matrix.blockDiagonal' (fun i => (p i).1),Matrix.blockDiagonal' (fun i => (p i).2))=
      Matrix.blockDiagonal' (fun i => sourcePurificationLayerMatrix (O i) (p i)) := by
  simp only [sourcePurificationLayerMatrix,Matrix.blockDiagonal'_conjTranspose]
  rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
end
noncomputable section

/-- Forming a block-diagonal matrix commutes with taking a finite list product. -/
theorem sourceBlockDiagonal_list_prod {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (l : List (∀ i,Matrix (S i) (S i) ℂ)) :
    Matrix.blockDiagonal' l.prod=(l.map Matrix.blockDiagonal').prod :=
  map_list_prod (Matrix.blockDiagonal'RingHom S ℂ) l
end
noncomputable section

/-- The block-diagonal purification program evaluates to the block-diagonal matrix of the
component programs truncated or padded to `L` layers. -/
theorem sourcePurificationBlockProgram_matrix {I : Type} [Fintype I] [DecidableEq I]
    {S : I → Type} [∀ i,Fintype (S i)] [∀ i,DecidableEq (S i)]
    (O : ∀ i,Matrix (S i) (S i) ℂ) (P : ∀ i,SourcePurificationProgram (S i)) (L : ℕ) :
    sourceWordMatrix (Matrix.blockDiagonal' O) (sourcePurificationProgramWord (sourcePurificationBlockProgram P L))=
      Matrix.blockDiagonal' (fun i => sourceWordMatrix (O i) (sourcePurificationProgramWord (sourcePurificationPad (P i) L))) := by
  rw [sourcePurificationProgramWord_matrix]
  simp only [sourcePurificationBlockProgram,List.map_ofFn,Function.comp_def,sourcePurificationLayer_block]
  let l : List (∀ i,Matrix (S i) (S i) ℂ) := List.ofFn (fun j : Fin L => fun i =>
    sourcePurificationLayerMatrix (O i) ((P i).layers.getD j.val (1,1)))
  have he : (List.ofFn (fun j : Fin L => Matrix.blockDiagonal' (fun i =>
      sourcePurificationLayerMatrix (O i) ((P i).layers.getD j.val (1,1))))).reverse.prod=
      Matrix.blockDiagonal' l.reverse.prod := by
    rw [sourceBlockDiagonal_list_prod,List.map_reverse]
    simp only [l,List.map_ofFn,Function.comp_def]
  rw [he,← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  rw [sourcePurificationProgramWord_matrix]
  simp only [sourcePurificationPad,Pi.list_prod_apply,Function.comp_def,l,
    List.map_reverse,List.map_ofFn]
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
