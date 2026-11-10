/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.GammaDuality
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem sourceRectValue_filter_embed_le {R S : Type} {n k : ℕ}
    (A : Matrix R S ℂ) (Y : Fin n → Matrix R S ℂ) (Z : Fin k → Matrix R S ℂ)
    (e : Fin n → Fin k) (he : Function.Injective e) (hz : ∀ j, Z (e j)=Y j) :
    sourceRectValue A Z ≤ sourceRectValue A Y := by
  apply sourceRectValue_le_of_cert_imp A Y A Z
  intro w _ hc
  obtain ⟨d,u,v,ha,hu,hv⟩ := hc
  let u' : R → Fin k → QState (Fin d) := fun r l => if h : ∃ j, e j=l then u r h.choose else 0
  let v' : S → Fin k → QState (Fin d) := fun s l => if h : ∃ j, e j=l then v s h.choose else 0
  have hchoose (j : Fin n) (h : ∃ i, e i=e j) : h.choose=j := he h.choose_spec
  have heq (r : R) (s : S) : (∑ l, Z l r s*∑ a, star (u' r l a)*v' s l a)=
      ∑ j, Y j r s*∑ a, star (u r j a)*v s j a := by
    symm
    apply Finset.sum_of_injOn e (by intro a _ b _ hab; exact he hab) (by simp)
    · intro l _ hl
      have hn : ¬ ∃ j, e j=l := by simpa using! hl
      simp [u',v',hn]
    · intro j _
      simp [u',v',hchoose,hz]
  have hum (r : R) : (∑ l, ‖toEuclidean_fromVec (u' r l)‖^2)=∑ j, ‖toEuclidean_fromVec (u r j)‖^2 := by
    symm
    apply Finset.sum_of_injOn e (by intro a _ b _ hab; exact he hab) (by simp)
    · intro l _ hl
      have hn : ¬ ∃ j, e j=l := by simpa using! hl
      simp only [u',dif_neg hn,norm_toEuclidean_fromVec_sq,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),Finset.sum_const_zero]
    · intro j _
      simp [u',hchoose]
  have hvm (s : S) : (∑ l, ‖toEuclidean_fromVec (v' s l)‖^2)=∑ j, ‖toEuclidean_fromVec (v s j)‖^2 := by
    symm
    apply Finset.sum_of_injOn e (by intro a _ b _ hab; exact he hab) (by simp)
    · intro l _ hl
      have hn : ¬ ∃ j, e j=l := by simpa using! hl
      simp only [v',dif_neg hn,norm_toEuclidean_fromVec_sq,Pi.zero_apply,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),Finset.sum_const_zero]
    · intro j _
      simp [v',hchoose]
  exact ⟨d,u',v',fun r s => (ha r s).trans (heq r s).symm,fun r => by rw [hum]; exact hu r,
    fun s => by rw [hvm]; exact hv s⟩

theorem sourceRectValue_independent_pullback_le {X D E : Type} [DecidableEq E] {n m q : ℕ}
    (inner : X → Fin n → Fin (q+1)) (g : X → E)
    (xs : D → Fin m → X) (j : Fin m) :
    sourceRectValue ((gramFunctionEvaluationMatrix g).submatrix (fun p => xs p j) (fun p => xs p j))
      (sourceAlphabetDelta (fun p => sourceIndependentInput inner m (xs p))) ≤
      sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner) := by
  apply (sourceRectValue_filter_embed_le _ _ _ (fun k => finProdFinEquiv (j,k)) ?_ ?_).trans
    (sourceRectValue_submatrix_le _ _ _ _)
  · intro k l he
    have hh := finProdFinEquiv.injective he
    exact congrArg Prod.snd hh
  · intro k
    ext p r
    simp only [sourceAlphabetDelta,sourceIndependentInput,Equiv.symm_apply_apply,Matrix.submatrix_apply]

theorem sourceFunctionComposition_upper {X Y E : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype E] [DecidableEq E]
    {n m q a : ℕ} (inner : X → Fin n → Fin (q+1)) (g : X → Fin (a+1))
    (outer : Y → Fin m → Fin (a+1)) (f : Y → E)
    (h : sourceAdversary (sourceAlphabetDelta outer) f < ⊤ ∨
      sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner) ≠ 0) :
    let D := {p : Y × (Fin m → X) // ∀ j, outer p.1 j=g (p.2 j)}
    let input := fun p : D => sourceIndependentInput inner m p.1.2
    let result := fun p : D => f p.1.1
    sourceAdversary (sourceAlphabetDelta input) result ≤
      sourceAdversary (sourceAlphabetDelta outer) f*sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner) := by
  let D := {p : Y × (Fin m → X) // ∀ j, outer p.1 j=g (p.2 j)}
  let input := fun p : D => sourceIndependentInput inner m p.1.2
  let result := fun p : D => f p.1.1
  let A := gramFunctionEvaluationMatrix result
  let Z := fun k => sourceAlphabetDelta input k ⊙ A
  let W := fun j => (sourceAlphabetDelta outer j ⊙ gramFunctionEvaluationMatrix f).submatrix
    (fun p : D => p.1.1) (fun p : D => p.1.1)
  let b := sourceRectValue (gramFunctionEvaluationMatrix g) (sourceAlphabetDelta inner)
  have hw : sourceRectValue A W ≤ sourceAdversary (sourceAlphabetDelta outer) f := by
    rw [sourceAdversary_eq_masked]
    exact sourceRectValue_submatrix_le (gramFunctionEvaluationMatrix f)
        (fun j => sourceAlphabetDelta outer j ⊙ gramFunctionEvaluationMatrix f)
        (fun p : D => p.1.1) (fun p : D => p.1.1)
  have hinner (j : Fin m) : sourceRectValue (W j) Z ≤ b := by
    let G :=
        (gramFunctionEvaluationMatrix g).submatrix (fun p : D => p.1.2 j) (fun p : D => p.1.2 j)
    have he : W j=G ⊙ A := by
      ext p r
      simp only [W,G,A,result,gramFunctionEvaluationMatrix,sourceAlphabetDelta,Matrix.submatrix_apply,Matrix.hadamard_apply,p.property j,r.property j]
    rw [he]
    exact (sourceRectValue_hadamard_filters_le G A (sourceAlphabetDelta input)).trans
      (sourceRectValue_independent_pullback_le inner g (fun p : D => p.1.2) j)
  have hb : (⨆ j, sourceRectValue (W j) Z) ≤ b := iSup_le hinner
  by_cases hzero : b=0
  · have houter : sourceAdversary (sourceAlphabetDelta outer) f < ⊤ := h.resolve_right (fun hn => hn hzero)
    have hwi : sourceRectValue A W < ⊤ := hw.trans_lt houter
    calc
      sourceAdversary (sourceAlphabetDelta input) result=sourceRectValue A Z := sourceAdversary_eq_masked input result
      _ ≤ sourceRectValue A W*(⨆ j, sourceRectValue (W j) Z) := sourceRectValue_composition A W Z (Or.inl hwi)
      _ ≤ sourceAdversary (sourceAlphabetDelta outer) f*b := mul_le_mul hw hb zero_le zero_le
  · by_cases htop : sourceAdversary (sourceAlphabetDelta outer) f=⊤
    · rw [htop,ENNReal.top_mul hzero]
      exact le_top
    · have hwi : sourceRectValue A W < ⊤ := hw.trans_lt (lt_top_iff_ne_top.mpr htop)
      calc
        sourceAdversary (sourceAlphabetDelta input) result=sourceRectValue A Z := sourceAdversary_eq_masked input result
        _ ≤ sourceRectValue A W*(⨆ j, sourceRectValue (W j) Z) := sourceRectValue_composition A W Z (Or.inl hwi)
        _ ≤ sourceAdversary (sourceAlphabetDelta outer) f*b := mul_le_mul hw hb zero_le zero_le

theorem sourceAlphabet_mask_isHermitian {X : Type} {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (G : Matrix X X ℂ) (hG : G.IsHermitian) (j : Fin n) :
    (G ⊙ sourceAlphabetDelta input j).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply,Matrix.hadamard_apply,star_mul,hG.apply]
  by_cases he : input x j=input y j <;> simp [sourceAlphabetDelta,he,eq_comm]

theorem sourceWeightedAlphabet_filter_identity {X : Type} [Fintype X] [DecidableEq X]
    {n m q : ℕ} (inner : X → Fin n → Fin (q+1)) (g : X → Bool)
    (Gf : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) (Gg : Matrix X X ℂ)
    (hzg : ∀ x y, g x=g y → Gg x y=0) (p : Fin m) (k : Fin n) :
    weightedAdvGamma (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg) ⊙
      sourceAlphabetDelta (sourceIndependentInput inner m) (finProdFinEquiv (p,k))=
    weightedAdvGamma (fun _ : Fin m => g) (fun _ => false)
      (Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) p)
      (Function.update (fun _ : Fin m => Gg) p (Gg ⊙ sourceAlphabetDelta inner k)) := by
  let Gg' := Function.update (fun _ : Fin m => Gg) p (Gg ⊙ sourceAlphabetDelta inner k)
  let K := Matrix.diagonal (fun _ : X => (‖Gg‖ : ℂ))+Gg
  let K' := fun j => Matrix.diagonal (fun _ : X => (‖Gg' j‖ : ℂ))+Gg' j
  ext x y
  have hrest : (∏ i ∈ Finset.univ.erase p,K' i (x i) (y i))=
      ∏ i ∈ Finset.univ.erase p,K (x i) (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [K',K,Gg',Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have hprod : (∏ i : Fin m,K (x i) (y i))=K (x p) (y p)*(∏ i ∈ Finset.univ.erase p,K (x i) (y i)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ p)).symm
  have hprod' : (∏ i : Fin m,K' i (x i) (y i))=K' p (x p) (y p)*(∏ i ∈ Finset.univ.erase p,K (x i) (y i)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p),hrest]
  have hp' : K' p=Matrix.diagonal (fun _ : X => (‖Gg ⊙ sourceAlphabetDelta inner k‖ : ℂ))+
      (Gg ⊙ sourceAlphabetDelta inner k) := by simp only [K',Gg',Function.update_self]
  simp only [Matrix.hadamard_apply,sourceAlphabetDelta,sourceIndependentInput,Equiv.symm_apply_apply]
  change (Gf (fun i => g (x i)) (fun i => g (y i))*(∏ i,K (x i) (y i)))*
      (if inner (x p) k=inner (y p) k then 0 else 1)=
    ((Gf (fun i => g (x i)) (fun i => g (y i)))*
      (if sourceBooleanSymbol (g (x p))=sourceBooleanSymbol (g (y p)) then 0 else 1))*
        (∏ i,K' i (x i) (y i))
  rw [hprod,hprod',hp']
  have hbool : sourceBooleanSymbol (g (x p))=sourceBooleanSymbol (g (y p)) ↔ g (x p)=g (y p) := by
    cases g (x p) <;> cases g (y p) <;> norm_num [sourceBooleanSymbol]
  by_cases hb : inner (x p) k=inner (y p) k
  · by_cases hg : g (x p)=g (y p)
    · simp [hb,hg]
    · have hxy : x p≠y p := fun he => hg (he ▸ rfl)
      simp [hb,hbool,hg,hxy,Matrix.add_apply,Matrix.hadamard_apply,sourceAlphabetDelta]
  · have hxy : x p≠y p := fun he => hb (he ▸ rfl)
    have hK : K (x p) (y p)=Gg (x p) (y p) := by simp [K,hxy]
    rw [hK]
    by_cases hg : g (x p)=g (y p)
    · simp [hb,hg,hzg _ _ hg]
    · simp [hb,hbool,hg,hxy,Matrix.add_apply,Matrix.hadamard_apply,sourceAlphabetDelta]

theorem sourceWeightedAlphabet_filter_norm {X : Type} [Fintype X] [DecidableEq X]
    {n m q : ℕ} (inner : X → Fin n → Fin (q+1)) (g : X → Bool)
    (Gf : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) (Gg : Matrix X X ℂ)
    (hGf : Gf.IsHermitian) (hGg : Gg.IsHermitian)
    (hzg : ∀ x y, g x=g y → Gg x y=0) (p : Fin m) (k : Fin n) :
    ‖weightedAdvGamma (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg) ⊙
      sourceAlphabetDelta (sourceIndependentInput inner m) (finProdFinEquiv (p,k))‖=
    ‖Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) p‖*
      ‖Gg ⊙ sourceAlphabetDelta inner k‖*‖Gg‖^(m-1) := by
  let Gg' := Function.update (fun _ : Fin m => Gg) p (Gg ⊙ sourceAlphabetDelta inner k)
  have hinner (i : Fin m) : (Gg' i).IsHermitian := by
    by_cases he : i=p
    · subst i
      simpa only [Gg',Function.update_self] using! sourceAlphabet_mask_isHermitian inner Gg hGg k
    · simpa only [Gg',Function.update_of_ne he] using! hGg
  have hzero (i : Fin m) (x y : X) (hg : g x=g y) : Gg' i x y=0 := by
    by_cases he : i=p
    · subst i
      simp [Gg',Matrix.hadamard_apply,hzg x y hg]
    · simpa only [Gg',Function.update_of_ne he] using! hzg x y hg
  rw [sourceWeightedAlphabet_filter_identity inner g Gf Gg hzg p k,
    weightedAdvGamma_norm_eq (fun _ : Fin m => g) (fun _ => false)
      (Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) p) Gg'
      (sourceAlphabet_mask_isHermitian _ Gf hGf p) hinner hzero]
  have hprod : (∏ i,‖Gg' i‖)=‖Gg ⊙ sourceAlphabetDelta inner k‖*‖Gg‖^(m-1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    simp only [Gg',Function.update_self]
    congr 1
    calc
      (∏ i ∈ Finset.univ.erase p, ‖Function.update (fun _ : Fin m => Gg) p (Gg ⊙ sourceAlphabetDelta inner k) i‖)=
          ∏ i ∈ Finset.univ.erase p, ‖Gg‖ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      _ = _ := by simp
  rw [hprod]
  ring

theorem sourceAdversary_zero_of_constant {X E : Type} [Fintype X] [DecidableEq X]
    [DecidableEq E] {n : ℕ} (Z : Fin n → Matrix X X ℂ) (f : X → E)
    (h : ∀ x y, f x=f y) : sourceAdversary Z f=0 := by
  apply le_antisymm _ zero_le
  unfold sourceAdversary
  apply iSup_le
  intro G
  have hg : G.val=0 := by ext x y; exact G.property.2.2.1 x y (h x y)
  simp [hg]

theorem sourceWeightedAlphabet_real {X : Type} [Fintype X] [DecidableEq X]
    {m : ℕ} (g : X → Bool) (Gf : Matrix (Fin m → Bool) (Fin m → Bool) ℂ)
    (Gg : Matrix X X ℂ) (hf : ∀ x y, (Gf x y).im=0) (hg : ∀ x y, (Gg x y).im=0) :
    ∀ x y, (weightedAdvGamma (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg) x y).im=0 := by
  have hf' (x y : Fin m → Bool) : star (Gf x y)=Gf x y := Complex.conj_eq_iff_im.mpr (hf x y)
  have hg' (x y : X) : star (Gg x y)=Gg x y := Complex.conj_eq_iff_im.mpr (hg x y)
  intro x y
  apply Complex.conj_eq_iff_im.mp
  change star (weightedAdvGamma (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg) x y)=_
  simp only [weightedAdvGamma,star_mul,star_prod,hf']
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases he : x i=y i <;> simp [Matrix.diagonal,Matrix.add_apply,star_add,hg',he]

theorem sourceFunctionComposition_matrix_lower {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n m q : ℕ}
    (inner : X → Fin n → Fin (q+1)) (g : X → Bool) (f : (Fin m → Bool) → E)
    (hm : 0<m)
    (Gf : Matrix (Fin m → Bool) (Fin m → Bool) ℂ) (Gg : Matrix X X ℂ)
    (hGf : Gf.IsHermitian) (hGg : Gg.IsHermitian)
    (hfr : ∀ x y, (Gf x y).im=0) (hgr : ∀ x y, (Gg x y).im=0)
    (hzf : ∀ x y, f x=f y → Gf x y=0) (hzg : ∀ x y, g x=g y → Gg x y=0)
    (hff : ∀ j, ‖Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) j‖ ≤ 1)
    (hgf : ∀ k, ‖Gg ⊙ sourceAlphabetDelta inner k‖ ≤ 1) :
    ENNReal.ofReal ‖Gf‖*ENNReal.ofReal ‖Gg‖ ≤
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m)) (fun xs => f (fun j => g (xs j))) := by
  by_cases hg0 : ‖Gg‖=0
  · simp [hg0]
  have hgp : 0<‖Gg‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0)
  let d := ‖Gg‖^(m-1)
  have hd : 0<d := pow_pos hgp _
  let H := weightedAdvGamma (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg)
  let C := d⁻¹ • H
  have hH : H.IsHermitian := weightedAdvGamma_isHermitian _ _ _ _ hGf (fun _ => hGg)
  have hCr : ∀ x y, (C x y).im=0 := by
    intro x y
    simp only [C,Matrix.smul_apply,Complex.real_smul,Complex.mul_im,Complex.ofReal_im,zero_mul,
      Complex.ofReal_re,sourceWeightedAlphabet_real g Gf Gg hfr hgr,mul_zero,add_zero,H]
  have hCz : ∀ x y, f (fun j => g (x j))=f (fun j => g (y j)) → C x y=0 := by
    intro x y he
    simp [C,H,weightedAdvGamma,hzf _ _ he]
  have hCf (j : Fin (m*n)) : ‖C ⊙ sourceAlphabetDelta (sourceIndependentInput inner m) j‖ ≤ 1 := by
    rcases he : finProdFinEquiv.symm j with ⟨p,k⟩
    have hej : j=finProdFinEquiv (p,k) := by
      rw [← he]; exact (finProdFinEquiv.apply_symm_apply j).symm
    rw [hej]
    simp only [C,Matrix.smul_hadamard,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
    rw [sourceWeightedAlphabet_filter_norm inner g Gf Gg hGf hGg hzg p k]
    have hb : ‖Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) p‖*
        ‖Gg ⊙ sourceAlphabetDelta inner k‖*‖Gg‖^(m-1) ≤ d := by
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul (hff p) (hgf k) (norm_nonneg _) zero_le_one) (pow_nonneg (norm_nonneg _) _)).trans (by simp [d])
    exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hd.le)).trans
        (by rw [inv_mul_cancel₀ hd.ne'])
  have hCn : ‖C‖=‖Gf‖*‖Gg‖ := by
    simp only [C,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd),H,
      weightedAdvGamma_norm_eq (fun _ : Fin m => g) (fun _ => false) Gf (fun _ => Gg) hGf
        (fun _ => hGg) (fun _ => hzg),Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have he : m=(m-1)+1 := by omega
    have hpow : ‖Gg‖^m=d*‖Gg‖ := by
      calc
        ‖Gg‖^m=‖Gg‖^((m-1)+1) := congrArg (fun k : ℕ => ‖Gg‖^k) he
        _ = d*‖Gg‖ := by rw [pow_add,pow_one]
    rw [hpow]
    field_simp
  have hh : ENNReal.ofReal ‖C‖ ≤ sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m))
      (fun xs => f (fun j => g (xs j))) := by
    unfold sourceAdversary
    exact le_iSup_of_le ⟨C,hH.smul (IsSelfAdjoint.all _),hCr,hCz,hCf⟩ le_rfl
  simpa only [hCn,ENNReal.ofReal_mul (norm_nonneg Gf)] using! hh

theorem sourceFunctionComposition_lower {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n m q : ℕ}
    (inner : X → Fin n → Fin (q+1)) (g : X → Bool) (f : (Fin m → Bool) → E) :
    sourceAdversary (sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j))) f*
      sourceAdversary (sourceAlphabetDelta inner) g ≤
      sourceAdversary (sourceAlphabetDelta (sourceIndependentInput inner m)) (fun xs => f (fun j => g (xs j))) := by
  by_cases hm : m=0
  · subst m
    rw [sourceAdversary_zero_of_constant _ f (fun x y => congrArg f (Subsingleton.elim x y)),zero_mul]
    exact zero_le
  have hmp : 0<m := Nat.pos_of_ne_zero hm
  change (⨆ Gf : {Gf : Matrix (Fin m → Bool) (Fin m → Bool) ℂ // Gf.IsHermitian ∧
    (∀ x y, (Gf x y).im=0) ∧ (∀ x y, f x=f y → Gf x y=0) ∧
    ∀ j, ‖Gf ⊙ sourceAlphabetDelta (fun bs j => sourceBooleanSymbol (bs j)) j‖ ≤ 1}, ENNReal.ofReal ‖Gf.val‖)*
    (⨆ Gg : {Gg : Matrix X X ℂ // Gg.IsHermitian ∧ (∀ x y, (Gg x y).im=0) ∧
    (∀ x y, g x=g y → Gg x y=0) ∧ ∀ j, ‖Gg ⊙ sourceAlphabetDelta inner j‖ ≤ 1}, ENNReal.ofReal ‖Gg.val‖) ≤ _
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro Gf
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro Gg
  exact sourceFunctionComposition_matrix_lower inner g f hmp Gf.val Gg.val Gf.property.1 Gg.property.1
    Gf.property.2.1 Gg.property.2.1 Gf.property.2.2.1 Gg.property.2.2.1 Gf.property.2.2.2 Gg.property.2.2.2

theorem functionCompositionBounds : FunctionCompositionBounds := by
  refine ⟨?_,?_⟩
  · intro X Y E _ _ _ _ _ _ n m q a inner g outer f
    (try dsimp only)
    intro h
    exact sourceFunctionComposition_upper inner g outer f h
  · intro X E _ _ _ _ n m q inner g f
    exact sourceFunctionComposition_lower inner g f

end Qatlib.Concepts.GramQueryCore.GammaDuality
