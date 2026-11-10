/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.FunctionEvaluationAdversaryAlgStat
import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Qatlib.Concepts.GramQueryCore.GammaDuality.FunctionCompositionBoundsQuan
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Mathlib.Logic.Equiv.Bool
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem sourceAdversary_gram_progress {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] (G : Matrix X X ℂ) (weight : QState X) (ψ φ : X → QState H) :
    advProgress G weight ψ-advProgress G weight φ=
      (Inner weight ((G ⊙ (gramStateMatrix ψ-gramStateMatrix φ))*ᵥweight)).re := by
  simp only [advProgress,← Complex.sub_re,← Finset.sum_sub_distrib]
  congr 1
  simp only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,
    Matrix.hadamard_apply,Matrix.sub_apply,gramStateMatrix]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem sourceWord_adversary_progress_bound {X S : Type}
    [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (C : SourceWord ((Fin (n+1) × Fin (q+1)) × S))
    (hC : sourceWordLegal C) (G : Matrix X X ℂ)
    (hf : ∀ j, ‖G ⊙ sourceAlphabetDelta input j‖ ≤ 1)
    (weight : QState X) (hw : Normalized weight)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × S)) (hn : ∀ x, Normalized (ψ x)) :
    |advProgress G weight ψ-advProgress G weight
      (fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ ψ x)| ≤ 2*sourceWordCalls C := by
  let φ := fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ ψ x
  let A := gramStateMatrix ψ-gramStateMatrix φ
  have hc := sourceRectValue_le_of_cert (by positivity : (0 : ℝ)≤2*sourceWordCalls C)
    (sourceRectCert_of_gram (sourceGram_word_cert input C hC ψ hn))
  have hd := (sourceRectValue_dual_norm_le A (sourceAlphabetDelta input) G
    (fun j => by rw [Matrix.hadamard_comm]; exact hf j)).trans hc
  have hnorm : ‖G ⊙ A‖ ≤ 2*sourceWordCalls C := by
    rw [Matrix.hadamard_comm] at hd
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ)≤2*sourceWordCalls C)).mp hd
  rw [sourceAdversary_gram_progress]
  have hw1 : ‖toEuclidean_fromVec weight‖=1 := (normalized_iff_norm_toEuclidean_fromVec _).mp hw
  calc
    _ ≤ ‖Inner weight ((G ⊙ A)*ᵥweight)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖G ⊙ A‖*‖toEuclidean_fromVec weight‖*‖toEuclidean_fromVec weight‖ := adv_inner_matrix_bound _ _ _
    _ = ‖G ⊙ A‖ := by rw [hw1]; simp
    _ ≤ _ := hnorm

theorem sourceBoolean_actual_word_lower {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (G : Matrix X X ℂ) (hG : G.IsHermitian)
    (hf : ∀ j, ‖G ⊙ sourceAlphabetDelta input j‖ ≤ 1)
    (f : X → Bool) (hz : ∀ x y, f x=f y → G x y=0)
    (ψ : QState ((Fin (n+1) × Fin (q+1)) × H)) (hn : Normalized ψ)
    (C : SourceWord ((Fin (n+1) × Fin (q+1)) × H)) (hC : sourceWordLegal C)
    (E : Finset ((Fin (n+1) × Fin (q+1)) × H))
    (hSuccess : ∀ x, (2 : ℝ)/3 ≤ MeasureProb
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ ψ) (if f x then E else Eᶜ)) :
    ‖G‖ ≤ 40*sourceWordCalls C := by
  by_cases hg0 : ‖G‖=0
  · rw [hg0]
    positivity
  letI : Nonempty X := weightedAdv_nonempty_of_norm_pos G (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0))
  obtain ⟨weight,lam,hw,hlam,_,hStart⟩ :=
      negative_adversary_extreme_eigenvector_and_start X _ G ψ hG hn
  let out := fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ ψ
  have hOutNorm (x : X) : Normalized (out x) := normalized_applyGate
    (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) C hC) hn
  have hEnd := negative_adversary_boolean_actual_output_progress X _ G weight out f E (1/3)
    hG hw hz (by norm_num) (by norm_num) hOutNorm (by intro x; convert! hSuccess x using 1; norm_num)
  have hDiff :=
      sourceWord_adversary_progress_bound input C hC G hf weight hw (fun _ => ψ) (fun _ => hn)
  rw [hStart] at hDiff
  have hTri := abs_sub_le lam (advProgress G weight out) 0
  have hs : Real.sqrt ((1/3 : ℝ)*(1-1/3)) ≤ 19/40 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤(1/3)*(1-1/3)),Real.sqrt_nonneg ((1/3 : ℝ)*(1-1/3))]
  have hBound : |advProgress G weight out| ≤ (19/20 : ℝ)*‖G‖ :=
    hEnd.trans (by nlinarith [norm_nonneg G])
  simp only [sub_zero] at hTri
  rw [hlam] at hTri
  change |lam-advProgress G weight out| ≤ _ at hDiff
  nlinarith

def sourceBooleanCut {X : Type} (G : Matrix X X ℂ) (f : X → Bool) : Matrix X X ℂ :=
  G ⊙ gramFunctionEvaluationMatrix f

theorem sourceBooleanCut_norm_le {X : Type} [Fintype X] [DecidableEq X]
    (G : Matrix X X ℂ) (f : X → Bool) : ‖sourceBooleanCut G f‖ ≤ ‖G‖ := by
  let yes := Finset.univ.filter (fun x => f x=true)
  let no := Finset.univ.filter (fun x => f x=false)
  have he : sourceBooleanCut G f=sourceRectMask yes no G+sourceRectMask no yes G := by
    ext x y
    cases hx : f x <;> cases hy : f y <;> simp [sourceBooleanCut,Matrix.hadamard_apply,
      gramFunctionEvaluationMatrix,sourceRectMask,yes,no,hx,hy]
  have hd : sourceRowColumnDisjoint (sourceRectMask yes no G) (sourceRectMask no yes G) := by
    constructor
    · intro x y z hxy
      cases hx : f x <;> simp [sourceRectMask,yes,no,hx] at hxy ⊢
    · intro y x z hxy
      cases hy : f y <;> simp [sourceRectMask,yes,no,hy] at hxy ⊢
  rw [he,sourceRowColumnDisjoint_norm_add _ _ hd]
  exact max_le (sourceRectMask_norm_le yes no G) (sourceRectMask_norm_le no yes G)

theorem sourceBooleanCut_isHermitian {X : Type} (G : Matrix X X ℂ) (hG : G.IsHermitian)
    (f : X → Bool) : (sourceBooleanCut G f).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply,sourceBooleanCut,Matrix.hadamard_apply,star_mul,hG.apply]
  by_cases he : f x=f y <;> simp [gramFunctionEvaluationMatrix,he,eq_comm]

theorem sourceBooleanCut_filter {X : Type} {n q : ℕ}
    (G : Matrix X X ℂ) (f : X → Bool) (input : X → Fin n → Fin (q+1)) (j : Fin n) :
    sourceBooleanCut G f ⊙ sourceAlphabetDelta input j=sourceBooleanCut (G ⊙ sourceAlphabetDelta input j) f := by
  ext x y
  simp only [sourceBooleanCut,Matrix.hadamard_apply]
  ring

theorem sourceBooleanCut_average {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (G : Matrix X X ℂ) (f : X → E)
    (hz : ∀ x y, f x=f y → G x y=0) :
    (2 : ℝ) • (∑ h : E → Bool, sourceBooleanCut G (h ∘ f))=
      (Fintype.card (E → Bool) : ℝ) • G := by
  ext x y
  by_cases he : f x=f y
  · simp [Matrix.smul_apply,sourceBooleanCut,Matrix.sum_apply,Matrix.hadamard_apply,hz x y he]
  let e : (E → Bool) ≃ (E → Bool) :=
      Equiv.piCongrRight (fun a : E => if a=f x then Equiv.boolNot else Equiv.refl Bool)
  have hp (h : E → Bool) : sourceBooleanCut G (h ∘ f) x y+sourceBooleanCut G ((e h) ∘ f) x y=G x y := by
    have hx : e h (f x)= !(h (f x)) := by simp [e,Equiv.piCongrRight,Equiv.boolNot]
    have hy : e h (f y)=h (f y) := by simp [e,Equiv.piCongrRight,Ne.symm he]
    simp only [sourceBooleanCut,Matrix.hadamard_apply,gramFunctionEvaluationMatrix,Function.comp_apply,hx,hy]
    have hb (a b : Bool) (z : ℂ) : z*(if a=b then 0 else 1)+z*(if (!a)=b then 0 else 1)=z := by
      cases a <;> cases b <;> simp
    exact hb _ _ _
  have hs := congrArg (fun a : (E → Bool) → ℂ => ∑ h, a h) (funext hp)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at hs
  rw [e.sum_comp (fun h => sourceBooleanCut G (h ∘ f) x y)] at hs
  simp only [Matrix.smul_apply,Complex.real_smul,Matrix.sum_apply]
  push_cast
  linear_combination hs

theorem sourceBooleanCut_large {X E : Type} [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (G : Matrix X X ℂ) (f : X → E)
    (hz : ∀ x y, f x=f y → G x y=0) :
    ∃ h : E → Bool, ‖G‖ ≤ 2*‖sourceBooleanCut G (h ∘ f)‖ := by
  obtain ⟨h,_,hm⟩ := Finset.exists_max_image Finset.univ
    (fun h : E → Bool => ‖sourceBooleanCut G (h ∘ f)‖) Finset.univ_nonempty
  refine ⟨h,?_⟩
  have hc : (0 : ℝ)<Fintype.card (E → Bool) := by exact_mod_cast Fintype.card_pos
  have he := congrArg norm (sourceBooleanCut_average G f hz)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2),abs_of_pos hc] at he
  have hn : ‖∑ h : E → Bool, sourceBooleanCut G (h ∘ f)‖ ≤
      (Fintype.card (E → Bool) : ℝ)*‖sourceBooleanCut G (h ∘ f)‖ := by
    calc
      _ ≤ ∑ h : E → Bool, ‖sourceBooleanCut G (h ∘ f)‖ := norm_sum_le _ _
      _ ≤ ∑ _ : E → Bool, ‖sourceBooleanCut G (h ∘ f)‖ := Finset.sum_le_sum fun h' _ => hm h' (Finset.mem_univ h')
      _ = _ := by simp
  nlinarith

theorem sourceFunction_actual_word_lower {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (f : X → E) (G : Matrix X X ℂ)
    (hG : G.IsHermitian) (hz : ∀ x y, f x=f y → G x y=0)
    (hf : ∀ j, ‖G ⊙ sourceAlphabetDelta input j‖ ≤ 1)
    (C : SourceWord (SourceSpace n q (Option E) r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, (2 : ℝ)/3 ≤ MeasureProb
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (Ket none))
      (Finset.univ.filter (fun p => p.2.1.2=some (f x)))) :
    ‖G‖ ≤ 80*sourceWordCalls C := by
  obtain ⟨h,hlarge⟩ := sourceBooleanCut_large G f hz
  let K := sourceBooleanCut G (h ∘ f)
  let M : Finset (SourceSpace n q (Option E) r) :=
    Finset.univ.filter (fun p => ∃ e : E, p.2.1.2=some e ∧ h e=true)
  have hFilter (j : Fin n) : ‖K ⊙ sourceAlphabetDelta input j‖ ≤ 1 := by
    rw [sourceBooleanCut_filter]
    exact (sourceBooleanCut_norm_le _ _).trans (hf j)
  have hZero (x y : X) (he : h (f x)=h (f y)) : K x y=0 := by
    simp [K,sourceBooleanCut,Matrix.hadamard_apply,gramFunctionEvaluationMatrix,Function.comp_apply,he]
  have hSuccess' (x : X) : (2 : ℝ)/3 ≤ MeasureProb
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (Ket none))
      (if h (f x) then M else Mᶜ) := by
    apply (hSuccess x).trans
    apply measureProb_mono
    intro p hp
    have hlabel : p.2.1.2=some (f x) := (Finset.mem_filter.mp hp).2
    cases he : h (f x) with
    | true =>
      change p ∈ M
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,f x,hlabel,he⟩
    | false =>
      change p ∈ Mᶜ
      apply Finset.mem_compl.mpr
      intro hm
      obtain ⟨a,ha,hab⟩ := (Finset.mem_filter.mp hm).2
      have heq : a=f x := Option.some.inj (ha.symm.trans hlabel)
      rw [heq,he] at hab
      contradiction
  have hBound := sourceBoolean_actual_word_lower input K (sourceBooleanCut_isHermitian G hG _)
    hFilter (h ∘ f) hZero (sourceClean n q r hr false (Ket none))
    (sourceClean_normalized n q r hr false _ (normalized_ket none)) C hC M hSuccess'
  nlinarith

theorem sourceAdversary_actual_word_lower {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q r : ℕ} (hr : 0<r)
    (input : X → Fin n → Fin (q+1)) (f : X → E)
    (C : SourceWord (SourceSpace n q (Option E) r)) (hC : sourceWordLegal C)
    (hSuccess : ∀ x, (2 : ℝ)/3 ≤ MeasureProb
      (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ sourceClean n q r hr false (Ket none))
      (Finset.univ.filter (fun p => p.2.1.2=some (f x)))) :
    sourceAdversary (sourceAlphabetDelta input) f ≤ (80 : ℝ≥0∞)*(sourceWordCalls C : ℝ≥0∞) := by
  unfold sourceAdversary
  apply iSup_le
  intro G
  have hh := sourceFunction_actual_word_lower hr input f G.val G.property.1 G.property.2.2.1
    G.property.2.2.2 C hC hSuccess
  calc
    ENNReal.ofReal ‖G.val‖ ≤ ENNReal.ofReal (80*sourceWordCalls C) := ENNReal.ofReal_le_ofReal hh
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤80),ENNReal.ofReal_natCast]; norm_num

theorem sourceAdversary_le_functionQ {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) :
    sourceAdversary (sourceAlphabetDelta input) f ≤ (80 : ℝ≥0∞)*sourceFunctionQ input f := by
  unfold sourceFunctionQ
  rw [sInf_eq_iInf]
  simp_rw [ENNReal.mul_iInf_of_ne (by norm_num : (80 : ℝ≥0∞)≠0) (by norm_num : (80 : ℝ≥0∞)≠⊤)]
  apply le_iInf
  intro b
  apply le_iInf
  intro hmem
  obtain ⟨r,hr,C,hb,hC,hSuccess⟩ := hmem
  rw [hb]
  exact sourceAdversary_actual_word_lower hr input f C hC hSuccess

theorem sourceAdversary_ge_one_of_nonconstant {X E : Type}
    [Fintype X] [DecidableEq X] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E)
    (hnc : ¬ ∀ x y, f x=f y) : 1 ≤ sourceAdversary (sourceAlphabetDelta input) f := by
  push Not at hnc
  obtain ⟨x,y,hxy⟩ := hnc
  have hne : x≠y := fun he => hxy (he ▸ rfl)
  let P := permMatrix (Equiv.swap x y)
  let h : X → Bool := fun u => decide (u=x)
  let G : Matrix X X ℂ := fun u v => if (u=x ∧ v=y) ∨ (u=y ∧ v=x) then 1 else 0
  have hcut : G=sourceBooleanCut P h := by
    ext u v
    by_cases hux : u=x <;> by_cases huy : u=y <;> by_cases hvx : v=x <;> by_cases hvy : v=y <;>
      simp_all [G,sourceBooleanCut,P,h,Matrix.hadamard_apply,gramFunctionEvaluationMatrix,permMatrix,Equiv.swap_apply_def,eq_comm]
  have hG : G.IsHermitian := by
    rw [hcut]
    exact sourceBooleanCut_isHermitian P (permMatrix_conjTranspose (Equiv.swap_apply_self x y)) h
  have hreal (u v : X) : (G u v).im=0 := by simp only [G]; split_ifs <;> norm_num
  have hzero (u v : X) (he : f u=f v) : G u v=0 := by
    by_cases hs : (u=x ∧ v=y) ∨ (u=y ∧ v=x)
    · rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hxy he).elim
      · exact (hxy he.symm).elim
    · simp only [G,if_neg hs]
  have hnorm : ‖G‖ ≤ 1 := by
    rw [hcut]
    exact (sourceBooleanCut_norm_le P h).trans
        (l2_norm_unitary_le_one (permMatrix_unitary (Equiv.swap_apply_self x y)))
  have hf (j : Fin n) : ‖G ⊙ sourceAlphabetDelta input j‖ ≤ 1 := by
    have he : G ⊙ sourceAlphabetDelta input j=if input x j=input y j then 0 else G := by
      by_cases hi : input x j=input y j
      · rw [if_pos hi]
        ext u v
        by_cases hs : (u=x ∧ v=y) ∨ (u=y ∧ v=x)
        · rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [G,sourceAlphabetDelta,Matrix.hadamard_apply,hi,eq_comm]
        · simp [G,hs,Matrix.hadamard_apply]
      · rw [if_neg hi]
        ext u v
        by_cases hs : (u=x ∧ v=y) ∨ (u=y ∧ v=x)
        · rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [G,sourceAlphabetDelta,Matrix.hadamard_apply,hi,eq_comm]
          exact Ne.symm hi
        · simp [G,hs,Matrix.hadamard_apply]
    rw [he]
    split_ifs
    · simp
    · exact hnorm
  have hentry : (1 : ℝ) ≤ ‖G‖ := by
    have hh := gamma2_operator_entry_bound G x y
    simpa [G] using! hh
  calc
    1 = ENNReal.ofReal 1 := by norm_num
    _ ≤ ENNReal.ofReal ‖G‖ := ENNReal.ofReal_le_ofReal hentry
    _ ≤ sourceAdversary (sourceAlphabetDelta input) f := by
      unfold sourceAdversary
      exact le_iSup_of_le ⟨G,hG,hreal,hzero,hf⟩ le_rfl

theorem sourceFunction_free_word_of_constant {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) (hc : ∀ x y, f x=f y) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q (Option E) r)),
      sourceWordLegal C ∧ sourceWordCalls C=0 ∧ ∀ x,
      MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Ket none))
        (Finset.univ.filter (fun p => p.2.1.2=some (f x))) ≥ 2/3 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨1,by norm_num,[],by simp [sourceWordLegal],rfl,?_⟩
    intro x
    exact isEmptyElim x
  · let x0 : X := Classical.arbitrary X
    let a : SourceSpace n q (Option E) 1 := ((0,0),((false,none),0))
    let b : SourceSpace n q (Option E) 1 := ((0,0),((false,some (f x0)),0))
    let G := permMatrix (Equiv.swap a b)
    let C : SourceWord (SourceSpace n q (Option E) 1) := [.inl G]
    have hG : G ∈ Matrix.unitaryGroup _ ℂ := permMatrix_unitary (Equiv.swap_apply_self a b)
    refine ⟨1,by norm_num,C,?_,by simp [C,sourceWordCalls],?_⟩
    · intro s hs
      have he : s=Sum.inl G := by simpa [C] using! hs
      subst s
      exact hG
    · intro x
      have hstart : sourceClean n q 1 (by norm_num) false (Ket (none : Option E))=Ket a := by
        simp only [sourceClean,tensorState_ket_ket]
        rfl
      have hout : G*ᵥKet a=Ket b := by
        simpa only [Equiv.swap_apply_left] using!
            applyGate_permMatrix_ket (Equiv.swap_apply_self a b) a
      simp only [C,sourceWordMatrix,List.map_cons,List.map_nil,List.reverse_singleton,List.prod_cons,
        List.prod_nil,Matrix.mul_one,hstart,hout]
      have hp : MeasureProb (Ket b) (Finset.univ.filter (fun p => p.2.1.2=some (f x)))=1 := by
        unfold MeasureProb
        rw [Finset.sum_eq_single b]
        · simp [BornProb,Ket]
        · intro z _ hzb
          simp [BornProb,Ket,hzb]
        · simp [b,hc x x0]
      rw [hp]
      norm_num

theorem sourceFunctionQ_zero_of_constant {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E) (hc : ∀ x y, f x=f y) :
    sourceFunctionQ input f=0 := by
  obtain ⟨r,hr,C,hC,hcalls,hSuccess⟩ := sourceFunction_free_word_of_constant input f hc
  apply le_antisymm _ zero_le
  apply sInf_le
  refine ⟨r,hr,C,?_,hC,hSuccess⟩
  simp [hcalls]

theorem sourceFunction_free_word_of_zero_adversary {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (input : X → Fin n → Fin (q+1)) (f : X → E)
    (hz : sourceAdversary (sourceAlphabetDelta input) f=0) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q (Option E) r)),
      sourceWordLegal C ∧ sourceWordCalls C=0 ∧ ∀ x,
      MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (Ket none))
        (Finset.univ.filter (fun p => p.2.1.2=some (f x))) ≥ 2/3 := by
  apply sourceFunction_free_word_of_constant input f
  by_contra hnc
  have hh := sourceAdversary_ge_one_of_nonconstant input f hnc
  rw [hz] at hh
  norm_num at hh

theorem sourceFunction_measure_of_overlap {E : Type} [Fintype E] [DecidableEq E]
    {n q r : ℕ} (hr : 0<r) (e : E) (out : QState (SourceSpace n q (Option E) r))
    (h : (∑ p, star (out p)*sourceClean n q r hr true (Ket (some e)) p).re ≥
      Real.sqrt (1-(1/3 : ℝ))) :
    MeasureProb out (Finset.univ.filter (fun p => p.2.1.2=some e)) ≥ 2/3 := by
  let t : SourceSpace n q (Option E) r := ((0,0),((true,some e),⟨0,hr⟩))
  have ht : sourceClean n q r hr true (Ket (some e))=Ket t := by
    simp only [sourceClean,tensorState_ket_ket]
    rfl
  rw [ht] at h
  have hre : Real.sqrt (1-(1/3 : ℝ)) ≤ (out t).re := by simpa [Ket] using! h
  have hp : (2 : ℝ)/3 ≤ ‖out t‖^2 := by
    have hnorm := Complex.re_le_norm (out t)
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤1-1/3),Real.sqrt_nonneg (1-(1/3 : ℝ))]
  exact hp.trans (Finset.single_le_sum (fun p _ => sq_nonneg ‖out p‖) (by simp [t]))

theorem sourceFunction_gram_difference {X E : Type} [Fintype E] [DecidableEq E]
    (f : X → E) :
    gramStateMatrix (fun _ : X => Ket (none : Option E))-
      gramStateMatrix (fun x => Ket (some (f x)))=gramFunctionEvaluationMatrix f := by
  ext x y
  by_cases he : f x=f y <;> simp [gramStateMatrix,gramFunctionEvaluationMatrix,Qatlib.Foundations.PureStateMath.Inner,dotProduct,Ket,he,eq_comm]

 theorem sourceFunction_word_from_conversion {X E : Type}
    [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E] {n q : ℕ}
    (c : ℕ) (hc : 0<c)
    (h15 : ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
      (n q : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0≤W →
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix σ) (sourceAlphabetDelta input) ≤ ENNReal.ofReal W →
      0<ε → ε≤1/3 → ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C≤c*Nat.ceil (W*Real.log (2/ε)/ε^2) ∧
        ((W=0 ∨ n=0 ∨ q=0) → sourceWordCalls C=0) ∧
        (∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥ Real.sqrt (1-ε)) ∧
        (ε≤W → ∀ x, ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖ < 4*ε))
    (input : X → Fin n → Fin (q+1)) (f : X → E) (W : ℝ) (hW : 0≤W)
    (hb : sourceAdversary (sourceAlphabetDelta input) f≤ENNReal.ofReal W) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q (Option E) r)),
      sourceWordLegal C ∧ (sourceWordCalls C : ℝ)≤(100*c : ℕ)*W ∧ ∀ x,
        MeasureProb (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (Ket none))
          (Finset.univ.filter (fun p => p.2.1.2=some (f x))) ≥ 2/3 := by
  by_cases hconst : ∀ x y, f x=f y
  · obtain ⟨r,hr,C,hC,hcalls,hSuccess⟩ := sourceFunction_free_word_of_constant input f hconst
    exact ⟨r,hr,C,hC,by rw [hcalls]; simp only [Nat.cast_zero]; positivity,hSuccess⟩
  have hW1 : 1≤W := by
    have hh := (sourceAdversary_ge_one_of_nonconstant input f hconst).trans hb
    rw [← ENNReal.ofReal_one] at hh
    exact (ENNReal.ofReal_le_ofReal_iff hW).mp hh
  have hn (x : X) : Normalized (Ket (none : Option E)) ∧ Normalized (Ket (some (f x))) :=
    ⟨normalized_ket _,normalized_ket _⟩
  have hv : sourceRectValue (gramStateMatrix (fun _ : X => Ket (none : Option E))-
      gramStateMatrix (fun x => Ket (some (f x)))) (sourceAlphabetDelta input)≤ENNReal.ofReal (2*W) := by
    rw [sourceFunction_gram_difference]
    have hh := (functionEvaluationNormSandwich X E n q input f).2.2.2
    have hc2 : ENNReal.ofReal (2*(1-1/(Fintype.card E : ℝ)))≤ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by
      have he : 0≤1/(Fintype.card E : ℝ) := by positivity
      linarith)
    exact (hh.trans (mul_le_mul hc2 hb zero_le zero_le)).trans_eq
        (ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)).symm
  obtain ⟨r,hr,C,hC,hCalls,_,hOverlap,_⟩ := h15 X (Option E) n q input
    (fun _ => Ket none) (fun x => Ket (some (f x))) (2*W) (1/3) hn (by positivity) hv (by norm_num) le_rfl
  refine ⟨r,hr,C,hC,?_,fun x => sourceFunction_measure_of_overlap hr (f x) _ (hOverlap x)⟩
  have hlog0 : 0≤Real.log 6 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 6≤5 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<6)
    norm_num at hh
    exact hh
  have hex : 0≤(2*W)*Real.log (2/(1/3 : ℝ))/(1/3 : ℝ)^2 := by
    have he : (2*W)*Real.log (2/(1/3 : ℝ))/(1/3 : ℝ)^2=18*W*Real.log 6 := by norm_num; ring
    rw [he]
    positivity
  have hceil := (Nat.ceil_lt_add_one hex).le
  have hcast :
      (sourceWordCalls C : ℝ)≤(c : ℝ)*(Nat.ceil ((2*W)*Real.log (2/(1/3 : ℝ))/(1/3 : ℝ)^2) : ℝ) :=
      by exact_mod_cast hCalls
  have hh := hcast.trans (mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg c))
  have he : (2*W)*Real.log (2/(1/3 : ℝ))/(1/3 : ℝ)^2=18*W*Real.log 6 := by norm_num; ring
  rw [he] at hh
  push_cast
  nlinarith [mul_nonneg (show (0 : ℝ)≤c by positivity) (mul_nonneg hW (sub_nonneg.mpr hlog))]

theorem functionEvaluationAdversaryAlgorithm_of_conversion
    (h15 : RealBudgetConversionAlgorithm) : FunctionEvaluationAdversaryAlgorithm := by
  obtain ⟨c,hc,h15⟩ := h15
  refine ⟨100*c+80,by positivity,?_⟩
  intro X E _ _ _ _ n q input f
  have h80 : (80 : ℝ≥0∞) ≤ ((100*c+80 : ℕ) : ℝ≥0∞) := by norm_cast; omega
  have h100 : ((100*c : ℕ) : ℝ) ≤ ((100*c+80 : ℕ) : ℝ) := by push_cast; linarith
  refine ⟨?_,?_,?_⟩
  · exact (sourceAdversary_le_functionQ input f).trans (mul_le_mul h80 le_rfl zero_le zero_le)
  · by_cases ht : sourceAdversary (sourceAlphabetDelta input) f=⊤
    · have hn : ((100*c+80 : ℕ) : ℝ≥0∞)≠0 := by norm_cast
      rw [ht,ENNReal.mul_top hn]
      exact le_top
    · let W := (sourceAdversary (sourceAlphabetDelta input) f).toReal
      have hW : 0≤W := ENNReal.toReal_nonneg
      have hval : ENNReal.ofReal W=sourceAdversary (sourceAlphabetDelta input) f :=
          ENNReal.ofReal_toReal ht
      obtain ⟨r,hr,C,hC,hCalls,hSuccess⟩ :=
          sourceFunction_word_from_conversion c hc h15 input f W hW (le_of_eq hval.symm)
      have hFQ : sourceFunctionQ input f≤(sourceWordCalls C : ℝ≥0∞) :=
          sInf_le ⟨r,hr,C,rfl,hC,hSuccess⟩
      calc
        sourceFunctionQ input f ≤ (sourceWordCalls C : ℝ≥0∞) := hFQ
        _ = ENNReal.ofReal (sourceWordCalls C : ℝ) := (ENNReal.ofReal_natCast _).symm
        _ ≤ ENNReal.ofReal (((100*c+80 : ℕ) : ℝ)*W) := ENNReal.ofReal_le_ofReal
          (hCalls.trans (mul_le_mul_of_nonneg_right h100 hW))
        _ = ((100*c+80 : ℕ) : ℝ≥0∞)*sourceAdversary (sourceAlphabetDelta input) f := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,hval]
  · intro W hW hb
    obtain ⟨r,hr,C,hC,hCalls,hSuccess⟩ :=
        sourceFunction_word_from_conversion c hc h15 input f W hW hb
    refine ⟨r,hr,C,hC,?_,hSuccess⟩
    have hrange : (sourceWordCalls C : ℝ)≤((100*c+80 : ℕ) : ℝ)*W :=
      hCalls.trans (mul_le_mul_of_nonneg_right h100 hW)
    have hh := hrange.trans (Nat.le_ceil (((100*c+80 : ℕ) : ℝ)*W))
    exact_mod_cast hh

theorem functionEvaluationAdversaryAlgorithm : FunctionEvaluationAdversaryAlgorithm :=
  functionEvaluationAdversaryAlgorithm_of_conversion realBudgetConversionAlgorithm

end Qatlib.Concepts.ConversionCore.WitnessCompile
