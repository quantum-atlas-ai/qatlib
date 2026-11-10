/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.StateConversion.RealBudgetConversionAlgorithmStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.GeneralOutputGramBridgesQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FunctionEvaluationNormSandwichQuan
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.QueryComplexity.StateConversion
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators ENNReal ComplexOrder

theorem sourceAlphabet_unfiltered_budget {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (A : Matrix X X ℂ)
    (W : ℝ) (hW : 0≤W)
    (hval : sourceRectValue A (sourceAlphabetDelta input)≤ENNReal.ofReal W) :
    sourceUnfiltered A≤ENNReal.ofReal (2*W) := by
  have hf : sourceRectValue A (sourceAlphabetDelta input)<⊤ :=
    lt_of_le_of_lt hval ENNReal.ofReal_lt_top
  have hfilter (j : Fin n) : sourceUnfiltered (sourceAlphabetDelta input j)≤ENNReal.ofReal 2 := by
    have h := sourceUnfiltered_functionEvaluation (fun x => input x j)
    have he : sourceAlphabetDelta input j=gramFunctionEvaluationMatrix (fun x => input x j) := rfl
    rw [he]
    exact h.trans (ENNReal.ofReal_le_ofReal (by
      have hp : 0≤1/(Fintype.card (Fin (q+1)) : ℝ) := by positivity
      linarith))
  have hb : (⨆ j,sourceUnfiltered (sourceAlphabetDelta input j))≤ENNReal.ofReal 2 :=
    iSup_le hfilter
  have hc := sourceRectValue_composition A (sourceAlphabetDelta input)
    (fun _ : Fin 1 => fun _ _ => (1 : ℂ)) (Or.inl hf)
  change sourceUnfiltered A≤_ at hc
  calc
    sourceUnfiltered A ≤ sourceRectValue A (sourceAlphabetDelta input)*
        ⨆ j,sourceUnfiltered (sourceAlphabetDelta input j) := hc
    _ ≤ ENNReal.ofReal W*ENNReal.ofReal 2 := mul_le_mul hval hb zero_le zero_le
    _ = ENNReal.ofReal (2*W) := by rw [← ENNReal.ofReal_mul hW,mul_comm W 2]

theorem source_free_word_native {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ) (ρ σ : X → QState H)
    (δ : ℝ) (hn : ∀ x, Normalized (ρ x)∧Normalized (σ x)) (hδ : 0≤δ)
    (hval : sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ)≤ENNReal.ofReal δ) :
    ∃ (r : ℕ) (hr : 0<r) (G : Matrix (SourceSpace n q H r) (SourceSpace n q H r) ℂ),
      G ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ x,
      ‖toEuclidean_fromVec (G *ᵥ sourceClean n q r hr false (ρ x)-
        sourceClean n q r hr true (σ x))‖≤Real.sqrt (2*δ) := by
  obtain ⟨r,hr,C,hC,hcalls,herr⟩ := sourceGram_free_word ρ σ δ hn hδ hval
  let U := sourceWordMatrix (1 : Matrix (SourceSpace 0 0 H r) _ ℂ) C
  have hU : U ∈ Matrix.unitaryGroup _ ℂ := sourceWordMatrix_unitary _
    (Matrix.unitaryGroup _ ℂ).one_mem C hC
  let e : SourceSpace 0 0 H r → SourceSpace n q H r := fun p => ((0,0),p.2)
  have he : Function.Injective e := by
    intro p t h
    have hp : p.1=(0,0) := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have ht : t.1=(0,0) := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hh := congrArg (fun p => p.2) h
    exact Prod.ext (hp.trans ht.symm) hh
  let F := sourceBasisFrame e
  have hF : Fᴴ*F=1 := sourceBasisFrame_isometry e he
  obtain ⟨G,hG,hGF⟩ := sourceExtendFrameUnitary F hF U hU
  have hclean (tag : Bool) (ψ : QState H) : F *ᵥ sourceClean 0 0 r hr tag ψ=
      sourceClean n q r hr tag ψ := by
    ext p
    simp [F,sourceBasisFrame,e,sourceClean,TensorState,Ket,Matrix.mulVec,dotProduct,
      Fintype.sum_prod_type,Prod.ext_iff]
    by_cases ha : p.1.1=0 ∧ p.1.2=0
    · simp only [ha,true_and]
      split_ifs <;> simp_all
    · simp [ha]
  refine ⟨r,hr,G,hG,?_⟩
  intro x
  rw [← hclean false,← hclean true,Matrix.mulVec_mulVec,hGF,← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_sub,isometry_mulVec_norm hF]
  exact herr x

theorem source_overlap_of_distance {H : Type} [Fintype H]
    (ψ φ : QState H) (hψ : Normalized ψ) (hφ : Normalized φ)
    (ε : ℝ) (_hε : 0≤ε) (hε1 : ε≤1)
    (hd : ‖toEuclidean_fromVec (ψ-φ)‖^2≤ε) :
    (Inner ψ φ).re≥Real.sqrt (1-ε) := by
  have hnψ := (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hnφ := (normalized_iff_norm_toEuclidean_fromVec φ).mp hφ
  have hid := norm_sub_sq (𝕜 := ℂ) (toEuclidean_fromVec ψ) (toEuclidean_fromVec φ)
  have hie : inner ℂ (toEuclidean_fromVec ψ) (toEuclidean_fromVec φ)=Inner ψ φ := by
    change φ ⬝ᵥ star ψ=star ψ ⬝ᵥ φ
    exact dotProduct_comm _ _
  rw [hie] at hid
  change ‖toEuclidean_fromVec (ψ-φ)‖^2=‖toEuclidean_fromVec ψ‖^2-
    2*(Inner ψ φ).re+‖toEuclidean_fromVec φ‖^2 at hid
  rw [hnψ,hnφ] at hid
  have hs : Real.sqrt (1-ε)≤1-ε/2 := by
    have hh := Real.sq_sqrt (sub_nonneg.mpr hε1)
    nlinarith [Real.sqrt_nonneg (1-ε),sq_nonneg ε]
  linarith

def sourceLogicalRoot {H : Type} [DecidableEq H] (n q m : ℕ) (tag : Bool)
    (ψ : QState H) : QState (SourceGeometry n q m H) :=
  Sum.elim (TensorState (Ket tag) ψ) 0

def sourceConversionEmbed {H : Type} [DecidableEq H] (b : ℕ) (ψ : QState H) :
    QState ((Bool×H)×Fin (2^b)) :=
  TensorState (TensorState (Ket false) ψ) (Ket 0)

def sourceConversionCode (H : Type) (n q m b : ℕ) :
    Bool×H → (Bool×SourceGeometry n q m H)×Fin (2^b) :=
  fun p => ((false,.inl p),0)

theorem sourceConversionCode_injective (H : Type) (n q m b : ℕ) :
    Function.Injective (sourceConversionCode H n q m b) := by
  intro p t he
  have h := congrArg (fun v => v.1.2) he
  exact Sum.inl.inj h

theorem sourceConversionFrame_root {H : Type} [Fintype H] [DecidableEq H]
    (n q m b : ℕ) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (sourceConversionCode H n q m b) *ᵥ TensorState (Ket tag) ψ=
      sourceConversionEmbed b (sourceLogicalRoot n q m tag ψ) := by
  ext p
  rcases p with ⟨⟨f,s⟩,c⟩
  cases s with
  | inl s =>
    simp [sourceBasisFrame,sourceConversionCode,Matrix.mulVec,dotProduct,
      sourceConversionEmbed,sourceLogicalRoot,TensorState,Ket,Fintype.sum_prod_type,Prod.ext_iff]
    split_ifs <;> simp_all
  | inr s =>
    simp [sourceBasisFrame,sourceConversionCode,Matrix.mulVec,dotProduct,
      sourceConversionEmbed,sourceLogicalRoot,TensorState]

theorem sourceNativeFrame_clean {H : Type} [Fintype H] [DecidableEq H]
    (n q r : ℕ) (hr : 0<r) (tag : Bool) (ψ : QState H) :
    sourceBasisFrame (fun p : Bool×H => ((0,0),(p,(⟨0,hr⟩ : Fin r))) :
      Bool×H → SourceSpace n q H r) *ᵥ TensorState (Ket tag) ψ=
      sourceClean n q r hr tag ψ := by
  ext p
  simp [sourceBasisFrame,sourceClean,TensorState,Ket,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,Prod.ext_iff]
  by_cases ha : p.1.1=0 ∧ p.1.2=0
  · simp only [ha,true_and]
    split_ifs <;> simp_all
  · simp [ha]

theorem sourceConversion_native_word {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q m b : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W η : ℝ) (hq : 0<q)
    (C : SourceWord ((Bool×SourceGeometry n q m H)×Fin (2^b)))
    (hC : sourceWordLegal C) (e : ℝ)
    (herr : ∀ x, ‖toEuclidean_fromVec
      (sourceWordMatrix (sourceControlledU (2^b) (ReflectionAbout (sourceKeep input x)*
        ReflectionAbout (sourceComplement input ρ σ u W η))) C *ᵥ
        sourceConversionEmbed b (sourceLogicalRoot n q m false (ρ x))-
        sourceConversionEmbed b (sourceLogicalRoot n q m true (σ x)))‖≤e) :
    ∃ (r : ℕ) (hr : 0<r) (D : SourceWord (SourceSpace n q H r)),
      sourceWordLegal D ∧ sourceWordCalls D≤2*sourceWordCalls C ∧ ∀ x,
      ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖≤e := by
  obtain ⟨r,hr,F,Q,hF,hQ,hcalls,hact⟩ :=
    alphabetPhaseWordAssembly X H n q m b input ρ σ u W η hq C hC
  let E := sourceBasisFrame (sourceConversionCode H n q m b)
  have hE : Eᴴ*E=1 := sourceBasisFrame_isometry _ (sourceConversionCode_injective H n q m b)
  let L := sourceBasisFrame (fun p : Bool×H => ((0,0),(p,(⟨0,hr⟩ : Fin r))) :
    Bool×H → SourceSpace n q H r)
  have hL : Lᴴ*L=1 := sourceBasisFrame_isometry _ (by
    intro p t he
    exact congrArg (fun v => v.2.1) he)
  have hGram : Lᴴ*L=(F*E)ᴴ*(F*E) := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F,hF,Matrix.one_mul,hE,hL]
  obtain ⟨B,hB,hBL⟩ := gram_equal_actual_unitary_transport _ _ L (F*E) hGram
  have hBadj : Bᴴ ∈ Matrix.unitaryGroup _ ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using! Unitary.star_mem hB
  let D : SourceWord (SourceSpace n q H r) := [.inl B]++Q++[.inl Bᴴ]
  have hD : sourceWordLegal D := by
    apply sourceWordLegal_append
    · apply sourceWordLegal_append
      · intro s hs
        simp only [List.mem_singleton] at hs
        subst s
        exact hB
      · exact hQ
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact hBadj
  have hDcalls : sourceWordCalls D=sourceWordCalls Q := by
    simp [D,sourceWordCalls]
  refine ⟨r,hr,D,hD,by rw [hDcalls]; exact hcalls,?_⟩
  have hBleft : Bᴴ*B=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hB.1
  have hclean (tag : Bool) (ψ : QState H) :
      B *ᵥ sourceClean n q r hr tag ψ=F *ᵥ sourceConversionEmbed b
        (sourceLogicalRoot n q m tag ψ) := by
    rw [← sourceNativeFrame_clean]
    change B *ᵥ (L *ᵥ TensorState (Ket tag) ψ)=_
    rw [Matrix.mulVec_mulVec,hBL,← Matrix.mulVec_mulVec,sourceConversionFrame_root]
  intro x
  have htarget : sourceClean n q r hr true (σ x)=
      Bᴴ *ᵥ (F *ᵥ sourceConversionEmbed b (sourceLogicalRoot n q m true (σ x))) := by
    rw [← hclean,Matrix.mulVec_mulVec,hBleft,Matrix.one_mulVec]
  have hmat : sourceWordMatrix (sourceAlphabetOracle input x) D=
      Bᴴ*sourceWordMatrix (sourceAlphabetOracle input x) Q*B := by
    dsimp only [D]
    rw [sourceWordMatrix_append,sourceWordMatrix_append]
    simp [sourceWordMatrix,Matrix.mul_assoc]
  rw [hmat,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hclean,hact,htarget,
    ← Matrix.mulVec_sub,← Matrix.mulVec_sub]
  rw [isometry_mulVec_norm (by change (Bᴴ)ᴴ*Bᴴ=1; simpa only [Matrix.conjTranspose_conjTranspose,Matrix.star_eq_conjTranspose] using! hB.2),
    isometry_mulVec_norm hF]
  exact herr x

theorem sourceWordMatrix_decidable_transport {S : Type} [Fintype S]
    (d e : DecidableEq S) (O : Matrix S S ℂ) (C : SourceWord S) :
    @sourceWordMatrix S _ d O C=@sourceWordMatrix S _ e O C := by
  cases Subsingleton.elim d e
  rfl

theorem sourceLogicalRoot_splits {H : Type} [DecidableEq H] (n q m : ℕ) (ρ σ : QState H) :
    sourceLogicalRoot n q m false ρ=(Real.sqrt 2 : ℂ)⁻¹ • (sourcePlus ρ σ+sourceMinus ρ σ) ∧
    sourceLogicalRoot n q m true σ=(Real.sqrt 2 : ℂ)⁻¹ • (sourcePlus ρ σ-sourceMinus ρ σ) := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2 : ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  constructor <;> ext p <;> cases p with
  | inl p =>
    rcases p with ⟨tag,h⟩
    cases tag <;> simp [sourceLogicalRoot,sourcePlus,sourceMinus,TensorState,Ket]
    all_goals
      field_simp
      first | linear_combination (ρ h)*hs | linear_combination (σ h)*hs
  | inr p => simp [sourceLogicalRoot,sourcePlus,sourceMinus]

theorem source_onepass_balanced_error {H : Type} [Fintype H] [DecidableEq H]
    (n q m : ℕ) (U : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ)
    (M : ℕ) (ρ σ : QState H) (a b : ℝ)
    (hp : ‖toEuclidean_fromVec (phaseReflectionState U M 1 (sourcePlus ρ σ)-
      phaseReflectionEmbed M 1 (sourcePlus ρ σ))‖≤a)
    (hm : ‖toEuclidean_fromVec (phaseReflectionState U M 1 (sourceMinus ρ σ)+
      phaseReflectionEmbed M 1 (sourceMinus ρ σ))‖≤b) :
    ‖toEuclidean_fromVec (phaseReflectionState U M 1 (sourceLogicalRoot n q m false ρ)-
      phaseReflectionEmbed M 1 (sourceLogicalRoot n q m true σ))‖≤a+b := by
  obtain ⟨hsource,htarget⟩ := sourceLogicalRoot_splits n q m ρ σ
  have he : phaseReflectionState U M 1 (sourceLogicalRoot n q m false ρ)-
      phaseReflectionEmbed M 1 (sourceLogicalRoot n q m true σ)=
      (Real.sqrt 2 : ℂ)⁻¹ • ((phaseReflectionState U M 1 (sourcePlus ρ σ)-
        phaseReflectionEmbed M 1 (sourcePlus ρ σ))+
        (phaseReflectionState U M 1 (sourceMinus ρ σ)+phaseReflectionEmbed M 1 (sourceMinus ρ σ))) := by
    rw [hsource,htarget,phaseReflectionState_smul,phaseReflectionState_add,
      phaseReflectionEmbed_smul,phaseReflectionEmbed_sub,← smul_sub]
    congr 1
    abel
  have hc : ‖(Real.sqrt 2 : ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))
  rw [he]
  change ‖(Real.sqrt 2 : ℂ)⁻¹ • (toEuclidean_fromVec _+toEuclidean_fromVec _)‖≤_
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
    (by rw [one_mul]; exact (norm_add_le _ _).trans (add_le_add hp hm))

theorem source_onepass_native_algorithm {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] {n q m : ℕ}
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u v : X → Fin n → QState (Fin m)) (W η : ℝ)
    (hn : ∀ x, Normalized (ρ x)∧Normalized (σ x)) (hq : 0<q) (hW : 0<W) (hη : 0<η)
    (hηW : η≤W) (a : ℕ) (hM : 2≤2^a)
    (hEq : ∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
      ∑ j,sourceAlphabetDelta input j y x*∑ k,star (u y j k)*v x j k)
    (hbudget : ∀ x,(∑ j,‖toEuclidean_fromVec (u x j)‖^2)≤W ∧
      (∑ j,‖toEuclidean_fromVec (v x j)‖^2)≤W) :
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
      sourceWordLegal C ∧ sourceWordCalls C≤4*(2^a-1) ∧ ∀ x,
      ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖≤
        2*η+4*W/(η*(2^a : ℕ)) := by
  letI : DecidableEq (SourceGeometry n q m H) := instDecidableEqSum
  letI : DecidableEq (PhaseReflectionSpace (SourceGeometry n q m H) (2^a) 1) := instDecidableEqProd
  obtain ⟨hL,hgeometry⟩ := sourceGeometry_of_witness input ρ σ u v W η hn hq hW hη hEq hbudget
  let C := phaseSourceCompile (sourcePhaseRoute (SourceGeometry n q m H) a 1)
    (phaseReflectionWord (2^a) 1)
  have hC := @phaseSourceCompile_legal
    (PhaseReflectionSpace (SourceGeometry n q m H) (2^a) 1)
    ((Bool×SourceGeometry n q m H)×Fin (2^(a*1)))
    inferInstance inferInstance inferInstance (Classical.decEq _)
    (sourcePhaseRoute (SourceGeometry n q m H) a 1) (phaseReflectionWord (2^a) 1)
    (phase_reflection_actual_queries_and_macros (I:=SourceGeometry n q m H) (2^a) 1 hM).1
  obtain ⟨r,hr,D,hD,hcalls,herr⟩ := sourceConversion_native_word input ρ σ u W η hq C hC
    (2*η+4*W/(η*(2^a : ℕ))) (by
      intro x
      obtain ⟨hP,hLf,hLt,hPt,hPf,hdist,hfw⟩ := hgeometry x
      let U : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ :=
          ReflectionAbout (sourceKeep (H := H) (m := m) input x)*ReflectionAbout
          (sourceComplement input ρ σ u W η)
      have hU : U ∈ Matrix.unitaryGroup _ ℂ :=
        (Matrix.unitaryGroup _ ℂ).mul_mem (reflectionAbout_unitary hP) (reflectionAbout_unitary hL)
      have hfix : ApplyGate U (sourceFixed input ρ σ v W η x)=sourceFixed input ρ σ v W η x := by
        dsimp only [U]
        rw [applyGate_mul,applyGate_reflectionAbout_of_fixed hLt,applyGate_reflectionAbout_of_fixed hPt]
      have hd : ‖toEuclidean_fromVec (sourceFixed input ρ σ v W η x-sourcePlus (ρ x) (σ x))‖≤η := by
        nlinarith [norm_nonneg (toEuclidean_fromVec (sourceFixed input ρ σ v W η x-sourcePlus (ρ x) (σ x)))]
      have hp := conversion_onepass_fixed_root_error (2^a) 1 hM (by omega) U hU
        (sourceFixed input ρ σ v W η x) (sourcePlus (ρ x) (σ x)) hfix η hd
      let w := ((Real.sqrt W/η : ℝ) : ℂ) • sourceForbidden input ρ σ u W η x
      have hLw : ApplyGate (sourceComplement input ρ σ u W η) w=0 := by
        dsimp only [w,ApplyGate]
        rw [Matrix.mulVec_smul,hLf,smul_zero]
      have hPw : ApplyGate (sourceKeep (H := H) (m := m) input x) w=sourceMinus (ρ x) (σ x) := by
        dsimp only [w,ApplyGate]
        rw [Matrix.mulVec_smul,hPf,smul_smul]
        have hc : ((Real.sqrt W/η : ℝ) : ℂ)*((η/Real.sqrt W : ℝ) : ℂ)=1 := by
          push_cast
          have hr : (Real.sqrt W : ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hW).ne'
          have he : (η : ℂ)≠0 := by exact_mod_cast hη.ne'
          field_simp
        rw [hc,one_smul]
      have hw : ‖toEuclidean_fromVec w‖≤2*W/η := by
        have ht : 1≤W/η := (le_div_iff₀ hη).mpr (by simpa using! hηW)
        have he : W^2/η^2=(W/η)^2 := by ring
        rw [he] at hfw
        change ‖toEuclidean_fromVec w‖^2≤(W/η)^2+1 at hfw
        rw [mul_div_assoc]
        nlinarith [norm_nonneg (toEuclidean_fromVec w)]
      have hm := conversion_onepass_forbidden_root_error (2^a) (by omega)
        (sourceKeep (H := H) (m := m) input x) (sourceComplement input ρ σ u W η) hP hL
        (sourceMinus (ρ x) (σ x)) w hLw hPw (2*W/η) hw
      have hb := source_onepass_balanced_error n q m U (2^a) (ρ x) (σ x)
        (2*η) (2*(2*W/η)/(2^a : ℕ)) hp hm
      rw [sourceWordMatrix_decidable_transport
        (Classical.decEq ((Bool×SourceGeometry n q m H)×Fin (2^(a*1))))
        (instDecidableEqProd : DecidableEq ((Bool×SourceGeometry n q m H)×Fin (2^(a*1))))]
      change ‖toEuclidean_fromVec (sourceWordMatrix (sourceControlledU (2^(a*1)) U) C *ᵥ
        sourceConversionEmbed (a*1) (sourceLogicalRoot n q m false (ρ x))-
        sourceConversionEmbed (a*1) (sourceLogicalRoot n q m true (σ x)))‖≤_
      dsimp only [C,sourceConversionEmbed]
      rw [sourcePhaseCompiledRun (H := SourceGeometry n q m H) a 1 U,← sourcePhaseRoute_embed]
      change ‖toEuclidean_fromVec (relabelState (sourcePhaseRoute _ a 1)
        (phaseReflectionState U (2^a) 1 (sourceLogicalRoot n q m false (ρ x))-
          phaseReflectionEmbed (2^a) 1 (sourceLogicalRoot n q m true (σ x))))‖≤_
      rw [norm_toEuclidean_relabelState]
      have he : 2*η+2*(2*W/η)/(2^a : ℕ)=2*η+4*W/(η*(2^a : ℕ)) := by ring
      rw [he] at hb
      exact hb)
  refine ⟨r,hr,D,hD,hcalls.trans ?_,herr⟩
  rw [phaseSourceCompile_calls,(phase_reflection_actual_queries_and_macros (I:=SourceGeometry n q m H) (2^a) 1 hM).2.1]
  omega

theorem sourceOnePass_resources (W ε : ℝ) (hε : 0<ε) (hε1 : ε≤1/3) (hW : ε/8≤W) :
    let K := max 1 (Nat.ceil (W/ε^2))
    let a := Nat.clog 2 (2048*K)
    let M := 2^a
    2≤M ∧ 2048*K≤M ∧ M≤4096*K ∧
      4*(M-1)≤65536*Nat.ceil (W*Real.log (2/ε)/ε^2) := by
  let K := max 1 (Nat.ceil (W/ε^2))
  let N := Nat.ceil (W*Real.log (2/ε)/ε^2)
  have hWp : 0<W := lt_of_lt_of_le (by positivity : (0 : ℝ)<ε/8) hW
  have hlog : (1/2 : ℝ)≤Real.log (2/ε) := by
    have he : ε≤1 := by linarith
    have hh := Real.log_le_log (by norm_num : (0 : ℝ)<2)
      ((le_div_iff₀ hε).mpr (by linarith : (2 : ℝ)*ε≤2))
    linarith [Real.log_two_gt_d9]
  have hNp : 1≤N := (Nat.one_le_ceil_iff).mpr (by positivity)
  have hN : W*Real.log (2/ε)/ε^2≤(N : ℝ) := Nat.le_ceil _
  have hceil : Nat.ceil (W/ε^2)≤2*N := by
    apply Nat.ceil_le.mpr
    push_cast
    have he : W*Real.log (2/ε)/ε^2=(W/ε^2)*Real.log (2/ε) := by ring
    rw [he] at hN
    have hx : 0≤W/ε^2 := by positivity
    nlinarith
  have hK : K≤2*N := max_le (by omega) hceil
  have hk : 1≤128*K := by dsimp [K]; omega
  obtain ⟨hl,hu,_⟩ := sourcePhaseClock_bounds (128*K) hk
  have hm : 2≤2^(Nat.clog 2 (2048*K)) := by
    have he : 16*(128*K)=2048*K := by omega
    rw [he] at hl
    have hKo : 1≤K := le_max_left _ _
    omega
  have he1 : 16*(128*K)=2048*K := by omega
  have he2 : 32*(128*K)=4096*K := by omega
  rw [he1] at hl hu
  rw [he2] at hu
  refine ⟨hm,hl,hu,?_⟩
  have hn := Nat.mul_le_mul_left 16384 hK
  change 4*(2^(Nat.clog 2 (2048*K))-1)≤65536*N
  omega

theorem sourceAlphabet_degenerate_gram {X : Type} [Fintype X] [DecidableEq X]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (A : Matrix X X ℂ)
    (W : ℝ) (_hW : 0≤W)
    (hb : sourceRectValue A (sourceAlphabetDelta input)≤ENNReal.ofReal W)
    (hd : W=0 ∨ n=0 ∨ q=0) : A=0 := by
  rcases hd with h0|h0|h0
  · apply (sourceRectValue_zero_iff A (sourceAlphabetDelta input)).mp
    apply le_antisymm
    simpa only [h0,ENNReal.ofReal_zero] using! hb
    exact bot_le
  · have hs := (sourceRectValue_finite_iff A (sourceAlphabetDelta input)).mp
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
    ext x y
    by_contra ha
    obtain ⟨j,_⟩ := hs x y ha
    subst n
    exact Fin.elim0 j
  · have hs := (sourceRectValue_finite_iff A (sourceAlphabetDelta input)).mp
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
    ext x y
    by_contra ha
    obtain ⟨j,hj⟩ := hs x y ha
    have he : input x j=input y j := by
      apply Fin.ext
      have hx := (input x j).isLt
      have hy := (input y j).isLt
      omega
    exact hj (by simp only [sourceAlphabetDelta,if_pos he])

theorem sourceOnePass_error_bound (W ε : ℝ) (hε : 0<ε) (_hW : ε/8≤W)
    (M : ℕ) (hM : 0<M) (hsize : 2048*(W/ε^2)≤(M : ℝ)) :
    2*(ε/64)+4*W/((ε/64)*(M : ℝ))≤ε/4 := by
  have hm : (0 : ℝ)<M := by exact_mod_cast hM
  have he2 : 0<ε^2 := sq_pos_of_pos hε
  rw [← mul_div_assoc] at hsize
  have hh := (div_le_iff₀ he2).mp hsize
  have hs : 4*W/((ε/64)*(M : ℝ))≤ε/8 := by
    apply (div_le_iff₀ (mul_pos (by positivity) hm)).mpr
    nlinarith only [hh]
  linarith

theorem realBudgetConversionAlgorithm : RealBudgetConversionAlgorithm := by
  refine ⟨65536,by norm_num,?_⟩
  intro X H _ _ _ _ _ n q input ρ σ W ε hn hW hb hε hε1
  have he1 : ε≤1 := by linarith
  let A := gramStateMatrix ρ-gramStateMatrix σ
  have free (δ : ℝ) (hδ : 0≤δ) (hval : sourceUnfiltered A≤ENNReal.ofReal δ)
      (hsmall : 2*δ≤ε) (hstrict : ε≤W → δ=0) :
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C≤65536*Nat.ceil (W*Real.log (2/ε)/ε^2) ∧
        ((W=0 ∨ n=0 ∨ q=0)→sourceWordCalls C=0) ∧
        (∀ x,(∑ p,star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re≥Real.sqrt (1-ε)) ∧
        (ε≤W→∀ x,‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖<4*ε) := by
    obtain ⟨r,hr,G,hG,herr⟩ := source_free_word_native n q ρ σ δ hn hδ hval
    let C : SourceWord (SourceSpace n q H r) := [.inl G]
    have hC : sourceWordLegal C := by
      intro s hs
      simp only [C,List.mem_singleton] at hs
      subst s
      exact hG
    have hcalls : sourceWordCalls C=0 := rfl
    have hmat (x : X) : sourceWordMatrix (sourceAlphabetOracle input x) C=G := by
      simp [C,sourceWordMatrix]
    refine ⟨r,hr,C,hC,by rw [hcalls]; exact Nat.zero_le _,by intro _; exact hcalls,?_,?_⟩
    · intro x
      rw [hmat]
      have hd : ‖toEuclidean_fromVec (G *ᵥ sourceClean n q r hr false (ρ x)-
          sourceClean n q r hr true (σ x))‖^2≤ε := by
        have hs := Real.sq_sqrt (show 0≤2*δ by positivity)
        have hx := herr x
        nlinarith [norm_nonneg (toEuclidean_fromVec (G *ᵥ sourceClean n q r hr false (ρ x)-
          sourceClean n q r hr true (σ x)))]
      exact source_overlap_of_distance _ _
        (normalized_applyGate hG (sourceClean_normalized n q r hr false (ρ x) (hn x).1))
        (sourceClean_normalized n q r hr true (σ x) (hn x).2) ε hε.le he1 hd
    · intro hεW x
      rw [hmat]
      have hx := herr x
      rw [hstrict hεW] at hx
      simp only [mul_zero,Real.sqrt_zero] at hx
      linarith
  by_cases hd : W=0 ∨ n=0 ∨ q=0
  · have hA : A=0 := sourceAlphabet_degenerate_gram input A W hW hb hd
    have hzero : sourceUnfiltered A≤ENNReal.ofReal 0 := by
      rw [hA]
      exact le_of_eq (by simp only [sourceUnfiltered,sourceRectValue_zero,ENNReal.ofReal_zero])
    exact free 0 le_rfl hzero (by linarith) (by intro _; rfl)
  by_cases hsmall : W≤ε/8
  · exact free (2*W) (by positivity) (sourceAlphabet_unfiltered_budget input A W hW hb)
      (by linarith) (by intro he; exfalso; linarith)
  have hWp : 0<W := lt_of_lt_of_le (by positivity : (0:ℝ)<ε/8) (le_of_lt (lt_of_not_ge hsmall))
  have hq : 0<q := by
    have hh : q≠0 := by intro h; exact hd (Or.inr (Or.inr h))
    omega
  obtain ⟨m,u,v,hEq,hu,hv⟩ :=
      (sourceRectValue_budget_boundary A (sourceAlphabetDelta input) W hW).mp hb
  let K := max 1 (Nat.ceil (W/ε^2))
  let a := Nat.clog 2 (2048*K)
  obtain ⟨hM,hMl,_,hqueries⟩ := sourceOnePass_resources W ε hε hε1 (le_of_not_ge hsmall)
  obtain ⟨r,hr,C,hC,hcalls,herr⟩ := source_onepass_native_algorithm input ρ σ u v W (ε/64)
    hn hq hWp (by positivity) (by linarith) a hM hEq (fun x => ⟨hu x,hv x⟩)
  have hsize : 2048*(W/ε^2)≤(2^a : ℕ) := by
    have hkceil : Nat.ceil (W/ε^(2 : ℕ))≤K := le_max_right _ _
    have hk : W/ε^2≤(K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hkceil)
    have hm : (2048:ℝ)*(K : ℝ)≤(2^a : ℕ) := by exact_mod_cast hMl
    exact (mul_le_mul_of_nonneg_left hk (by norm_num)).trans hm
  have herror (x : X) : ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
      sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖≤ε/4 :=
    (herr x).trans (sourceOnePass_error_bound W ε hε (le_of_not_ge hsmall) (2^a) (by have hh : 2≤2^a := hM; omega) hsize)
  refine ⟨r,hr,C,hC,hcalls.trans hqueries,by intro h; exact (hd h).elim,?_,?_⟩
  · intro x
    have hψ := normalized_applyGate (sourceWordMatrix_unitary _ (sourceAlphabetOracle_unitary input x) C hC)
      (sourceClean_normalized n q r hr false (ρ x) (hn x).1)
    have hd2 : ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖^2≤ε := by
      have hh := herror x
      nlinarith [norm_nonneg (toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x)))]
    exact source_overlap_of_distance _ _ hψ (sourceClean_normalized n q r hr true (σ x) (hn x).2)
      ε hε.le he1 hd2
  · intro _ x
    exact (herror x).trans_lt (by linarith)

end Qatlib.Concepts.QueryComplexity.StateConversion
