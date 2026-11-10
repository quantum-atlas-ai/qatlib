/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.DualNormSDPAndClosureStat
import Qatlib.Concepts.GramQueryCore.FilteredNorm.FilteredNormCompositionAndProductsQuan
import Mathlib.Analysis.Matrix.Order
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators ENNReal ComplexOrder Kronecker

def sourceSDPImage {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (Z : Fin n → Matrix R S ℂ) (Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) : Matrix R S ℂ :=
  fun r s => ∑ j, Z j r s*Y j (.inl r) (.inr s)

def sourceDualPairing {R S : Type} [Fintype R] [Fintype S]
    (A B : Matrix R S ℂ) : ℝ := (∑ r, ∑ s, star (A r s)*B r s).re

theorem sourceRectCert_iff_psd_family {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (w : ℝ) :
    sourceRectCert n B Z w ↔ ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
      (∀ j, (Y j).PosSemidef) ∧ sourceSDPImage Z Y=B ∧
      ∀ i, ∑ j, (Y j i i).re ≤ w := by
  constructor
  · rintro ⟨m,u,v,heq,hu,hv⟩
    let C (j : Fin n) : Matrix (Fin m) (R ⊕ S) ℂ :=
        fun k i => Sum.elim (fun r => u r j k) (fun s => v s j k) i
    refine ⟨fun j => (C j)ᴴ*C j,fun j => Matrix.posSemidef_conjTranspose_mul_self (C j),?_,?_⟩
    · ext r s
      simpa only [sourceSDPImage,Matrix.mul_apply,Matrix.conjTranspose_apply,C,Sum.elim_inl,Sum.elim_inr] using! (heq r s).symm
    · intro i
      cases i with
      | inl r =>
        simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,C,Sum.elim_inl,
          Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.re_sum,Complex.ofReal_re,
          Complex.normSq_eq_norm_sq,← norm_toEuclidean_fromVec_sq] using! hu r
      | inr s =>
        simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,C,Sum.elim_inr,
          Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.re_sum,Complex.ofReal_re,
          Complex.normSq_eq_norm_sq,← norm_toEuclidean_fromVec_sq] using! hv s
  · rintro ⟨Y,hY,heq,hdiag⟩
    choose C hC using fun j => gram_positive_matrix_actual_factorization (R ⊕ S) (Y j) (hY j)
    apply sourceRectCert_of_finiteWitness
      (fun r j k => C j k (.inl r)) (fun s j k => C j k (.inr s))
    · intro r s
      rw [← heq]
      unfold sourceSDPImage
      apply Finset.sum_congr rfl
      intro j _
      rw [← hC j]
      rfl
    · intro r
      have hd := hdiag (.inl r)
      simp_rw [← hC] at hd
      simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,← Complex.normSq_eq_conj_mul_self,
        Complex.re_sum,Complex.ofReal_re] using! hd
    · intro s
      have hd := hdiag (.inr s)
      simp_rw [← hC] at hd
      simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,← Complex.normSq_eq_conj_mul_self,
        Complex.re_sum,Complex.ofReal_re] using! hd

theorem sourceUnitBall_iff_psd_family {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue B Z ≤ 1 ↔ ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
      (∀ j, (Y j).PosSemidef) ∧ sourceSDPImage Z Y=B ∧
      ∀ i, ∑ j, (Y j i i).re ≤ 1 := by
  rw [← ENNReal.ofReal_one,sourceRectValue_budget_boundary B Z 1 zero_le_one]
  exact sourceRectCert_iff_psd_family B Z 1

theorem sourceDualNorm_filterUnion_le {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n m : ℕ} (A : Matrix R S ℂ) (Y : Fin m → Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceDualNorm A Z ≤ sourceDualNorm A (sourceFilterUnion Y Z) := by
  unfold sourceDualNorm
  apply iSup_le
  intro B
  exact le_iSup_of_le ⟨B.val,(sourceRectValue_filterUnion_le B.val Y Z).trans B.property⟩ le_rfl

theorem sourceDualNorm_convexFilter {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (p : Fin n → ℂ)
    (hp : (∑ j, ‖p j‖) ≤ 1) :
    sourceDualNorm A (sourceFilterUnion Z (fun _ : Fin 1 => ∑ j, p j • Z j))=sourceDualNorm A Z := by
  unfold sourceDualNorm
  apply le_antisymm
  · apply iSup_le
    intro B
    have hf : sourceRectValue B.val Z ≤ 1 := by
      rw [← sourceRectValue_convexFilter B.val Z p hp]
      exact B.property
    exact le_iSup_of_le ⟨B.val,hf⟩ le_rfl
  · apply iSup_le
    intro B
    have hf : sourceRectValue B.val (sourceFilterUnion Z (fun _ : Fin 1 => ∑ j, p j • Z j)) ≤ 1 := by
      rw [sourceRectValue_convexFilter B.val Z p hp]
      exact B.property
    exact le_iSup_of_le ⟨B.val,hf⟩ le_rfl

theorem sourceHermitianLift_pairing {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (C : Matrix R S ℂ) (Y : Matrix (R ⊕ S) (R ⊕ S) ℂ) (hY : Y.IsHermitian) :
    (Matrix.trace (Yᴴ*sourceHermitianLift C)).re =
      2*(∑ r, ∑ s, star (C r s)*Y (.inl r) (.inr s)).re := by
  have hy (r : R) (s : S) : star (Y (.inr s) (.inl r))=Y (.inl r) (.inr s) := by
    simpa only [Matrix.conjTranspose_apply] using! congrFun (congrFun hY (.inl r)) (.inr s)
  have ht : Matrix.trace (Yᴴ*sourceHermitianLift C)=
      (∑ r, ∑ s, star (C r s)*Y (.inl r) (.inr s))+
        star (∑ r, ∑ s, star (C r s)*Y (.inl r) (.inr s)) := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_sum_type,sourceHermitianLift,mul_zero,Finset.sum_const_zero,zero_add,add_zero,hy]
    rw [Finset.sum_comm (f := fun s r => star (Y (.inl r) (.inr s))*C r s)]
    simp only [star_sum,star_mul,star_star]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
  rw [ht]
  simp only [Complex.add_re,Complex.star_def,Complex.conj_re]
  ring

theorem sourceSDPImage_pairing {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ)
    (Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) (hY : ∀ j, (Y j).IsHermitian) :
    (∑ j, Matrix.trace ((Y j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re =
      2*sourceDualPairing A (sourceSDPImage Z Y) := by
  simp_rw [Complex.re_sum,sourceHermitianLift_pairing _ _ (hY _)]
  simp only [sourceDualPairing,sourceSDPImage,Matrix.hadamard_apply,sourceConjugate,
    star_mul,star_star,Complex.re_sum,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

def sourceSDPBudget {K : Type} [Fintype K] {n : ℕ} :
    Set (Fin n → Matrix K K ℂ) :=
  {Y | (∀ j, (Y j).PosSemidef) ∧ ∀ i, ∑ j, (Y j i i).re ≤ 1}

section CompactPrimal
open scoped Matrix.Norms.Elementwise

theorem sourcePSD_closed {K : Type} [Fintype K] [DecidableEq K] :
    IsClosed {B : Matrix K K ℂ | B.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · apply isClosed_eq <;> fun_prop
  · change IsClosed {B : Matrix K K ℂ | ∀ v, 0 ≤ star v ⬝ᵥ (B*ᵥv)}
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply]
    fun_prop

theorem sourceSDPBudget_compact {K : Type} [Fintype K] [DecidableEq K] (n : ℕ) :
    IsCompact (sourceSDPBudget (K := K) (n := n)) := by
  have hc : IsClosed (sourceSDPBudget (K := K) (n := n)) := by
    apply IsClosed.inter
    · change IsClosed {Y : Fin n → Matrix K K ℂ | ∀ j, (Y j).PosSemidef}
      rw [Set.setOf_forall]
      apply isClosed_iInter
      intro j
      exact IsClosed.preimage (f := fun Y : Fin n → Matrix K K ℂ => Y j)
        (continuous_apply j) sourcePSD_closed
    · change IsClosed {Y : Fin n → Matrix K K ℂ | ∀ i, ∑ j, (Y j i i).re ≤ 1}
      rw [Set.setOf_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_le _ continuous_const
      fun_prop
  apply (isCompact_closedBall (0 : Fin n → Matrix K K ℂ) 1).of_isClosed_subset hc
  intro Y hY
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro s
  apply gamma2_psd_entry_norm_le (Y j) (hY.1 j) 1 zero_le_one
  intro i
  exact (Finset.single_le_sum
    (fun j _ => (Complex.nonneg_iff.mp (hY.1 j).diag_nonneg).1) (Finset.mem_univ j)).trans (hY.2 i)

theorem sourceDualNorm_psd_attained {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
      Y ∈ sourceSDPBudget ∧ sourceDualNorm A Z=ENNReal.ofReal (sourceDualPairing A (sourceSDPImage Z Y)) ∧
      ∀ Y' ∈ sourceSDPBudget, sourceDualPairing A (sourceSDPImage Z Y') ≤ sourceDualPairing A (sourceSDPImage Z Y) := by
  have h0 : (0 : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) ∈ sourceSDPBudget := by
    exact ⟨fun _ => Matrix.PosSemidef.zero,by simp⟩
  have hc : Continuous (fun Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ => sourceDualPairing A (sourceSDPImage Z Y)) := by
    dsimp [sourceDualPairing,sourceSDPImage]
    fun_prop
  obtain ⟨Y,hY,hm⟩ := (sourceSDPBudget_compact (K := R ⊕ S) n).exists_isMaxOn ⟨0,h0⟩ hc.continuousOn
  refine ⟨Y,hY,?_,fun Y' hY' => hm hY'⟩
  unfold sourceDualNorm
  apply le_antisymm
  · apply iSup_le
    intro B
    obtain ⟨Y',hY',hi,hd⟩ := (sourceUnitBall_iff_psd_family B.val Z).mp B.property
    exact ENNReal.ofReal_le_ofReal (by
      change sourceDualPairing A B.val ≤ _
      rw [← hi]
      exact hm ⟨hY',hd⟩)
  · have hf : sourceRectValue (sourceSDPImage Z Y) Z ≤ 1 :=
      (sourceUnitBall_iff_psd_family _ Z).mpr ⟨Y,hY.1,rfl,hY.2⟩
    exact le_iSup (fun B : {B : Matrix R S ℂ // sourceRectValue B Z ≤ 1} =>
      ENNReal.ofReal (sourceDualPairing A B.val)) ⟨sourceSDPImage Z Y,hf⟩

theorem sourcePsdFamily_norm_bound {K : Type} [Fintype K] [DecidableEq K] {n : ℕ}
    (Y : Fin n → Matrix K K ℂ) (hY : ∀ j, (Y j).PosSemidef)
    (d : K → ℝ) (hd : ∀ i, ∑ j, (Y j i i).re ≤ d i)
    (R : ℝ) (hR : 0 ≤ R) (hbound : ‖d‖ ≤ R) : ‖Y‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro r
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro s
  apply gamma2_psd_entry_norm_le (Y j) (hY j) R hR
  intro i
  exact (Finset.single_le_sum (fun j _ => (Complex.nonneg_iff.mp (hY j).diag_nonneg).1)
    (Finset.mem_univ j)).trans ((hd i).trans ((le_abs_self (d i)).trans ((norm_le_pi_norm d i).trans hbound)))

def sourceSDPHypograph {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : Set (((R ⊕ S) → ℝ) × ℝ) :=
  {c | ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
    (∀ j, (Y j).PosSemidef) ∧ (∀ i, ∑ j, (Y j i i).re ≤ c.1 i) ∧
    c.2 ≤ sourceDualPairing A (sourceSDPImage Z Y)}

open Filter Topology in

 theorem sourceSDPHypograph_closed {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    IsClosed (sourceSDPHypograph A Z) := by
  apply IsSeqClosed.isClosed
  intro c s hs ht
  choose Y hY hd hp using hs
  have hdt : Tendsto (fun k => (c k).1) atTop (𝓝 s.1) := continuous_fst.tendsto s |>.comp ht
  obtain ⟨radius,hR,hbound⟩ := (Metric.isBounded_range_of_tendsto _ hdt).exists_pos_norm_le
  have hb (k : ℕ) : ‖Y k‖ ≤ radius := sourcePsdFamily_norm_bound
    (Y k) (hY k) ((c k).1) (hd k) radius hR.le (hbound _ ⟨k,rfl⟩)
  obtain ⟨W,hW,φ,hφ,hwt⟩ := (isCompact_closedBall (0 : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) radius).tendsto_subseq
    (fun k => by simpa only [Metric.mem_closedBall,dist_zero_right] using! hb k)
  refine ⟨W,?_,?_,?_⟩
  · intro j
    exact sourcePSD_closed.mem_of_tendsto
      ((continuous_apply j).tendsto W |>.comp hwt) (Filter.Eventually.of_forall fun k => hY (φ k) j)
  · intro i
    have hcont : Continuous (fun Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ => ∑ j, (Y j i i).re) := by
      fun_prop
    have hl := hcont.tendsto W |>.comp hwt
    have hr := ((continuous_apply i).tendsto s.1).comp (hdt.comp hφ.tendsto_atTop)
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun k => hd (φ k) i)
  · have hcont : Continuous (fun Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ => sourceDualPairing A (sourceSDPImage Z Y)) := by
      dsimp [sourceDualPairing,sourceSDPImage]
      fun_prop
    have hr := hcont.tendsto W |>.comp hwt
    have hl := (continuous_snd.tendsto s |>.comp ht).comp hφ.tendsto_atTop
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun k => hp (φ k))

theorem sourceSDPImage_add {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (Z : Fin n → Matrix R S ℂ) (Y W : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) :
    sourceSDPImage Z (Y+W)=sourceSDPImage Z Y+sourceSDPImage Z W := by
  ext r s
  simp [sourceSDPImage,Finset.sum_add_distrib,mul_add]

theorem sourceSDPImage_smul {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (Z : Fin n → Matrix R S ℂ) (Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) (c : ℝ) :
    sourceSDPImage Z (c • Y)=c • sourceSDPImage Z Y := by
  ext r s
  simp only [sourceSDPImage,Pi.smul_apply,Matrix.smul_apply,Complex.real_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceDualPairing_add {R S : Type} [Fintype R] [Fintype S]
    (A B C : Matrix R S ℂ) : sourceDualPairing A (B+C)=sourceDualPairing A B+sourceDualPairing A C := by
  simp [sourceDualPairing,mul_add,Finset.sum_add_distrib]

theorem sourceDualPairing_smul {R S : Type} [Fintype R] [Fintype S]
    (A B : Matrix R S ℂ) (c : ℝ) : sourceDualPairing A (c • B)=c*sourceDualPairing A B := by
  simp only [sourceDualPairing,Matrix.smul_apply,Complex.real_smul,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_im]
  ring

def sourceSDPHypographCone {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    PointedCone ℝ (((R ⊕ S) → ℝ) × ℝ) where
  carrier := sourceSDPHypograph A Z
  zero_mem' := by
    refine ⟨0,fun _ => Matrix.PosSemidef.zero,by simp,?_⟩
    simp [sourceDualPairing,sourceSDPImage]
  add_mem' := by
    rintro c d ⟨Y,hY,hd,hp⟩ ⟨W,hW,hd',hp'⟩
    refine ⟨Y+W,fun j => (hY j).add (hW j),?_,?_⟩
    · intro i
      simpa only [Pi.add_apply,Matrix.add_apply,Complex.add_re,Finset.sum_add_distrib,Prod.fst_add] using! add_le_add (hd i) (hd' i)
    · simpa only [sourceSDPImage_add,sourceDualPairing_add,Prod.snd_add] using! add_le_add hp hp'
  smul_mem' := by
    rintro a c ⟨Y,hY,hd,hp⟩
    refine ⟨(a.val : ℝ) • Y,fun j => (hY j).smul a.property,?_,?_⟩
    · intro i
      change (∑ j, ((a.val : ℝ) • Y j i i).re) ≤ a.val*c.1 i
      simpa only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,← Finset.mul_sum] using! mul_le_mul_of_nonneg_left (hd i) a.property
    · simpa only [sourceSDPImage_smul,sourceDualPairing_smul,Prod.smul_snd,smul_eq_mul] using!
        mul_le_mul_of_nonneg_left hp a.property

theorem sourceSDPHypograph_separator {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (c : ((R ⊕ S) → ℝ) × ℝ)
    (hc : c ∉ sourceSDPHypograph A Z) :
    ∃ l : StrongDual ℝ (((R ⊕ S) → ℝ) × ℝ),
      (∀ d ∈ sourceSDPHypograph A Z, 0 ≤ l d) ∧ l c < 0 := by
  letI : LocallyConvexSpace ℝ (((R ⊕ S) → ℝ) × ℝ) := NormedSpace.toLocallyConvexSpace' ℝ
  let K : ProperCone ℝ (((R ⊕ S) → ℝ) × ℝ) :=
    ⟨sourceSDPHypographCone A Z,sourceSDPHypograph_closed A Z⟩
  exact K.hyperplane_separation_point hc

theorem sourceBudget_functional_coordinates {K : Type} [Fintype K] [DecidableEq K]
    (l : StrongDual ℝ ((K → ℝ) × ℝ)) : ∃ α : K → ℝ, ∃ c : ℝ,
      ∀ d : K → ℝ, ∀ t : ℝ, l (d,t)=(∑ i, α i*d i)+c*t := by
  let α : K → ℝ := fun i => l (Pi.single i 1,0)
  let c := l (0,1)
  refine ⟨α,c,?_⟩
  intro d t
  have hd : l (d,0)=∑ i, α i*d i := by
    have he : (d,(0 : ℝ))=(∑ i : K, d i • (Pi.single i 1,(0 : ℝ))) := by
      apply Prod.ext
      · simp only [Prod.fst_sum,Prod.smul_fst]
        ext j
        simp [Pi.single_apply]
      · simp only [Prod.snd_sum,Prod.smul_snd,smul_zero,Finset.sum_const_zero]
    rw [he,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul,α]
    ring
  have ht : l (0,t)=c*t := by
    rw [show (0,t)=t • ((0 : K → ℝ),1) by simp,map_smul]
    simp only [c,smul_eq_mul]
    ring
  rw [show (d,t)=(d,0)+(0,t) by simp,map_add,hd,ht]

theorem sourceHermitianLift_isHermitian {R S : Type} (C : Matrix R S ℂ) :
    (sourceHermitianLift C).IsHermitian := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.conjTranspose_apply,sourceHermitianLift]

theorem sourceTrace_rankOne {K : Type} [Fintype K] (H : Matrix K K ℂ) (v : K → ℂ) :
    Matrix.trace ((Matrix.vecMulVec v (star v))ᴴ*H)=star v ⬝ᵥ (H*ᵥv) := by
  rw [(Matrix.posSemidef_vecMulVec_self_star v).isHermitian.eq,
    Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

theorem sourceDualNorm_minApprox {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (w : ℝ)
    (hw : sourceDualNorm A Z < ENNReal.ofReal w) :
    ∃ α : (R ⊕ S) → ℝ, (∀ i, 0 ≤ α i) ∧
      (∀ j, (Matrix.diagonal (fun i => (α i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) ∧ (∑ i, α i)<2*w := by
  have hout : ((fun _ : R ⊕ S => (1 : ℝ)),w) ∉ sourceSDPHypograph A Z := by
    rintro ⟨Y,hY,hd,hp⟩
    have hf : sourceRectValue (sourceSDPImage Z Y) Z ≤ 1 :=
      (sourceUnitBall_iff_psd_family _ Z).mpr ⟨Y,hY,rfl,hd⟩
    have hb : ENNReal.ofReal (sourceDualPairing A (sourceSDPImage Z Y)) ≤ sourceDualNorm A Z :=
      le_iSup (fun B : {B : Matrix R S ℂ // sourceRectValue B Z ≤ 1} =>
        ENNReal.ofReal (sourceDualPairing A B.val)) ⟨sourceSDPImage Z Y,hf⟩
    exact (not_le_of_gt hw) ((ENNReal.ofReal_le_ofReal hp).trans hb)
  obtain ⟨l,hl,hlt⟩ := sourceSDPHypograph_separator A Z _ hout
  obtain ⟨a,c,hrepr⟩ := sourceBudget_functional_coordinates l
  have ha (i : R ⊕ S) : 0 ≤ a i := by
    have hm : (Pi.single i (1 : ℝ),0) ∈ sourceSDPHypograph A Z := by
      refine ⟨0,fun _ => Matrix.PosSemidef.zero,?_,?_⟩
      · intro k
        simp only [Pi.zero_apply,Matrix.zero_apply,Complex.zero_re,Finset.sum_const_zero,Pi.single_apply]
        split_ifs <;> norm_num
      · simp [sourceDualPairing,sourceSDPImage]
    have hh := hl _ hm
    rw [hrepr] at hh
    simpa [Pi.single_apply] using! hh
  have hc : c ≤ 0 := by
    have hm : ((0 : (R ⊕ S) → ℝ),(-1 : ℝ)) ∈ sourceSDPHypograph A Z := by
      refine ⟨0,fun _ => Matrix.PosSemidef.zero,by simp,?_⟩
      simp [sourceDualPairing,sourceSDPImage]
    have hh := hl _ hm
    rw [hrepr] at hh
    simpa using! hh
  rw [hrepr] at hlt
  simp only [mul_one] at hlt
  have hcneg : c<0 := by
    apply lt_of_le_of_ne hc
    intro he
    have hs : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
    rw [he,zero_mul,add_zero] at hlt
    exact (not_lt_of_ge hs) hlt
  let scale := -c
  have hscale : 0<scale := neg_pos.mpr hcneg
  let α : (R ⊕ S) → ℝ := fun i => 2*a i/scale
  refine ⟨α,fun i => div_nonneg (mul_nonneg (by norm_num) (ha i)) hscale.le,?_,?_⟩
  · intro j
    have hherm : (Matrix.diagonal (fun i => (α i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))).IsHermitian :=
      (Matrix.isHermitian_diagonal_iff.mpr (by intro i; simp [IsSelfAdjoint])).sub (sourceHermitianLift_isHermitian _)
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
    intro v
    let V := Matrix.vecMulVec v (star v)
    have hV : V.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    have hm : ((fun i => Complex.normSq (v i)),sourceDualPairing A (sourceSDPImage Z (Pi.single j V))) ∈ sourceSDPHypograph A Z := by
      refine ⟨Pi.single j V,?_,?_,le_rfl⟩
      · intro k
        by_cases he : k=j
        · subst k; simpa using! hV
        · rw [Pi.single_eq_of_ne he]; exact Matrix.PosSemidef.zero
      · intro i
        rw [Finset.sum_eq_single j]
        · simp [V,Matrix.vecMulVec_apply,Complex.normSq_apply]
        · intro k _ hk
          simp [hk]
        · simp
    have hh := hl _ hm
    rw [hrepr] at hh
    have htrace : (star v ⬝ᵥ (sourceHermitianLift (A ⊙ sourceConjugate (Z j))*ᵥv)).re=
        2*sourceDualPairing A (sourceSDPImage Z (Pi.single j V)) := by
      have hp := sourceSDPImage_pairing A Z (Pi.single j V) (fun k => by
        by_cases he : k=j
        · subst k; simpa using! hV.isHermitian
        · rw [Pi.single_eq_of_ne he]; exact Matrix.isHermitian_zero)
      rw [Finset.sum_eq_single j] at hp
      · simpa only [Pi.single_eq_same,V,sourceTrace_rankOne] using! hp
      · intro k _ hk; simp [hk]
      · simp
    have hquad : (star v ⬝ᵥ ((Matrix.diagonal (fun i => (α i : ℂ))-
          sourceHermitianLift (A ⊙ sourceConjugate (Z j)))*ᵥv)).re=
        (2/scale)*((∑ i, a i*Complex.normSq (v i))+c*sourceDualPairing A (sourceSDPImage Z (Pi.single j V))) := by
      rw [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re,gamma2_weighted_diagonal_quad,htrace]
      simp only [α,div_eq_mul_inv]
      rw [show (∑ i, 2*a i*scale⁻¹*Complex.normSq (v i))=(2*scale⁻¹)*(∑ i, a i*Complex.normSq (v i)) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      dsimp only [scale]
      field_simp [hcneg.ne]
      ring
    apply Complex.nonneg_iff.mpr
    exact ⟨by rw [hquad]; exact mul_nonneg (div_nonneg (by norm_num) hscale.le) hh,
      (hherm.im_star_dotProduct_mulVec_self v).symm⟩
  · simp only [α,div_eq_mul_inv]
    rw [show (∑ i, 2*a i*scale⁻¹)=(2/scale)*(∑ i,a i) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
    apply (mul_lt_mul_of_pos_left (by linarith [hlt] : (∑ i,a i)<(-c)*w) (div_pos (by norm_num : (0 : ℝ)<2) hscale)).trans_le
    rw [← mul_assoc]
    dsimp only [scale]
    rw [div_mul_cancel₀ _ (neg_ne_zero.mpr hcneg.ne)]

theorem sourcePSD_trace_mul_nonneg {K : Type} [Fintype K] [DecidableEq K]
    (Y T : Matrix K K ℂ) (hY : Y.PosSemidef) (hT : T.PosSemidef) :
    0 ≤ (Matrix.trace (Yᴴ*T)).re := by
  obtain ⟨C,hC⟩ := gram_positive_matrix_actual_factorization K Y hY
  have hp := (hT.mul_mul_conjTranspose_same C).trace_nonneg
  rw [Matrix.trace_mul_cycle] at hp
  rw [hY.isHermitian.eq,← hC]
  exact (Complex.nonneg_iff.mp hp).1

theorem sourceDiagonal_trace_pairing {K : Type} [Fintype K] [DecidableEq K]
    (Y : Matrix K K ℂ) (α : K → ℝ) :
    (Matrix.trace (Yᴴ*Matrix.diagonal (fun i => (α i : ℂ)))).re=∑ i, α i*(Y i i).re := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Matrix.conjTranspose_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.star_def,Complex.conj_re]
  ring

theorem sourceDualNorm_le_diagonal {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (α : (R ⊕ S) → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hPSD : ∀ j, (Matrix.diagonal (fun i => (α i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) :
    sourceDualNorm A Z ≤ ENNReal.ofReal ((∑ i, α i)/2) := by
  unfold sourceDualNorm
  apply iSup_le
  intro B
  obtain ⟨Y,hY,hi,hd⟩ := (sourceUnitBall_iff_psd_family B.val Z).mp B.property
  have hp (j : Fin n) : (Matrix.trace ((Y j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re ≤
      ∑ i, α i*(Y j i i).re := by
    have hh := sourcePSD_trace_mul_nonneg (Y j) _ (hY j) (hPSD j)
    rw [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,sourceDiagonal_trace_pairing] at hh
    linarith
  have hh : (∑ j, (Matrix.trace ((Y j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j)))).re) ≤
      ∑ j, ∑ i, α i*(Y j i i).re := Finset.sum_le_sum fun j _ => hp j
  rw [Finset.sum_comm] at hh
  have hb : (∑ i, ∑ j, α i*(Y j i i).re) ≤ ∑ i, α i := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hd i) (hα i)
  have hm := hh.trans hb
  rw [← Complex.re_sum,sourceSDPImage_pairing A Z Y (fun j => (hY j).isHermitian),hi] at hm
  apply ENNReal.ofReal_le_ofReal
  change sourceDualPairing A B.val ≤ _
  linarith

theorem sourceDualNorm_finite {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) : sourceDualNorm A Z ≠ ⊤ := by
  obtain ⟨Y,_,hval,_⟩ := sourceDualNorm_psd_attained A Z
  rw [hval]
  exact ENNReal.ofReal_ne_top

open Filter Topology in

 theorem sourceDualNorm_diagonal_attained {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    ∃ α : (R ⊕ S) → ℝ, (∀ i, 0 ≤ α i) ∧
      (∀ j, (Matrix.diagonal (fun i => (α i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) ∧
      sourceDualNorm A Z=ENNReal.ofReal ((∑ i, α i)/2) := by
  let t := (sourceDualNorm A Z).toReal
  have hval : ENNReal.ofReal t=sourceDualNorm A Z :=
      ENNReal.ofReal_toReal (sourceDualNorm_finite A Z)
  have htp : 0 ≤ t := ENNReal.toReal_nonneg
  let ε : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0<ε k := by dsimp [ε]; positivity
  choose α hα hPSD hsum using fun k => sourceDualNorm_minApprox A Z (t+ε k)
    (by rw [← hval]; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg htp |>.mpr (lt_add_of_pos_right t (hε k)))
  have hb (k : ℕ) : ‖α k‖ ≤ 2*(t+1) := by
    have hε1 : ε k ≤ 1 := by
      dsimp [ε]
      apply (div_le_one (by positivity)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg k)
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*(t+1))).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hα k i)]
    exact ((Finset.single_le_sum (fun i _ => hα k i) (Finset.mem_univ i)).trans (hsum k).le).trans
        (by linarith)
  obtain ⟨a,ha,φ,hφ,hat⟩ := (isCompact_closedBall (0 : (R ⊕ S) → ℝ) (2*(t+1))).tendsto_subseq
    (fun k => by simpa only [Metric.mem_closedBall,dist_zero_right] using! hb k)
  have hap (i : R ⊕ S) : 0 ≤ a i := le_of_tendsto_of_tendsto tendsto_const_nhds ((continuous_apply i).tendsto a |>.comp hat)
    (Filter.Eventually.of_forall fun k => hα (φ k) i)
  have hpsd (j : Fin n) : (Matrix.diagonal (fun i => (a i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef := by
    have hc : Continuous (fun a : (R ⊕ S) → ℝ => Matrix.diagonal (fun i => (a i : ℂ))-
        sourceHermitianLift (A ⊙ sourceConjugate (Z j))) := by fun_prop
    exact sourcePSD_closed.mem_of_tendsto (hc.tendsto a |>.comp hat)
      (Filter.Eventually.of_forall fun k => hPSD (φ k) j)
  have hsumlim : (∑ i, a i) ≤ 2*t := by
    have hεt : Tendsto ε atTop (𝓝 0) := by
      dsimp only [ε]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hl : Tendsto (fun k => ∑ i, α (φ k) i) atTop (𝓝 (∑ i, a i)) := by
      have hc : Continuous (fun a : (R ⊕ S) → ℝ => ∑ i, a i) := by fun_prop
      exact hc.tendsto a |>.comp hat
    have hr : Tendsto (fun k => 2*(t+ε (φ k))) atTop (𝓝 (2*t)) := by
      convert! (tendsto_const_nhds.add (hεt.comp hφ.tendsto_atTop)).const_mul 2 using 1
      simp
    exact le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall fun k => (hsum (φ k)).le)
  refine ⟨a,hap,hpsd,le_antisymm (sourceDualNorm_le_diagonal A Z a hap hpsd) ?_⟩
  rw [← hval]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end CompactPrimal

theorem sourceSDPBudget_saturate {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (hn : 0<n) (Z : Fin n → Matrix R S ℂ)
    (Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) (hY : Y ∈ sourceSDPBudget) :
    ∃ Y' : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
      (∀ j, (Y' j).PosSemidef) ∧ (∀ i, ∑ j, Y' j i i=1) ∧ sourceSDPImage Z Y'=sourceSDPImage Z Y := by
  let j0 : Fin n := ⟨0,hn⟩
  let D : Matrix (R ⊕ S) (R ⊕ S) ℂ := Matrix.diagonal (fun i => ((1-∑ j, (Y j i i).re : ℝ) : ℂ))
  have hD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr fun i =>
    Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hY.2 i),by simp⟩
  let Y' := Y+Pi.single j0 D
  refine ⟨Y',?_,?_,?_⟩
  · intro j
    by_cases hh : j=j0
    · subst j
      exact (hY.1 j0).add (by simpa only [Pi.single_eq_same] using! hD)
    · simpa only [Y',Pi.add_apply,Pi.single_eq_of_ne hh,add_zero] using! hY.1 j
  · intro i
    have hreal (j : Fin n) : Y j i i=((Y j i i).re : ℂ) := by
      have he := congrFun (congrFun (hY.1 j).isHermitian i) i
      simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_eq_iff_im] at he
      exact Complex.ext (by simp) (by simpa using! he)
    simp only [Y',Pi.add_apply,Matrix.add_apply,Finset.sum_add_distrib]
    rw [show (∑ j, (Pi.single j0 D : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ) j i i)=D i i by
      rw [Finset.sum_eq_single j0]
      · simp
      · intro j _ hj
        simp [hj]
      · simp]

    simp only [D,Matrix.diagonal_apply_eq]
    have hs : (∑ j, Y j i i)=((∑ j, (Y j i i).re : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun j _ => hreal j
    rw [hs,← Complex.ofReal_add]
    norm_num
  · ext r s
    simp only [sourceSDPImage,Y',Pi.add_apply,Matrix.add_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : j=j0 <;> simp [he,D,Matrix.diagonal]

theorem sourceDualNorm_maxSDP {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (hn : 0<n) :
    ∃ Y : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
      (∀ j, (Y j).PosSemidef) ∧ (∀ i, ∑ j, Y j i i=1) ∧
      sourceDualNorm A Z=ENNReal.ofReal
        ((∑ j, (Matrix.trace ((Y j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j))))).re/2) ∧
      (∀ Y' : Fin n → Matrix (R ⊕ S) (R ⊕ S) ℂ,
        (∀ j, (Y' j).PosSemidef) → (∀ i, ∑ j, Y' j i i=1) →
        (∑ j, (Matrix.trace ((Y' j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j))))).re ≤
        (∑ j, (Matrix.trace ((Y j)ᴴ*sourceHermitianLift (A ⊙ sourceConjugate (Z j))))).re) := by
  obtain ⟨W,hW,hval,hmax⟩ := sourceDualNorm_psd_attained A Z
  obtain ⟨Y,hY,hdiag,hi⟩ := sourceSDPBudget_saturate hn Z W hW
  refine ⟨Y,hY,hdiag,?_,?_⟩
  · rw [sourceSDPImage_pairing _ _ _ (fun j => (hY j).isHermitian),hi]
    simpa using! hval
  · intro Y' hY' hd'
    rw [sourceSDPImage_pairing _ _ _ (fun j => (hY' j).isHermitian),
      sourceSDPImage_pairing _ _ _ (fun j => (hY j).isHermitian),hi]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ)≤2)
    apply hmax Y'
    refine ⟨hY',?_⟩
    intro i
    have hh := congrArg Complex.re (hd' i)
    simpa only [Complex.re_sum,Complex.one_re] using! hh.le

theorem sourceDualNorm_minSDP {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    ∃ Ω : Matrix (R ⊕ S) (R ⊕ S) ℂ,
      Ω.PosSemidef ∧ (∀ r s, r ≠ s → Ω r s=0) ∧
      (∀ j, (Ω-sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) ∧
      sourceDualNorm A Z=ENNReal.ofReal ((Matrix.trace Ω).re/2) ∧
      (∀ Ω' : Matrix (R ⊕ S) (R ⊕ S) ℂ,
        Ω'.PosSemidef → (∀ r s, r ≠ s → Ω' r s=0) →
        (∀ j, (Ω'-sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef) →
        (Matrix.trace Ω).re ≤ (Matrix.trace Ω').re) := by
  obtain ⟨α,hα,hPSD,hval⟩ := sourceDualNorm_diagonal_attained A Z
  let Ω := Matrix.diagonal (fun i => (α i : ℂ))
  have ht : (Matrix.trace Ω).re=∑ i, α i := by
    simp [Ω,Matrix.trace,Matrix.diag_apply,Complex.re_sum]
  refine ⟨Ω,Matrix.posSemidef_diagonal_iff.mpr (fun i => Complex.nonneg_iff.mpr ⟨hα i,by simp⟩),
    ?_,hPSD,by simpa only [ht] using! hval,?_⟩
  · intro r s hrs
    exact Matrix.diagonal_apply_ne _ hrs
  · intro Ω' hp hd hs
    let β : (R ⊕ S) → ℝ := fun i => (Ω' i i).re
    have hβ (i : R ⊕ S) : 0 ≤ β i := (Complex.nonneg_iff.mp hp.diag_nonneg).1
    have hΩ : Ω'=Matrix.diagonal (fun i => (β i : ℂ)) := by
      ext r s
      by_cases he : r=s
      · subst s
        have hh := congrFun (congrFun hp.isHermitian r) r
        simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_eq_iff_im] at hh
        simpa only [Matrix.diagonal_apply_eq,β] using!
            Complex.ext (by simp : (Ω' r r).re=((Ω' r r).re : ℂ).re) (by simpa using! hh)
      · simp only [Matrix.diagonal_apply_ne _ he,hd r s he]
    have hb := sourceDualNorm_le_diagonal A Z β hβ (by simpa only [← hΩ] using! hs)
    rw [hval] at hb
    have hh :=
        (ENNReal.ofReal_le_ofReal_iff (div_nonneg (Finset.sum_nonneg fun i _ => hβ i) (by norm_num))).mp hb
    rw [ht]
    have htrace : (Matrix.trace Ω').re=∑ i, β i := by
      simp [Matrix.trace,Matrix.diag_apply,Complex.re_sum,β]
    rw [htrace]
    linarith

theorem sourceUnitBall_hadamard_image {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (C B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue C (fun j => Z j ⊙ B) ≤ 1 ↔
      ∃ P : Matrix R S ℂ, sourceRectValue P Z ≤ 1 ∧ C=P ⊙ B := by
  constructor
  · intro hc
    obtain ⟨m,u,v,heq,hu,hv⟩ :=
        (sourceRectValue_budget_boundary C (fun j => Z j ⊙ B) 1 zero_le_one).mp (by simpa using! hc)
    let P : Matrix R S ℂ := fun r s => ∑ j, Z j r s*∑ k, star (u r j k)*v s j k
    have hp : sourceRectValue P Z ≤ 1 := by
      exact_mod_cast sourceRectValue_le_of_cert zero_le_one ⟨m,u,v,fun _ _ => rfl,hu,hv⟩
    refine ⟨P,hp,?_⟩
    ext r s
    rw [heq]
    simp only [Matrix.hadamard_apply,P,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rintro ⟨P,hP,rfl⟩
    exact (sourceRectValue_hadamard_filters_le P B Z).trans hP

theorem sourceDualNorm_hadamard_transport {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceDualNorm (A ⊙ B) Z=sourceDualNorm A (fun j => Z j ⊙ sourceConjugate B) := by
  have hp (P : Matrix R S ℂ) : sourceDualPairing (A ⊙ B) P=sourceDualPairing A (P ⊙ sourceConjugate B) := by
    unfold sourceDualPairing
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    simp only [Matrix.hadamard_apply,sourceConjugate,star_mul]
    ring
  unfold sourceDualNorm
  apply le_antisymm
  · apply iSup_le
    intro P
    have hf := (sourceRectValue_hadamard_filters_le P.val (sourceConjugate B) Z).trans P.property
    exact le_iSup_of_le ⟨P.val ⊙ sourceConjugate B,hf⟩
        (by change ENNReal.ofReal (sourceDualPairing (A ⊙ B) P.val) ≤ _; rw [hp]; exact le_rfl)
  · apply iSup_le
    intro C
    obtain ⟨P,hP,he⟩ := (sourceUnitBall_hadamard_image C.val (sourceConjugate B) Z).mp C.property
    exact le_iSup_of_le ⟨P,hP⟩
        (by change ENNReal.ofReal (sourceDualPairing A C.val) ≤ _; rw [he,← hp]; exact le_rfl)

theorem sourcePSD_diag_real {K : Type} [Fintype K] [DecidableEq K]
    (G : Matrix K K ℂ) (hG : G.PosSemidef) (i : K) : G i i=((G i i).re : ℂ) := by
  have hh := congrFun (congrFun hG.isHermitian i) i
  simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_eq_iff_im] at hh
  exact Complex.ext (by simp) (by simpa using! hh)

theorem sourceDiagonal_hadamard {K : Type} [Fintype K] [DecidableEq K]
    (α : K → ℝ) (G : Matrix K K ℂ) (hG : G.PosSemidef) :
    Matrix.diagonal (fun i => (α i : ℂ)) ⊙ G=
      Matrix.diagonal (fun i => ((α i*(G i i).re : ℝ) : ℂ)) := by
  rw [Matrix.hadamard_comm,Matrix.hadamard_diagonal]
  congr 1
  funext i
  change G i i*(α i : ℂ)=((α i*(G i i).re : ℝ) : ℂ)
  calc
    _ = ((G i i).re : ℂ)*(α i : ℂ) := congrArg (fun z : ℂ => z*(α i : ℂ)) (sourcePSD_diag_real G hG i)
    _ = _ := by push_cast; ring

theorem sourceHermitianLift_hadamard {R S : Type}
    (C B : Matrix R S ℂ) (G : Matrix (R ⊕ S) (R ⊕ S) ℂ)
    (hG : G.IsHermitian) (hcorner : ∀ r s, G (.inl r) (.inr s)=B r s) :
    sourceHermitianLift C ⊙ G=sourceHermitianLift (C ⊙ B) := by
  have hlower (r : R) (s : S) : G (.inr s) (.inl r)=star (B r s) := by
    simpa only [Matrix.conjTranspose_apply,hcorner] using!
      (congrFun (congrFun hG (.inr s)) (.inl r)).symm
  ext i j
  cases i <;> cases j <;> simp [sourceHermitianLift,Matrix.hadamard_apply,hcorner,hlower]

theorem sourceDualNorm_hadamard_le {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A B : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceDualNorm (A ⊙ B) Z ≤ sourceDualNorm A Z*sourceUnfiltered B := by
  obtain ⟨α,hα,hPSD,hval⟩ := sourceDualNorm_diagonal_attained A Z
  let b := (sourceUnfiltered B).toReal
  have hb : ENNReal.ofReal b=sourceUnfiltered B :=
      ENNReal.ofReal_toReal (sourceUnfiltered_finite B).ne
  have hcert : sourceRectCert 1 B (fun _ : Fin 1 => fun _ _ => 1) b :=
    (sourceRectValue_budget_boundary B _ b ENNReal.toReal_nonneg).mp (le_of_eq hb.symm)
  obtain ⟨Y,hY,hi,hd⟩ := (sourceRectCert_iff_psd_family B _ b).mp hcert
  let G := Y 0
  have hg : G.PosSemidef := hY 0
  have hc (r : R) (s : S) : G (.inl r) (.inr s)=B r s := by
    simpa [sourceSDPImage,G] using! congrFun (congrFun hi r) s
  have hgd (i : R ⊕ S) : (G i i).re ≤ b := by simpa [G] using! hd i
  let β : (R ⊕ S) → ℝ := fun i => α i*(G i i).re
  have hβ (i : R ⊕ S) : 0 ≤ β i := mul_nonneg (hα i) (Complex.nonneg_iff.mp hg.diag_nonneg).1
  have hβPSD (j : Fin n) : (Matrix.diagonal (fun i => (β i : ℂ))-
      sourceHermitianLift ((A ⊙ B) ⊙ sourceConjugate (Z j))).PosSemidef := by
    have hp := (hPSD j).hadamard hg
    have hsub : (Matrix.diagonal (fun i => (α i : ℂ))-sourceHermitianLift (A ⊙ sourceConjugate (Z j))) ⊙ G=
        Matrix.diagonal (fun i => (α i : ℂ)) ⊙ G-sourceHermitianLift (A ⊙ sourceConjugate (Z j)) ⊙ G := by
      ext r s
      simp only [Matrix.hadamard_apply,Matrix.sub_apply,sub_mul]
    rw [hsub,sourceDiagonal_hadamard α G hg,
      sourceHermitianLift_hadamard _ B G hg.isHermitian hc] at hp
    have he : (A ⊙ sourceConjugate (Z j)) ⊙ B=(A ⊙ B) ⊙ sourceConjugate (Z j) := by
      ext r s
      simp only [Matrix.hadamard_apply]
      ring
    simpa only [he,β] using! hp
  calc
    sourceDualNorm (A ⊙ B) Z ≤ ENNReal.ofReal ((∑ i, β i)/2) := sourceDualNorm_le_diagonal _ _ β hβ hβPSD
    _ ≤ ENNReal.ofReal (((∑ i, α i)/2)*b) := ENNReal.ofReal_le_ofReal (by
      have hh : (∑ i, β i) ≤ (∑ i, α i)*b := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgd i) (hα i)
      linarith)
    _ = sourceDualNorm A Z*sourceUnfiltered B := by
      rw [ENNReal.ofReal_mul (div_nonneg (Finset.sum_nonneg fun i _ => hα i) (by norm_num)),← hval,hb]

theorem sourceDualNorm_real_smul {R S : Type} [Fintype R] [Fintype S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (t : ℝ) (ht : 0 ≤ t) :
    sourceDualNorm (t • A) Z=ENNReal.ofReal t*sourceDualNorm A Z := by
  have hp (P : Matrix R S ℂ) : sourceDualPairing (t • A) P=t*sourceDualPairing A P := by
    have he : sourceDualPairing (t • A) P=sourceDualPairing A (t • P) := by
      dsimp [sourceDualPairing]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      change star ((t : ℂ)*A r s)*P r s=star (A r s)*((t : ℂ)*P r s)
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    rw [he,sourceDualPairing_smul]
  unfold sourceDualNorm
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro P
  change ENNReal.ofReal (sourceDualPairing (t • A) P.val)=ENNReal.ofReal t*ENNReal.ofReal
      (sourceDualPairing A P.val)
  rw [hp,ENNReal.ofReal_mul ht]

theorem sourceDiagonal_scaledPSD {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (C : Matrix R S ℂ) (α : (R ⊕ S) → ℝ) (t : ℝ)
    (hp : (Matrix.diagonal (fun i => (α i : ℂ))-sourceHermitianLift C).PosSemidef) :
    (Matrix.diagonal (fun i => (Sum.elim (fun r => t^2*α (.inl r)) (fun s => α (.inr s)) i : ℂ))-
      sourceHermitianLift (t • C)).PosSemidef := by
  let d : (R ⊕ S) → ℂ := Sum.elim (fun _ => (t : ℂ)) (fun _ => 1)
  let D := Matrix.diagonal d
  have hh := hp.mul_mul_conjTranspose_same D
  have he : D*(Matrix.diagonal (fun i => (α i : ℂ))-sourceHermitianLift C)*Dᴴ=
      Matrix.diagonal (fun i => (Sum.elim (fun r => t^2*α (.inl r)) (fun s => α (.inr s)) i : ℂ))-
      sourceHermitianLift (t • C) := by
    ext i j
    simp only [D,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Matrix.sub_apply]
    cases i <;> cases j <;>
      simp [d,sourceHermitianLift,Matrix.smul_apply,Complex.real_smul,Matrix.diagonal,star_mul]
    all_goals split_ifs <;> ring
  rw [he] at hh
  exact hh

theorem sourceDiagonal_balanced {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (α : (R ⊕ S) → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hPSD : ∀ j, (Matrix.diagonal (fun i => (α i : ℂ))-
      sourceHermitianLift (A ⊙ sourceConjugate (Z j))).PosSemidef)
    (hval : sourceDualNorm A Z=ENNReal.ofReal ((∑ i,α i)/2)) :
    (∑ r, α (.inl r))=(∑ s, α (.inr s)) := by
  let L := ∑ r, α (.inl r)
  let T := ∑ s, α (.inr s)
  have hL : 0 ≤ L := Finset.sum_nonneg fun r _ => hα (.inl r)
  have hT : 0 ≤ T := Finset.sum_nonneg fun s _ => hα (.inr s)
  have ht (t : ℝ) (ht : 0<t) : t*(L+T) ≤ t^2*L+T := by
    let β : (R ⊕ S) → ℝ := Sum.elim (fun r => t^2*α (.inl r)) (fun s => α (.inr s))
    have hβ (i : R ⊕ S) : 0 ≤ β i := by
      cases i with
      | inl r => exact mul_nonneg (sq_nonneg t) (hα (.inl r))
      | inr s => exact hα (.inr s)
    have hp (j : Fin n) := sourceDiagonal_scaledPSD (A ⊙ sourceConjugate (Z j)) α t (hPSD j)
    have hh := sourceDualNorm_le_diagonal (t • A) Z β hβ (by
      intro j
      rw [Matrix.smul_hadamard]
      convert! hp j using 1
      congr 2
      ext i
      cases i <;> simp [β])
    rw [sourceDualNorm_real_smul A Z t ht.le,hval,← ENNReal.ofReal_mul ht.le] at hh
    have hsum : (∑ i, β i)=t^2*L+T := by
      simp only [Fintype.sum_sum_type,β,Sum.elim_inl,Sum.elim_inr,← Finset.mul_sum,L,T]
    rw [hsum] at hh
    have hb : 0 ≤ (t^2*L+T)/2 := by positivity
    have hineq := (ENNReal.ofReal_le_ofReal_iff hb).mp hh
    rw [Fintype.sum_sum_type] at hineq
    change t*((L+T)/2) ≤ (t^2*L+T)/2 at hineq
    linarith
  change L=T
  by_cases hz : L=0
  · have hh := ht 2 (by norm_num)
    rw [hz] at hh
    nlinarith
  have hLp : 0<L := lt_of_le_of_ne hL (Ne.symm hz)
  let t := (L+T)/(2*L)
  have htp : 0<t := div_pos (by linarith) (by positivity)
  have hh := ht t htp
  have he : t*(2*L)=L+T := by dsimp [t]; field_simp
  nlinarith [sq_nonneg (L-T)]

theorem sourcePSD_tensor {K L : Type} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (P : Matrix K K ℂ) (Q : Matrix L L ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (sourceTensor P Q).PosSemidef := by
  obtain ⟨C,hC⟩ := gram_positive_matrix_actual_factorization K P hP
  obtain ⟨D,hD⟩ := gram_positive_matrix_actual_factorization L Q hQ
  change (P ⊗ₖ Q).PosSemidef
  rw [← hC,← hD,Matrix.mul_kronecker_mul,← Matrix.conjTranspose_kronecker]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sourceDiagonal_plusPSD {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (C : Matrix R S ℂ) (α : (R ⊕ S) → ℝ)
    (hp : (Matrix.diagonal (fun i => (α i : ℂ))-sourceHermitianLift C).PosSemidef) :
    (Matrix.diagonal (fun i => (α i : ℂ))+sourceHermitianLift C).PosSemidef := by
  have hh := sourceDiagonal_scaledPSD C α (-1) hp
  convert! hh using 1
  ext i j
  cases i <;> cases j <;> simp [sourceHermitianLift,Matrix.diagonal]

theorem sourceDiagonal_tensorPSD {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (C : Matrix R S ℂ) (D : Matrix U V ℂ)
    (α : (R ⊕ S) → ℝ) (β : (U ⊕ V) → ℝ)
    (hC : (Matrix.diagonal (fun i => (α i : ℂ))-sourceHermitianLift C).PosSemidef)
    (hD : (Matrix.diagonal (fun i => (β i : ℂ))-sourceHermitianLift D).PosSemidef) :
    (Matrix.diagonal (fun i => (Sum.elim (fun r : R × U => α (.inl r.1)*β (.inl r.2))
        (fun s : S × V => α (.inr s.1)*β (.inr s.2)) i : ℂ))-
      sourceHermitianLift (sourceTensor C D)).PosSemidef := by
  let P := Matrix.diagonal (fun i => (α i : ℂ))
  let Q := Matrix.diagonal (fun i => (β i : ℂ))
  let H := sourceHermitianLift C
  let K := sourceHermitianLift D
  have hp := sourcePSD_tensor (P-H) (Q+K) hC (sourceDiagonal_plusPSD D β hD)
  have hq := sourcePSD_tensor (P+H) (Q-K) (sourceDiagonal_plusPSD C α hC) hD
  have hs := (hp.add hq).smul (by norm_num : (0 : ℝ) ≤ 1/2)
  have he : (1/2 : ℝ) • (sourceTensor (P-H) (Q+K)+sourceTensor (P+H) (Q-K))=
      sourceTensor P Q-sourceTensor H K := by
    ext r s
    simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Complex.real_smul,sourceTensor]
    norm_num
    ring
  rw [he] at hs
  let e : (R × U) ⊕ (S × V) → (R ⊕ S) × (U ⊕ V) :=
    Sum.elim (fun r => (.inl r.1,.inl r.2)) (fun s => (.inr s.1,.inr s.2))
  have ht := hs.submatrix e
  have hm : (sourceTensor P Q-sourceTensor H K).submatrix e e=
      Matrix.diagonal (fun i => (Sum.elim (fun r : R × U => α (.inl r.1)*β (.inl r.2))
        (fun s : S × V => α (.inr s.1)*β (.inr s.2)) i : ℂ))-
      sourceHermitianLift (sourceTensor C D) := by
    ext i j
    cases i <;> cases j <;>
      simp [P,Q,H,K,e,sourceTensor,sourceHermitianLift,Matrix.diagonal,Matrix.submatrix_apply]
    all_goals split_ifs <;> simp_all [Prod.ext_iff]
  rw [hm] at ht
  exact ht

theorem sourceDualNorm_tensor_le {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] {n m : ℕ}
    (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    sourceDualNorm (sourceTensor A B) (sourceFilterTensor Y Z) ≤ sourceDualNorm A Y*sourceDualNorm B Z := by
  obtain ⟨α,hα,hαPSD,hαval⟩ := sourceDualNorm_diagonal_attained A Y
  obtain ⟨β,hβ,hβPSD,hβval⟩ := sourceDualNorm_diagonal_attained B Z
  have hαbal := sourceDiagonal_balanced A Y α hα hαPSD hαval
  have hβbal := sourceDiagonal_balanced B Z β hβ hβPSD hβval
  let γ : ((R × U) ⊕ (S × V)) → ℝ :=
    Sum.elim (fun r => α (.inl r.1)*β (.inl r.2)) (fun s => α (.inr s.1)*β (.inr s.2))
  have hγ (i : (R × U) ⊕ (S × V)) : 0 ≤ γ i := by
    cases i with
    | inl r => exact mul_nonneg (hα _) (hβ _)
    | inr s => exact mul_nonneg (hα _) (hβ _)
  have hγPSD (j : Fin (n*m)) : (Matrix.diagonal (fun i => (γ i : ℂ))-
      sourceHermitianLift (sourceTensor A B ⊙ sourceConjugate (sourceFilterTensor Y Z j))).PosSemidef := by
    have hp := sourceDiagonal_tensorPSD
      (A ⊙ sourceConjugate (Y (finProdFinEquiv.symm j).1))
      (B ⊙ sourceConjugate (Z (finProdFinEquiv.symm j).2)) α β
      (hαPSD _) (hβPSD _)
    have he : sourceTensor (A ⊙ sourceConjugate (Y (finProdFinEquiv.symm j).1))
        (B ⊙ sourceConjugate (Z (finProdFinEquiv.symm j).2))=
        sourceTensor A B ⊙ sourceConjugate (sourceFilterTensor Y Z j) := by
      ext r s
      simp only [sourceTensor,sourceFilterTensor,Matrix.hadamard_apply,sourceConjugate,star_mul]
      ring
    rw [he] at hp
    convert! hp using 1
    congr 2
    ext i
    cases i <;> simp [γ]
  have hcost : (∑ i,γ i)/2=((∑ i,α i)/2)*((∑ i,β i)/2) := by
    simp only [Fintype.sum_sum_type,γ,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum,← Finset.sum_mul_sum,hαbal,hβbal]
    ring
  calc
    sourceDualNorm (sourceTensor A B) (sourceFilterTensor Y Z) ≤ ENNReal.ofReal ((∑ i,γ i)/2) :=
      sourceDualNorm_le_diagonal _ _ γ hγ hγPSD
    _ = sourceDualNorm A Y*sourceDualNorm B Z := by
      rw [hcost,ENNReal.ofReal_mul (div_nonneg (Finset.sum_nonneg fun i _ => hα i) (by norm_num)),← hαval,← hβval]

theorem sourceDualNorm_real_pair_attained {R S : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] {n : ℕ}
    (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    ∃ P : Matrix R S ℂ, ∃ p : ℝ, 0 ≤ p ∧ sourceRectValue P Z ≤ 1 ∧
      (∑ r, ∑ s, star (A r s)*P r s)=(p : ℂ) ∧ sourceDualNorm A Z=ENNReal.ofReal p := by
  obtain ⟨Y,hY,hval,_⟩ := sourceDualNorm_psd_attained A Z
  let P := sourceSDPImage Z Y
  have hf : sourceRectValue P Z ≤ 1 := (sourceUnitBall_iff_psd_family _ Z).mpr ⟨Y,hY.1,rfl,hY.2⟩
  let z : ℂ := ∑ r, ∑ s, star (A r s)*P r s
  by_cases hz : z=0
  · refine ⟨P,0,le_rfl,hf,hz,?_⟩
    simpa only [sourceDualPairing,P,← show z=(∑ r, ∑ s, star (A r s)*P r s) from rfl,hz,Complex.zero_re] using! hval
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let c : ℂ := star z/(‖z‖ : ℂ)
  have hc : ‖c‖=1 := by
    dsimp only [c]
    rw [norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z),div_self hn]
  have hcz : c*z=(‖z‖ : ℂ) := by
    dsimp only [c]
    rw [div_mul_eq_mul_div]
    have he : star z*z=((‖z‖^2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
      rfl
    rw [he]
    push_cast
    field_simp
  have hf' : sourceRectValue (c • P) Z ≤ 1 := by
    rw [sourceRectValue_smul P Z c,hc,ENNReal.ofReal_one,one_mul]
    exact hf
  have hp : (∑ r, ∑ s, star (A r s)*(c • P) r s)=(‖z‖ : ℂ) := by
    simp only [Matrix.smul_apply,smul_eq_mul]
    rw [show (∑ r, ∑ s, star (A r s)*(c*P r s))=c*(∑ r, ∑ s, star (A r s)*P r s) by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _; ring]
    exact hcz
  refine ⟨c • P,‖z‖,norm_nonneg _,hf',hp,le_antisymm ?_ ?_⟩
  · rw [hval]
    apply ENNReal.ofReal_le_ofReal
    exact Complex.re_le_norm z
  · have hh := le_iSup (fun B : {B : Matrix R S ℂ // sourceRectValue B Z ≤ 1} =>
      ENNReal.ofReal (sourceDualPairing A B.val)) ⟨c • P,hf'⟩
    simpa only [sourceDualPairing,hp,Complex.ofReal_re] using! hh

theorem sourceDualNorm_tensor_ge {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] {n m : ℕ}
    (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    sourceDualNorm A Y*sourceDualNorm B Z ≤ sourceDualNorm (sourceTensor A B) (sourceFilterTensor Y Z) := by
  obtain ⟨P,p,hp,hP,hpairP,hvalP⟩ := sourceDualNorm_real_pair_attained A Y
  obtain ⟨Q,q,hq,hQ,hpairQ,hvalQ⟩ := sourceDualNorm_real_pair_attained B Z
  have hf : sourceRectValue (sourceTensor P Q) (sourceFilterTensor Y Z) ≤ 1 := by
    rw [sourceRectValue_tensor]
    exact (mul_le_mul hP hQ zero_le zero_le).trans (by simp)
  have he : sourceDualPairing (sourceTensor A B) (sourceTensor P Q)=p*q := by
    have hm : (∑ r : R × U, ∑ s : S × V, star (sourceTensor A B r s)*sourceTensor P Q r s)=
        (∑ r, ∑ s, star (A r s)*P r s)*(∑ u, ∑ v, star (B u v)*Q u v) := by
      simp only [sourceTensor,Fintype.sum_prod_type,star_mul]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro v _
      ring
    dsimp only [sourceDualPairing]
    rw [hm,hpairP,hpairQ]
    simp
  rw [hvalP,hvalQ,← ENNReal.ofReal_mul hp]
  have hh := le_iSup (fun C : {C : Matrix (R × U) (S × V) ℂ // sourceRectValue C (sourceFilterTensor Y Z) ≤ 1} =>
    ENNReal.ofReal (sourceDualPairing (sourceTensor A B) C.val)) ⟨sourceTensor P Q,hf⟩
  simpa only [he] using! hh

theorem sourceDualNorm_tensor {R S U V : Type}
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] {n m : ℕ}
    (A : Matrix R S ℂ) (B : Matrix U V ℂ)
    (Y : Fin n → Matrix R S ℂ) (Z : Fin m → Matrix U V ℂ) :
    sourceDualNorm (sourceTensor A B) (sourceFilterTensor Y Z)=sourceDualNorm A Y*sourceDualNorm B Z :=
  le_antisymm (sourceDualNorm_tensor_le A B Y Z) (sourceDualNorm_tensor_ge A B Y Z)

theorem dualNormSDPAndClosure : DualNormSDPAndClosure := by
  refine ⟨?_,?_,?_,?_⟩
  · intro R S _ _ _ _ n A Z
    exact sourceDualNorm_minSDP A Z
  · intro R S _ _ _ _ n A Z hn
    simpa only [Complex.re_sum] using! sourceDualNorm_maxSDP A Z hn
  · intro R S _ _ _ _ n m A Y Z p B
    exact ⟨sourceDualNorm_filterUnion_le A Y Z,sourceDualNorm_convexFilter A Z p,
      sourceDualNorm_hadamard_transport A B Z,sourceDualNorm_hadamard_le A B Z⟩
  · intro R S U V _ _ _ _ _ _ _ _ n m A B Y Z
    exact sourceDualNorm_tensor A B Y Z

end Qatlib.Concepts.GramQueryCore.FilteredNorm
