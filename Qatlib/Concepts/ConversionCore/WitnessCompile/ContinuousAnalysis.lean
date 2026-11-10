/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.StateConversion
import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.GramQueryCore.ModelSemantics.BooleanValueCompatibilityQuan
import Qatlib.Concepts.GramQueryCore.ModelSemantics.VolterraAndOracleLogSemanticsQuan
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DensityPurification
import Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveInstrumentPurificationQuan
import Qatlib.Concepts.QueryComplexity.StateConversion.OptimizedConversionEndpointsQuan
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib
open Qatlib
open Qatlib.Concepts.GramQueryCore.ModelSemantics
open Qatlib.Concepts.QueryComplexity.StateConversion
open scoped BigOperators Classical Matrix.Norms.L2Operator ENNReal ComplexOrder

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
set_option maxHeartbeats 300000 in
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
noncomputable section

theorem continuousConversion_log_action {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (x : X)
    (ψ : QState ((Fin (n+1) × Fin (q+1)) × W))
    (j : Fin (n+1)) (a : Fin (q+1)) (w : W) :
    (sourceLogOracle input x *ᵥ ψ) ((j,a),w) =
      (sourceLog (sourceValueQuery (sourcePaddedSymbol input x j)) *ᵥ
        (fun b => ψ ((j,b),w))) a := by
  simp only [Matrix.mulVec, dotProduct, sourceLogOracle, Fintype.sum_prod_type]
  simp only [ite_mul, ite_and]
  simp only [Finset.sum_ite_irrel]
  simp
end
noncomputable section
def continuousConversion_source_slice {X W : Type} {n q : ℕ}
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) :
    X → Fin n → QState (Fin (q+1) × W) := fun x j p => ψ x ((j.castSucc,p.1),p.2)
end
noncomputable section

theorem continuousConversion_source_active_mass {W : Type} [Fintype W] {n q : ℕ}
    (ψ : QState ((Fin (n+1) × Fin (q+1)) × W)) :
    (∑ j : Fin n, ∑ p : Fin (q+1) × W, Complex.normSq (ψ ((j.castSucc,p.1),p.2))) ≤
      ∑ p, Complex.normSq (ψ p) := by
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)))
end
noncomputable section
set_option maxHeartbeats 400000 in

theorem continuousConversion_source_tangent_cert {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    gramFilteredCert
      (continuousConversionTangent (continuousConversion_source_slice ψ)
        (continuousConversion_source_slice (fun x => sourceLogOracle input x *ᵥ ψ x)))
      (sourceAlphabetDelta input) (1 + Real.pi ^ 2) := by
  apply continuousConversionTangent_cert input _ _ 1 (Real.pi ^ 2)
  · intro x
    apply (continuousConversion_source_active_mass (ψ x)).trans
    exact le_of_eq (by simpa only [Complex.normSq_eq_norm_sq] using! hψ x)
  · intro x
    apply (continuousConversion_source_active_mass (sourceLogOracle input x *ᵥ ψ x)).trans
    have hb := l2_norm_mulVec_fromVec_le (sourceLogOracle input x) (ψ x)
    rw [(normalized_iff_norm_toEuclidean_fromVec _).mp (hψ x),mul_one] at hb
    have hp := hb.trans (sourceLogOracle_hermitian_norm X W input x).2
    have hs := pow_le_pow_left₀ (norm_nonneg _) hp 2
    simpa only [norm_toEuclidean_fromVec_sq,Complex.normSq_eq_norm_sq] using! hs
  · intro x y j hxy
    have hp (x : X) : sourcePaddedSymbol input x j.castSucc = input x j := by
      simp [sourcePaddedSymbol,j.isLt]
    have hU : sourceValueQuery (input x j) ∈ Matrix.unitaryGroup (Fin (q+1)) ℂ :=
      permMatrix_unitary_of_injective (by intro a b h; exact add_right_cancel h)
    have hL := (sourceLog_hermitian_norm _ _ hU).1
    simp only [continuousConversion_source_slice,
        Qatlib.Foundations.PureStateMath.inner_apply, Fintype.sum_prod_type]
    simp_rw [continuousConversion_log_action, hp, ← hxy]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    exact continuousConversion_hermitian_pair _ hL _ _
end
set_option maxHeartbeats 300000 in
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option maxHeartbeats 400000 in
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.ModelSemantics Qatlib.Concepts.QueryComplexity.StateConversion
open MeasureTheory Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator Topology

noncomputable section

local instance continuousConversionAnalysis_matrixENormed (H : Type) [Fintype H] :
    ENormedAddCommMonoid (Matrix H H ℂ) :=
  @NormedAddCommGroup.toENormedAddCommMonoid _ Matrix.instL2OpNormedAddCommGroup

local instance continuousConversionAnalysis_matrixPseudoMetrizable (H : Type) [Fintype H] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix H H ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (H → H → ℂ)
  infer_instance

set_option maxHeartbeats 400000 in

theorem continuousConversion_source_state_equation {H : Type} [Fintype H] [DecidableEq H]
    (K V : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hK : IntervalIntegrable K volume 0 T) (hV : sourceVolterra K T V)
    (ψ : QState H) (i : H) :
    (∀ t ∈ Icc 0 T, (V t *ᵥ ψ) i = ψ i +
      ∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s *ᵥ (V s *ᵥ ψ))) i) ∧
    IntervalIntegrable (fun s => ((-Complex.I) • (K s *ᵥ (V s *ᵥ ψ))) i) volume 0 T := by
  let L : Matrix H H ℂ →L[ℝ] ℂ := ∑ j, (ψ j) • sourceMatrixEntryCLM H i j
  have hL (A : Matrix H H ℂ) : L A = (A *ᵥ ψ) i := by
    simp [L,sourceMatrixEntryCLM,Matrix.mulVec,dotProduct,mul_comm]; rfl
  have hLi (s : ℝ) : L ((-Complex.I) • (K s * V s)) =
      ((-Complex.I) • (K s *ᵥ (V s *ᵥ ψ))) i := by
    rw [hL, Matrix.smul_mulVec,Matrix.mulVec_mulVec]
  obtain ⟨hEq,hI⟩ := sourceVolterra_matrix_equation H K V T hT hK hV
  refine ⟨?_,?_⟩
  · intro t ht
    have hint := hI.mono_set (by
      rw [Set.uIcc_of_le ht.1,Set.uIcc_of_le hT]
      exact Set.Icc_subset_Icc le_rfl ht.2)
    have he := congrArg L (hEq t ht)
    rw [map_add, hL, hL] at he
    have hInt := L.intervalIntegral_comp_comm hint
    have hInt' : (∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s *ᵥ (V s *ᵥ ψ))) i) =
        L (∫ s in (0 : ℝ)..t, (-Complex.I) • (K s * V s)) :=
      (intervalIntegral.integral_congr (fun s _ => (hLi s).symm)).trans hInt
    rw [← hInt'] at he
    simpa only [Matrix.one_mulVec] using! he
  · have hi : IntervalIntegrable (fun s => L ((-Complex.I) • (K s * V s))) volume 0 T :=
      ⟨L.integrable_comp hI.1,L.integrable_comp hI.2⟩
    simpa only [hLi] using! hi

theorem continuousConversion_source_state_regularity {H : Type} [Fintype H] [DecidableEq H]
    (K V : ℝ → Matrix H H ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hK : IntervalIntegrable K volume 0 T) (hV : sourceVolterra K T V)
    (ψ : QState H) (i : H) :
    AbsolutelyContinuousOnInterval (fun t => ((V t *ᵥ ψ) i).re) 0 T ∧
    AbsolutelyContinuousOnInterval (fun t => ((V t *ᵥ ψ) i).im) 0 T ∧
    ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt (fun t => (V t *ᵥ ψ) i)
      (((-Complex.I) • (K t *ᵥ (V t *ᵥ ψ))) i) t := by
  obtain ⟨hEq,hI⟩ := continuousConversion_source_state_equation K V T hT hK hV ψ i
  have hEq' : EqOn (fun t => (V t *ᵥ ψ) i)
      (fun t => ψ i + ∫ s in (0 : ℝ)..t, ((-Complex.I) • (K s *ᵥ (V s *ᵥ ψ))) i)
      (uIcc 0 T) := by simpa only [uIcc_of_le hT] using! hEq
  refine ⟨?_,?_,?_⟩
  · exact continuousConversion_ac_congr (continuousConversion_ac_re_integral hI (ψ i))
      (fun t ht => congrArg Complex.re (hEq' ht))
  · exact continuousConversion_ac_congr (continuousConversion_ac_im_integral hI (ψ i))
      (fun t ht => congrArg Complex.im (hEq' ht))
  · have hp := continuousConversion_primitive_ae_deriv hI (ψ i)
    filter_upwards [hp,(show ∀ᵐ t : ℝ, t ≠ 0 from by simp [ae_iff]),
      (show ∀ᵐ t : ℝ, t ≠ T from by simp [ae_iff])] with t ht ht0 htT hmem
    have hinner : t ∈ Ioo 0 T :=
      ⟨lt_of_le_of_ne hmem.1 ht0.symm,lt_of_le_of_ne hmem.2 htT⟩
    apply (ht (uIcc_of_le hT ▸ hmem)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hinner.1 hinner.2] with u hu
    exact hEq u ⟨hu.1.le,hu.2.le⟩
set_option maxHeartbeats 600000 in

theorem continuousConversion_source_pair_integral {H : Type} [Fintype H] [DecidableEq H]
    (K U V : ℝ → Matrix H H ℂ) (A B : Matrix H H ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hK : IntervalIntegrable K volume 0 T) (hHerm : ∀ t ∈ Icc 0 T, (K t).IsHermitian)
    (hU : sourceVolterra (fun t => K t + A) T U)
    (hV : sourceVolterra (fun t => K t + B) T V) (ψ φ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (U T *ᵥ ψ) (V T *ᵥ φ) - Qatlib.Foundations.PureStateMath.Inner ψ φ =
      ∫ s in (0 : ℝ)..T, Complex.I *
        (Qatlib.Foundations.PureStateMath.Inner (A *ᵥ (U s *ᵥ ψ)) (V s *ᵥ φ) - Qatlib.Foundations.PureStateMath.Inner (U s *ᵥ ψ) (B *ᵥ (V s *ᵥ φ))) := by
  have hKA : IntervalIntegrable (fun t => K t + A) volume 0 T :=
    hK.add (continuous_const.intervalIntegrable 0 T)
  have hKB : IntervalIntegrable (fun t => K t + B) volume 0 T :=
    hK.add (continuous_const.intervalIntegrable 0 T)
  have hRegU := fun i => continuousConversion_source_state_regularity _ U T hT hKA hU ψ i
  have hRegV := fun i => continuousConversion_source_state_regularity _ V T hT hKB hV φ i
  obtain ⟨hACr,hACi⟩ := continuousConversion_inner_ac
    (fun i => ⟨(hRegU i).1,(hRegU i).2.1⟩) (fun i => ⟨(hRegV i).1,(hRegV i).2.1⟩)
  have hUcont := continuousConversion_mulVec_continuousOn hU.2.1 (continuousOn_const (c := ψ))
  have hVcont := continuousConversion_mulVec_continuousOn hV.2.1 (continuousOn_const (c := φ))
  have hAcont := continuousConversion_mulVec_continuousOn (continuousOn_const (c := A)) hUcont
  have hBcont := continuousConversion_mulVec_continuousOn (continuousOn_const (c := B)) hVcont
  have hIntCont := (continuousOn_const (c := Complex.I)).mul
    ((continuousConversion_inner_continuousOn hAcont hVcont).sub
      (continuousConversion_inner_continuousOn hUcont hBcont))
  have hInt := hIntCont.intervalIntegrable_of_Icc (μ := volume) hT
  have hAEU : ∀ᵐ t, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun t => (U t *ᵥ ψ) i)
        (((-Complex.I) • ((K t + A) *ᵥ (U t *ᵥ ψ))) i) t :=
    ae_all_iff.mpr (fun i => (hRegU i).2.2)
  have hAEV : ∀ᵐ t, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun t => (V t *ᵥ φ) i)
        (((-Complex.I) • ((K t + B) *ᵥ (V t *ᵥ φ))) i) t :=
    ae_all_iff.mpr (fun i => (hRegV i).2.2)
  have hDer : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (fun t => Qatlib.Foundations.PureStateMath.Inner (U t *ᵥ ψ) (V t *ᵥ φ))
        (Complex.I * (Qatlib.Foundations.PureStateMath.Inner (A *ᵥ (U t *ᵥ ψ)) (V t *ᵥ φ) -
          Qatlib.Foundations.PureStateMath.Inner (U t *ᵥ ψ) (B *ᵥ (V t *ᵥ φ)))) t := by
    filter_upwards [hAEU,hAEV] with t htU htV ht
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using! ht
    have hd := continuousConversion_inner_deriv (fun i => htU i ht') (fun i => htV i ht')
    rw [Matrix.add_mulVec,Matrix.add_mulVec,
      continuousConversion_driver_cancellation (K t) (hHerm t ht')] at hd
    exact hd
  have he := continuousConversion_complex_ftc hACr hACi hInt hDer
  rw [hU.1,hV.1,Matrix.one_mulVec] at he
  simpa only [Matrix.one_mulVec,Pi.mul_apply,Pi.sub_apply] using! he.symm
end
set_option maxHeartbeats 300000 in
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option maxHeartbeats 400000 in
open Qatlib.Concepts.ConversionCore.WitnessCompile Matrix
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.ConversionCore.WitnessCompile Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.ModelSemantics Qatlib.Concepts.QueryComplexity.StateConversion
open MeasureTheory Set Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator Topology
set_option maxHeartbeats 600000 in
noncomputable section

theorem continuousConversion_source_log_local {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (x y : X)
    (j : Fin (n+1)) (hsym : sourcePaddedSymbol input x j = sourcePaddedSymbol input y j) :
    Qatlib.Foundations.PureStateMath.Inner (fun p : Fin (q+1) × W => (sourceLogOracle input x *ᵥ ψ x) ((j,p.1),p.2))
        (fun p => ψ y ((j,p.1),p.2)) =
    Qatlib.Foundations.PureStateMath.Inner (fun p : Fin (q+1) × W => ψ x ((j,p.1),p.2))
        (fun p => (sourceLogOracle input y *ᵥ ψ y) ((j,p.1),p.2)) := by
  have hU : sourceValueQuery (sourcePaddedSymbol input x j) ∈ Matrix.unitaryGroup (Fin (q+1)) ℂ :=
    permMatrix_unitary_of_injective (by intro a b h; exact add_right_cancel h)
  have hL := (sourceLog_hermitian_norm _ _ hU).1
  simp only [Qatlib.Foundations.PureStateMath.inner_apply,Fintype.sum_prod_type]
  simp_rw [continuousConversion_log_action,← hsym]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact continuousConversion_hermitian_pair _ hL _ _
end
noncomputable section

theorem continuousConversion_source_generator_eq {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1))
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (x y : X) :
    Complex.I * (Qatlib.Foundations.PureStateMath.Inner (sourceLogOracle input x *ᵥ ψ x) (ψ y) -
      Qatlib.Foundations.PureStateMath.Inner (ψ x) (sourceLogOracle input y *ᵥ ψ y)) =
    continuousConversionTangent (continuousConversion_source_slice ψ)
      (continuousConversion_source_slice (fun x => sourceLogOracle input x *ᵥ ψ x)) x y := by
  have hfull : Complex.I * (Qatlib.Foundations.PureStateMath.Inner (sourceLogOracle input x *ᵥ ψ x) (ψ y) -
      Qatlib.Foundations.PureStateMath.Inner (ψ x) (sourceLogOracle input y *ᵥ ψ y)) =
      ∑ j : Fin (n+1), Complex.I *
        (Qatlib.Foundations.PureStateMath.Inner (fun p : Fin (q+1) × W => (sourceLogOracle input x *ᵥ ψ x) ((j,p.1),p.2))
          (fun p => ψ y ((j,p.1),p.2)) -
        Qatlib.Foundations.PureStateMath.Inner (fun p : Fin (q+1) × W => ψ x ((j,p.1),p.2))
          (fun p => (sourceLogOracle input y *ᵥ ψ y) ((j,p.1),p.2))) := by
    simp only [Qatlib.Foundations.PureStateMath.inner_apply,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]
  rw [hfull,Fin.sum_univ_castSucc]
  have hidle := continuousConversion_source_log_local input ψ x y (Fin.last n)
    (by simp [sourcePaddedSymbol])
  rw [hidle,sub_self,mul_zero,add_zero]
  rfl
end
noncomputable section

theorem continuousConversion_inner_neg_left {H : Type} [Fintype H] (ψ φ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (-ψ) φ = -Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simpa only [neg_one_smul,star_neg,star_one,neg_one_mul] using!
    continuousConversion_inner_smul_left (-1 : ℂ) ψ φ
end
noncomputable section

theorem continuousConversion_inner_neg_right {H : Type} [Fintype H] (ψ φ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner ψ (-φ) = -Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  simpa only [neg_one_smul,neg_one_mul] using!
    continuousConversion_inner_smul_right (-1 : ℂ) ψ φ
end
noncomputable section

theorem continuousConversion_source_signed_cert {X W : Type} [Fintype W] [DecidableEq W]
    {n q : ℕ} (input : X → Fin n → Fin (q+1)) (adj : Bool)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    gramFilteredCert (fun x y => Complex.I *
      (Qatlib.Foundations.PureStateMath.Inner ((if adj then -sourceLogOracle input x else sourceLogOracle input x) *ᵥ ψ x) (ψ y) -
       Qatlib.Foundations.PureStateMath.Inner (ψ x) ((if adj then -sourceLogOracle input y else sourceLogOracle input y) *ᵥ ψ y)))
      (sourceAlphabetDelta input) (1 + Real.pi ^ 2) := by
  have hc := continuousConversion_source_tangent_cert input ψ hψ
  cases adj
  · simpa only [Bool.false_eq_true,ite_false,continuousConversion_source_generator_eq] using! hc
  · have he : (fun x y => Complex.I *
        (Qatlib.Foundations.PureStateMath.Inner (-sourceLogOracle input x *ᵥ ψ x) (ψ y) -
          Qatlib.Foundations.PureStateMath.Inner (ψ x) (-sourceLogOracle input y *ᵥ ψ y))) =
        -(continuousConversionTangent (continuousConversion_source_slice ψ)
          (continuousConversion_source_slice (fun x => sourceLogOracle input x *ᵥ ψ x))) := by
      ext x y
      rw [Matrix.neg_mulVec,Matrix.neg_mulVec,continuousConversion_inner_neg_left,
        continuousConversion_inner_neg_right]
      change _ = -_
      rw [← continuousConversion_source_generator_eq]
      ring
    simpa [he] using! gramFilteredCert_neg hc
end
noncomputable section
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in

theorem continuousConversion_source_evolve_distance {X W : Type} [Fintype X] [DecidableEq X]
    [Fintype W] [DecidableEq W] {n q : ℕ}
    (input : X → Fin n → Fin (q+1))
    (K : ℝ → Matrix ((Fin (n+1) × Fin (q+1)) × W) ((Fin (n+1) × Fin (q+1)) × W) ℂ)
    (T : ℝ) (adj : Bool) (hT : 0 ≤ T)
    (hKi : ∀ i j, IntervalIntegrable (fun t => K t i j) volume 0 T)
    (hKh : ∀ t ∈ Icc 0 T, (K t).IsHermitian)
    (ψ : X → QState ((Fin (n+1) × Fin (q+1)) × W)) (hψ : ∀ x, Normalized (ψ x)) :
    sourceRectValue (gramStateMatrix
      (fun x => sourceVolterraMatrix (fun t => K t +
        (if adj then -sourceLogOracle input x else sourceLogOracle input x)) T *ᵥ ψ x) -
      gramStateMatrix ψ) (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1 + Real.pi^2)*T) := by
  let O := fun x => if adj then -sourceLogOracle (W := W) input x else sourceLogOracle input x
  have hK := sourceVolterra_matrix_integrable _ K T hKi
  have hOi (x : X) : ∀ i j, IntervalIntegrable (fun t => (K t + O x) i j) volume 0 T := by
    intro i j
    exact (hKi i j).add (continuous_const.intervalIntegrable 0 T)
  have hOh (x : X) : (O x).IsHermitian := by
    dsimp only [O]
    split
    · exact (sourceLogOracle_hermitian_norm X W input x).1.neg
    · exact (sourceLogOracle_hermitian_norm X W input x).1
  have hex (x : X) := sourceVolterra_exists _ (fun t => K t + O x) T hT (hOi x)
    (fun t ht => (hKh t ht).add (hOh x))
  choose U hU hUunit using hex
  let states := fun t x => U x t *ᵥ ψ x
  let D : ℝ → Matrix X X ℂ := fun t x y => Complex.I *
    (Qatlib.Foundations.PureStateMath.Inner (O x *ᵥ states t x) (states t y) - Qatlib.Foundations.PureStateMath.Inner (states t x) (O y *ᵥ states t y))
  have hStates (x : X) : ContinuousOn (fun t => states t x) (Icc 0 T) :=
    continuousConversion_mulVec_continuousOn (hU x).2.1 continuousOn_const
  have hDcont : ContinuousOn D (Icc 0 T) := by
    apply continuousOn_pi.mpr
    intro x
    apply continuousOn_pi.mpr
    intro y
    exact continuousOn_const.mul
      ((continuousConversion_inner_continuousOn
          (continuousConversion_mulVec_continuousOn continuousOn_const (hStates x)) (hStates y)).sub
        (continuousConversion_inner_continuousOn (hStates x)
          (continuousConversion_mulVec_continuousOn continuousOn_const (hStates y))))
  have hDI := hDcont.intervalIntegrable_of_Icc (μ := volume) hT
  have hCert (t : ℝ) (ht : t ∈ Icc 0 T) :
      gramFilteredCert (D t) (sourceAlphabetDelta input) (1 + Real.pi^2) :=
    continuousConversion_source_signed_cert input adj (states t)
      (fun x => normalized_applyGate (hUunit x t ht) (hψ x))
  have hBound := continuousConversion_filtered_integral (sourceAlphabetDelta input) D T
    (1 + Real.pi^2) hT (by positivity) hDI hCert
  have hGram : gramStateMatrix (states T) - gramStateMatrix ψ = ∫ t in (0 : ℝ)..T,D t := by
    ext x y
    have he := continuousConversion_source_pair_integral K (U x) (U y) (O x) (O y) T hT hK hKh
      (hU x) (hU y) (ψ x) (ψ y)
    have hEntry := (sourceMatrixEntryCLM X x y).intervalIntegral_comp_comm hDI
    exact he.trans hEntry
  have hEndpoint (x : X) : sourceVolterraMatrix (fun t => K t + O x) T = U x T :=
    sourceVolterraMatrix_eq _ T hT (hOi x) (U x) (hU x)
  have hResult : sourceRectValue (gramStateMatrix (states T) - gramStateMatrix ψ)
      (sourceAlphabetDelta input) ≤ ENNReal.ofReal ((1 + Real.pi^2)*T) := by
    rw [sourceSquareValue_eq,hGram]
    exact hBound
  simpa only [states, ← hEndpoint] using! hResult
end
end Qatlib.Concepts.ConversionCore.WitnessCompile
