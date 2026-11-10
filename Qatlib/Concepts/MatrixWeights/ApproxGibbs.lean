/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationSharedDefs
import QuantumInfo.ForMathlib.HermitianMat.CFC
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.ConeSeparation
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.MatrixWeights.ApproxGibbs

theorem exp_log_mat {n : ℕ} (A : HermitianMat (Fin n) ℂ) (h : A.mat.PosDef) :
    (HermitianMat.exp (HermitianMat.log A)).mat = A.mat := by
  have hcomp : (HermitianMat.exp (HermitianMat.log A)) = A.cfc (Real.exp ∘ Real.log) := by
    unfold HermitianMat.exp HermitianMat.log
    rw [← HermitianMat.cfc_comp]
  have hcongr : A.cfc (Real.exp ∘ Real.log) = A.cfc id := by
    apply HermitianMat.cfc_congr
    intro x hx
    have hpos : x ∈ Set.Ioi (0 : ℝ) :=
      HermitianMat.Matrix.PosDef.spectrum_subset_Ioi h hx
    exact Real.exp_log hpos
  rw [hcomp, hcongr, HermitianMat.cfc_id]

theorem gt_gap_nonneg {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    0 ≤ gtHermitianGap H K := by
  unfold gtHermitianGap
  have :=
      Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential n H K hH hK
  linarith

theorem log_input_gt_le {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    logInputGT A B ≤ (Matrix.trace (A.mat * B.mat)).re := by
  have hgt : logInputGT A B ≤
      (Matrix.trace
        (NormedSpace.exp (spectralLog A) * NormedSpace.exp (spectralLog B))).re :=
    Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential n
      (spectralLog A) (spectralLog B) (HermitianMat.log A).H (HermitianMat.log B).H
  have hbridgeA : NormedSpace.exp (spectralLog A) = (HermitianMat.log A).exp.mat :=
    (Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat (HermitianMat.log A)).symm
  have hbridgeB : NormedSpace.exp (spectralLog B) = (HermitianMat.log B).exp.mat :=
    (Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat (HermitianMat.log B)).symm
  rw [hbridgeA, hbridgeB, exp_log_mat A hA, exp_log_mat B hB] at hgt
  exact hgt

theorem mat_regularized {n : ℕ} (A : HermitianMat (Fin n) ℂ) (ε : ℝ) :
    (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat
      = A.mat + ε • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [HermitianMat.mat_add, HermitianMat.mat_smul, HermitianMat.mat_one]

theorem posDef_regularized {n : ℕ} (A : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat.PosDef := by
  rw [mat_regularized]
  refine Matrix.PosDef.posSemidef_add hA ?_
  exact Matrix.PosDef.smul (α := ℝ) Matrix.PosDef.one hε

theorem regularized_gt_le {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    psdRegularizedGT A B ε ≤ psdRegularizedProductTrace A.mat B.mat ε := by
  have hA' : (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat.PosDef :=
    posDef_regularized A hA hε
  have hB' : (B + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat.PosDef :=
    posDef_regularized B hB hε
  have h := log_input_gt_le (A + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ))
    (B + (ε : ℝ) • (1 : HermitianMat (Fin n) ℂ)) hA' hB'
  rw [mat_regularized, mat_regularized] at h
  exact h

theorem gt_trace_exp_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    0 ≤ (Matrix.trace (NormedSpace.exp H)).re := by
  have h : 0 ≤ (HermitianMat.exp (⟨H, hH⟩ : HermitianMat (Fin n) ℂ)).trace :=
    HermitianMat.trace_nonneg (HermitianMat.exp_nonneg _)
  rw [HermitianMat.trace_eq_re_trace, Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat,
    HermitianMat.mat_mk] at h
  exact h

theorem gt_trace_exp_pos {n : ℕ} (hn : 0 < n) (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) :
    0 < (Matrix.trace (NormedSpace.exp H)).re := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : 0 < (HermitianMat.exp (⟨H, hH⟩ : HermitianMat (Fin n) ℂ)).trace :=
    HermitianMat.trace_pos (HermitianMat.exp_pos _)
  rw [HermitianMat.trace_eq_re_trace, Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat,
    HermitianMat.mat_mk] at h
  exact h

theorem regularized_gt_nonneg {n : ℕ} (A B : HermitianMat (Fin n) ℂ) (ε : ℝ) :
    0 ≤ psdRegularizedGT A B ε := by
  unfold psdRegularizedGT logInputGT spectralLog
  refine gt_trace_exp_nonneg _ ?_
  exact (HermitianMat.log _).H.add (HermitianMat.log _).H

theorem trace_exp_monotone {n : ℕ} {H K : HermitianMat (Fin n) ℂ} (h : H ≤ K) :
    (Matrix.trace (NormedSpace.exp H.mat)).re ≤
      (Matrix.trace (NormedSpace.exp K.mat)).re := by
  have hsub : H.mat = K.mat + (H - K).mat := by
    rw [HermitianMat.mat_sub]
    abel
  have hgt := Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential n
    K.mat (H - K).mat K.H (H - K).H
  rw [← hsub] at hgt
  have hle : (H - K).exp ≤ (1 : HermitianMat (Fin n) ℂ) := by
    have h0 : (H - K) ≤ (0 : HermitianMat (Fin n) ℂ) := by
      rw [HermitianMat.le_iff]
      have := HermitianMat.le_iff.mp h
      simp [HermitianMat.mat_sub] at this ⊢
      exact this
    have h1 : (H - K).exp ≤ (0 : HermitianMat (Fin n) ℂ).exp :=
      HermitianMat.cfc_le_cfc_of_commute Real.exp Real.exp_monotone
        (Commute.zero_right (H - K).mat) h0
    have h2 : (0 : HermitianMat (Fin n) ℂ).exp = 1 := by
      show (0 : HermitianMat (Fin n) ℂ).cfc Real.exp = 1
      rw [HermitianMat.cfc_apply_zero, Real.exp_zero, one_smul]
    rw [h2] at h1
    exact h1
  have hP : 0 ≤ K.exp := HermitianMat.exp_nonneg K
  have hQ : 0 ≤ (1 : HermitianMat (Fin n) ℂ) - (H - K).exp :=
    HermitianMat.zero_le_iff.mpr (HermitianMat.le_iff.mp hle)
  have htrace : 0 ≤ (Matrix.trace (K.exp.mat * ((1 : HermitianMat (Fin n) ℂ) - (H - K).exp).mat)).re :=
    HermitianMat.inner_ge_zero hP hQ
  have hmuleq : K.exp.mat * ((1 : HermitianMat (Fin n) ℂ) - (H - K).exp).mat
      = K.exp.mat - K.exp.mat * (H - K).exp.mat := by
    rw [HermitianMat.mat_sub, HermitianMat.mat_one, Matrix.mul_sub, Matrix.mul_one]
  have hre : 0 ≤ (Matrix.trace K.exp.mat).re
      - (Matrix.trace (K.exp.mat * (H - K).exp.mat)).re := by
    rw [hmuleq, Matrix.trace_sub, Complex.sub_re] at htrace
    exact htrace
  have hkey : (Matrix.trace (NormedSpace.exp K.mat * NormedSpace.exp (H - K).mat)).re ≤
      (Matrix.trace (NormedSpace.exp K.mat)).re := by
    rw [← Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat K,
      ← Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat (H - K)]
    linarith
  exact hgt.trans hkey

theorem logInputGT_mono {n : ℕ} {A A' B B' : HermitianMat (Fin n) ℂ}
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) (hAA' : A ≤ A') (hBB' : B ≤ B') :
    logInputGT A B ≤ logInputGT A' B' := by
  have hsum : A.log + B.log ≤ A'.log + B'.log :=
    add_le_add (HermitianMat.log_mono hA hAA') (HermitianMat.log_mono hB hBB')
  have h2 : spectralLog A + spectralLog B = (A.log + B.log).mat := by
    simp [spectralLog, HermitianMat.mat_add]
  have h3 : spectralLog A' + spectralLog B' = (A'.log + B'.log).mat := by
    simp [spectralLog, HermitianMat.mat_add]
  unfold logInputGT
  rw [h2, h3]
  exact trace_exp_monotone hsum

theorem psdRegularizedGT_monotoneOn {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) :
    MonotoneOn (psdRegularizedGT A B) (Set.Ioi (0:ℝ)) := by
  intro ε1 h1 ε2 h2 hle
  have hε1 : 0 < ε1 := Set.mem_Ioi.mp h1
  have hε2 : 0 < ε2 := Set.mem_Ioi.mp h2
  have hmonoA : A + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)
      ≤ A + (ε2:ℝ) • (1 : HermitianMat (Fin n) ℂ) := by
    rw [HermitianMat.le_iff]
    have hsub : (A + (ε2:ℝ) • (1 : HermitianMat (Fin n) ℂ))
        - (A + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ))
        = ((ε2 - ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)) := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
    rw [hsub, HermitianMat.mat_smul, HermitianMat.mat_one]
    exact Matrix.PosSemidef.rsmul Matrix.PosSemidef.one (sub_nonneg.mpr hle)
  have hmonoB : B + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)
      ≤ B + (ε2:ℝ) • (1 : HermitianMat (Fin n) ℂ) := by
    rw [HermitianMat.le_iff]
    have hsub : (B + (ε2:ℝ) • (1 : HermitianMat (Fin n) ℂ))
        - (B + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ))
        = ((ε2 - ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)) := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
    rw [hsub, HermitianMat.mat_smul, HermitianMat.mat_one]
    exact Matrix.PosSemidef.rsmul Matrix.PosSemidef.one (sub_nonneg.mpr hle)
  have hposA : (A + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat.PosDef :=
    posDef_regularized A hA hε1
  have hposB : (B + (ε1:ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat.PosDef :=
    posDef_regularized B hB hε1
  exact logInputGT_mono hposA hposB hmonoA hmonoB

theorem psdRegularizedProductTrace_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    psdRegularizedProductTrace A B ε =
      (Matrix.trace (A * B)).re + ε * (Matrix.trace (A + B)).re + ε ^ 2 * (n : ℝ) := by
  have hmul : (A + ε • (1 : Matrix (Fin n) (Fin n) ℂ))
      * (B + ε • (1 : Matrix (Fin n) (Fin n) ℂ))
      = A * B + ε • (A + B) + (ε ^ 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, smul_smul, ← pow_two]
    have hstep : (A * B + ε • A) + (ε • B + (ε ^ 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        = A * B + (ε • A + ε • B) + (ε ^ 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ac_rfl
    rw [hstep, ← smul_add]
  unfold psdRegularizedProductTrace
  rw [hmul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one]
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Fintype.card_fin]
  simp

theorem regularized_product_trace_tendsto {n : ℕ} (A B : HermitianMat (Fin n) ℂ) :
    Filter.Tendsto (fun ε : ℝ => psdRegularizedProductTrace A.mat B.mat ε)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((Matrix.trace (A.mat * B.mat)).re)) := by
  set P : ℝ → ℝ := fun ε => (Matrix.trace (A.mat * B.mat)).re
      + ε * (Matrix.trace (A.mat + B.mat)).re + ε ^ 2 * (n : ℝ) with hP
  have heq : (fun ε : ℝ => psdRegularizedProductTrace A.mat B.mat ε) = P := by
    funext ε
    rw [hP]
    exact psdRegularizedProductTrace_eq A.mat B.mat ε
  have hcont : Continuous P := by
    rw [hP]
    exact (continuous_const.add (continuous_id.mul continuous_const)).add
      ((continuous_id.pow 2).mul continuous_const)
  have h0 : P 0 = (Matrix.trace (A.mat * B.mat)).re := by
    rw [hP]
    ring
  have h := (hcont.tendsto (0:ℝ)).mono_left
    (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi (0:ℝ)))
  rw [h0] at h
  rw [heq]
  exact h

theorem psd_inf_nonneg {n : ℕ} (A B : HermitianMat (Fin n) ℂ) :
    0 ≤ psdGTInfimum A B := by
  unfold psdGTInfimum
  refine le_ciInf (c := (0:ℝ)) ?_
  intro ε
  show (0:ℝ) ≤ ⨅ (h : ε ∈ Set.Ioi (0:ℝ)), psdRegularizedGT A B ε
  rcases le_or_gt ε 0 with hε | hε
  · rw [ciInf_neg (show ¬ (ε ∈ Set.Ioi (0:ℝ)) by simpa using! hε.not_gt)]
    simp
  · rw [ciInf_pos (show ε ∈ Set.Ioi (0:ℝ) by simpa using! hε)]
    exact regularized_gt_nonneg A B ε

theorem psdGTInfimum_le_regularized {n : ℕ} (A B : HermitianMat (Fin n) ℂ) {ε : ℝ}
    (hε : 0 < ε) : psdGTInfimum A B ≤ psdRegularizedGT A B ε := by
  unfold psdGTInfimum
  have hg : ∀ t : ℝ, (0:ℝ) ≤ ⨅ (h : t ∈ Set.Ioi (0:ℝ)), psdRegularizedGT A B t := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · rw [ciInf_neg (show ¬ (t ∈ Set.Ioi (0:ℝ)) by simpa using! ht.not_gt)]
      simp
    · rw [ciInf_pos (show t ∈ Set.Ioi (0:ℝ) by simpa using! ht)]
      exact regularized_gt_nonneg A B t
  have hbdd : BddBelow
      (Set.range fun t : ℝ => (⨅ (h : t ∈ Set.Ioi (0:ℝ)), psdRegularizedGT A B t)) :=
    ⟨0, fun _x hx => by obtain ⟨t, rfl⟩ := hx; exact hg t⟩
  have h := ciInf_le (f := fun t : ℝ => (⨅ (h : t ∈ Set.Ioi (0:ℝ)), psdRegularizedGT A B t))
    hbdd ε
  rw [ciInf_pos (show ε ∈ Set.Ioi (0:ℝ) by simpa using! hε)] at h
  exact h

theorem psd_inf_le_product {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) :
    psdGTInfimum A B ≤ (Matrix.trace (A.mat * B.mat)).re := by
  have hle : ∀ ε : ℝ, ε ∈ Set.Ioi (0:ℝ) →
      psdGTInfimum A B ≤ psdRegularizedProductTrace A.mat B.mat ε := by
    intro ε hε
    exact (psdGTInfimum_le_regularized A B (Set.mem_Ioi.mp hε)).trans
      (regularized_gt_le A B hA hB (Set.mem_Ioi.mp hε))
  have hlim := regularized_product_trace_tendsto A B
  haveI : Filter.NeBot (nhdsWithin (0:ℝ) (Set.Ioi 0)) := inferInstance
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      psdGTInfimum A B ≤ psdRegularizedProductTrace A.mat B.mat ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hle ε hε
  exact ge_of_tendsto hlim hev

theorem psdGTInfimum_eq_trueInf_inf_sInf_empty {n : ℕ} (A B : HermitianMat (Fin n) ℂ) :
    psdGTInfimum A B
      = (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε) ⊓ sInf (∅ : Set ℝ) := by
  unfold psdGTInfimum
  refine cbiInf_eq_of_not_forall
    (p := fun ε : ℝ => ε ∈ Set.Ioi (0:ℝ))
    (f := fun x : Set.Ioi (0:ℝ) => psdRegularizedGT A B x.val) ?_
  intro H
  have h1 := H (-1)
  norm_num at h1

theorem psd_trueInf_eq_sInf {n : ℕ} (A B : HermitianMat (Fin n) ℂ) :
    (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε)
      = sInf (psdRegularizedGT A B '' Set.Ioi (0:ℝ)) :=
  (sInf_image' (f := psdRegularizedGT A B) (s := Set.Ioi (0:ℝ))).symm

theorem psd_regularized_gt_tendsto_trueInf {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) :
    Filter.Tendsto (fun ε : ℝ => psdRegularizedGT A B ε)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε)) := by
  have hmono : MonotoneOn (psdRegularizedGT A B) (Set.Ioi (0:ℝ)) :=
    psdRegularizedGT_monotoneOn A B hA hB
  have hbdd : BddBelow (psdRegularizedGT A B '' Set.Ioi (0:ℝ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨ε, -, rfl⟩
    exact regularized_gt_nonneg A B ε
  have h := MonotoneOn.tendsto_nhdsGT (f := psdRegularizedGT A B) (x := (0:ℝ)) hmono hbdd
  rw [psd_trueInf_eq_sInf A B]
  exact h

theorem commute_regularized {n : ℕ} {A B : HermitianMat (Fin n) ℂ}
    (h : Commute A.mat B.mat) (ε : ℝ) :
    Commute (A + (ε:ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat
      (B + (ε:ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat := by
  rw [mat_regularized, mat_regularized]
  have hcA : Commute A.mat (ε • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [show (ε : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) = (ε : ℂ) • 1 from rfl]
    exact Commute.smul_right (Commute.one_right A.mat) (ε : ℂ)
  have hcB : Commute B.mat (ε • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [show (ε : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) = (ε : ℂ) • 1 from rfl]
    exact Commute.smul_right (Commute.one_right B.mat) (ε : ℂ)
  have hcc : Commute (ε • (1 : Matrix (Fin n) (Fin n) ℂ))
      (ε • (1 : Matrix (Fin n) (Fin n) ℂ)) := Commute.refl _
  refine Commute.add_left (Commute.add_right h hcA) ?_
  exact Commute.add_right hcB.symm hcc

theorem regularized_product_trace_ge {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    (Matrix.trace (A.mat * B.mat)).re ≤ psdRegularizedProductTrace A.mat B.mat ε := by
  rw [psdRegularizedProductTrace_eq]
  have hreA : 0 ≤ (Matrix.trace A.mat).re :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hA)).1
  have hreB : 0 ≤ (Matrix.trace B.mat).re :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hB)).1
  have htr : (Matrix.trace (A.mat + B.mat)).re
      = (Matrix.trace A.mat).re + (Matrix.trace B.mat).re := by
    rw [Matrix.trace_add, Complex.add_re]
  have hs : 0 ≤ (Matrix.trace (A.mat + B.mat)).re := by rw [htr]; linarith
  have hε1 : 0 ≤ ε * (Matrix.trace (A.mat + B.mat)).re := mul_nonneg hε hs
  have hε2 : 0 ≤ ε ^ 2 * (n : ℝ) := by positivity
  linarith

theorem regularized_gt_eq_product_of_commute {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) {ε : ℝ} (hε : 0 < ε)
    (hcomm : Commute A.mat B.mat) :
    psdRegularizedGT A B ε = psdRegularizedProductTrace A.mat B.mat ε := by
  set Aε : HermitianMat (Fin n) ℂ := A + (ε:ℝ) • (1 : HermitianMat (Fin n) ℂ) with hAε
  set Bε : HermitianMat (Fin n) ℂ := B + (ε:ℝ) • (1 : HermitianMat (Fin n) ℂ) with hBε
  have hA'pos : Aε.mat.PosDef := by rw [hAε]; exact posDef_regularized A hA hε
  have hB'pos : Bε.mat.PosDef := by rw [hBε]; exact posDef_regularized B hB hε
  have hcomm' : Commute Aε.mat Bε.mat := by
    rw [hAε, hBε]
    exact commute_regularized hcomm ε
  have hlog : Commute (HermitianMat.log Aε).mat (HermitianMat.log Bε).mat :=
    Commute.log_right (Commute.log_left hcomm')
  have hgt := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_commuting_trace_potential n
    (spectralLog Aε) (spectralLog Bε) hlog
  unfold spectralLog at hgt
  rw [← Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat (HermitianMat.log Aε),
    exp_log_mat Aε hA'pos,
    ← Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_hermitian_exp_mat (HermitianMat.log Bε),
    exp_log_mat Bε hB'pos] at hgt
  rw [hAε, hBε, mat_regularized, mat_regularized] at hgt
  exact hgt

theorem psd_inf_commuting_trueInf {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) (hcomm : Commute A.mat B.mat) :
    (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε)
      = (Matrix.trace (A.mat * B.mat)).re := by
  haveI : Filter.NeBot (nhdsWithin (0:ℝ) (Set.Ioi 0)) := inferInstance
  have hbdd : BddBelow (Set.range fun ε : Set.Ioi (0:ℝ) => psdRegularizedGT A B ε) := by
    refine ⟨0, ?_⟩
    rintro x ⟨ε, rfl⟩
    exact regularized_gt_nonneg A B ε
  have h1 : (Matrix.trace (A.mat * B.mat)).re ≤ (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε) := by
    haveI : Nonempty (Set.Ioi (0:ℝ)) := ⟨⟨1, by norm_num⟩⟩
    refine le_ciInf (c := (Matrix.trace (A.mat * B.mat)).re) ?_
    intro ε
    rw [regularized_gt_eq_product_of_commute A B hA hB (Set.mem_Ioi.mp ε.2) hcomm]
    exact regularized_product_trace_ge A B hA hB (Set.mem_Ioi.mp ε.2).le
  have hle : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (⨅ t : Set.Ioi (0:ℝ), psdRegularizedGT A B t)
        ≤ psdRegularizedProductTrace A.mat B.mat ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h : (⨅ t : Set.Ioi (0:ℝ), psdRegularizedGT A B t) ≤ psdRegularizedGT A B ε :=
      ciInf_le_of_le hbdd ⟨ε, Set.mem_Ioi.mpr (Set.mem_Ioi.mp hε)⟩ le_rfl
    rw [regularized_gt_eq_product_of_commute A B hA hB (Set.mem_Ioi.mp hε) hcomm] at h
    exact h
  have h2 : (⨅ t : Set.Ioi (0:ℝ), psdRegularizedGT A B t)
      ≤ (Matrix.trace (A.mat * B.mat)).re :=
    ge_of_tendsto (regularized_product_trace_tendsto A B) hle
  exact le_antisymm h2 h1

theorem trace_cycle3 {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (A * B * C) = Matrix.trace (B * C * A) := by
  rw [mul_assoc, Matrix.trace_mul_comm]

theorem gap0_half_commutator_identity {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.trace (X ^ 2 * Y ^ 2)).re - (Matrix.trace ((X * Y) ^ 2)).re
      = -(1 / 2 : ℝ) * (Matrix.trace ((X * Y - Y * X) ^ 2)).re := by
  have htr : (X * Y - Y * X) ^ 2 =
      (X * Y) * (X * Y) - (X * Y) * (Y * X) - (Y * X) * (X * Y) + (Y * X) * (Y * X) := by
    noncomm_ring
  have h1 : Matrix.trace ((X * Y) * (X * Y)) = Matrix.trace ((X * Y) ^ 2) := by
    rw [pow_two]
  have h2 : Matrix.trace ((X * Y) * (Y * X)) = Matrix.trace (X ^ 2 * Y ^ 2) := by
    have e1 : (X * Y) * (Y * X) = X * Y ^ 2 * X := by noncomm_ring
    rw [e1, trace_cycle3 X (Y ^ 2) X]
    have e2 : Y ^ 2 * X * X = Y ^ 2 * X ^ 2 := by noncomm_ring
    rw [e2, Matrix.trace_mul_comm]
  have h3 : Matrix.trace ((Y * X) * (X * Y)) = Matrix.trace (X ^ 2 * Y ^ 2) := by
    have e1 : (Y * X) * (X * Y) = Y * X ^ 2 * Y := by noncomm_ring
    rw [e1, trace_cycle3 Y (X ^ 2) Y]
    have e2 : X ^ 2 * Y * Y = X ^ 2 * Y ^ 2 := by noncomm_ring
    rw [e2]
  have h4 : Matrix.trace ((Y * X) * (Y * X)) = Matrix.trace ((X * Y) ^ 2) := by
    have e1 : (Y * X) * (Y * X) = (Y * X) ^ 2 := by noncomm_ring
    rw [e1]
    exact (Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_mul_power_swap X Y 2).symm
  have hc : Matrix.trace (X ^ 2 * Y ^ 2) - Matrix.trace ((X * Y) ^ 2)
      = ((-(1 / 2 : ℝ) : ℂ)) * Matrix.trace ((X * Y - Y * X) ^ 2) := by
    rw [htr]
    simp only [Matrix.trace_add, Matrix.trace_sub, h1, h2, h3, h4]
    push_cast
    ring
  have hr := congrArg Complex.re hc
  simp only [Complex.sub_re] at hr
  have hscal : ((-(1 / 2 : ℝ) : ℂ)).re = -(1 / 2)
      ∧ ((-(1 / 2 : ℝ) : ℂ)).im = 0 := by norm_num
  rw [Complex.mul_re, hscal.1, hscal.2, zero_mul, sub_zero] at hr
  exact hr

theorem gap0_nonneg {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    0 ≤ (Matrix.trace (X ^ 2 * Y ^ 2)).re - (Matrix.trace ((X * Y) ^ 2)).re := by
  have h := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_dyadic_trace_power_le X Y hX hY 1
  simp only [pow_one] at h
  linarith

theorem commutator_skew {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Matrix.conjTranspose (X * Y - Y * X) = -(X * Y - Y * X) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  rw [hX.eq, hY.eq]
  noncomm_ring

theorem commutator_trace_sq {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Matrix.trace ((X * Y - Y * X) ^ 2)
      = -Matrix.trace (Matrix.conjTranspose (X * Y - Y * X) * (X * Y - Y * X)) := by
  have hskew := commutator_skew X Y hX hY
  have h1 : (X * Y - Y * X) ^ 2 = (X * Y - Y * X) * (X * Y - Y * X) := pow_two _
  rw [h1, hskew, neg_mul, Matrix.trace_neg]
  ring_nf

theorem gram_trace_zero {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (h : (Matrix.trace (Matrix.conjTranspose C * C)).re = 0) : C = 0 := by
  have hpsd : (Matrix.conjTranspose C * C).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self C
  have hherm : (Matrix.conjTranspose C * C).IsHermitian := hpsd.1
  have htrace : Matrix.trace (Matrix.conjTranspose C * C) = 0 := by
    have h' : RCLike.re (Matrix.trace (Matrix.conjTranspose C * C)) = 0 := h
    have hre := hherm.re_trace_eq_trace
    rw [h'] at hre
    simp only [map_zero] at hre
    exact hre.symm
  exact Matrix.conjTranspose_mul_self_eq_zero.1 (hpsd.trace_zero htrace)

theorem gap0_zero_iff_commute {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (Matrix.trace (X ^ 2 * Y ^ 2)).re = (Matrix.trace ((X * Y) ^ 2)).re ↔ Commute X Y := by
  constructor
  · intro h
    have hid := gap0_half_commutator_identity X Y
    have hzero : (Matrix.trace ((X * Y - Y * X) ^ 2)).re = 0 := by
      have hgap : (Matrix.trace (X ^ 2 * Y ^ 2)).re - (Matrix.trace ((X * Y) ^ 2)).re = 0 := by
        linarith
      rw [hid] at hgap
      linarith
    have hgram := commutator_trace_sq X Y hX hY
    rw [hgram] at hzero
    simp only [Complex.neg_re] at hzero
    have hgram0 : (Matrix.trace (Matrix.conjTranspose (X * Y - Y * X)
        * (X * Y - Y * X))).re = 0 := by linarith
    have hC : X * Y - Y * X = 0 := gram_trace_zero (X * Y - Y * X) hgram0
    show X * Y = Y * X
    exact sub_eq_zero.1 hC
  · intro h
    have hpow : (X * Y) ^ 2 = X ^ 2 * Y ^ 2 := by
      have e : X * Y * (X * Y) = X * X * (Y * Y) := by
        calc X * Y * (X * Y) = X * (Y * X) * Y := by noncomm_ring
          _ = X * (X * Y) * Y := by rw [← h]
          _ = X * X * (Y * Y) := by noncomm_ring
      rw [pow_two, pow_two, pow_two]
      exact e
    rw [hpow]

noncomputable def dyadicProduct {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (NormedSpace.exp (((2 ^ m : ℕ) : ℝ)⁻¹ • H) *
    NormedSpace.exp (((2 ^ m : ℕ) : ℝ)⁻¹ • K)) ^ (2 ^ m)

theorem exp_smul_pow {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (q : ℕ) :
    (NormedSpace.exp (s • H)) ^ q = NormedSpace.exp (((q : ℝ) * s) • H) := by
  have h := Qatlib.Concepts.LchsSimulation.LchsRep.imaginary_exp_power (-H) s q
  simp only [neg_smul, smul_neg, neg_neg] at h
  exact h

theorem exp_smul_hermitian {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian) (s : ℝ) : (NormedSpace.exp (s • H)).IsHermitian := by
  exact (hH.smul (by simp [IsSelfAdjoint])).exp

theorem dyadic_step_trace_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (k : ℕ) :
    (Matrix.trace ((X * Y) ^ (2 ^ (k + 1)))).re ≤
      (Matrix.trace ((X ^ 2 * Y ^ 2) ^ (2 ^ k))).re := by
  have hp : 0 < 2 ^ k := by positivity
  have hth := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_even_power_le (X * Y) (2 ^ k) hp
  have hgram : Matrix.conjTranspose (X * Y) * (X * Y) = Y * X ^ 2 * Y := by
    rw [Matrix.conjTranspose_mul, hX.eq, hY.eq, pow_two]
    noncomm_ring
  have ht : Matrix.trace ((Y * X ^ 2 * Y) ^ (2 ^ k)) =
      Matrix.trace ((X ^ 2 * Y ^ 2) ^ (2 ^ k)) := by
    rw [mul_assoc Y (X ^ 2) Y,
        Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_trace_mul_power_swap Y (X ^ 2 * Y)]
    congr 2
    noncomm_ring
  rw [hgram, ht] at hth
  have hn : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  rw [hn]
  exact (Complex.re_le_norm _).trans hth

theorem two_mul_inv_pow_succ (m : ℕ) :
    (((2 : ℕ) : ℝ) * (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹)) = (((2 ^ m : ℕ) : ℝ)⁻¹) := by
  have hp : (2:ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  push_cast
  rw [pow_succ]
  field_simp [hp]

theorem dyadic_trace_monotone {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (m : ℕ) :
    (Matrix.trace (dyadicProduct H K (m + 1))).re ≤
      (Matrix.trace (dyadicProduct H K m)).re := by
  have hX : (NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • H)).IsHermitian :=
    exp_smul_hermitian hH _
  have hY : (NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • K)).IsHermitian :=
    exp_smul_hermitian hK _
  have hstep := dyadic_step_trace_le
    (NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • H))
    (NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • K)) hX hY m
  have harith := two_mul_inv_pow_succ m
  have hpowH : NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • H) ^ 2
      = NormedSpace.exp (((2 ^ m : ℕ) : ℝ)⁻¹ • H) := by
    rw [exp_smul_pow, harith]
  have hpowK : NormedSpace.exp (((2 ^ (m + 1) : ℕ) : ℝ)⁻¹ • K) ^ 2
      = NormedSpace.exp (((2 ^ m : ℕ) : ℝ)⁻¹ • K) := by
    rw [exp_smul_pow, harith]
  dsimp [dyadicProduct] at hstep ⊢
  rw [hpowH, hpowK] at hstep
  exact hstep

theorem dyadicProduct_zero {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) :
    dyadicProduct H K 0 = NormedSpace.exp H * NormedSpace.exp K := by
  simp [dyadicProduct]

theorem exp_commute_iff {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Commute (NormedSpace.exp H) (NormedSpace.exp K) ↔ Commute H K := by
  have eH : ((HermitianMat.exp ⟨H, hH⟩ : HermitianMat (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = NormedSpace.exp H :=
    mmw_hermitian_exp_mat ⟨H, hH⟩
  have eK : ((HermitianMat.exp ⟨K, hK⟩ : HermitianMat (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = NormedSpace.exp K :=
    mmw_hermitian_exp_mat ⟨K, hK⟩
  refine ⟨fun h => ?_, fun h => Commute.exp h⟩
  rw [← eH, ← eK] at h
  have lH : (HermitianMat.exp ⟨H, hH⟩).log = (⟨H, hH⟩ : HermitianMat (Fin n) ℂ) := by
    unfold HermitianMat.exp HermitianMat.log
    rw [← HermitianMat.cfc_comp, Real.log_comp_exp, HermitianMat.cfc_id]
  have lK : (HermitianMat.exp ⟨K, hK⟩).log = (⟨K, hK⟩ : HermitianMat (Fin n) ℂ) := by
    unfold HermitianMat.exp HermitianMat.log
    rw [← HermitianMat.cfc_comp, Real.log_comp_exp, HermitianMat.cfc_id]
  have h1 : Commute ((HermitianMat.exp ⟨H, hH⟩).log : Matrix (Fin n) (Fin n) ℂ)
      ((HermitianMat.exp ⟨K, hK⟩).log : Matrix (Fin n) (Fin n) ℂ) :=
    (Commute.log_left h).log_right
  rw [lH, lK] at h1
  exact h1

theorem traceNorm_le_two_of_traceDistance {D : ℕ} (ρ σ : Operator D) {ξ : ℝ}
    (h : Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance ρ σ ≤ ξ) :
    Matrix.traceNorm (ρ - σ) ≤ 2 * ξ := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have h' : Matrix.traceNorm (ρ - σ) / 2 ≤ ξ := h
  have h3 : Matrix.traceNorm (ρ - σ) ≤ ξ * 2 := (div_le_iff₀ h2).mp h'
  linarith

theorem clause22 :
    ∀ (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) (σ : Operator D)
      (approx : ℕ → Operator D) (z ξ ζ : ℕ → ℝ),
    0 < D → 0 < η → η ≤ 1 →
    (∀ s < T, (M s).IsHermitian ∧ ‖M s‖ ≤ 1) →
    IsDensityOperator σ →
    (∀ t < T, IsDensityOperator (approx t)) →
    (∀ t < T, 0 ≤ ξ t ∧ 0 ≤ ζ t) →
    (∀ t < T, Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance (approx t) (Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D M η t) ≤ ξ t) →
    (∀ t < T, |z t - (Matrix.trace (M t * approx t)).re| ≤ ζ t) →
    ((∑ t ∈ Finset.range T, z t) - ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re ≤
        η * T + Real.log D / η + ∑ t ∈ Finset.range T, (2 * ξ t + ζ t))
    ∧ ((∑ t ∈ Finset.range T, (Matrix.trace (M t * approx t)).re) -
        ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re ≤
        η * T + Real.log D / η + ∑ t ∈ Finset.range T, (2 * ξ t))
    ∧ (∀ (Ω : Type) (_ : Fintype Ω) (S : FiniteSupportSpace Ω) (Z : ℕ → Ω → ℝ),
        (∀ t < T, ∀ ω : Ω, |Z t ω - (Matrix.trace (M t * approx t)).re| ≤ ζ t) →
        ((∑ t ∈ Finset.range T, ∑ ω : Ω, S.prob ω * Z t ω) -
            ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re ≤
          η * T + Real.log D / η + ∑ t ∈ Finset.range T, (2 * ξ t + ζ t))) := by
  intro D T M η σ approx z ξ ζ hD hη hη1 hM hσ happ hxi hdist hz

  let M' : ℕ → Operator D := fun t => if t < T then M t else 0
  have hM'eq : ∀ t < T, M' t = M t := fun t ht => if_pos ht
  have hM'glob : ∀ t, (M' t).IsHermitian ∧ ‖M' t‖ ≤ 1 := by
    intro t
    by_cases ht : t < T
    · rw [hM'eq t ht]
      exact hM t ht
    · have h0 : M' t = 0 := if_neg ht
      rw [h0]
      exact ⟨Matrix.isHermitian_zero, by simp⟩
  have hweight : ∀ t < T,
      (∑ s ∈ Finset.range t, M' s) = (∑ s ∈ Finset.range t, M s) := by
    intro t ht
    apply Finset.sum_congr rfl
    intro s hs
    have hst : s < T := lt_of_lt_of_le (Finset.mem_range.mp hs) (Nat.le_of_lt ht)
    exact hM'eq s hst
  have hstate_eq : ∀ t < T, Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D M' η t
      = Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D M η t := by
    intro t ht
    simp only [Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState,
        Qatlib.Concepts.MatrixWeights.WeightsCore.mmwWeight, hweight t ht]

  have hstate : ∀ t ∈ Finset.range T,
      (approx t - Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D M' η t).traceNorm ≤ 2 * ξ t := by
    intro t ht
    have hlt : t < T := Finset.mem_range.mp ht
    have h := hdist t hlt
    rw [hstate_eq t hlt]
    exact traceNorm_le_two_of_traceDistance _ _ h

  have hrecord : ∀ t ∈ Finset.range T,
      |z t - (Matrix.trace (M' t * approx t)).re| ≤ ζ t := by
    intro t ht
    have hlt : t < T := Finset.mem_range.mp ht
    rw [hM'eq t hlt]
    exact hz t hlt
  have hrec := Qatlib.Concepts.SdpDuality.ConeSeparation.recorded_history_regret
    D T M' approx z (fun t => 2 * ξ t) ζ η σ hD hη hη1 hM'glob hσ hstate hrecord
  have hσsum : (∑ t ∈ Finset.range T, (Matrix.trace (M' t * σ)).re)
      = ∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hM'eq t (Finset.mem_range.mp ht)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hσsum] at hrec
    exact hrec
  · have hz0 : ∀ t ∈ Finset.range T,
        |(Matrix.trace (M t * approx t)).re - (Matrix.trace (M' t * approx t)).re| ≤ (0:ℝ) := by
      intro t ht
      rw [hM'eq t (Finset.mem_range.mp ht)]
      simp
    have hrec2 := Qatlib.Concepts.SdpDuality.ConeSeparation.recorded_history_regret
      D T M' approx (fun t => (Matrix.trace (M t * approx t)).re)
      (fun t => 2 * ξ t) (fun _ => (0:ℝ)) η σ hD hη hη1 hM'glob hσ hstate hz0
    rw [hσsum] at hrec2
    have hsum0 : (∑ t ∈ Finset.range T, (2 * ξ t + (0:ℝ)))
        = ∑ t ∈ Finset.range T, (2 * ξ t) := by
      apply Finset.sum_congr rfl
      intro t _
      simp
    rw [hsum0] at hrec2
    exact hrec2
  · intro Ω _inst S Z hZ
    have hzexp : ∀ t < T,
        |(∑ ω : Ω, S.prob ω * Z t ω) - (Matrix.trace (M t * approx t)).re| ≤ ζ t := by
      intro t ht
      have hrew : (∑ ω : Ω, S.prob ω * Z t ω) - (Matrix.trace (M t * approx t)).re
          = ∑ ω : Ω, S.prob ω * (Z t ω - (Matrix.trace (M t * approx t)).re) := by
        have hstep : (∑ ω : Ω, S.prob ω * (Z t ω - (Matrix.trace (M t * approx t)).re))
            = (∑ ω : Ω, S.prob ω * Z t ω)
              - (∑ ω : Ω, S.prob ω) * (Matrix.trace (M t * approx t)).re := by
          have hm : ∀ ω : Ω,
              S.prob ω * (Z t ω - (Matrix.trace (M t * approx t)).re)
              = S.prob ω * Z t ω - S.prob ω * (Matrix.trace (M t * approx t)).re := by
            intro ω
            ring
          conv_lhs => simp only [hm]
          simp only [Finset.sum_sub_distrib, Finset.sum_mul]
        rw [hstep, S.prob_sum, one_mul]
      rw [hrew]
      have habs := Finset.abs_sum_le_sum_abs
        (fun ω : Ω => S.prob ω * (Z t ω - (Matrix.trace (M t * approx t)).re)) Finset.univ
      refine le_trans habs ?_
      have hle : (∑ ω ∈ Finset.univ, |S.prob ω * (Z t ω - (Matrix.trace (M t * approx t)).re)|)
          ≤ ∑ ω ∈ Finset.univ, S.prob ω * ζ t := by
        apply Finset.sum_le_sum
        intro ω _
        rw [abs_mul, abs_of_nonneg (S.prob_nonneg ω)]
        exact mul_le_mul_of_nonneg_left (hZ t ht ω) (S.prob_nonneg ω)
      refine le_trans hle ?_
      rw [← Finset.sum_mul, S.prob_sum, one_mul]
    have hrec3 := Qatlib.Concepts.SdpDuality.ConeSeparation.recorded_history_regret
      D T M' approx (fun t => ∑ ω : Ω, S.prob ω * Z t ω)
      (fun t => 2 * ξ t) ζ η σ hD hη hη1 hM'glob hσ hstate
      (by
        intro t ht
        have hlt : t < T := Finset.mem_range.mp ht
        rw [hM'eq t hlt]
        exact hzexp t hlt)
    rw [hσsum] at hrec3
    exact hrec3

open Filter Topology

lemma dyadic_cast_ne_zero (k : ℕ) : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by
  have h : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  exact_mod_cast (ne_of_gt h)

lemma dyadic_exp_shift_left {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    NormedSpace.exp (-(1 / ((2 ^ k : ℕ) : ℝ)) • (‖H‖ • (1 : Operator n) - H))
      = Real.exp (-(‖H‖ * ((2 ^ k : ℕ) : ℝ)⁻¹)) •
        NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • H) := by
  have hsum : -(1 / ((2 ^ k : ℕ) : ℝ)) • (‖H‖ • (1 : Operator n) - H)
      = ((2 ^ k : ℕ) : ℝ)⁻¹ • H + (-(‖H‖ * ((2 ^ k : ℕ) : ℝ)⁻¹)) • (1 : Operator n) := by
    rw [one_div]
    module
  rw [hsum]
  exact Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_exp_scalar_shift n (((2 ^ k : ℕ) : ℝ)⁻¹ • H)
    (-(‖H‖ * ((2 ^ k : ℕ) : ℝ)⁻¹))

lemma dyadic_scalar_pow (a b : ℝ) (k : ℕ) :
    (Real.exp (-(a * ((2 ^ k : ℕ) : ℝ)⁻¹)) * Real.exp (-(b * ((2 ^ k : ℕ) : ℝ)⁻¹))) ^ (2 ^ k)
      = Real.exp (-(a + b)) := by
  have hne : ((2 ^ k : ℕ) : ℝ) ≠ 0 := dyadic_cast_ne_zero k
  have hadd : Real.exp (-(a * ((2 ^ k : ℕ) : ℝ)⁻¹)) * Real.exp (-(b * ((2 ^ k : ℕ) : ℝ)⁻¹))
      = Real.exp (-(a * ((2 ^ k : ℕ) : ℝ)⁻¹) + -(b * ((2 ^ k : ℕ) : ℝ)⁻¹)) :=
    (Real.exp_add _ _).symm
  rw [hadd, ← Real.exp_nat_mul]
  congr 1
  have ha : ((2 ^ k : ℕ) : ℝ) * (a * ((2 ^ k : ℕ) : ℝ)⁻¹) = a := by
    rw [← mul_assoc, mul_comm ((2 ^ k : ℕ) : ℝ) a, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hb : ((2 ^ k : ℕ) : ℝ) * (b * ((2 ^ k : ℕ) : ℝ)⁻¹) = b := by
    rw [← mul_assoc, mul_comm ((2 ^ k : ℕ) : ℝ) b, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [mul_add, mul_neg, mul_neg, ha, hb, neg_add]

theorem dyadicProduct_tendsto_exp {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Filter.Tendsto (fun m : ℕ => dyadicProduct H K m) Filter.atTop
      (𝓝 (NormedSpace.exp (H + K))) := by
  by_cases hn : n = 0
  · subst hn
    have hconst : (fun m : ℕ => dyadicProduct H K m) = fun _ => NormedSpace.exp (H + K) :=
      funext fun m => Matrix.ext fun i j => Fin.elim0 i
    rw [hconst]
    exact tendsto_const_nhds
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    set A₀ : Operator n := ‖H‖ • (1 : Operator n) - H with hA₀
    set B₀ : Operator n := ‖K‖ • (1 : Operator n) - K with hB₀
    have hpsdA : A₀.PosSemidef := by
      rw [hA₀]
      exact Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_shift_posSemidef n H hH hn0
    have hpsdB : B₀.PosSemidef := by
      rw [hB₀]
      exact Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_shift_posSemidef n K hK hn0
    have hrun (k : ℕ) :
        Qatlib.Concepts.LchsSimulation.LchsRep.imaginaryRun A₀ B₀ 1 (2 ^ k)
          = Real.exp (-(‖H‖ + ‖K‖)) • dyadicProduct H K k := by
      rw [Qatlib.Concepts.LchsSimulation.LchsRep.imaginaryRun_power A₀ B₀ 1 (2 ^ k), hA₀, hB₀,
        dyadic_exp_shift_left H k, dyadic_exp_shift_left K k]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_pow,
        dyadic_scalar_pow ‖H‖ ‖K‖ k]
      rfl
    have hlim : NormedSpace.exp (-(A₀ + B₀))
        = Real.exp (-(‖H‖ + ‖K‖)) • NormedSpace.exp (H + K) := by
      have hsum : -(A₀ + B₀) = (H + K) + (-((‖H‖ + ‖K‖))) • (1 : Operator n) := by
        rw [hA₀, hB₀]
        module
      rw [hsum]
      exact Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_exp_scalar_shift n (H + K)
          (-((‖H‖ + ‖K‖)))
    have htend : Tendsto (fun k : ℕ => Real.exp (-(‖H‖ + ‖K‖)) • dyadicProduct H K k) atTop
        (𝓝 (Real.exp (-(‖H‖ + ‖K‖)) • NormedSpace.exp (H + K))) := by
      have h :=
          Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_psd_dyadic_lie_limit n A₀ B₀ hpsdA hpsdB
      simp only [hrun, hlim] at h
      exact h
    have hne : Real.exp (-(‖H‖ + ‖K‖)) ≠ 0 := Real.exp_ne_zero _
    have h2 : Tendsto (fun k : ℕ => dyadicProduct H K k) atTop (𝓝 (NormedSpace.exp (H + K))) := by
      have h3 := htend.const_smul (Real.exp (-(‖H‖ + ‖K‖)))⁻¹
      simp only [inv_smul_smul₀ hne] at h3
      exact h3
    exact h2

theorem tendsto_trace_re {n : ℕ} {f : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {L : Matrix (Fin n) (Fin n) ℂ} (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun m => (Matrix.trace (f m)).re) atTop (𝓝 ((Matrix.trace L).re)) := by
  let T : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap
  have hcomp : Tendsto (fun m => T (f m)) atTop (𝓝 (T L)) :=
    (T.continuous.tendsto L).comp hf
  exact hcomp

theorem dyadic_trace_le_one {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    ∀ m : ℕ, 1 ≤ m → (Matrix.trace (dyadicProduct H K m)).re ≤
      (Matrix.trace (dyadicProduct H K 1)).re := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    rcases m with _ | m
    · exact le_rfl
    · refine le_trans (dyadic_trace_monotone H K hH hK (m + 1)) ?_
      exact ih (by omega)

theorem trace_dyadicProduct_ge_exp {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (H + K))).re ≤ (Matrix.trace (dyadicProduct H K 1)).re := by
  have hlim := dyadicProduct_tendsto_exp H K hH hK
  have htr := tendsto_trace_re hlim
  have hbound : ∀ᶠ m : ℕ in atTop,
      (Matrix.trace (dyadicProduct H K m)).re ≤ (Matrix.trace (dyadicProduct H K 1)).re := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact dyadic_trace_le_one H K hH hK m hm
  exact le_of_tendsto htr hbound

theorem commute_smul_right_iff {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (hc : c ≠ 0) : Commute (c • H) (c • K) ↔ Commute H K := by
  constructor
  · intro h
    have h1 : (c * c) • (H * K) = (c * c) • (K * H) := by
      rw [← smul_mul_smul, ← smul_mul_smul]
      exact h
    have h2 : ((c * c)⁻¹) • ((c * c) • (H * K))
        = ((c * c)⁻¹) • ((c * c) • (K * H)) := congrArg (((c * c)⁻¹) • ·) h1
    simp only [inv_smul_smul₀ (mul_ne_zero hc hc)] at h2
    exact h2
  · intro h
    have h1 : (c * c) • (H * K) = (c * c) • (K * H) := by rw [h]
    rw [← smul_mul_smul, ← smul_mul_smul] at h1
    exact h1

theorem gt_gap_zero_iff_commute {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    gtHermitianGap H K = 0 ↔ Commute H K := by
  constructor
  · intro hgap
    set X : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (((2 : ℕ) : ℝ)⁻¹ • H) with hX0
    set Y : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (((2 : ℕ) : ℝ)⁻¹ • K) with hY0
    have hX : X.IsHermitian := by
      rw [hX0]; exact exp_smul_hermitian hH _
    have hY : Y.IsHermitian := by
      rw [hY0]; exact exp_smul_hermitian hK _
    have hx2 : X ^ 2 = NormedSpace.exp H := by
      rw [hX0, exp_smul_pow]
      congr 1
      have h2 : (((2 : ℕ) : ℝ)) * (((2 : ℕ) : ℝ))⁻¹ = 1 :=
        mul_inv_cancel₀ (by norm_num : (((2 : ℕ) : ℝ)) ≠ 0)
      rw [h2, one_smul]
    have hy2 : Y ^ 2 = NormedSpace.exp K := by
      rw [hY0, exp_smul_pow]
      congr 1
      have h2 : (((2 : ℕ) : ℝ)) * (((2 : ℕ) : ℝ))⁻¹ = 1 :=
        mul_inv_cancel₀ (by norm_num : (((2 : ℕ) : ℝ)) ≠ 0)
      rw [h2, one_smul]
    have hp1 : dyadicProduct H K 1 = (X * Y) ^ 2 := by
      simp [dyadicProduct, pow_one, hX0, hY0]
    have hp0 : dyadicProduct H K 0 = NormedSpace.exp H * NormedSpace.exp K :=
      dyadicProduct_zero H K
    unfold gtHermitianGap at hgap
    rw [← hp0] at hgap
    have hmono : (Matrix.trace (dyadicProduct H K 1)).re ≤
        (Matrix.trace (dyadicProduct H K 0)).re :=
      dyadic_trace_monotone H K hH hK 0
    have hge : (Matrix.trace (NormedSpace.exp (H + K))).re ≤
        (Matrix.trace (dyadicProduct H K 1)).re :=
      trace_dyadicProduct_ge_exp H K hH hK
    have hgap0 : (Matrix.trace (dyadicProduct H K 0)).re
        - (Matrix.trace (dyadicProduct H K 1)).re = 0 := by
      have h0e : (Matrix.trace (dyadicProduct H K 0)).re
          = (Matrix.trace (NormedSpace.exp (H + K))).re := by linarith
      have h1e : (Matrix.trace (dyadicProduct H K 1)).re
          = (Matrix.trace (NormedSpace.exp (H + K))).re := by linarith
      linarith
    have hxy : (Matrix.trace (X ^ 2 * Y ^ 2)).re = (Matrix.trace ((X * Y) ^ 2)).re := by
      rw [hx2, hy2, ← hp0, ← hp1]
      exact sub_eq_zero.mp hgap0
    have hcomm : Commute X Y := (gap0_zero_iff_commute X Y hX hY).mp hxy
    have hsmul : Commute (((2 : ℕ) : ℝ)⁻¹ • H) (((2 : ℕ) : ℝ)⁻¹ • K) :=
      (exp_commute_iff _ _ (hH.smul (by simp [IsSelfAdjoint]))
        (hK.smul (by simp [IsSelfAdjoint]))).mp (by
        rw [← hX0, ← hY0]; exact hcomm)
    exact (commute_smul_right_iff H K
      (by norm_num : (((2 : ℕ) : ℝ))⁻¹ ≠ 0)).mp hsmul
  · intro hcomm
    unfold gtHermitianGap
    have h := Qatlib.Concepts.MatrixWeights.WeightsCore.mmw_commuting_trace_potential n H K hcomm
    linarith

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
set_option warningAsError false
namespace G6

noncomputable local instance : DecidableEq QuantumStep := Classical.decEq _
noncomputable local instance : DecidableEq QueryDesc := Classical.decEq _

end G6

namespace G7

end G7

namespace G8

end G8

namespace G9

end G9

end Qatlib.Concepts.MatrixWeights.ApproxGibbs
