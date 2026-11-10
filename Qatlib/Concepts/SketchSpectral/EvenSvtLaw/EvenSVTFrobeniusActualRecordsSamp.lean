/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.OriginalActualRecords

import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusActualRecordsStat
import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusRecordTools
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

private def unitLaw : FinDist Unit where
  prob := fun _ => 1
  nonneg := fun _ => by norm_num
  sum_one := by simp

theorem hermitianFunction_id {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    hermitianFunction A hA (fun x => (x : ℂ)) = A :=
  (orderedHermitian_diagonal hA).symm

private theorem zero_records_error (v w : Fin 0 → Unit) :
    spectralFrobenius
      ((compactSketched (compactSketchData unitLaw 0 v) (1 : Matrix Unit Unit ℂ))ᴴ *
        hermitianFunction
          ((compactSketched (compactSketchData unitLaw 0 w)
            ((compactSketched (compactSketchData unitLaw 0 v) (1 : Matrix Unit Unit ℂ))ᴴ))ᴴ *
            compactSketched (compactSketchData unitLaw 0 w)
              ((compactSketched (compactSketchData unitLaw 0 v) (1 : Matrix Unit Unit ℂ))ᴴ))
          (Matrix.isHermitian_conjTranspose_mul_self _) (fun _ => 1) *
        compactSketched (compactSketchData unitLaw 0 v) (1 : Matrix Unit Unit ℂ) +
        (0 : ℂ) • (1 : Matrix Unit Unit ℂ) -
        hermitianFunction ((1 : Matrix Unit Unit ℂ)ᴴ * 1)
          (Matrix.isHermitian_conjTranspose_mul_self _) (fun x => (x : ℂ))) = 1 := by
  rw [hermitianFunction_id]
  norm_num [Matrix.mul_apply, spectralFrobenius, Matrix.one_apply]

theorem not_evenSVTFrobeniusActualRecords : ¬ evenSVTFrobeniusActualRecordsLegacy := by
  intro h
  obtain ⟨Q, _hQ, hbad⟩ := h Unit Unit (1 : Matrix Unit Unit ℂ) 0 0
    (fun x => (x : ℂ)) (fun _ => 1) 1 1 1 (1 / 2) (1 / 2) 0 0 unitLaw (fun _ => unitLaw)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sketchSquared, sketchRowSquared, Matrix.one_apply])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i; cases i; norm_num [unitLaw, sketchSquared, sketchRowSquared, Matrix.one_apply])
    (by
      intro v j henergy
      have hz : sketchSquared
          ((compactSketched (compactSketchData unitLaw 0 v) (1 : Matrix Unit Unit ℂ))ᴴ) = 0 := by
        simp [sketchSquared, sketchRowSquared]
      rw [hz] at henergy
      norm_num at henergy)
    (by
      intro x y _hx _hy
      simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact le_rfl)
    (by intro x y _hx _hy; simp)
    (by intro x _hx _hband; simp)
  norm_num only [Complex.ofReal_zero] at hbad
  simp_rw [zero_records_error] at hbad
  norm_num [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Q.sum_probOf 1] at hbad

private theorem hermitianFunction_congr_matrix {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ)
    (h : A = B) : hermitianFunction A hA f = hermitianFunction B hB f := by
  subst B
  rfl

theorem evenSVTFrobeniusActualRecords_proof : EvenSVTFrobeniusActualRecords := by
  intro K C _ _ _ _ A r c f fbar L Lbar d ε δ η₁ η₂ qs condQ
    hr hc hL hLb _hd hε hδ hδ1 hA hη₁ hη₂ _hbudget hε₁ hε₂ hband hqs hcond hLip hLipb hcons
  let R (v : Fin r → K) := compactSketched (compactSketchData qs r v) A
  let U (v : Fin r → K) (w : Fin c → C) := compactSketched (compactSketchData (condQ v) c w) (R v)ᴴ
  let T (v : Fin r → K) (w : Fin c → C) : Matrix C (Fin c) ℂ :=
    (compactSketchMatrix (compactSketchData (condQ v) c w))ᴴ
  have hU (v : Fin r → K) (w : Fin c → C) : (U v w)ᴴ = R v * T v w := by
    have h := (compact_sketch_actual_pairs_entries_and_queries C (Fin r) (Fin r)
      (condQ v) c (R v)ᴴ (R v)ᴴ w).2.2.2.1
    dsimp only [U]
    rw [h, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hd3 : 0 < δ / 3 := by positivity
  have hd31 : δ / 3 < 1 := by linarith
  have hlog : 0 < Real.log (2 / (δ / 3)) :=
    Real.log_pos ((lt_div_iff₀ hd3).mpr (by linarith))
  have hη₁p : 0 < η₁ := by rw [hη₁]; positivity
  have hη₂p : 0 < η₂ := by rw [hη₂]; positivity
  let E₁ (v : Fin r → K) := η₁ ≤ spectralFrobenius ((R v)ᴴ * R v - Aᴴ * A)
  let E₂ (v : Fin r → K) (w : Fin c → C) :=
    η₂ ≤ spectralFrobenius ((U v w)ᴴ * U v w - R v * (R v)ᴴ)
  have hrow : qs.probEvent E₁ ≤ δ / 3 := by
    dsimp only [E₁, R]
    rw [hη₁]
    exact exact_gram_tail qs r A (δ / 3) hr hA hd3 hd31 hqs
  have henergy (v : Fin r → K) : sketchSquared (R v)ᴴ ≤ sketchSquared A := by
    rw [sketchSquared_adjoint]
    exact exact_sketch_energy_bound qs r A hr hA hqs v
  have hcol (v : Fin r → K) : (condQ v).probEvent (E₂ v) ≤ δ / 3 := by
    by_cases he : sketchSquared (R v)ᴴ = 0
    · have hz : (R v)ᴴ = 0 := sketchSquared_zero_matrix _ he
      have hR : R v = 0 := by simpa using! congrArg Matrix.conjTranspose hz
      have hUz (w : Fin c → C) : U v w = 0 := by
        ext i j
        simp [U, hR, compactSketched, compactSketchEntry]
      have hf : (Finset.univ.filter (E₂ v)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w _
        dsimp only [E₂]
        simp only [hUz, hR, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero,
          spectralFrobenius, Matrix.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, Real.sqrt_zero]
        exact not_le_of_gt hη₂p
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      rw [hf, Finset.sum_empty]
      exact hd3.le
    · have hep : 0 < sketchSquared (R v)ᴴ :=
        lt_of_le_of_ne (sketchSquared_nonneg _) (Ne.symm he)
      have ht := exact_gram_tail (condQ v) c (R v)ᴴ (δ / 3) hc hep hd3 hd31
        (fun j => hcond v j hep)
      simp only [Matrix.conjTranspose_conjTranspose] at ht
      have hth : Real.sqrt (8 * Real.log (2 / (δ / 3)) / (c : ℝ)) * sketchSquared (R v)ᴴ ≤ η₂ := by
        rw [hη₂]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        linarith [henergy v, hA]
      apply le_trans _ ht
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro w hw
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
        exact hth.trans (Finset.mem_filter.mp hw).2
      · intro w _ _
        exact Finset.prod_nonneg fun _ _ => (condQ v).nonneg _
  let Bad (z : (Fin r → K) × (Fin c → C)) :=
    ε < spectralFrobenius ((R z.1)ᴴ * hermitianFunction ((U z.1 z.2)ᴴ * U z.1 z.2)
      (Matrix.isHermitian_conjTranspose_mul_self _) fbar * R z.1 + (f 0) • 1 -
        hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self _) f)
  have hsub (v : Fin r → K) (w : Fin c → C) : Bad (v, w) → E₁ v ∨ E₂ v w := by
    intro hb
    by_contra hn
    have hE1 : spectralFrobenius ((R v)ᴴ * R v - Aᴴ * A) ≤ η₁ :=
      le_of_lt (lt_of_not_ge (fun h => hn (Or.inl h)))
    have hE2 : spectralFrobenius ((U v w)ᴴ * U v w - R v * (R v)ᴴ) ≤ η₂ :=
      le_of_lt (lt_of_not_ge (fun h => hn (Or.inr h)))
    have hgram : (R v * T v w) * (R v * T v w)ᴴ = (U v w)ᴴ * U v w := by
      rw [← hU, Matrix.conjTranspose_conjTranspose]
    have h := evenSVT_band_core A (R v) (T v w) f fbar L Lbar d η₁ η₂
      hL.le hLb.le hη₁p.le hη₂p.le hband hLip hLipb hcons hE1 (by rw [hgram]; exact hE2)
    have hfun : hermitianFunction ((R v * T v w) * (R v * T v w)ᴴ)
        (Matrix.isHermitian_mul_conjTranspose_self _) fbar =
        hermitianFunction ((U v w)ᴴ * U v w)
          (Matrix.isHermitian_conjTranspose_mul_self _) fbar := by
      exact hermitianFunction_congr_matrix _ _ fbar hgram
    rw [hfun] at h
    have hend : L * η₁ + (‖Aᴴ * A‖ + η₁) * (Lbar * η₂) ≤ ε := by
      linarith [show (‖Aᴴ * A‖ + η₁) * (Lbar * η₂) ≤ ε / 2 by simpa only [mul_assoc] using! hε₂]
    exact (not_lt_of_ge (h.trans hend)) hb
  refine ⟨twoSketchRecordLaw qs r c condQ, (fun _ _ => rfl), ?_⟩
  have h := twoSketch_union_bound qs r c condQ E₁ E₂ Bad (δ / 3) (δ / 3) hsub hrow hcol
  exact h.trans (by linarith)

end Qatlib.Concepts.SketchSpectral.EvenSvtLaw
