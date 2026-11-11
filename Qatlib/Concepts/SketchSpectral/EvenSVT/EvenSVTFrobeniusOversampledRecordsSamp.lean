/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.EvenSVTFrobeniusOversampledRecordsStat

/-!
# Frobenius guarantees for oversampled SVT records

This module proves `evenSVTFrobeniusOversampledRecords`, the Frobenius accuracy guarantee for
the output of an oversampled even-SVT run. It combines row and conditional-column concentration
events under the explicit error budgets of the sampling-based framework in [ChiaEtAl2022].

## Main statements

* `evenSVTFrobeniusOversampledRecords`: Under the specified domination, spectral regularity, and
  error budgets, an oversampled even-SVT run has Frobenius error greater than `ε` with
  probability at most `δ`. See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw.SamplingBasedLowRank2019
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Hermitian functional calculus is unchanged when its matrix argument is replaced by an equal
Hermitian matrix. -/
private theorem oversampled_function_congr {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ)
    (h : A = B) : hermitianFunction A hA f = hermitianFunction B hB f := by
  subst B
  rfl

/-- The probability of a union of two sample events is at most the sum of their probabilities. -/
private theorem oversampled_event_union {K : Type} [Fintype K] [DecidableEq K]
    (q : FinDist K) (r : ℕ) (P S : (Fin r → K) → Prop) :
    q.probEvent (fun v => P v ∨ S v) ≤ q.probEvent P + q.probEvent S := by
  unfold FinDist.probEvent
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hn : 0 ≤ q.probOf v := Finset.prod_nonneg fun _ _ => q.nonneg _
  by_cases hp : P v <;> by_cases hs : S v <;> simp [hp, hs, hn]

/-- Under the specified domination, spectral regularity, and error budgets, an oversampled
even-SVT run has Frobenius error greater than `ε` with probability at most `δ`. See
[ChiaEtAl2022]. -/
theorem evenSVTFrobeniusOversampledRecords : EvenSVTFrobeniusOversampledRecords := by
  classical
  intro K C _ _ _ _ A r c f fbar L Lbar d ε δ η₁ η₂ φrow φcol qs condQ
    hr hc hφrow hφcol hL hLb _hd hε hδ hδ1 hη₁ hη₂ hbudget hε₁ hε₂
    hband hqs hcond hLip hLipb hcons
  let R (v : Fin r → K) := compactSketched (compactSketchData qs r v) A
  let U (v : Fin r → K) (w : Fin c → C) :=
    compactSketched (compactSketchData (condQ v) c w) (R v)ᴴ
  let T (v : Fin r → K) (w : Fin c → C) : Matrix C (Fin c) ℂ :=
    (compactSketchMatrix (compactSketchData (condQ v) c w))ᴴ
  have hU (v : Fin r → K) (w : Fin c → C) : (U v w)ᴴ = R v * T v w := by
    have h := (compact_sketch_actual_pairs_entries_and_queries C (Fin r) (Fin r)
      (condQ v) c (R v)ᴴ (R v)ᴴ w).2.2.2.1
    dsimp only [U]
    rw [h, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hout (v : Fin r → K) (w : Fin c → C) :
      (oversampledEvenSVTRun A r c f fbar qs condQ v w).output =
        (R v)ᴴ * hermitianFunction ((U v w)ᴴ * U v w)
          (Matrix.isHermitian_conjTranspose_mul_self _) fbar * R v + (f 0) • 1 := by
    let run := oversampledEvenSVTRun A r c f fbar qs condQ v w
    have hs := oversampledEvenSVTRun_records K C A r c f fbar qs condQ v w
    change run.rowsᴴ * hermitianFunction (run.columns * run.columnsᴴ)
      (Matrix.isHermitian_mul_conjTranspose_self _) fbar * run.rows + (f 0) • 1 = _
    have hrows : run.rows = R v := hs.2.2.2.2.1
    have hcolumns : run.columns = (U v w)ᴴ := hs.2.2.2.2.2
    have hgram : run.columns * run.columnsᴴ = (U v w)ᴴ * U v w := by
      rw [hcolumns, Matrix.conjTranspose_conjTranspose]
    have hfun := oversampled_function_congr (Matrix.isHermitian_mul_conjTranspose_self _)
      (Matrix.isHermitian_conjTranspose_mul_self _) fbar hgram
    rw [hfun, hrows]
  have hη₁nn : 0 ≤ η₁ := by
    rw [hη₁]
    exact mul_nonneg (Real.sqrt_nonneg _) (sketchSquared_nonneg _)
  have hη₂nn : 0 ≤ η₂ := by
    rw [hη₂]
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (sketchSquared_nonneg _))
  let Bad (z : (Fin r → K) × (Fin c → C)) :=
    ε < spectralFrobenius
      ((oversampledEvenSVTRun A r c f fbar qs condQ z.1 z.2).output -
        hermitianFunction (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self _) f)
  have hdet (v : Fin r → K) (w : Fin c → C)
      (hE1 : spectralFrobenius ((R v)ᴴ * R v - Aᴴ * A) ≤ η₁)
      (hE2 : spectralFrobenius ((U v w)ᴴ * U v w - R v * (R v)ᴴ) ≤ η₂) :
      ¬Bad (v, w) := by
    have hgram : (R v * T v w) * (R v * T v w)ᴴ = (U v w)ᴴ * U v w := by
      rw [← hU, Matrix.conjTranspose_conjTranspose]
    have h := evenSVT_band_core A (R v) (T v w) f fbar L Lbar d η₁ η₂
      hL.le hLb.le hη₁nn hη₂nn hband hLip hLipb hcons hE1 (by rw [hgram]; exact hE2)
    have hfun := oversampled_function_congr (Matrix.isHermitian_mul_conjTranspose_self _)
      (Matrix.isHermitian_conjTranspose_mul_self _) fbar hgram
    rw [hfun] at h
    have hend : L * η₁ + (‖Aᴴ * A‖ + η₁) * (Lbar * η₂) ≤ ε := by
      linarith [show (‖Aᴴ * A‖ + η₁) * (Lbar * η₂) ≤ ε / 2 by
        simpa only [mul_assoc] using! hε₂]
    dsimp only [Bad]
    rw [hout]
    exact not_lt_of_ge (h.trans hend)
  refine ⟨twoSketchRecordLaw qs r c condQ, (fun _ _ => rfl), ?_⟩
  change (twoSketchRecordLaw qs r c condQ).probEvent (fun ω => Bad (ω 0)) ≤ δ
  by_cases hz : sketchSquared A = 0
  · have hAz : A = 0 := sketchSquared_zero_matrix A hz
    have hRz (v : Fin r → K) : R v = 0 := by
      ext i j
      simp [R, hAz, compactSketched, compactSketchEntry]
    have hUz (v : Fin r → K) (w : Fin c → C) : U v w = 0 := by
      ext i j
      simp [U, hRz, compactSketched, compactSketchEntry]
    have hn (v : Fin r → K) (w : Fin c → C) : ¬Bad (v, w) := hdet v w
      (by simpa [hRz, hAz, spectralFrobenius] using! hη₁nn)
      (by simpa [hUz, hRz, spectralFrobenius] using! hη₂nn)
    have hf : (Finset.univ.filter (fun ω : Fin 1 → ((Fin r → K) × (Fin c → C)) =>
        Bad (ω 0))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro ω _
      exact hn (ω 0).1 (ω 0).2
    unfold FinDist.probEvent
    rw [hf, Finset.sum_empty]
    exact hδ.le
  · have hA : 0 < sketchSquared A := lt_of_le_of_ne (sketchSquared_nonneg _) (Ne.symm hz)
    have hd3 : 0 < δ / 3 := by positivity
    have hd31 : δ / 3 < 1 := by linarith
    have hlog : 0 < Real.log (2 / (δ / 3)) :=
      Real.log_pos ((lt_div_iff₀ hd3).mpr (by linarith))
    have hη₁p : 0 < η₁ := by rw [hη₁]; positivity
    have hη₂p : 0 < η₂ := by rw [hη₂]; positivity
    let E₁ (v : Fin r → K) := η₁ ≤ spectralFrobenius ((R v)ᴴ * R v - Aᴴ * A)
    let E₂ (v : Fin r → K) (w : Fin c → C) :=
      η₂ ≤ spectralFrobenius ((U v w)ᴴ * U v w - R v * (R v)ᴴ)
    let κ := Real.sqrt (φrow ^ 2 * Real.log (2 / (δ / 3)) / (2 * r : ℝ))
    let Eg (v : Fin r → K) := κ * sketchSquared A ≤ |sketchSquared (R v) - sketchSquared A|
    let Frow (v : Fin r → K) := E₁ v ∨ Eg v
    let Fcol (v : Fin r → K) (w : Fin c → C) := ¬Eg v ∧ E₂ v w
    have hrow : qs.probEvent E₁ ≤ δ / 3 := by
      dsimp only [E₁, R]
      rw [hη₁]
      exact oversampledActualGramTail K C qs r A φrow (δ / 3) hr hφrow hA hd3 hd31 hqs
    have heg : qs.probEvent Eg ≤ δ / 3 :=
      (compact_sketch_frobenius_norm_bounds_and_tail K C qs r A φrow hr hφrow hA hqs).2.2.2
        (δ / 3) hd3 hd31
    have hκ : κ ≤ 1 := by
      have h := Real.sqrt_le_sqrt hbudget
      norm_num only [Real.sqrt_one] at h
      exact h
    have henergy (v : Fin r → K) (hg : ¬Eg v) : sketchSquared (R v)ᴴ ≤ 2 * sketchSquared A := by
      have hlt : |sketchSquared (R v) - sketchSquared A| < κ * sketchSquared A := lt_of_not_ge hg
      have ht := mul_le_mul_of_nonneg_right hκ hA.le
      rw [sketchSquared_adjoint]
      linarith [le_abs_self (sketchSquared (R v) - sketchSquared A)]
    have hcol (v : Fin r → K) : (condQ v).probEvent (Fcol v) ≤ δ / 3 := by
      by_cases hg : Eg v
      · unfold FinDist.probEvent
        simp [Fcol, hg, hd3.le]
      · have hevent : (condQ v).probEvent (E₂ v) ≤ δ / 3 := by
          by_cases he : sketchSquared (R v)ᴴ = 0
          · have hzR : (R v)ᴴ = 0 := sketchSquared_zero_matrix _ he
            have hRz : R v = 0 := by simpa using! congrArg Matrix.conjTranspose hzR
            have hUz (w : Fin c → C) : U v w = 0 := by
              ext i j
              simp [U, hRz, compactSketched, compactSketchEntry]
            have hf : (Finset.univ.filter (E₂ v)) = ∅ := by
              apply Finset.filter_eq_empty_iff.mpr
              intro w _
              dsimp only [E₂]
              simp only [hUz, hRz, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero,
                spectralFrobenius, Matrix.zero_apply, Complex.normSq_zero,
                Finset.sum_const_zero, Real.sqrt_zero]
              exact not_le_of_gt hη₂p
            unfold FinDist.probEvent
            rw [hf, Finset.sum_empty]
            exact hd3.le
          · have hep : 0 < sketchSquared (R v)ᴴ :=
              lt_of_le_of_ne (sketchSquared_nonneg _) (Ne.symm he)
            have ht := oversampledActualGramTail C (Fin r) (condQ v) c (R v)ᴴ φcol (δ / 3)
              hc hφcol hep hd3 hd31 (fun j => hcond v j hep)
            simp only [Matrix.conjTranspose_conjTranspose] at ht
            have hth : Real.sqrt (8 * φcol ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) *
                sketchSquared (R v)ᴴ ≤ η₂ := by
              rw [hη₂]
              exact mul_le_mul_of_nonneg_left (henergy v hg) (Real.sqrt_nonneg _)
            apply le_trans _ ht
            unfold FinDist.probEvent
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro w hw
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hth.trans (Finset.mem_filter.mp hw).2⟩
            · intro w _ _
              exact Finset.prod_nonneg fun _ _ => (condQ v).nonneg _
        simpa only [Fcol, hg, not_false_eq_true, true_and] using! hevent
    have hrowall : qs.probEvent Frow ≤ δ / 3 + δ / 3 :=
      (oversampled_event_union qs r E₁ Eg).trans (add_le_add hrow heg)
    have hsub (v : Fin r → K) (w : Fin c → C) : Bad (v, w) → Frow v ∨ Fcol v w := by
      intro hb
      by_contra hn
      have hE1 : ¬E₁ v := fun h => hn (Or.inl (Or.inl h))
      have hEg : ¬Eg v := fun h => hn (Or.inl (Or.inr h))
      have hE2 : ¬E₂ v w := fun h => hn (Or.inr ⟨hEg, h⟩)
      exact hdet v w (le_of_lt (lt_of_not_ge hE1)) (le_of_lt (lt_of_not_ge hE2)) hb
    exact (twoSketch_union_bound qs r c condQ Frow Fcol Bad (δ / 3 + δ / 3) (δ / 3)
      hsub (by
        unfold FinDist.probEvent at hrowall ⊢
        convert! hrowall using 1
        congr 2)
      (fun v => by
        have hv := hcol v
        unfold FinDist.probEvent at hv ⊢
        convert! hv using 1
        congr 2)).trans
      (by linarith)

end Qatlib.Concepts.SketchSpectral.EvenSVT
