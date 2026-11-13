/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualSketch

/-!
# Concentration of the actual PCA sketch

Bounds the two Gram matrix errors arising from length-squared row sampling and conditional
column sampling. The joint event `pcaBadGram` controls squared singular values of the small
sketch, providing the concentration step for the classical PCA algorithm in [Tang2021].

## Main statements

* `pca_actual_gram_concentration`: The joint row and conditional column record has Gram failure
  probability at most `delta` at the prescribed sample count [Tang2021].
* `pca_actual_small_spectrum`: Outside `pcaBadGram`, each squared singular value indexed below
  `min n d` differs from that of the input by at most `2 * t * sketchSquared A`.

## References

* [Tang, 2021][Tang2021]
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SketchSpectral.SketchAnalysis

/-- Event probability for independent samples is monotone under pointwise implication. -/
theorem pca_event_mono {X : Type} [Fintype X] (p : FinDist X) {L : ℕ}
    (P Q : (Fin L → X) → Prop) (h : ∀ z, P z → Q z) : p.probEvent P ≤ p.probEvent Q := by
  unfold FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, h z (Finset.mem_filter.mp hz).2⟩
  · intro z _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- The row sketch Gram error exceeds `pcaGramTolerance K e` times the input energy with
probability at most `delta / 2`, under the stated positivity and confidence assumptions. -/
theorem pca_actual_row_gram_tail {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (K e delta : ℝ) (hK : 0 < K) (he : 0 < e)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (pcaRowLaw A hA).probEvent (fun rows : Fin (pcaGramSamples K e delta) → Fin n =>
      pcaGramTolerance K e * sketchSquared A <
        spectralFrobenius ((pcaRowSketch A hA _ rows)ᴴ * pcaRowSketch A hA _ rows - Aᴴ * A))
      ≤ delta / 2 := by
  have hq := (pcaGramSamples_rank K e delta).1
  have ht := pca_gram_tail A hA _ hq (delta / 2) (by positivity) (by linarith)
  have hdiv : 2 / (delta / 2) = 4 / delta := by ring
  rw [hdiv] at ht
  apply (pca_event_mono (pcaRowLaw A hA) _ _ ?_).trans ht
  intro rows hrow
  exact (mul_le_mul_of_nonneg_right (pcaGramSamples_scale K e delta hK he) hA.le).trans hrow.le

/-- For each fixed row record, the conditional column sketch Gram error exceeds the prescribed
input-energy-scaled tolerance with probability at most `delta / 2`. -/
theorem pca_actual_column_gram_tail {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (K e delta : ℝ) (hK : 0 < K) (he : 0 < e)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (rows : Fin (pcaGramSamples K e delta) → Fin n) :
    (pcaColumnLaw A hA hd _ rows).probEvent
      (fun cols : Fin (pcaGramSamples K e delta) → Fin d =>
        pcaGramTolerance K e * sketchSquared A <
          spectralFrobenius (pcaSmallMatrix A hA hd _ rows cols *
            (pcaSmallMatrix A hA hd _ rows cols)ᴴ -
            pcaRowSketch A hA _ rows * (pcaRowSketch A hA _ rows)ᴴ)) ≤ delta / 2 := by
  let R := pcaRowSketch A hA (pcaGramSamples K e delta) rows
  have hq := (pcaGramSamples_rank K e delta).1
  have ht0 : 0 < pcaGramTolerance K e := by unfold pcaGramTolerance; positivity
  have henergy : sketchSquared Rᴴ ≤ sketchSquared A := by
    rw [sketchSquared_adjoint]
    exact pcaRowSketch_energy A hA _ hq rows
  by_cases hR : 0 < sketchSquared Rᴴ
  · have ht := pca_gram_tail Rᴴ hR _ hq (delta / 2) (by positivity) (by linarith)
    have hdiv : 2 / (delta / 2) = 4 / delta := by ring
    rw [hdiv] at ht
    simp only [Matrix.conjTranspose_conjTranspose] at ht
    have hcol : pcaColumnLaw A hA hd (pcaGramSamples K e delta) rows = pcaRowLaw Rᴴ hR := by
      simp only [pcaColumnLaw, R, dif_pos hR]
    rw [hcol]
    apply (pca_event_mono (pcaRowLaw Rᴴ hR) _ _ ?_).trans ht
    intro cols hbad
    have hscale := pcaGramSamples_scale K e delta hK he
    have hthreshold : Real.sqrt (8 * Real.log (4 / delta) / (pcaGramSamples K e delta : ℝ)) *
        sketchSquared Rᴴ ≤ pcaGramTolerance K e * sketchSquared A :=
      (mul_le_mul_of_nonneg_right hscale (sketchSquared_nonneg Rᴴ)).trans
        (mul_le_mul_of_nonneg_left henergy ht0.le)
    have herror :
        spectralFrobenius (pcaSmallMatrix A hA hd _ rows cols *
          (pcaSmallMatrix A hA hd _ rows cols)ᴴ - R * Rᴴ) =
        spectralFrobenius ((pcaRowSketch Rᴴ hR _ cols)ᴴ * pcaRowSketch Rᴴ hR _ cols - R * Rᴴ) := by
      simp only [pcaSmallMatrix, hcol, pcaRowSketch, Matrix.conjTranspose_conjTranspose]
      rfl
    change _ ≤ spectralFrobenius ((pcaRowSketch Rᴴ hR _ cols)ᴴ * pcaRowSketch Rᴴ hR _ cols - R * Rᴴ)
    rw [herror] at hbad
    exact hthreshold.trans hbad.le
  · have hzeroE : sketchSquared Rᴴ = 0 := le_antisymm (le_of_not_gt hR) (sketchSquared_nonneg _)
    have hzeroH : Rᴴ = 0 := sketchSquared_zero_matrix Rᴴ hzeroE
    have hzero : R = 0 := by
      simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using!
        congrArg Matrix.conjTranspose hzeroH
    have hzeroRaw : pcaRowSketch A hA (pcaGramSamples K e delta) rows = 0 := hzero
    have hsmall (cols : Fin (pcaGramSamples K e delta) → Fin d) :
        pcaSmallMatrix A hA hd _ rows cols = 0 := by
      ext i j
      simp [pcaSmallMatrix, hzeroRaw, compactSketched, compactSketchEntry]
    have hbadFalse (cols : Fin (pcaGramSamples K e delta) → Fin d) :
        ¬ pcaGramTolerance K e * sketchSquared A <
          spectralFrobenius (pcaSmallMatrix A hA hd _ rows cols *
            (pcaSmallMatrix A hA hd _ rows cols)ᴴ - R * Rᴴ) := by
      simp only [hsmall, hzero, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero,
        spectralFrobenius, Matrix.zero_apply, Complex.normSq_zero, Finset.sum_const_zero, Real.sqrt_zero]
      exact not_lt_of_ge (mul_pos ht0 hA).le
    unfold FinDist.probEvent
    have hf : Finset.univ.filter (fun cols : Fin (pcaGramSamples K e delta) → Fin d =>
        pcaGramTolerance K e * sketchSquared A <
          spectralFrobenius (pcaSmallMatrix A hA hd _ rows cols *
            (pcaSmallMatrix A hA hd _ rows cols)ᴴ - R * Rᴴ)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun cols _ => hbadFalse cols
    change (∑ cols ∈ Finset.univ.filter (fun cols => _), _) ≤ _
    rw [hf]
    simp only [Finset.sum_empty]
    positivity

/-- The failure predicate asserting that either the row Gram error or the conditional column
Gram error exceeds `t` times the input energy. -/
def pcaBadGram {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (t : ℝ)
    (z : (Fin q → Fin n) × (Fin q → Fin d)) : Prop :=
  t * sketchSquared A < spectralFrobenius ((pcaRowSketch A hA q z.1)ᴴ *
      pcaRowSketch A hA q z.1 - Aᴴ * A) ∨
    t * sketchSquared A < spectralFrobenius (pcaSmallMatrix A hA hd q z.1 z.2 *
      (pcaSmallMatrix A hA hd q z.1 z.2)ᴴ - pcaRowSketch A hA q z.1 * (pcaRowSketch A hA q z.1)ᴴ)

/-- The joint row and conditional column record has Gram failure probability at most `delta` at
the prescribed sample count [Tang2021]. -/
theorem pca_actual_gram_concentration {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (K e delta : ℝ) (hK : 0 < K) (he : 0 < e)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (pcaSketchLaw A hA hd (pcaGramSamples K e delta)).probEvent
      (fun omega : Fin 1 → ((Fin (pcaGramSamples K e delta) → Fin n) ×
        (Fin (pcaGramSamples K e delta) → Fin d)) =>
        pcaBadGram A hA hd _ (pcaGramTolerance K e) (omega 0)) ≤ delta := by
  have h := twoSketch_union_bound (pcaRowLaw A hA) (pcaGramSamples K e delta)
    (pcaGramSamples K e delta) (pcaColumnLaw A hA hd _)
    (fun rows => pcaGramTolerance K e * sketchSquared A <
      spectralFrobenius ((pcaRowSketch A hA _ rows)ᴴ * pcaRowSketch A hA _ rows - Aᴴ * A))
    (fun rows cols => pcaGramTolerance K e * sketchSquared A <
      spectralFrobenius (pcaSmallMatrix A hA hd _ rows cols * (pcaSmallMatrix A hA hd _ rows cols)ᴴ -
        pcaRowSketch A hA _ rows * (pcaRowSketch A hA _ rows)ᴴ))
    (pcaBadGram A hA hd _ (pcaGramTolerance K e)) (delta / 2) (delta / 2)
    (fun _ _ hbad => hbad) (pca_actual_row_gram_tail A hA K e delta hK he hdelta hdelta1)
    (pca_actual_column_gram_tail A hA hd K e delta hK he hdelta hdelta1)
  exact h.trans_eq (by ring)

/-- Outside `pcaBadGram`, each squared singular value indexed below `min n d` differs from that
of the input by at most `2 * t * sketchSquared A`. -/
theorem pca_actual_small_spectrum {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t)
    (z : (Fin q → Fin n) × (Fin q → Fin d))
    (hgood : ¬ pcaBadGram A hA hd q t z) {i : ℕ} (hi : i < min n d) :
    |(matrixSingularValues (pcaSmallMatrix A hA hd q z.1 z.2) i) ^ 2 -
      (matrixSingularValues A i) ^ 2| ≤ 2 * t * sketchSquared A := by
  have hrow : spectralFrobenius ((pcaRowSketch A hA q z.1)ᴴ * pcaRowSketch A hA q z.1 - Aᴴ * A)
      ≤ t * sketchSquared A := le_of_not_gt fun hb => hgood (Or.inl hb)
  have hcol : spectralFrobenius (pcaSmallMatrix A hA hd q z.1 z.2 *
      (pcaSmallMatrix A hA hd q z.1 z.2)ᴴ - pcaRowSketch A hA q z.1 * (pcaRowSketch A hA q z.1)ᴴ)
      ≤ t * sketchSquared A := le_of_not_gt fun hb => hgood (Or.inr hb)
  have hL := sketchSingularValueL2Stability_deterministic (Fin n) (Fin d) (Fin q) (Fin q)
    A (pcaRowSketch A hA q z.1) (pcaSmallMatrix A hA hd q z.1 z.2)
    (t * sketchSquared A) (t * sketchSquared A) (mul_nonneg ht hA.le) (mul_nonneg ht hA.le) hrow hcol
  simp only [Fintype.card_fin] at hL
  have hs : ((matrixSingularValues (pcaSmallMatrix A hA hd q z.1 z.2) i) ^ 2 -
      (matrixSingularValues A i) ^ 2) ^ 2 ≤
      ∑ j ∈ Finset.range (min n d), ((matrixSingularValues (pcaSmallMatrix A hA hd q z.1 z.2) j) ^ 2 -
        (matrixSingularValues A j) ^ 2) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg
      ((matrixSingularValues (pcaSmallMatrix A hA hd q z.1 z.2) j) ^ 2 -
        (matrixSingularValues A j) ^ 2)) (Finset.mem_range.mpr hi)
  calc
    _ = Real.sqrt (((matrixSingularValues (pcaSmallMatrix A hA hd q z.1 z.2) i) ^ 2 -
      (matrixSingularValues A i) ^ 2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt hs
    _ ≤ _ := hL.trans_eq (by ring)

end Qatlib.Papers.QPCAAssume18.ClassicalPca
