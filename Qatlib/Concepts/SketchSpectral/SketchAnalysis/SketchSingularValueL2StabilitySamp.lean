/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchSingularValueL2StabilityStat
import Qatlib.Concepts.SketchSpectral.SketchPerturb.SketchSingularValueStabilitySamp
import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusRecordTools
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration

/-!
# Euclidean stability of sampled squared singular values

This module proves a two-stage probabilistic bound on the Euclidean error of squared singular
values. Under row and conditional column energy domination, the sample-scale budget yields a
joint sampling law with failure probability at most `δ`, as used in the sketch framework of
[ChiaEtAl2022].

The deterministic estimate `sketchSingularValueL2Stability_deterministic` bounds the error by
the sum of the two Frobenius Gram errors, and the sampling theorem combines the corresponding
concentration events.

## Main statements

* `sketchSingularValueL2Stability_deterministic`: an additive bound from two fixed Gram errors.
* `sketchSingularValueL2Stability`: the conditional two-stage probability bound.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The Euclidean norm of a finite pointwise sum is at most the sum of the two Euclidean norms. -/
private theorem l2_minkowski (s : Finset ℕ) (f g : ℕ → ℝ) :
    Real.sqrt (∑ i ∈ s, (f i + g i)^2) ≤
      Real.sqrt (∑ i ∈ s, (f i)^2) + Real.sqrt (∑ i ∈ s, (g i)^2) := by
  have hf : 0 ≤ ∑ i ∈ s, (f i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg : 0 ≤ ∑ i ∈ s, (g i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : ∑ i ∈ s, (f i + g i)^2 =
      (∑ i ∈ s, (f i)^2) + 2*(∑ i ∈ s, f i*g i) + (∑ i ∈ s, (g i)^2) := by
    calc
      _ = ∑ i ∈ s, ((f i)^2 + 2*(f i*g i) + (g i)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [he]
  nlinarith [Real.sum_mul_le_sqrt_mul_sqrt s f g, Real.sq_sqrt hf, Real.sq_sqrt hg]

/-- A singular value vanishes when its index is at least the number of rows. -/
private theorem singular_zero_of_row_card {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq I] (A : Matrix O I ℂ) (i : ℕ) (hi : Fintype.card O ≤ i) :
    matrixSingularValues A i = 0 := by
  have hr : Module.finrank ℂ A.toEuclideanLin.range ≤ Fintype.card O := by
    exact (Submodule.finrank_le _).trans_eq finrank_euclideanSpace
  apply le_antisymm _ (matrixSingularValues_nonneg A i)
  apply le_of_not_gt
  intro hpos
  have hp := (matrixSingularValues_pos_iff_lt_finrank_range A).mp hpos
  omega

/-- For a nonnegative sequence vanishing from index `m` onward, every initial partial sum is at
most the sum of its first `m` terms. -/
private theorem sum_range_zero_tail (f : ℕ → ℝ) (m n : ℕ)
    (hf : ∀ i, 0 ≤ f i) (ht : ∀ i, m ≤ i → f i = 0) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range m, f i := by
  by_cases hn : n ≤ m
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => hf i)
  · have hm : m ≤ n := by omega
    apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono hm)
    intro i _ hi
    exact ht i (by simpa only [Finset.mem_range, not_lt] using! hi)

/-- If the two Gram differences have Frobenius bounds `η₁` and `η₂`, the Euclidean error of the
squared singular values over the source dimension range is at most η₁ + η₂. -/
theorem sketchSingularValueL2Stability_deterministic
    (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ)
    (η₁ η₂ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (h₁ : spectralFrobenius (Rᴴ*R-Aᴴ*A) ≤ η₁)
    (h₂ : spectralFrobenius (Cc*Ccᴴ-R*Rᴴ) ≤ η₂) :
    Real.sqrt (∑ i ∈ Finset.range (min (Fintype.card K) (Fintype.card C)),
      ((matrixSingularValues Cc i)^2-(matrixSingularValues A i)^2)^2) ≤ η₁+η₂ := by
  let n := min (Fintype.card K) (Fintype.card C)
  let f (i : ℕ) := (matrixSingularValues Cc i)^2-(matrixSingularValues R i)^2
  let g (i : ℕ) := (matrixSingularValues R i)^2-(matrixSingularValues A i)^2
  have hin := (ordered_hermitian_weyl_and_hoffman_wielandt C (Rᴴ*R) (Aᴴ*A)
    (Matrix.isHermitian_conjTranspose_mul_self R) (Matrix.isHermitian_conjTranspose_mul_self A)).2
  simp_rw [(singular_gram_ordered R).2, (singular_gram_ordered A).2] at hin
  change (∑ i : Fin (Fintype.card C), (g i)^2) ≤ spectralFrobenius (Rᴴ*R-Aᴴ*A)^2 at hin
  rw [Fin.sum_univ_eq_sum_range (fun i => (g i)^2)] at hin
  have hout := (ordered_hermitian_weyl_and_hoffman_wielandt RS (Cc*Ccᴴ) (R*Rᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self Cc) (Matrix.isHermitian_mul_conjTranspose_self R)).2
  simp_rw [sketchSingularValueStability_outer_gram RS CT Cc,
    sketchSingularValueStability_outer_gram RS C R] at hout
  change (∑ i : Fin (Fintype.card RS), (f i)^2) ≤ spectralFrobenius (Cc*Ccᴴ-R*Rᴴ)^2 at hout
  rw [Fin.sum_univ_eq_sum_range (fun i => (f i)^2)] at hout
  have hf : ∑ i ∈ Finset.range n, (f i)^2 ≤ η₂^2 := by
    apply (sum_range_zero_tail (fun i => (f i)^2) (Fintype.card RS) n
      (fun _ => sq_nonneg _) ?_).trans
      (hout.trans (pow_le_pow_left₀ (spectralFrobenius_nonneg _) h₂ 2))
    intro i hi
    simp only [f, singular_zero_of_row_card Cc i hi, singular_zero_of_row_card R i hi,
      sub_self, zero_pow (by decide : 2 ≠ 0)]
  have hg : ∑ i ∈ Finset.range n, (g i)^2 ≤ η₁^2 := by
    apply (sum_range_zero_tail (fun i => (g i)^2) (Fintype.card C) n
      (fun _ => sq_nonneg _) ?_).trans
      (hin.trans (pow_le_pow_left₀ (spectralFrobenius_nonneg _) h₁ 2))
    intro i hi
    simp only [g, matrixSingularValues_of_card_le R hi, matrixSingularValues_of_card_le A hi,
      sub_self, zero_pow (by decide : 2 ≠ 0)]
  have hsum : (fun i => (f i+g i)^2) =
      (fun i => ((matrixSingularValues Cc i)^2-(matrixSingularValues A i)^2)^2) := by
    funext i
    dsimp [f, g]
    ring
  have hm := l2_minkowski (Finset.range n) f g
  rw [hsum] at hm
  exact hm.trans (by
    have hs₁ : Real.sqrt (∑ i ∈ Finset.range n, (g i)^2) ≤ η₁ :=
      (Real.sqrt_le_sqrt hg).trans_eq (Real.sqrt_sq hη₁)
    have hs₂ : Real.sqrt (∑ i ∈ Finset.range n, (f i)^2) ≤ η₂ :=
      (Real.sqrt_le_sqrt hf).trans_eq (Real.sqrt_sq hη₂)
    linarith)

/-- The row product mass of a matrix with itself equals its total squared energy. -/
private theorem rowProductMass_self {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) : sketchRowProductMass A A = sketchSquared A := by
  unfold sketchRowProductMass sketchSquared
  apply Finset.sum_congr rfl
  intro k _
  exact Real.mul_self_sqrt (sketchRowSquared_nonneg A k)

/-- Under row energy domination, the probability that the Frobenius Gram error reaches the
stated oversampling threshold is at most `δ`. -/
private theorem oversampling_gram_tail {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (p : FinDist K) (r : ℕ) (A : Matrix K C ℂ)
    (φ δ : ℝ) (hr : 0 < r) (hφ : 1 ≤ φ) (hA : 0 < sketchSquared A)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdom : ∀ k, sketchRowSquared A k/(φ*sketchSquared A) ≤ p.prob k) :
    p.probEvent (fun v : Fin r → K =>
      Real.sqrt (8*φ^2*Real.log (2/δ)/(r : ℝ))*sketchSquared A ≤
        spectralFrobenius ((compactSketched (compactSketchData p r v) A)ᴴ *
          compactSketched (compactSketchData p r v) A-Aᴴ*A)) ≤ δ := by
  have ht := compact_sketch_two_sided_source_frobenius_tail K C C p r A A φ δ hr hφ
    (by simpa only [rowProductMass_self] using! hA) hδ hδ1 (by
      intro k
      simpa only [rowProductMass_self, Real.mul_self_sqrt (sketchRowSquared_nonneg A k)]
        using! hdom k)
  simp only [rowProductMass_self] at ht
  simp_rw [(compact_sketch_actual_pairs_entries_and_queries K C C p r A A _).2.2.2.2.2,
    ← spectralFrobenius_eq_sampling_norm] at ht
  exact ht

/-- Under the domination and sample-scale assumptions in `SketchSingularValueL2Stability`, a
joint two-stage sampling law gives failure probability at most `δ` for the Euclidean
squared-singular-value error bound. See [ChiaEtAl2022]. -/
theorem sketchSingularValueL2Stability : SketchSingularValueL2Stability := by
  intro K C _ _ _ _ A r c ε δ φ₁ φ₂ qs condQ
    hr hc hφ₁ hφ₂ _hε hδ hδ1 hA hqs hcond hbudget
  let R (v : Fin r → K) := compactSketched (compactSketchData qs r v) A
  let U (v : Fin r → K) (w : Fin c → C) :=
    compactSketched (compactSketchData (condQ v) c w) (R v)ᴴ
  let η₁ := Real.sqrt (8*φ₁^2*Real.log (2/(δ/2))/(r : ℝ))*sketchSquared A
  let η₂ := Real.sqrt (8*φ₂^2*Real.log (2/(δ/2))/(c : ℝ))*(φ₁*sketchSquared A)
  have hd2 : 0 < δ/2 := by positivity
  have hd21 : δ/2 < 1 := by linarith
  have hlog : 0 < Real.log (2/(δ/2)) :=
    Real.log_pos ((lt_div_iff₀ hd2).mpr (by linarith))
  have hφ₁p : 0 < φ₁ := by linarith
  have hφ₂p : 0 < φ₂ := by linarith
  have hη₁p : 0 < η₁ := by dsimp [η₁]; positivity
  have hη₂p : 0 < η₂ := by dsimp [η₂]; positivity
  let E₁ (v : Fin r → K) := η₁ ≤ spectralFrobenius ((R v)ᴴ*R v-Aᴴ*A)
  let E₂ (v : Fin r → K) (w : Fin c → C) :=
    η₂ ≤ spectralFrobenius ((U v w)ᴴ*U v w-R v*(R v)ᴴ)
  have hrow : qs.probEvent E₁ ≤ δ/2 :=
    oversampling_gram_tail qs r A φ₁ (δ/2) hr hφ₁ hA hd2 hd21 hqs
  have henergy (v : Fin r → K) : sketchSquared (R v)ᴴ ≤ φ₁*sketchSquared A := by
    rw [sketchSquared_adjoint]
    exact (compact_sketch_frobenius_norm_bounds_and_tail K C qs r A φ₁ hr hφ₁ hA hqs).2.1 v
  have hcol (v : Fin r → K) : (condQ v).probEvent (E₂ v) ≤ δ/2 := by
    by_cases he : sketchSquared (R v)ᴴ = 0
    · have hz : (R v)ᴴ = 0 := sketchSquared_zero_matrix _ he
      have hR : R v = 0 := by simpa using! congrArg Matrix.conjTranspose hz
      have hUz (w : Fin c → C) : U v w = 0 := by
        ext i j
        simp [U, hR, compactSketched, compactSketchEntry]
      have hf : Finset.univ.filter (E₂ v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro w _
        dsimp only [E₂]
        simp only [hUz, hR, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero,
          spectralFrobenius, Matrix.zero_apply, Complex.normSq_zero, Finset.sum_const_zero,
          Real.sqrt_zero]
        exact not_le_of_gt hη₂p
      unfold FinDist.probEvent
      rw [hf, Finset.sum_empty]
      exact hd2.le
    · have hep : 0 < sketchSquared (R v)ᴴ :=
        lt_of_le_of_ne (sketchSquared_nonneg _) (Ne.symm he)
      have ht := oversampling_gram_tail (condQ v) c (R v)ᴴ φ₂ (δ/2) hc hφ₂ hep hd2 hd21
        (hcond v hep)
      simp only [Matrix.conjTranspose_conjTranspose] at ht
      have hth : Real.sqrt (8*φ₂^2*Real.log (2/(δ/2))/(c : ℝ))*sketchSquared (R v)ᴴ ≤ η₂ :=
        mul_le_mul_of_nonneg_left (henergy v) (Real.sqrt_nonneg _)
      apply le_trans _ ht
      unfold FinDist.probEvent
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro w hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
          hth.trans (Finset.mem_filter.mp hw).2⟩
      · intro w _ _
        exact Finset.prod_nonneg fun _ _ => (condQ v).nonneg _
  let Bad (z : (Fin r → K) × (Fin c → C)) :=
    ε*sketchSquared A < Real.sqrt (∑ i ∈ Finset.range (min (Fintype.card K) (Fintype.card C)),
      ((matrixSingularValues (U z.1 z.2)ᴴ i)^2-(matrixSingularValues A i)^2)^2)
  have hsub (v : Fin r → K) (w : Fin c → C) : Bad (v,w) → E₁ v ∨ E₂ v w := by
    intro hb
    by_contra hn
    have hE1 : spectralFrobenius ((R v)ᴴ*R v-Aᴴ*A) ≤ η₁ :=
      le_of_lt (lt_of_not_ge (fun h => hn (Or.inl h)))
    have hE2 : spectralFrobenius ((U v w)ᴴ*U v w-R v*(R v)ᴴ) ≤ η₂ :=
      le_of_lt (lt_of_not_ge (fun h => hn (Or.inr h)))
    have h := sketchSingularValueL2Stability_deterministic K C (Fin r) (Fin c)
      A (R v) (U v w)ᴴ η₁ η₂ hη₁p.le hη₂p.le hE1
      (by simpa only [Matrix.conjTranspose_conjTranspose] using! hE2)
    exact (not_lt_of_ge (h.trans hbudget)) hb
  refine ⟨twoSketchRecordLaw qs r c condQ, (fun _ _ => rfl), ?_⟩
  have h := twoSketch_union_bound qs r c condQ E₁ E₂ Bad (δ/2) (δ/2) hsub hrow hcol
  exact h.trans (by linarith)

end Qatlib.Concepts.SketchSpectral.SketchAnalysis
