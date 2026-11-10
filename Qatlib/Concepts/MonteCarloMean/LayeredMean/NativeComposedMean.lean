/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
import Mathlib.Data.Fin.Tuple.Sort
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.NativeNumerics.LayeredMean

namespace Qatlib.Concepts.MonteCarloMean.LayeredMean
open Matrix
open scoped BigOperators

def nativeRationalMedian (r : ℕ) (v : Fin (2*r+1) → ℚ) : ℚ :=
  ((List.ofFn v).mergeSort (fun a b => a ≤ b)).getD r 0

def nativeLayerOutput (k : ℕ) (ω : LayerRecord k) : ℚ :=
  ∑ l : Fin (k+2), (2 : ℚ)^l.val * nativeRationalMedian (layerRepetitions k)
    (fun z => nativeAEDecode (layerGrid k) (2*k+8) (ω l z))

noncomputable section
open scoped Classical
set_option warningAsError false

theorem nativeRationalMedian_cast (r : ℕ) (v : Fin (2*r+1) → ℚ) :
    (nativeRationalMedian r v : ℝ) = sortedBlockMedian r (fun i => (v i : ℝ)) := by
  let xs := List.ofFn v
  have hp := ((List.mergeSort_perm xs (fun a b => a ≤ b)).map (fun x : ℚ => (x : ℝ))).trans
    (insertionSortCounted_perm (xs.map (fun x : ℚ => (x : ℝ)))).symm
  have hq : ((xs.mergeSort (fun a b => a ≤ b)).map (fun x : ℚ => (x : ℝ))).SortedLE := by
    rw [List.sortedLE_iff_pairwise, List.pairwise_map]
    exact (List.sortedLE_iff_pairwise.mp List.sortedLE_mergeSort).imp
      (fun h => by exact_mod_cast h)
  have hc := hp.eq_of_pairwise' (List.sortedLE_iff_pairwise.mp hq)
    (List.sortedLE_iff_pairwise.mp (insertionSortCounted_sorted _))
  unfold nativeRationalMedian
  rw [show (((List.ofFn v).mergeSort (fun a b => a ≤ b)).getD r 0 : ℝ) =
    (((xs.mergeSort (fun a b => a ≤ b)).map (fun x : ℚ => (x : ℝ))).getD r 0) by
      simpa only [Rat.cast_zero] using! (List.getD_map (xs.mergeSort (fun a b => a ≤ b)) 0
        (n := r) (fun x : ℚ => (x : ℝ))).symm]
  rw [hc]
  simp only [xs, List.map_ofFn, Function.comp_def, sortedBlockMedian]

private def nativeRank {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : ℝ := v (Tuple.sort v i)

private theorem native_sorted_filter_card {n : ℕ} (v : Fin n → ℝ) (a : ℝ) :
    (Finset.univ.filter (fun i => nativeRank v i ≤ a)).card =
      (Finset.univ.filter (fun i => v i ≤ a)).card := by
  apply Finset.card_bij (fun i _ => Tuple.sort v i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, nativeRank] using! hi
  · intro i _ j _ hij
    exact (Tuple.sort v).injective hij
  · intro j hj
    refine ⟨(Tuple.sort v).symm j, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, nativeRank,
      Equiv.apply_symm_apply] using! hj

private theorem nativeRank_mono {n : ℕ} (v w : Fin n → ℝ)
    (h : ∀ i, v i ≤ w i) (i : Fin n) : nativeRank v i ≤ nativeRank w i := by
  have hw : i.val < (Finset.univ.filter (fun j => w j ≤ nativeRank w i)).card := by
    rw [← native_sorted_filter_card]
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort w)).mpr le_rfl
  have hsub : (Finset.univ.filter (fun j => w j ≤ nativeRank w i)) ⊆
      (Finset.univ.filter (fun j => v j ≤ nativeRank w i)) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (h j).trans (Finset.mem_filter.mp hj).2⟩
  have hv := hw.trans_le (Finset.card_le_card hsub)
  rw [← native_sorted_filter_card] at hv
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort v)).mp hv

private theorem nativeRank_add {n : ℕ} (v : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    nativeRank (fun j => v j+c) i = nativeRank v i+c := by
  have hm : Monotone ((fun j => v j+c) ∘ Tuple.sort v) := by
    intro x y hxy
    simpa only [Function.comp_apply, add_comm] using! add_le_add_right (Tuple.monotone_sort v hxy) c
  have he := Tuple.unique_monotone (Tuple.monotone_sort (fun j => v j+c)) hm
  exact congrFun he i

private theorem native_median_rank (r : ℕ) (v : Fin (2*r+1) → ℝ) :
    sortedBlockMedian r v = nativeRank v ⟨r, by omega⟩ := by
  have hp := (insertionSortCounted_perm (List.ofFn v)).trans
    ((Tuple.sort v).ofFn_comp_perm v).symm
  have he := hp.eq_of_pairwise' (List.sortedLE_iff_pairwise.mp (insertionSortCounted_sorted _))
    (List.sortedLE_iff_pairwise.mp (Tuple.monotone_sort v).sortedLE_ofFn)
  unfold sortedBlockMedian
  rw [he, List.getD_eq_getElem _ 0 (by simp; omega)]
  simp only [List.getElem_ofFn, Function.comp_apply, nativeRank]

theorem native_sorted_median_uniform_error (r : ℕ) (v w : Fin (2*r+1) → ℝ)
    (δ : ℝ) (h : ∀ i, |v i-w i| ≤ δ) :
    |sortedBlockMedian r v-sortedBlockMedian r w| ≤ δ := by
  rw [native_median_rank, native_median_rank]
  have h1 := nativeRank_mono v (fun i => w i+δ) (fun i => by
    have hi := (abs_le.mp (h i)).2; linarith) ⟨r, by omega⟩
  have h2 := nativeRank_mono w (fun i => v i+δ) (fun i => by
    have hi := (abs_le.mp (h i)).1; linarith) ⟨r, by omega⟩
  rw [nativeRank_add] at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem native_geom_two_sum_le (n : ℕ) : (∑ l : Fin n, (2 : ℝ)^l.val) ≤ (2 : ℝ)^n := by
  have hh : (∑ l : Fin n, (2 : ℝ)^l.val) = (2 : ℝ)^n-1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, pow_succ]
      ring
  rw [hh]
  linarith

theorem native_layered_readout_uniform_error :
    ∀ (k : ℕ),
      let out := fun ω : LayerRecord k =>
        ∑ l : Fin (k+2), (2 : ℚ)^l.val *
          (((List.ofFn (fun z : Fin (2*layerRepetitions k+1) =>
            nativeAEDecode (layerGrid k) (2*k+8) (ω l z))).mergeSort (fun a b => a ≤ b)).getD (layerRepetitions k) 0)
      ∀ ω : LayerRecord k,
        |(out ω : ℝ)-layerEstimate k ω| ≤ (1/2 : ℝ)^(k+6) := by
  intro k out ω
  have hmed (l : Fin (k+2)) :
      |(nativeRationalMedian (layerRepetitions k)
        (fun z => nativeAEDecode (layerGrid k) (2*k+8) (ω l z)) : ℝ) -
          meanMedian (layerRepetitions k) (layerGrid k) (ω l)| ≤ (1/2 : ℝ)^(2*k+8) := by
    rw [nativeRationalMedian_cast]
    apply native_sorted_median_uniform_error
    intro z
    simpa only [show ((2 : ℝ)⁻¹) = 1/2 by norm_num] using!
      (native_ae_computed_scalar_precision (layerGrid k) (2*k+8) (ω l z)).2.2
  change |(nativeLayerOutput k ω : ℝ)-layerEstimate k ω| ≤ _
  simp only [nativeLayerOutput, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    layerEstimate, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l : Fin (k+2), |(2 : ℝ)^l.val *
      (nativeRationalMedian (layerRepetitions k)
        (fun z => nativeAEDecode (layerGrid k) (2*k+8) (ω l z)) : ℝ)-
        (2 : ℝ)^l.val*meanMedian (layerRepetitions k) (layerGrid k) (ω l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin (k+2), (2 : ℝ)^l.val*(1/2 : ℝ)^(2*k+8) := by
      apply Finset.sum_le_sum
      intro l _
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2^l.val)]
      exact mul_le_mul_of_nonneg_left (hmed l) (by positivity)
    _ ≤ (2 : ℝ)^(k+2)*(1/2 : ℝ)^(2*k+8) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (native_geom_two_sum_le (k+2)) (by positivity)
    _ = _ := by
      rw [show 2*k+8 = (k+2)+(k+6) by omega,
        pow_add (1/2 : ℝ) (k+2) (k+6), ← mul_assoc, ← mul_pow]
      norm_num

theorem native_layered_rational_output_success :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (j : I) (f : I → ℚ) (k : ℕ) (_hA : A ∈ Matrix.unitaryGroup I ℂ),
      (∀ i, 0 ≤ f i) → (∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ)^2) ≤ 1 →
      ∃ (hP : ∀ l : Fin (k+2), nativeLayerPrepare A f k l.val ∈ Matrix.unitaryGroup (I×Bool) ℂ),
      let out := fun ω : LayerRecord k =>
        ∑ l : Fin (k+2), (2 : ℚ)^l.val *
          (((List.ofFn (fun z : Fin (2*layerRepetitions k+1) =>
            nativeAEDecode (layerGrid k) (2*k+8) (ω l z))).mergeSort (fun a b => a ≤ b)).getD (layerRepetitions k) 0)
      let law := nativeLayerLaw A j f k hP
      (∑ ω ∈ Finset.univ.filter (fun ω : LayerRecord k =>
        |(out ω : ℝ)-∑ i, BornProb (A *ᵥ Ket j) i*(f i : ℝ)| ≤ 2*(1/2 : ℝ)^k), law.prob ω) ≥
          1-2*(1/2 : ℝ)^k := by
  intro I _ _ A j f k hA hf hE
  let hP := fun l : Fin (k+2) => nativeLayerPrepare_unitary A f k l.val hA hf
  refine ⟨hP, ?_⟩
  (try dsimp only)
  have hg := native_layered_actual_mean_guarantee I A j f k hA hf hP
    (nativeLayerLaw A j f k hP) (fun _ => rfl) hE
  refine hg.trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ω _ _ => (nativeLayerLaw A j f k hP).nonneg ω))
  intro ω hω
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hold := (Finset.mem_filter.mp hω).2
  have hdecode := native_layered_readout_uniform_error k ω
  have hp : (1/2 : ℝ)^(k+6) ≤ (1/2 : ℝ)^k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact (abs_sub_le _ (layerEstimate k ω) _).trans (by linarith)

end
end Qatlib.Concepts.MonteCarloMean.LayeredMean
