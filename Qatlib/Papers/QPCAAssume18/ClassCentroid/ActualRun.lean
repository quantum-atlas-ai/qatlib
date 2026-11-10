/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualQueries
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

def centroidMeanRead {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    ℂ × List (CentroidCall n d) :=
  let records := List.ofFn fun t => centroidRecordRead anchor u V (omega t)
  ((records.map Prod.fst).sum / (m : ℂ), (records.map Prod.snd).flatten)

theorem centroidMeanRead_value {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidMeanRead anchor u V omega).1 =
      sqMean (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V) omega := by
  simp only [centroidMeanRead, List.map_ofFn, List.sum_ofFn, centroidRecordRead,
    importanceRead_value anchor u V hn ha, sqMean, Function.comp_def]

theorem centroidMeanRead_queries {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidMeanRead anchor u V omega).2.length ≤ 10 * m := by
  simp only [centroidMeanRead, List.map_ofFn, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin m, 10 := Finset.sum_le_sum fun t _ => centroidRecordRead_queries anchor u V _
    _ = 10 * m := by simp; omega

def centroidRunRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    ℂ × List (CentroidCall n d) × ℕ :=
  let means := fun b => centroidMeanRead anchor u V (omega b)
  let re := sqSelect (List.ofFn fun b => (means b).1.re) r
  let im := sqSelect (List.ofFn fun b => (means b).1.im) r
  (((re.1 : ℂ) + (im.1 : ℂ) * Complex.I),
    (List.ofFn fun b => (means b).2).flatten, re.2 + im.2)

theorem centroidRunRead_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidRunRead anchor u V m r omega).1 =
      (sqMedianCounted (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
        m r omega).1 := by
  simp only [centroidRunRead, centroidMeanRead_value anchor u V hn ha, sqMedianCounted]

theorem centroidRunRead_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidRunRead anchor u V m r omega).2.1.length ≤ 10 * (2 * r + 1) * m := by
  simp only [centroidRunRead, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin (2 * r + 1), 10 * m :=
      Finset.sum_le_sum fun b _ => centroidMeanRead_queries anchor u V _
    _ = 10 * (2 * r + 1) * m := by simp; ring

theorem centroidRunRead_comparisons {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidRunRead anchor u V m r omega).2.2 ≤ 20000 * (2 * r + 1) := by
  have hre := (sqSelect_rank_and_cost
    (List.ofFn fun b : Fin (2 * r + 1) => (centroidMeanRead anchor u V (omega b)).1.re) r
      (by simp; omega)).2
  have him := (sqSelect_rank_and_cost
    (List.ofFn fun b : Fin (2 * r + 1) => (centroidMeanRead anchor u V (omega b)).1.im) r
      (by simp; omega)).2
  simp only [List.length_ofFn] at hre him
  exact Nat.add_le_add hre him |>.trans_eq (by ring)

def centroidRunWork {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ) (T : ℝ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) : ℝ :=
  T * (centroidRunRead anchor u V m r omega).2.1.length +
    (centroidRunRead anchor u V m r omega).2.2

theorem centroidRunWork_bound {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    centroidRunWork anchor u V m r T omega ≤
      (10 * T * m + 20000) * (2 * r + 1) := by
  have hq : ((centroidRunRead anchor u V m r omega).2.1.length : ℝ) ≤
      10 * (2 * r + 1) * m := by exact_mod_cast centroidRunRead_queries anchor u V m r omega
  have hc : ((centroidRunRead anchor u V m r omega).2.2 : ℝ) ≤
      20000 * (2 * r + 1) := by exact_mod_cast centroidRunRead_comparisons anchor u V m r omega
  unfold centroidRunWork
  nlinarith [mul_le_mul_of_nonneg_left hq hT]

def centroidFailureMass {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ) (eps : ℝ) : ℝ :=
  ∑ omega ∈ Finset.univ.filter (fun omega : Fin (2 * r + 1) → Fin m →
      (Fin d × Fin (n + 1) × Fin (n + 1)) =>
    eps < |(centroidRunRead anchor u V m r omega).1.re -
      ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)|),
    ∏ b, (centroidTensorInput anchor u V hn ha).samples.probOf (omega b)

theorem centroidFailureMass_le {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ) (eps : ℝ) :
    centroidFailureMass anchor u V hn ha m r eps ≤
      sqBadMass (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V) m r eps := by
  classical
  unfold centroidFailureMass sqBadMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro omega hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    by_contra hgood
    have hacc := centroid_actual_output_error anchor u V hn ha m r eps omega hgood
    rw [← centroidRunRead_value anchor u V hn ha] at hacc
    exact (not_lt_of_ge hacc) hmem
  · intro omega _ _
    apply Finset.prod_nonneg
    intro b _
    exact Finset.prod_nonneg fun t _ => (centroidTensorInput anchor u V hn ha).samples.nonneg (omega b t)

theorem source_nearest_centroid_actual {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    centroidFailureMass (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)
      (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) eps ≤ delta := by
  exact (centroidFailureMass_le (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)
    _ _ eps).trans (centroid_chosen_failure (coordinateAnchor hd) u V hn
      (coordinateAnchor_energy hd) eps delta heps hdelta)

theorem source_nearest_centroid_empty {n : ℕ} (u : Fin 0 → ℂ) (V : Matrix (Fin n) (Fin 0) ℂ) :
    (∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)) = 0 := by simp

end Qatlib.Papers.QPCAAssume18.ClassCentroid
