/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.ActualQueries

/-!
# Executed centroid estimates and resource bounds

This module assembles traced importance samples into means and a componentwise median, recording
both primitive input calls and selection comparisons. It connects the actual real-valued output
to the squared distance from the input vector to the mean matrix row, giving a concrete version
of the classical nearest-centroid guarantee in [Tang2021].

## Main statements

* `centroidMeanRead_value` and `centroidRunRead_value` identify the traced output with the
  sample-and-query estimator.
* `centroidRunRead_queries`, `centroidRunRead_comparisons`, and `centroidRunWork_bound` give
  explicit query, comparison, and weighted-work bounds.
* `centroidFailureMass_le` transfers the complex estimator's failure bound to the real distance
  estimate.
* `source_nearest_centroid_actual` proves failure mass at most `delta` for the chosen budgets;
  `source_nearest_centroid_empty` handles dimension zero.

## References

* [Tang, 2021][Tang2021], *Quantum principal component analysis only achieves an exponential
  speedup because of its state preparation assumptions*, Theorem 4 and Algorithm 4.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Averages the importance values from `m` centroid sample records and concatenates their
primitive access traces. -/
def centroidMeanRead {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    ℂ × List (CentroidCall n d) :=
  let records := List.ofFn fun t => centroidRecordRead anchor u V (omega t)
  ((records.map Prod.fst).sum / (m : ℂ), (records.map Prod.snd).flatten)

/-- For positive `n` and a unit anchor, the traced sample mean equals `sqMean` for the centroid
tensor estimator. -/
theorem centroidMeanRead_value {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidMeanRead anchor u V omega).1 =
      sqMean (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V) omega := by
  simp only [centroidMeanRead, List.map_ofFn, List.sum_ofFn, centroidRecordRead,
    importanceRead_value anchor u V hn ha, sqMean, Function.comp_def]

/-- The trace of a centroid mean formed from `m` sample records has length at most `10 * m`. -/
theorem centroidMeanRead_queries {n d m : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ)
    (omega : Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidMeanRead anchor u V omega).2.length ≤ 10 * m := by
  simp only [centroidMeanRead, List.map_ofFn, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin m, 10 := Finset.sum_le_sum fun t _ => centroidRecordRead_queries anchor u V _
    _ = 10 * m := by simp; omega

/-- Computes the componentwise median of `2 * r + 1` traced centroid means using `sqSelect` on
their real and imaginary parts. It returns the complex estimate, concatenated input-access
trace, and total selection-comparison count. -/
def centroidRunRead {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    ℂ × List (CentroidCall n d) × ℕ :=
  let means := fun b => centroidMeanRead anchor u V (omega b)
  let re := sqSelect (List.ofFn fun b => (means b).1.re) r
  let im := sqSelect (List.ofFn fun b => (means b).1.im) r
  (((re.1 : ℂ) + (im.1 : ℂ) * Complex.I),
    (List.ofFn fun b => (means b).2).flatten, re.2 + im.2)

/-- For positive `n` and a unit anchor, the traced centroid run returns the same complex value
as `sqMedianCounted`. -/
theorem centroidRunRead_value {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidRunRead anchor u V m r omega).1 =
      (sqMedianCounted (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
        m r omega).1 := by
  simp only [centroidRunRead, centroidMeanRead_value anchor u V hn ha, sqMedianCounted]

/-- A centroid run with `2 * r + 1` means of `m` samples records at most `10 * (2 * r + 1) * m`
primitive calls. -/
theorem centroidRunRead_queries {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) :
    (centroidRunRead anchor u V m r omega).2.1.length ≤ 10 * (2 * r + 1) * m := by
  simp only [centroidRunRead, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin (2 * r + 1), 10 * m :=
      Finset.sum_le_sum fun b _ => centroidMeanRead_queries anchor u V _
    _ = 10 * (2 * r + 1) * m := by simp; ring

/-- The real and imaginary median selections together use at most `20000 * (2 * r + 1)`
comparisons. -/
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

/-- The weighted work of a centroid run, charging `T` for each recorded input call and one unit
for each selection comparison. -/
def centroidRunWork {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (m r : ℕ) (T : ℝ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1))) : ℝ :=
  T * (centroidRunRead anchor u V m r omega).2.1.length +
    (centroidRunRead anchor u V m r omega).2.2

/-- For nonnegative input-call cost `T`, the weighted work is at most `(10 * T * m + 20000) * (2
* r + 1)`. -/
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

/-- The probability mass of sample records for which the real output of the traced centroid run
differs from the squared centroid distance by more than `eps`, under independent tensor
draws. -/
def centroidFailureMass {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ) (eps : ℝ) : ℝ :=
  ∑ omega ∈ Finset.univ.filter (fun omega : Fin (2 * r + 1) → Fin m →
      (Fin d × Fin (n + 1) × Fin (n + 1)) =>
    eps < |(centroidRunRead anchor u V m r omega).1.re -
      ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)|),
    ∏ b, (centroidTensorInput anchor u V hn ha).samples.probOf (omega b)

/-- The failure mass of the real centroid-distance output is at most the bad mass of the
underlying complex median estimator. -/
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

/-- For positive row count and dimension and positive `eps` and `delta`, the traced
nearest-centroid estimate with the coordinate anchor and chosen budgets has failure mass at
most `delta`. This realizes the classical nearest-centroid guarantee of [Tang2021] for the
original complex inputs. -/
theorem source_nearest_centroid_actual {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (hd : 0 < d)
    (eps delta : ℝ) (heps : 0 < eps) (hdelta : 0 < delta) :
    centroidFailureMass (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)
      (centroidSamples (averageNormSq u V) eps) (centroidRounds delta) eps ≤ delta := by
  exact (centroidFailureMass_le (coordinateAnchor hd) u V hn (coordinateAnchor_energy hd)
    _ _ eps).trans (centroid_chosen_failure (coordinateAnchor hd) u V hn
      (coordinateAnchor_energy hd) eps delta heps hdelta)

/-- In dimension zero, the squared distance from `u` to the mean matrix row is zero. -/
theorem source_nearest_centroid_empty {n : ℕ} (u : Fin 0 → ℂ) (V : Matrix (Fin n) (Fin 0) ℂ) :
    (∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)) = 0 := by simp

end Qatlib.Papers.QPCAAssume18.ClassCentroid
