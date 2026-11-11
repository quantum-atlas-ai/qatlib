/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.NearestCentroid

/-!
# Normalizing general centroid inputs

Constructs normalized vectors and rows for the classical nearest-centroid reduction of
[Tang2021], using an anchor for zero vectors. `centroidBlock` and `centroidWeights` recover the
original centroid difference and retain the normalization and positive-row-norm properties
needed by the estimator.

## Main statements

* `centroidBlock_energy`: With a unit-energy anchor and a positive number of rows, the centroid
  block has Frobenius energy two.
* `centroidBlock_rowNorm_pos`: With a unit-energy anchor and a positive number of rows, every
  row of the centroid block has positive norm.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

/-- The squared Euclidean energy of a finite complex vector is nonnegative. -/
theorem vectorEnergy_nonneg {d : ℕ} (v : Fin d → ℂ) : 0 ≤ vectorEnergy v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)

/-- Every entry of a finite complex vector with zero energy is zero. -/
theorem vectorEnergy_zero_entries {d : ℕ} (v : Fin d → ℂ)
    (h : vectorEnergy v = 0) : ∀ i, v i = 0 := by
  intro i
  apply Complex.normSq_eq_zero.mp
  have hsingle : Complex.normSq (v i) ≤ vectorEnergy v :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
  exact le_antisymm (h ▸ hsingle) (Complex.normSq_nonneg _)

/-- The vector divided by the square root of its energy when that energy is nonzero, and the
supplied anchor otherwise. -/
def normalizeInput {d : ℕ} (anchor v : Fin d → ℂ) : Fin d → ℂ :=
  if vectorEnergy v = 0 then anchor else
    fun i => ((Real.sqrt (vectorEnergy v) : ℂ))⁻¹ * v i

/-- Multiplying a normalized input by the square root of its original energy recovers each
original entry, including the zero-energy case. -/
theorem normalizeInput_scale {d : ℕ} (anchor v : Fin d → ℂ) (i : Fin d) :
    (Real.sqrt (vectorEnergy v) : ℂ) * normalizeInput anchor v i = v i := by
  by_cases hv : vectorEnergy v = 0
  · simp [normalizeInput, hv, vectorEnergy_zero_entries v hv i]
  · have hp : 0 < vectorEnergy v := lt_of_le_of_ne (vectorEnergy_nonneg v) (Ne.symm hv)
    have hs : (Real.sqrt (vectorEnergy v) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
    simp [normalizeInput, hv, hs]

/-- Normalizing any input with a unit-energy anchor produces a unit-energy vector. -/
theorem normalizeInput_energy {d : ℕ} (anchor v : Fin d → ℂ)
    (ha : vectorEnergy anchor = 1) : vectorEnergy (normalizeInput anchor v) = 1 := by
  by_cases hv : vectorEnergy v = 0
  · simpa [normalizeInput, hv] using! ha
  · have hs : Complex.normSq (Real.sqrt (vectorEnergy v) : ℂ) = vectorEnergy v := by
      rw [Complex.normSq_ofReal, ← sq]
      exact Real.sq_sqrt (vectorEnergy_nonneg v)
    rw [normalizeInput, if_neg hv]
    simp only [vectorEnergy, Complex.normSq_mul, Complex.normSq_inv, ← Finset.mul_sum]
    change (Complex.normSq (Real.sqrt (vectorEnergy v) : ℂ))⁻¹ * vectorEnergy v = 1
    rw [hs, inv_mul_cancel₀ hv]

/-- The coordinate vector equal to one at index zero and zero elsewhere in positive dimension. -/
def coordinateAnchor {d : ℕ} (hd : 0 < d) : Fin d → ℂ :=
  fun i => if i = ⟨0, hd⟩ then 1 else 0

/-- The coordinate anchor has energy one. -/
theorem coordinateAnchor_energy {d : ℕ} (hd : 0 < d) :
    vectorEnergy (coordinateAnchor hd) = 1 := by
  classical
  simp [vectorEnergy, coordinateAnchor]

/-- The matrix obtained by applying `normalizeInput` to each row with a common anchor. -/
def normalizedRows {n d : ℕ} (anchor : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) : Matrix (Fin n) (Fin d) ℂ :=
  fun i => normalizeInput anchor (V i)

/-- The nearest-centroid block matrix formed from the normalized input vector and normalized
matrix rows. -/
def centroidBlock {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) : Matrix (Fin (n + 1)) (Fin d) ℂ :=
  ncMatrix (normalizeInput anchor u) (normalizedRows anchor V)

/-- The weights consisting of the input norm and the negative row norms divided by the square
root of the number of rows. -/
def centroidWeights {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) : Fin (n + 1) → ℂ :=
  fun j => Fin.cases (Real.sqrt (vectorEnergy u) : ℂ)
    (fun i => -(Real.sqrt (vectorEnergy (V i)) : ℂ) *
      (Real.sqrt (n : ℝ) : ℂ)⁻¹) j

/-- The weighted centroid block recovers each coordinate of the input vector minus the mean of
the original matrix rows. -/
theorem centroidBlock_reduction {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (k : Fin d) :
    ∑ j, centroidWeights u V j * centroidBlock anchor u V j k =
      u k - (n : ℂ)⁻¹ * ∑ i, V i k := by
  have hs : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
  have hi : (Real.sqrt (n : ℝ) : ℂ)⁻¹ ^ 2 = (n : ℂ)⁻¹ := by
    rw [inv_pow, hs]
  rw [Fin.sum_univ_succ]
  simp only [centroidWeights, centroidBlock, ncMatrix, Fin.cases_zero, Fin.cases_succ]
  rw [normalizeInput_scale]
  have hterm (i : Fin n) :
      (-(Real.sqrt (vectorEnergy (V i)) : ℂ) * (Real.sqrt (n : ℝ) : ℂ)⁻¹) *
          ((Real.sqrt (n : ℝ) : ℂ)⁻¹ * normalizedRows anchor V i k) =
        -(n : ℂ)⁻¹ * V i k := by
    calc
      _ = -((Real.sqrt (n : ℝ) : ℂ)⁻¹ ^ 2) *
          ((Real.sqrt (vectorEnergy (V i)) : ℂ) * normalizeInput anchor (V i) k) := by
        unfold normalizedRows
        ring
      _ = -(n : ℂ)⁻¹ * V i k := by rw [hi, normalizeInput_scale]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  ring

/-- The sum of squared moduli of the centroid weights equals `averageNormSq u V`. -/
theorem centroidWeights_energy {n d : ℕ} (u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) :
    (∑ j, Complex.normSq (centroidWeights u V j)) = averageNormSq u V := by
  have hroot (x : ℝ) (hx : 0 ≤ x) : Complex.normSq (Real.sqrt x : ℂ) = x := by
    rw [Complex.normSq_ofReal, ← sq]
    exact Real.sq_sqrt hx
  rw [Fin.sum_univ_succ]
  simp only [centroidWeights, Fin.cases_zero, Fin.cases_succ, Complex.normSq_mul,
    Complex.normSq_neg, Complex.normSq_inv]
  simp_rw [hroot _ (vectorEnergy_nonneg _), hroot _ (Nat.cast_nonneg n)]
  unfold averageNormSq frobeniusEnergy vectorEnergy
  rw [Finset.mul_sum]
  refine congrArg (fun z => (∑ k, Complex.normSq (u k)) + z) ?_
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- With a unit-energy anchor and a positive number of rows, the centroid block has Frobenius
energy two. -/
theorem centroidBlock_energy {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (ha : vectorEnergy anchor = 1) : frobeniusEnergy (centroidBlock anchor u V) = 2 := by
  exact source_theorem6_matrix_energy (normalizeInput anchor u) (normalizedRows anchor V)
    hn (normalizeInput_energy anchor u ha) (fun i => normalizeInput_energy anchor (V i) ha)

/-- With a unit-energy anchor and a positive number of rows, every row of the centroid block has
positive norm. -/
theorem centroidBlock_rowNorm_pos {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n)
    (ha : vectorEnergy anchor = 1) : ∀ j, 0 < rowNorm (centroidBlock anchor u V) j := by
  exact source_theorem6_rowNorm_pos (normalizeInput anchor u) (normalizedRows anchor V)
    hn (normalizeInput_energy anchor u ha) (fun i => normalizeInput_energy anchor (V i) ha)

end Qatlib.Papers.QPCAAssume18.ClassCentroid
