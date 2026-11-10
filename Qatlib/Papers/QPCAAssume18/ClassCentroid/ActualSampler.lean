/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassCentroid.GeneralInput
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassCentroid

open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

def generalTensorA {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) : Fin d × Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun p => tensorA (centroidBlock anchor u V) p.1 p.2.1 p.2.2

def generalTensorB {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) : Fin d × Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun p => tensorB (centroidWeights u V) (centroidBlock anchor u V) p.1 p.2.1 p.2.2

theorem generalTensorA_energy {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1) :
    sqSquaredNorm (generalTensorA anchor u V) = 4 := by
  simp only [sqSquaredNorm, generalTensorA, Fintype.sum_prod_type]
  rw [source_theorem6_tensor_energy_a, centroidBlock_energy anchor u V hn ha]
  norm_num

theorem generalTensorB_energy {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1) :
    sqSquaredNorm (generalTensorB anchor u V) = (averageNormSq u V) ^ 2 := by
  simp only [sqSquaredNorm, generalTensorB, Fintype.sum_prod_type]
  rw [source_theorem6_tensor_energy_b (centroidWeights u V) (centroidBlock anchor u V)
      (centroidBlock_rowNorm_pos anchor u V hn ha), centroidWeights_energy]

theorem generalTensor_inner_objective {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1) :
    (sqInnerTarget (generalTensorA anchor u V) (generalTensorB anchor u V)).re =
      ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k) := by
  simp only [sqInnerTarget, generalTensorA, generalTensorB, Fintype.sum_prod_type]
  rw [source_theorem6_tensor_inner (centroidWeights u V) (centroidBlock anchor u V)
    (centroidBlock_rowNorm_pos anchor u V hn ha)]
  have hswap : (∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
      centroidWeights u V k * star (centroidWeights u V j) *
        (∑ i, centroidBlock anchor u V k i * star (centroidBlock anchor u V j i))) =
      ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
      centroidWeights u V j * star (centroidWeights u V k) *
        (∑ i, centroidBlock anchor u V j i * star (centroidBlock anchor u V k i)) :=
    Finset.sum_comm
  rw [hswap, ← source_theorem6_gram]
  simp_rw [centroidBlock_reduction]

def centroidTensorInput {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1) :
    FiniteSQInput (Fin d × Fin (n + 1) × Fin (n + 1)) where
  target := generalTensorA anchor u V
  envelope := generalTensorA anchor u V
  samples := {
    prob := fun p => Complex.normSq (generalTensorA anchor u V p) / 4
    nonneg := fun p => div_nonneg (Complex.normSq_nonneg _) (by norm_num)
    sum_one := by
      rw [← Finset.sum_div]
      change sqSquaredNorm (generalTensorA anchor u V) / 4 = 1
      rw [generalTensorA_energy anchor u V hn ha]
      norm_num
  }
  cachedEnvelopeSquaredNorm := 4
  norm_spec := (generalTensorA_energy anchor u V hn ha).symm
  envelope_pos := by rw [generalTensorA_energy anchor u V hn ha]; norm_num
  domination := fun _ => le_refl _
  sample_spec := by
    intro p
    change Complex.normSq (generalTensorA anchor u V p) / 4 =
      Complex.normSq (generalTensorA anchor u V p) / sqSquaredNorm (generalTensorA anchor u V)
    rw [generalTensorA_energy anchor u V hn ha]

theorem centroidTensorInput_fields {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1) :
    (centroidTensorInput anchor u V hn ha).target = generalTensorA anchor u V ∧
      (centroidTensorInput anchor u V hn ha).envelope = generalTensorA anchor u V ∧
      (centroidTensorInput anchor u V hn ha).cachedEnvelopeSquaredNorm = 4 :=
  ⟨rfl, rfl, rfl⟩

theorem centroid_actual_median_guarantee {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ) (eps : ℝ) (hm : 0 < m) (heps : 0 < eps)
    (hbudget : 256 * (averageNormSq u V) ^ 2 ≤ (m : ℝ) * eps ^ 2) :
    sqBadMass (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
      m r eps ≤ 2 * (2 : ℝ) ^ (2 * r + 1) * (1 / 16 : ℝ) ^ (r + 1) := by
  apply finite_sq_component_median_complex_guarantee _ _ _ m r eps hm heps
  change 64 * sqSquaredNorm (generalTensorA anchor u V) *
    sqSquaredNorm (generalTensorB anchor u V) ≤ _
  rw [generalTensorA_energy anchor u V hn ha, generalTensorB_energy anchor u V hn ha]
  nlinarith

theorem centroid_actual_output_error {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (m r : ℕ) (eps : ℝ)
    (omega : Fin (2 * r + 1) → Fin m → (Fin d × Fin (n + 1) × Fin (n + 1)))
    (hgood : ¬ eps < ‖sqMedian (centroidTensorInput anchor u V hn ha)
      (generalTensorB anchor u V) m r omega -
        sqInnerTarget (generalTensorA anchor u V) (generalTensorB anchor u V)‖) :
    |(sqMedianCounted (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V)
        m r omega).1.re - ∑ k, Complex.normSq (u k - (n : ℂ)⁻¹ * ∑ i, V i k)| ≤ eps := by
  have hledger := finite_sq_linear_median_and_actual_query_ledger _
    (centroidTensorInput anchor u V hn ha) (generalTensorB anchor u V) m r omega
  rw [hledger.2.2.2.2.2.2.1]
  rw [← generalTensor_inner_objective anchor u V hn ha]
  exact (Complex.abs_re_le_norm _).trans (le_of_not_gt hgood)

def centroidRowScale (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  Fin.cases 1 (fun _ => (Real.sqrt (n : ℝ))⁻¹) j

def centroidUnitRow {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) : Fin d → ℂ :=
  Fin.cases (normalizeInput anchor u) (fun i => normalizeInput anchor (V i)) j

theorem centroidBlock_factor {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (j : Fin (n + 1)) (i : Fin d) :
    centroidBlock anchor u V j i =
      (centroidRowScale n j : ℂ) * centroidUnitRow anchor u V j i := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [centroidBlock, ncMatrix, centroidRowScale, centroidUnitRow]
  · simp [centroidBlock, ncMatrix, centroidRowScale, centroidUnitRow, normalizedRows]

theorem centroidUnitRow_energy {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (ha : vectorEnergy anchor = 1)
    (j : Fin (n + 1)) : vectorEnergy (centroidUnitRow anchor u V j) = 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact normalizeInput_energy anchor u ha
  · exact normalizeInput_energy anchor (V _) ha

theorem centroidBlock_row_norm {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (ha : vectorEnergy anchor = 1)
    (j : Fin (n + 1)) :
    (rowNorm (centroidBlock anchor u V) j) ^ 2 = centroidRowScale n j ^ 2 := by
  rw [rowNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)]
  simp_rw [centroidBlock_factor, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  have h := centroidUnitRow_energy anchor u V ha j
  unfold vectorEnergy at h
  rw [h]
  ring

def centroidRowLaw (n : ℕ) (hn : 0 < n) : FinDist (Fin (n + 1)) where
  prob := Fin.cases (1 / 2) (fun _ => 1 / (2 * (n : ℝ)))
  nonneg := by
    intro j
    refine Fin.cases (by norm_num) (fun _ => ?_) j
    change 0 ≤ 1 / (2 * (n : ℝ))
    positivity
  sum_one := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

theorem centroidRowLaw_prob (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) :
    (centroidRowLaw n hn).prob j = (centroidRowScale n j) ^ 2 / 2 := by
  refine Fin.cases (by norm_num [centroidRowLaw, centroidRowScale]) (fun i => ?_) j
  simp only [centroidRowLaw, centroidRowScale, Fin.cases_succ]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

theorem centroidTensorInput_hierarchical {n d : ℕ} (anchor u : Fin d → ℂ)
    (V : Matrix (Fin n) (Fin d) ℂ) (hn : 0 < n) (ha : vectorEnergy anchor = 1)
    (p : Fin d × Fin (n + 1) × Fin (n + 1)) :
    (centroidTensorInput anchor u V hn ha).samples.prob p =
      (centroidRowLaw n hn).prob p.2.1 * (centroidRowLaw n hn).prob p.2.2 *
        Complex.normSq (centroidUnitRow anchor u V p.2.1 p.1) := by
  change Complex.normSq (generalTensorA anchor u V p) / 4 = _
  simp only [generalTensorA, tensorA, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [show rowNorm (centroidBlock anchor u V) p.2.2 *
      rowNorm (centroidBlock anchor u V) p.2.2 =
      rowNorm (centroidBlock anchor u V) p.2.2 ^ 2 by ring,
    centroidBlock_row_norm anchor u V ha p.2.2, centroidBlock_factor,
    Complex.normSq_mul, Complex.normSq_ofReal, centroidRowLaw_prob, centroidRowLaw_prob]
  ring

theorem normalizeInput_probability {d : ℕ} (anchor v : Fin d → ℂ)
    (hv : vectorEnergy v ≠ 0) (i : Fin d) :
    Complex.normSq (normalizeInput anchor v i) =
      Complex.normSq (v i) / vectorEnergy v := by
  rw [normalizeInput, if_neg hv]
  simp only [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal]
  rw [show Real.sqrt (vectorEnergy v) * Real.sqrt (vectorEnergy v) = vectorEnergy v by
    exact Real.mul_self_sqrt (vectorEnergy_nonneg v)]
  ring

end Qatlib.Papers.QPCAAssume18.ClassCentroid
