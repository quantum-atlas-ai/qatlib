/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualColumnAccess
import Qatlib.Papers.QPCAAssume18.ClassicalPca.OutputAccuracy

/-!
# Proposal laws for lifted PCA vectors

Expresses lifted PCA vectors as linear combinations of conjugated sketch rows and constructs
their coordinate proposal and rejection coin. Weighted cached row energies identify the envelope
distribution and the query count required for the output access model in [Tang2021].

## Main statements

* `pcaVectorProposal_probability`: For positive `q`, the vector proposal equals the normalized
  squared-amplitude distribution of the linear envelope.
* `pca_vector_query_count`: Querying one coordinate of the linear combination returns its exact
  value and records exactly `q` row-coordinate queries.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SqEstimation.RejectionSample

/-- The small-sketch eigenvector coordinates scaled by the inverse square root of the
corresponding squared singular value. -/
def pcaOutputCoefficients {q : ℕ} (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (t : Fin q) : ℂ :=
  (Real.sqrt (pcaSmallValue W i) : ℂ)⁻¹ * pcaSmallVector W i t

/-- The coordinatewise conjugate of a row of `R`. -/
def pcaConjugateRows {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ) (t : Fin q) (j : Fin d) : ℂ :=
  star (R t j)

/-- The sum of coefficient squared magnitudes weighted by cached sketch row energies. -/
def pcaWeightedEnergy {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (rows : Fin q → Fin n) (c : Fin q → ℂ) : ℝ :=
  ∑ t, Complex.normSq (c t)*pcaCachedRowEnergy A hA q rows t

/-- The cached weighted energy equals the sum of coefficient squared magnitudes times the
energies of the conjugated sketch rows. -/
theorem pcaWeightedEnergy_spec {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (rows : Fin q → Fin n) (c : Fin q → ℂ) :
    pcaWeightedEnergy A hA rows c = ∑ t, Complex.normSq (c t)*
      ∑ j, Complex.normSq (pcaConjugateRows (pcaRowSketch A hA q rows) t j) := by
  simp only [pcaWeightedEnergy,pcaCachedRowEnergy_spec,sketchRowSquared,pcaConjugateRows,
    Complex.star_def,Complex.normSq_conj]

/-- The squared magnitude of a linear combination is bounded coordinatewise by that of its
sampling envelope. -/
theorem pca_linear_dominance {q d : ℕ} (c : Fin q → ℂ) (u : Fin q → Fin d → ℂ) (j : Fin d) :
    Complex.normSq (sqLinearValue c u j) ≤ Complex.normSq (sqLinearEnvelope c u j) := by
  rw [sqLinearEnvelope_normSq,Complex.normSq_eq_norm_sq,sqLinearValue]
  have hn := norm_sum_le Finset.univ (fun t => c t*u t j)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun t => ‖c t*u t j‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hc
  calc
    _ ≤ (∑ t, ‖c t*u t j‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := hc
    _ = _ := by simp_rw [← Complex.normSq_eq_norm_sq]; ring

/-- The total squared envelope magnitude equals `q` times the weighted row energy. -/
theorem pca_envelope_energy {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (rows : Fin q → Fin n) (c : Fin q → ℂ) :
    (∑ j, Complex.normSq (sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows)) j)) =
      q * pcaWeightedEnergy A hA rows c := by
  rw [pcaWeightedEnergy_spec]
  simp_rw [sqLinearEnvelope_normSq,Complex.normSq_mul]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp only [Fintype.card_fin,← Finset.mul_sum]

/-- A linear combination with positive energy has positive weighted row energy. -/
theorem pca_weighted_energy_pos {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (rows : Fin q → Fin n) (c : Fin q → ℂ)
    (hu : 0 < ∑ j,Complex.normSq (sqLinearValue c (pcaConjugateRows (pcaRowSketch A hA q rows)) j)) :
    0 < pcaWeightedEnergy A hA rows c := by
  have hd := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
    pca_linear_dominance c (pcaConjugateRows (pcaRowSketch A hA q rows)) j)
  rw [pca_envelope_energy] at hd
  have hp : 0<(q:ℝ)*pcaWeightedEnergy A hA rows c := hu.trans_le hd
  have hnonneg : 0≤(q:ℝ) := Nat.cast_nonneg q
  nlinarith

/-- The coordinate proposal formed by mixing raw row coordinate laws with weights proportional
to coefficient squared magnitudes times cached row energies. -/
def pcaVectorProposal {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (rows : Fin q → Fin n) (c : Fin q → ℂ)
    (hweight : 0 < pcaWeightedEnergy A hA rows c) : FinDist (Fin d) where
  prob j := ∑ t, (Complex.normSq (c t)*pcaCachedRowEnergy A hA q rows t /
      pcaWeightedEnergy A hA rows c) * (pcaRawCoordinateLaw A hd (rows t)).prob j
  nonneg j := Finset.sum_nonneg fun t _ => mul_nonneg (div_nonneg
    (mul_nonneg (Complex.normSq_nonneg _) (by rw [pcaCachedRowEnergy_spec]; exact sketchRowSquared_nonneg _ _)) hweight.le)
    ((pcaRawCoordinateLaw A hd (rows t)).nonneg j)
  sum_one := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,(pcaRawCoordinateLaw A hd _).sum_one,mul_one,← Finset.sum_div]
    exact div_self hweight.ne'

/-- For positive `q`, the vector proposal equals the normalized squared-amplitude distribution
of the linear envelope. -/
theorem pcaVectorProposal_probability {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (hq : 0<q)
    (rows : Fin q → Fin n) (c : Fin q → ℂ) (hweight : 0 < pcaWeightedEnergy A hA rows c) (j : Fin d) :
    (pcaVectorProposal A hA hd rows c hweight).prob j =
      Complex.normSq (sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows)) j) /
        (∑ j,Complex.normSq (sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows)) j)) := by
  rw [pca_envelope_energy,sqLinearEnvelope_normSq]
  simp only [pcaVectorProposal,Fintype.card_fin]
  have hqR : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  calc
    _ = (∑ t,Complex.normSq (c t)*Complex.normSq (pcaRowSketch A hA q rows t j)) /
        pcaWeightedEnergy A hA rows c := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [← pcaColumnMixture_entry A hA hd q rows t j, ← pcaCachedRowEnergy_spec]
      ring
    _ = _ := by
      simp only [pcaConjugateRows,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj]
      field_simp

/-- The Boolean coin with success probability equal to the output-to-envelope acceptance ratio. -/
def pcaVectorCoin {q d : ℕ} (c : Fin q → ℂ) (u : Fin q → Fin d → ℂ)
    (hen : SQEnvelope (sqLinearValue c u) (sqLinearEnvelope c u)) (j : Fin d) : FinDist Bool where
  prob b := if b then sqRatio (sqLinearValue c u) (sqLinearEnvelope c u) j else
    1-sqRatio (sqLinearValue c u) (sqLinearEnvelope c u) j
  nonneg b := by
    cases b
    · exact sub_nonneg.mpr (sqRatio_range _ _ hen j).2
    · exact (sqRatio_range _ _ hen j).1
  sum_one := by simp

/-- The success probability of `pcaVectorCoin` is the corresponding `sqRatio`. -/
theorem pcaVectorCoin_probability {q d : ℕ} (c : Fin q → ℂ) (u : Fin q → Fin d → ℂ)
    (hen : SQEnvelope (sqLinearValue c u) (sqLinearEnvelope c u)) (j : Fin d) :
    (pcaVectorCoin c u hen j).prob true=sqRatio (sqLinearValue c u) (sqLinearEnvelope c u) j := rfl

/-- Querying one coordinate of the linear combination returns its exact value and records
exactly `q` row-coordinate queries. -/
theorem pca_vector_query_count {q d : ℕ} (c : Fin q → ℂ) (u : Fin q → Fin d → ℂ) (j : Fin d) :
    (sqLinearQuery c u j).1=sqLinearValue c u j ∧ (sqLinearQuery c u j).2=q := by
  simpa only [Fintype.card_fin] using! sqLinearQuery_value_count c u j

end Qatlib.Papers.QPCAAssume18.ClassicalPca
