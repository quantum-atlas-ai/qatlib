/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualVectorSQ

/-!
# Rejection and norm runs for PCA outputs

Identifies lifted PCA coordinates with a row linear combination and verifies the corresponding
sampling envelope. Exact rejection masses, expected rejection cost, and a relative squared-norm
estimation tail bound establish output access for [Tang2021].

## Main statements

* `pca_actual_output_rejection`: For a nonzero output, bounded rejection sampling has the stated
  geometric failure mass, normalized squared-amplitude success masses, and expected recorded
  cost at most `4 * phi` [Tang2021].
* `pca_actual_output_norm`: For a nonzero PCA output, the prescribed median-of-means estimator
  has relative squared-norm error greater than `1 / 100` with mass at most `2^(2 * r + 1) * (1 /
  16)^(r + 1)`.

## References

* [Tang, 2021][Tang2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SqEstimation.RejectionSample

/-- The linear combination of conjugated rows with output coefficients equals the corresponding
PCA output coordinate. -/
theorem pca_output_coordinate {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (j : Fin d) :
    sqLinearValue (pcaOutputCoefficients W i) (pcaConjugateRows R) j = pcaOutput R W i j := by
  simp only [sqLinearValue,pcaOutputCoefficients,pcaConjugateRows,pcaOutput,
    Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,PiLp.smul_apply,
    Matrix.conjTranspose_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The energy of the row linear combination equals the squared norm of the PCA output. -/
theorem pca_output_energy {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) :
    (∑ j,Complex.normSq (sqLinearValue (pcaOutputCoefficients W i) (pcaConjugateRows R) j)) =
      ‖pcaOutput R W i‖^2 := by
  simp_rw [pca_output_coordinate,Complex.normSq_eq_norm_sq]
  exact (EuclideanSpace.norm_sq_eq _).symm

/-- A nonzero PCA output has a valid linear sampling envelope and positive weighted row energy. -/
theorem pca_output_envelope {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q)
    (hu : 0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖) :
    SQEnvelope (sqLinearValue (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows)))
      (sqLinearEnvelope (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows))) ∧
    0<pcaWeightedEnergy A hA rows (pcaOutputCoefficients W i) := by
  have he : 0<∑ j,Complex.normSq (sqLinearValue (pcaOutputCoefficients W i)
      (pcaConjugateRows (pcaRowSketch A hA q rows)) j) := by
    rw [pca_output_energy]
    positivity
  exact ⟨⟨he,pca_linear_dominance _ _⟩,pca_weighted_energy_pos A hA rows _ he⟩

/-- For a nonzero output, bounded rejection sampling has the stated geometric failure mass,
normalized squared-amplitude success masses, and expected recorded cost at most `4 * phi`
[Tang2021]. -/
theorem pca_actual_output_rejection {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q)
    (hu : 0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖) (B : ℕ) :
    let c := pcaOutputCoefficients W i;
    let env := sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows));
    let hen := (pca_output_envelope A hA rows W i hu).1;
    let proposal := pcaVectorProposal A hA hd rows c (pca_output_envelope A hA rows W i hu).2;
    let coin := pcaVectorCoin c (pcaConjugateRows (pcaRowSketch A hA q rows)) hen;
    let phi := (∑ j,Complex.normSq (env j))/‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2;
    sqRejectMass proposal coin B none=(1-1/phi)^B ∧
    (∀ j,sqRejectMass proposal coin B (some j)=
      (1-(1-1/phi)^B)*Complex.normSq (pcaOutput (pcaRowSketch A hA q rows) W i j)/
        ‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2) ∧
    sqRejectExpectedCost proposal coin B≤4*phi := by
  (try dsimp only)
  have hen := (pca_output_envelope A hA rows W i hu).1
  have hw := (pca_output_envelope A hA rows W i hu).2
  have hp := pcaVectorProposal_probability A hA hd hq rows (pcaOutputCoefficients W i) hw
  have hc := pcaVectorCoin_probability (pcaOutputCoefficients W i)
    (pcaConjugateRows (pcaRowSketch A hA q rows)) hen
  have hmass := sqRejectMass_closed _ _ _ _ hen hp hc B
  have hcost := sqRejectExpectedCost_le _ _ _ _ hen hp hc B
  simp_rw [pca_output_energy,pca_output_coordinate] at hmass hcost
  exact ⟨hmass.1,hmass.2,hcost⟩

/-- The rejection run's recorded cost multiplied by the per-operation access charge `3 * q + 3`. -/
def pcaVectorRejectPaidCost {d B : ℕ} (q : ℕ) (records : Fin B→Fin d×Bool) : ℕ :=
  (3*q+3)*(sqRejectRun records).2

/-- The paid rejection cost for `B` supplied trials is at most `(3 * q + 3) * (4 * B)`. -/
theorem pca_vector_reject_paid_bound {d B : ℕ} (q : ℕ) (records : Fin B→Fin d×Bool) :
    pcaVectorRejectPaidCost q records≤(3*q+3)*(4*B) :=
  Nat.mul_le_mul_left _ (sqRejectRun_cost_le records)

/-- The norm-estimation batch size given by the natural ceiling of `160000 * phi`, plus one. -/
def pcaNormSamples (phi : ℝ) : ℕ := ⌈160000*phi⌉₊+1

/-- The norm-estimation batch size is positive and at least `16 * phi / (1 / 100)^2`. -/
theorem pcaNormSamples_budget (phi : ℝ) :
    0<pcaNormSamples phi ∧ 16*phi/(1/100:ℝ)^2≤(pcaNormSamples phi:ℝ) := by
  refine ⟨by unfold pcaNormSamples; omega,?_⟩
  have h := Nat.le_ceil (160000*phi)
  unfold pcaNormSamples
  push_cast
  norm_num
  linarith

/-- For a nonzero PCA output, the prescribed median-of-means estimator has relative squared-norm
error greater than `1 / 100` with mass at most `2^(2 * r + 1) * (1 / 16)^(r + 1)`. -/
theorem pca_actual_output_norm {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q)
    (hu : 0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖) (r : ℕ) :
    let c := pcaOutputCoefficients W i;
    let env := sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows));
    let hen := (pca_output_envelope A hA rows W i hu).1;
    let proposal := pcaVectorProposal A hA hd rows c (pca_output_envelope A hA rows W i hu).2;
    let coin := pcaVectorCoin c (pcaConjugateRows (pcaRowSketch A hA q rows)) hen;
    let energy := ‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2;
    let envelopeEnergy := ∑ j,Complex.normSq (env j);
    let B := pcaNormSamples (envelopeEnergy/energy);
    (∑ omega ∈ Finset.univ.filter (fun omega : Fin (2*r+1)→Fin B→Fin d×Bool =>
      (1/100:ℝ)*energy < |sqNormSquaredEstimate envelopeEnergy r B omega-energy|),
      ∏ j,sqTrialProduct proposal coin (omega j))≤(2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) := by
  (try dsimp only)
  have hen := (pca_output_envelope A hA rows W i hu).1
  have hw := (pca_output_envelope A hA rows W i hu).2
  have hp := pcaVectorProposal_probability A hA hd hq rows (pcaOutputCoefficients W i) hw
  have hc := pcaVectorCoin_probability (pcaOutputCoefficients W i)
    (pcaConjugateRows (pcaRowSketch A hA q rows)) hen
  have h := sq_rejection_acceptance_norm_estimation (Fin d) _ _ _ _ r
    (pcaNormSamples ((∑ j,Complex.normSq (sqLinearEnvelope (pcaOutputCoefficients W i)
      (pcaConjugateRows (pcaRowSketch A hA q rows)) j))/‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2))
    (1/100) hen hp hc (pcaNormSamples_budget _).1 (by norm_num) (by norm_num) (by
      rw [pca_output_energy]
      exact (pcaNormSamples_budget _).2)
  simp_rw [pca_output_energy] at h
  exact h.1

end Qatlib.Papers.QPCAAssume18.ClassicalPca
