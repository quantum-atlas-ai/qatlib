/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.BatchProbability

/-!
# Sampling protocols for actual PCA vectors

Builds the proposal, acceptance coin, and joint norm-estimation and rejection-sampling record
for lifted PCA outputs. It identifies the exact output distribution and bounds failure of one
access protocol, as used in the sample-and-query construction of [Tang2021].

## Main statements

* `pca_actual_protocol_output_law`: For a nonzero PCA output, bounded rejection sampling fails
  with mass `(1 - 1 / phi)^B` and returns each coordinate with the remaining mass times its
  normalized squared amplitude [Tang2021].
* `pca_actual_protocol_failure`: For a nonzero output with inflation at most `4 * q * K`, the
  prescribed norm and rejection budgets bound total protocol failure by `2 * alpha` [Tang2021].

## References

* [Tang, 2021][Tang2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SqEstimation.RejectionSample

/-- The Boolean distribution concentrated on `false`. -/
def pcaFalseCoin : FinDist Bool where
  prob b := if b then 0 else 1
  nonneg b := by cases b <;> norm_num
  sum_one := by simp

/-- The coordinate proposal for an actual PCA output, using the weighted row mixture when its
energy is positive and a point distribution otherwise. -/
def pcaActualProposal {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) : FinDist (Fin d) :=
  if hweight : 0<pcaWeightedEnergy A hA rows (pcaOutputCoefficients W i) then
    pcaVectorProposal A hA hd rows (pcaOutputCoefficients W i) hweight
  else pcaPointLaw hd

/-- The acceptance ratio for a linear combination and its envelope lies in the interval `[0,
1]`. -/
theorem pca_actual_ratio_range {q d : ℕ} (c : Fin q→ℂ) (u : Fin q→Fin d→ℂ) (j : Fin d) :
    0≤sqRatio (sqLinearValue c u) (sqLinearEnvelope c u) j ∧
      sqRatio (sqLinearValue c u) (sqLinearEnvelope c u) j≤1 := by
  refine ⟨div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),?_⟩
  by_cases hz : Complex.normSq (sqLinearEnvelope c u j)=0
  · simp only [sqRatio,hz,div_zero,zero_le_one]
  · exact (div_le_one (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hz))).mpr
      (pca_linear_dominance c u j)

/-- The Boolean acceptance law whose success probability is the squared-amplitude ratio of the
PCA output to its envelope. -/
def pcaActualCoin {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (j : Fin d) : FinDist Bool where
  prob b := if b then sqRatio (sqLinearValue (pcaOutputCoefficients W i)
    (pcaConjugateRows (pcaRowSketch A hA q rows)))
    (sqLinearEnvelope (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows))) j else
    1-sqRatio (sqLinearValue (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows)))
      (sqLinearEnvelope (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows))) j
  nonneg b := by
    cases b
    · exact sub_nonneg.mpr (pca_actual_ratio_range _ _ j).2
    · exact (pca_actual_ratio_range _ _ j).1
  sum_one := by simp

/-- The joint law of a proposed coordinate and its acceptance outcome for an actual PCA vector. -/
def pcaActualTrial {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) : FinDist (Fin d×Bool) :=
  sqTrialLaw (pcaActualProposal A hA hd rows W i) (pcaActualCoin A hA rows W i)

/-- The joint law of independent norm-estimation batches and an independent rejection-sampling
record. -/
def pcaProtocolLaw {d : ℕ} (trial : FinDist (Fin d×Bool)) (r B C : ℕ) :
    FinDist ((Fin (2*r+1)→Fin B→Fin d×Bool) × (Fin C→Fin d×Bool)) :=
  pcaJointLaw (independentSampleLaw (fun _ : Fin (2*r+1) =>
    independentSampleLaw (fun _ : Fin B => trial)))
    (fun _ => independentSampleLaw (fun _ : Fin C => trial))

/-- The protocol failure predicate: the squared-norm estimate has relative error greater than `1
/ 100`, or rejection sampling returns no coordinate. -/
def pcaProtocolBad {d : ℕ} (energy envelopeEnergy : ℝ) (q r B C : ℕ)
    (z : (Fin (2*r+1)→Fin B→Fin d×Bool) × (Fin C→Fin d×Bool)) : Prop :=
  (1/100:ℝ)*energy < |(pcaNormRun envelopeEnergy q r B z.1).1-energy| ∨ (sqRejectRun z.2).1=none

/-- For a nonzero PCA output, bounded rejection sampling fails with mass `(1 - 1 / phi)^B` and
returns each coordinate with the remaining mass times its normalized squared amplitude
[Tang2021]. -/
theorem pca_actual_protocol_output_law {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q)
    (hu : 0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖) (B : ℕ) :
    let phi := pcaSQInflation A hA rows W i;
    sqRejectMass (pcaActualProposal A hA hd rows W i) (pcaActualCoin A hA rows W i) B none=(1-1/phi)^B ∧
    ∀j,sqRejectMass (pcaActualProposal A hA hd rows W i) (pcaActualCoin A hA rows W i) B (some j)=
      (1-(1-1/phi)^B)*Complex.normSq (pcaOutput (pcaRowSketch A hA q rows) W i j)/
        ‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2 := by
  have hen := (pca_output_envelope A hA rows W i hu).1
  have hw := (pca_output_envelope A hA rows W i hu).2
  have hp : ∀j,(pcaActualProposal A hA hd rows W i).prob j=
      Complex.normSq (sqLinearEnvelope (pcaOutputCoefficients W i)
        (pcaConjugateRows (pcaRowSketch A hA q rows)) j)/
      (∑j,Complex.normSq (sqLinearEnvelope (pcaOutputCoefficients W i)
        (pcaConjugateRows (pcaRowSketch A hA q rows)) j)) := by
    intro j
    simp only [pcaActualProposal,dif_pos hw]
    exact pcaVectorProposal_probability A hA hd hq rows _ hw j
  have hc : ∀j,(pcaActualCoin A hA rows W i j).prob true=
      sqRatio (sqLinearValue (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows)))
        (sqLinearEnvelope (pcaOutputCoefficients W i) (pcaConjugateRows (pcaRowSketch A hA q rows))) j := fun _ => rfl
  have h := sqRejectMass_closed _ _ _ _ hen hp hc B
  simp_rw [pca_output_energy,pca_output_coordinate] at h
  exact h

/-- For a nonzero output with inflation at most `4 * q * K`, the prescribed norm and rejection
budgets bound total protocol failure by `2 * alpha` [Tang2021]. -/
theorem pca_actual_protocol_failure {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0<sketchSquared A) (hd : 0<d) (hq : 0<q) (rows : Fin q→Fin n)
    (W : Matrix (Fin q) (Fin q) ℂ) (i : Fin q) (K alpha : ℝ)
    (hu : 0<‖pcaOutput (pcaRowSketch A hA q rows) W i‖)
    (hphi : pcaSQInflation A hA rows W i≤4*(q:ℝ)*K)
    (halpha : 0<alpha) (halpha1 : alpha≤1) :
    let energy := ‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2;
    let envelopeEnergy := ∑ j,Complex.normSq (sqLinearEnvelope (pcaOutputCoefficients W i)
      (pcaConjugateRows (pcaRowSketch A hA q rows)) j);
    let r := pcaNormRounds alpha;
    let B := pcaNormSamples (4*(q:ℝ)*K);
    let C := pcaRejectSamples q K alpha;
    pcaFiniteMass (pcaProtocolLaw (pcaActualTrial A hA hd rows W i) r B C)
      (pcaProtocolBad energy envelopeEnergy q r B C)≤2*alpha := by
  (try dsimp only)
  let c := pcaOutputCoefficients W i
  let u := sqLinearValue c (pcaConjugateRows (pcaRowSketch A hA q rows))
  let env := sqLinearEnvelope c (pcaConjugateRows (pcaRowSketch A hA q rows))
  let prop := pcaActualProposal A hA hd rows W i
  let coin := pcaActualCoin A hA rows W i
  have hen := (pca_output_envelope A hA rows W i hu).1
  have hp : ∀j,prop.prob j=Complex.normSq (env j)/(∑j,Complex.normSq (env j)) := by
    intro j
    have hw := (pca_output_envelope A hA rows W i hu).2
    simp only [prop,pcaActualProposal,dif_pos hw]
    exact pcaVectorProposal_probability A hA hd hq rows c _ j
  have hc : ∀j,(coin j).prob true=sqRatio u env j := by
    intro j
    rfl
  have he : 0<∑j,Complex.normSq (u j) := hen.1
  have hphiEq : (∑j,Complex.normSq (env j))/(∑j,Complex.normSq (u j))=pcaSQInflation A hA rows W i := by
    rw [pca_output_energy]
    rfl
  have hphi1 : 1≤pcaSQInflation A hA rows W i := by
    rw [← hphiEq]
    exact (one_le_div he).mpr (sqEnvelope_energy u env hen).2
  let r := pcaNormRounds alpha
  let B := pcaNormSamples (4*(q:ℝ)*K)
  let C := pcaRejectSamples q K alpha
  have hnorm := (sq_rejection_acceptance_norm_estimation (Fin d) u env prop coin r B (1/100)
    hen hp hc (pcaNormSamples_budget _).1 (by norm_num) (by norm_num) (by
      rw [hphiEq]
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hphi (by norm_num)) (by norm_num)).trans
        (pcaNormSamples_budget _).2)).1
  have hn : pcaFiniteMass (independentSampleLaw (fun _ : Fin (2*r+1) =>
      independentSampleLaw (fun _ : Fin B => pcaActualTrial A hA hd rows W i)))
      (fun z => (1/100:ℝ)*‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2 <
        |(pcaNormRun (∑ j,Complex.normSq (env j)) q r B z).1-
          ‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2|)≤alpha := by
    have ht := pcaNormRounds_failure alpha halpha
    have hp0 : 0≤(2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) := by positivity
    have hbound : (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)≤alpha := by
      have ht' : 2*((2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1))≤alpha := by
        simpa only [mul_assoc] using! ht
      linarith
    have hN := hnorm.trans hbound
    dsimp only [u,c] at hN
    simp_rw [pca_output_energy] at hN
    simpa only [pcaFiniteMass,pcaNormRun_value,independentSampleLaw,pcaActualTrial,
      prop,coin,sqTrialProduct] using! hN
  have hs : pcaFiniteMass (independentSampleLaw (fun _ : Fin C => pcaActualTrial A hA hd rows W i))
      (fun z => (sqRejectRun z).1=none)≤alpha := by
    have hm := (sqRejectMass_closed u env prop coin hen hp hc C).1
    rw [hphiEq] at hm
    have hbound := hm.trans_le (pca_rejection_cap_failure q K _ alpha hphi1 hphi halpha halpha1)
    rw [sqRejectMass_eq_filter] at hbound
    simpa only [pcaFiniteMass_eq,independentSampleLaw,pcaActualTrial,sqTrialProduct,prop,coin,sqTrialLaw] using! hbound
  have hj := pca_joint_failure
    (independentSampleLaw (fun _ : Fin (2*r+1) => independentSampleLaw (fun _ : Fin B => pcaActualTrial A hA hd rows W i)))
    (fun _ => independentSampleLaw (fun _ : Fin C => pcaActualTrial A hA hd rows W i))
    (fun z => (1/100:ℝ)*‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2 <
      |(pcaNormRun (∑ j,Complex.normSq (env j)) q r B z).1-‖pcaOutput (pcaRowSketch A hA q rows) W i‖^2|)
    (fun _ z => (sqRejectRun z).1=none) alpha alpha halpha.le hn (fun _ _ => hs)
  calc
    _ ≤ alpha+alpha := hj
    _ = 2*alpha := by ring

end Qatlib.Papers.QPCAAssume18.ClassicalPca
