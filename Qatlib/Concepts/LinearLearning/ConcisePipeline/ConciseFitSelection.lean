/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Qatlib.Concepts.QsvtLinearSolve.RangeDataFit.ComputedRangeProjection
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail

/-!
# Coordinate selection for concise least-squares fits

This module studies least-squares fitting after selecting a subset of design-matrix columns. It
defines `selectedDesignMatrix` and `coordinateTail`, bounds the selected residual by the omitted
coefficient norm, and transfers an approximation of the normalized coefficient direction into a
tail bound. This supports the concise-fitting setting of [WiebeBraunLloyd2012].

The sampling construction `histogramSampleLaw` selects coordinates from a normalized state's
Born distribution. Exact unseen-coordinate probabilities give expected missed-mass bounds and a
probability guarantee for the selected set, with a two-dimensional identity example computing
the residual and tail explicitly.

## Main statements

* `conciseFit_selected_residual_bounds`: lower and upper bounds for the selected-fit residual.
* `conciseFit_direction_tail_bound`: coefficient-tail control from a direction approximation.
* `conciseFit_histogram_expectation_exact`: the exact expected missed mass.
* `conciseFit_histogram_markov`: a probability bound for small missed mass.
* `conciseFit_identity_values`: explicit residual and tail values in dimension two.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
-/

set_option warningAsError false


open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The design matrix with columns outside the selected finite set replaced by zero. -/
noncomputable def selectedDesignMatrix {O I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (S : Finset I) : Matrix O I ℂ :=
  A * Matrix.diagonal (fun i => if i ∈ S then (1:ℂ) else 0)

/-- The vector retaining exactly the coordinates outside the selected finite set. -/
def coordinateTail {I : Type} [DecidableEq I] (S : Finset I) (x : QState I) : QState I :=
  fun i => if i ∈ S then 0 else x i

/-- The sum of Born weights on coordinates outside the selected finite set. -/
noncomputable def missedSelectionMass {I : Type} [Fintype I]
    (φ : QState I) (S : Finset I) : ℝ := ∑ i ∈ Sᶜ, BornProb φ i

/-- The probability mass function of one Born-distributed coordinate sample from a normalized
state. -/
noncomputable def histogramTrial {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (BornProb φ i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg φ i),
      bornProb_sum_eq_one hφ]
    exact ENNReal.ofReal_one)

/-- The law of a list of independent Born-distributed coordinate samples of the specified
length. -/
noncomputable def histogramSampleLaw {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) : ℕ → PMF (List I)
  | 0 => PMF.pure []
  | R+1 => (histogramSampleLaw φ hφ R).bind
      fun l => (histogramTrial φ hφ).map fun i => i :: l

/-- Applying the selected design matrix is equivalent to applying the original matrix after
removing the coordinate tail. -/
theorem selectedDesignMatrix_mulVec {O I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (S : Finset I) (x : QState I) :
    selectedDesignMatrix A S *ᵥ x = A *ᵥ (x - coordinateTail S x) := by
  unfold selectedDesignMatrix
  rw [← Matrix.mulVec_mulVec]
  congr 1
  ext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i ∈ S <;> simp [coordinateTail, h]

/-- The squared Euclidean norm of the coordinate tail equals the missed selection mass. -/
theorem coordinateTail_norm_sq {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : QState I) :
    ‖stateVector (coordinateTail S x)‖^2 = missedSelectionMass x S := by
  rw [stateVector_norm_sq]
  unfold MeasureProb missedSelectionMass
  calc
    _ = ∑ i : I, if i ∈ Sᶜ then BornProb x i else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : i ∈ S <;> simp [BornProb, coordinateTail, h]
    _ = _ := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp

/-- Removing selected coordinates does not increase the Euclidean norm. -/
theorem coordinateTail_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : QState I) :
    ‖stateVector (coordinateTail S x)‖ ≤ ‖stateVector x‖ := by
  have hsq : ‖stateVector (coordinateTail S x)‖^2 ≤ ‖stateVector x‖^2 := by
    rw [coordinateTail_norm_sq, stateVector_norm_sq]
    unfold missedSelectionMass MeasureProb
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _hi _hni
    exact bornProb_nonneg x i
  nlinarith [norm_nonneg (stateVector (coordinateTail S x)), norm_nonneg (stateVector x)]

/-- For a normalized target, the squared residual of the least-squares vector is one minus the
squared least-squares overlap. -/
private theorem full_fit_residual {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (hb : Normalized b) :
    ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖^2 = 1 - leastSquaresOverlap A b ^ 2 := by
  have h := (leastSquares_overlap_and_zero A b).2.2.2
  rw [(normalized_iff_stateVector_norm b).mp hb, one_pow] at h
  linarith

/-- For a normalized target and a design matrix of norm at most one, the selected fit's squared
residual lies between the full-fit squared residual and the square of the full-fit residual
norm plus the omitted coefficient norm. -/
theorem conciseFit_selected_residual_bounds :
    ∀ {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O) (S : Finset I),
      Normalized b → ‖A‖ ≤ 1 →
      1 - leastSquaresOverlap A b ^ 2 ≤
        ‖stateVector (selectedDesignMatrix A S *ᵥ
          leastSquaresVector (selectedDesignMatrix A S) b - b)‖^2 ∧
      ‖stateVector (selectedDesignMatrix A S *ᵥ
          leastSquaresVector (selectedDesignMatrix A S) b - b)‖^2 ≤
        (Real.sqrt (1 - leastSquaresOverlap A b ^ 2) +
          ‖stateVector (coordinateTail S (leastSquaresVector A b))‖)^2 := by
  intro O I _ _ _ _ A b S hb hA
  let x := leastSquaresVector A b
  let AS := selectedDesignMatrix A S
  let xS := leastSquaresVector AS b
  have hq := full_fit_residual A b hb
  have hlo : ‖stateVector (A *ᵥ x - b)‖ ≤ ‖stateVector (AS *ᵥ xS - b)‖ := by
    have h := (leastSquares_minimum_residual_and_norm A b).1.1
      ((Matrix.diagonal fun i => if i ∈ S then (1 : ℂ) else 0) *ᵥ xS)
    simpa [AS, selectedDesignMatrix, Matrix.mulVec_mulVec] using! h
  have hmin := (leastSquares_minimum_residual_and_norm AS b).1.1 x
  have htail : ‖stateVector (A *ᵥ coordinateTail S x)‖ ≤
      ‖stateVector (coordinateTail S x)‖ := by
    have h := stateVector_mulVec_norm_le A (coordinateTail S x)
    nlinarith [norm_nonneg (stateVector (coordinateTail S x))]
  have heq : AS *ᵥ x - b = (A *ᵥ x - b) - A *ᵥ coordinateTail S x := by
    rw [show AS = selectedDesignMatrix A S from rfl, selectedDesignMatrix_mulVec,
      Matrix.mulVec_sub]
    abel
  have htri : ‖stateVector (AS *ᵥ x - b)‖ ≤
      ‖stateVector (A *ᵥ x - b)‖ + ‖stateVector (coordinateTail S x)‖ := by
    rw [heq]
    exact (norm_sub_le (stateVector (A *ᵥ x - b))
      (stateVector (A *ᵥ coordinateTail S x))).trans (add_le_add_right htail _)
  have hsqrt : Real.sqrt (1 - leastSquaresOverlap A b ^ 2) =
      ‖stateVector (A *ᵥ x - b)‖ := by
    rw [← hq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  constructor
  · rw [← hq]
    exact pow_le_pow_left₀ (norm_nonneg _) hlo 2
  · rw [hsqrt]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin.trans htri) 2

/-- If a normalized state approximates the normalized least-squares direction within `η` and has
missed mass at most `μ ≥ 0`, the squared coefficient-tail norm is at most the full
coefficient norm squared times `2 * μ + 2 * η ^ 2`. -/
theorem conciseFit_direction_tail_bound :
    ∀ {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O) (S : Finset I) (φ : QState I) (η μ : ℝ),
      Normalized φ → 0 ≤ μ →
      ‖stateVector φ - NormedSpace.normalize (stateVector (leastSquaresVector A b))‖ ≤ η →
      missedSelectionMass φ S ≤ μ →
      ‖stateVector (coordinateTail S (leastSquaresVector A b))‖^2 ≤
        ‖stateVector (leastSquaresVector A b)‖^2 * (2 * μ + 2 * η^2) := by
  intro O I _ _ _ _ A b S φ η μ _hφ _hμ herr hmass
  let x := leastSquaresVector A b
  let d : QState I := (NormedSpace.normalize (stateVector x)).ofLp
  have hx : x = ‖stateVector x‖ • d := by
    exact (congrArg (fun y : EuclideanSpace ℂ I => y.ofLp)
      (NormedSpace.norm_smul_normalize (stateVector x))).symm
  have hη : 0 ≤ η := (norm_nonneg _).trans herr
  have hdiff : ‖stateVector (φ - d)‖ ≤ η := herr
  have ht : coordinateTail S d = coordinateTail S φ - coordinateTail S (φ - d) := by
    ext i
    by_cases h : i ∈ S <;> simp [coordinateTail, h]
  have hd : ‖stateVector (coordinateTail S d)‖ ≤
      ‖stateVector (coordinateTail S φ)‖ + η := by
    rw [ht]
    exact (norm_sub_le (stateVector (coordinateTail S φ))
      (stateVector (coordinateTail S (φ - d)))).trans
      (add_le_add_right ((coordinateTail_norm_le S (φ - d)).trans hdiff) _)
  have hsq : ‖stateVector (coordinateTail S φ)‖^2 ≤ μ := by
    rw [coordinateTail_norm_sq]
    exact hmass
  have hdsq : ‖stateVector (coordinateTail S d)‖^2 ≤ 2 * μ + 2 * η^2 := by
    nlinarith [norm_nonneg (stateVector (coordinateTail S d)),
      norm_nonneg (stateVector (coordinateTail S φ)),
      sq_nonneg (‖stateVector (coordinateTail S φ)‖ - η)]
  have htail : stateVector (coordinateTail S x) =
      ‖stateVector x‖ • stateVector (coordinateTail S d) := by
    conv_lhs => rw [hx]
    ext i
    by_cases h : i ∈ S <;> simp [coordinateTail, h]
  calc
    _ = ‖stateVector x‖^2 * ‖stateVector (coordinateTail S d)‖^2 := by
      rw [htail, norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdsq (sq_nonneg _)

/-- For `0 ≤ p ≤ 1`, the unseen point mass `p * (1 - p) ^ R` is at most `1 / (R + 1)`. -/
theorem conciseFit_point_mass_tail_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (R : ℕ) :
    p * (1 - p)^R ≤ 1 / ((R : ℝ) + 1) := by
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hq1 : 1 - p ≤ 1 := by linarith
  have hsum (n : ℕ) : p * (∑ i ∈ Finset.range n, (1 - p)^i) = 1 - (1 - p)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hlow : ((R : ℝ) + 1) * (1 - p)^R ≤ ∑ i ∈ Finset.range (R + 1), (1 - p)^i := by
    calc
      _ = ∑ _i ∈ Finset.range (R + 1), (1 - p)^R := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_of_le_one hq0 hq1 (by simpa using! Finset.mem_range.mp hi)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) + 1)).2
  have hm := mul_le_mul_of_nonneg_left hlow hp
  rw [hsum] at hm
  nlinarith [pow_nonneg hq0 (R + 1)]

/-- With zero samples from a normalized state, the expected missed selection mass is one. -/
theorem conciseFit_histogram_zero_expectation {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ 0)
      (fun l => ENNReal.ofReal (missedSelectionMass φ l.toFinset)) = 1 := by
  simp [histogramSampleLaw, missedSelectionMass, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
    bornProb_sum_eq_one hφ]

/-- A single Born-distributed sample avoids coordinate `i` with probability `1 - BornProb φ i`. -/
private theorem histogramTrial_avoid {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) (i : I) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramTrial φ hφ) (fun j => j ≠ i) =
      ENNReal.ofReal (1 - BornProb φ i) := by
  classical
  have hs : (∑ j : I, if j ≠ i then BornProb φ j else 0) = 1 - BornProb φ i := by
    classical
    have hsplit : (∑ j : I, if j ≠ i then BornProb φ j else 0) + BornProb φ i = 1 := by
      classical
      calc
        _ = (∑ j : I, ((if j ≠ i then BornProb φ j else 0) +
          (if j = i then BornProb φ j else 0))) := by simp [Finset.sum_add_distrib]
        _ = ∑ j : I, BornProb φ j := by
          classical
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : j = i <;> simp [h]
        _ = 1 := bornProb_sum_eq_one hφ
    linarith
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype]
  calc
    _ = ∑ j : I, ENNReal.ofReal (if j ≠ i then BornProb φ j else 0) := by
      classical
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = i <;> simp [histogramTrial, h]
    _ = ENNReal.ofReal (∑ j : I, if j ≠ i then BornProb φ j else 0) := by
      classical
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro j _
      split_ifs
      · exact bornProb_nonneg φ j
      · positivity
    _ = _ := by rw [hs]

/-- After `R` independent samples, coordinate `i` remains unseen with probability `(1 - BornProb
φ i) ^ R`, viewed in `ℝ≥0∞`. -/
theorem conciseFit_histogram_unseen {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) (i : I) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw φ hφ R) (fun l => i ∉ l.toFinset) =
      (ENNReal.ofReal (1 - BornProb φ i)) ^ R := by
  classical
  have hbind {X Y : Type} (p : PMF X) (q : X → PMF Y) (E : Y → Prop) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.bind q) E =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (q x) E) := by
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  induction R with
  | zero => simp [histogramSampleLaw, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  | succ R ih =>
    rw [histogramSampleLaw, hbind]
    have hc (l : List I) :
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((histogramTrial φ hφ).map fun j => j :: l)
          (fun xs => i ∉ xs.toFinset) =
        ENNReal.ofReal (1 - BornProb φ i) * (if i ∉ l.toFinset then 1 else 0) := by
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      by_cases hl : i ∈ l.toFinset
      · rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_zero _ _ (by intro j; simp [hl])]
        simp [hl]
      · have hp : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramTrial φ hφ) (fun j => i ∉ (j :: l).toFinset) =
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramTrial φ hφ) (fun j => j ≠ i) :=
          Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun j => by simp [hl, eq_comm])
        rw [hp, histogramTrial_avoid]
        simp [hl]
    have hind : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R)
        (fun l => if i ∉ l.toFinset then 1 else 0) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw φ hφ R) (fun l => i ∉ l.toFinset) := by
      unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro l
      by_cases h : i ∈ l.toFinset <;> simp [h]
    calc
      _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R)
          (fun l => ENNReal.ofReal (1 - BornProb φ i) * (if i ∉ l.toFinset then 1 else 0)) :=
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hc
      _ = ENNReal.ofReal (1 - BornProb φ i) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw φ hφ R) (fun l => i ∉ l.toFinset) := by
        rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, hind]
      _ = _ := by rw [ih, pow_succ]; exact mul_comm _ _

/-- The expected missed mass after `R` samples is the sum over coordinates of their Born weight
times their probability of remaining unseen. -/
theorem conciseFit_histogram_expectation_exact {I : Type} [Fintype I] [DecidableEq I]
    (φ : QState I) (hφ : Normalized φ) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R)
      (fun l => ENNReal.ofReal (missedSelectionMass φ l.toFinset)) =
      ∑ i : I, ENNReal.ofReal (BornProb φ i) *
        ENNReal.ofReal (1 - BornProb φ i) ^ R := by
  classical
  have hm (l : List I) : ENNReal.ofReal (missedSelectionMass φ l.toFinset) =
      ∑ i : I, ENNReal.ofReal (BornProb φ i) * (if i ∉ l.toFinset then 1 else 0) := by
    classical
    unfold missedSelectionMass
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg φ i)]
    calc
      _ = ∑ i : I, if i ∉ l.toFinset then ENNReal.ofReal (BornProb φ i) else 0 := by
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp
      _ = _ := by simp [mul_ite]
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hm]
  have hlinear (s : Finset I) (f : I → List I → ℝ≥0∞) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R) (fun l => ∑ i ∈ s, f i l) =
        ∑ i ∈ s, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R) (f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, ih]
  rw [hlinear]
  apply Finset.sum_congr rfl
  intro i _
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  have hind : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R)
      (fun l => if i ∉ l.toFinset then 1 else 0) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw φ hφ R) (fun l => i ∉ l.toFinset) := by
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro l
    by_cases h : i ∈ l.toFinset <;> simp [h]
  rw [hind, conciseFit_histogram_unseen]

/-- The expected missed selection mass after `R` samples is at most the number of coordinates
divided by `R + 1`. -/
theorem conciseFit_histogram_expectation :
    ∀ {I : Type} [Fintype I] [DecidableEq I] (φ : QState I) (hφ : Normalized φ) (R : ℕ),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (histogramSampleLaw φ hφ R)
      (fun l => ENNReal.ofReal (missedSelectionMass φ l.toFinset)) ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) / (R + 1)) := by
  classical
  intro I _ _ φ hφ R
  rw [conciseFit_histogram_expectation_exact]
  have hpi (i : I) : BornProb φ i ≤ 1 := by
    classical
    rw [← bornProb_sum_eq_one hφ]
    exact Finset.single_le_sum (fun j _ => bornProb_nonneg φ j) (Finset.mem_univ i)
  calc
    _ ≤ ∑ _i : I, ENNReal.ofReal (1 / ((R : ℝ) + 1)) := by
      classical
      apply Finset.sum_le_sum
      intro i _
      rw [← ENNReal.ofReal_pow (by linarith [hpi i] : 0 ≤ 1 - BornProb φ i),
        ← ENNReal.ofReal_mul (bornProb_nonneg φ i)]
      exact ENNReal.ofReal_le_ofReal
        (conciseFit_point_mass_tail_bound _ (bornProb_nonneg φ i) (hpi i) R)
    _ = _ := by
      classical
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp [div_eq_mul_inv]

/-- The real probabilities of an event and its complement sum to one. -/
private theorem event_complement_real {X : Type} (p : PMF X) (E : X → Prop) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E).toReal + (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬ E x)).toReal = 1 := by
  classical
  have hsum : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun x => ¬ E x) = 1 := by
    classical
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
    rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
    rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const p (1 : ℝ≥0∞)]
    apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
    intro x
    by_cases h : E x <;> simp [h]

  have hfin (E : X → Prop) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E ≠ ⊤ :=
    ne_of_lt ((Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one p E).trans_lt (by simp))
  simpa only [ENNReal.toReal_add (hfin E) (hfin _), ENNReal.toReal_one]
    using! congrArg ENNReal.toReal hsum

/-- For `μ > 0`, the probability that missed mass after `R` samples is at most `μ` is at least
`1 - Fintype.card I / ((R + 1) * μ)`. -/
theorem conciseFit_histogram_markov :
    ∀ {I : Type} [Fintype I] [DecidableEq I] (φ : QState I) (hφ : Normalized φ)
      (R : ℕ) (μ : ℝ), 0 < μ →
    1 - (Fintype.card I : ℝ) / ((R + 1) * μ) ≤
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw φ hφ R)
        (fun l => missedSelectionMass φ l.toFinset ≤ μ)).toReal := by
  classical
  intro I _ _ φ hφ R μ hμ
  let p := histogramSampleLaw φ hφ R
  let E := fun l : List I => missedSelectionMass φ l.toFinset ≤ μ
  have hb : ENNReal.ofReal μ * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun l => ¬ E l) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun l => ENNReal.ofReal (missedSelectionMass φ l.toFinset)) := by
    classical
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro l
    by_cases h : E l
    · simp [h]
    · simp only [if_pos h, mul_one]
      rw [mul_comm (ENNReal.ofReal μ)]
      apply mul_le_mul_right
      apply ENNReal.ofReal_le_ofReal
      exact le_of_lt (lt_of_not_ge h)
  have ht := hb.trans (conciseFit_histogram_expectation φ hφ R)
  have hr : μ * (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun l => ¬ E l)).toReal ≤
      (Fintype.card I : ℝ) / ((R : ℝ) + 1) := by
    classical
    have h := ENNReal.toReal_mono (by simp) ht
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hμ.le,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (Fintype.card I : ℝ) / ((R : ℝ) + 1))] using! h
  have hgood := event_complement_real p E
  have hbad : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun l => ¬ E l)).toReal ≤
      (Fintype.card I : ℝ) / (((R : ℝ) + 1) * μ) := by
    classical
    rw [← div_div]
    exact (le_div_iff₀ hμ).mpr (by simpa [mul_comm] using! hr)
  dsimp only [p, E] at hgood hbad
  linarith

/-- For the two-dimensional identity design and uniform target, the full fit is exact and the
selected fit satisfies residual and tail bounds; fifteen histogram samples achieve missed
mass at most one half with probability at least three quarters. -/
theorem conciseFit_identity_consumer :
let A : Matrix (Fin 2) (Fin 2) ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ)
let b : QState (Fin 2) := fun _ => (1/Real.sqrt 2 : ℂ)
let S : Finset (Fin 2) := {0}
Normalized b ∧
leastSquaresVector A b = b ∧
leastSquaresOverlap A b = 1 ∧
0 ≤ ‖stateVector (selectedDesignMatrix A S*ᵥ
    leastSquaresVector (selectedDesignMatrix A S) b-b)‖^2 ∧
‖stateVector (selectedDesignMatrix A S*ᵥ
    leastSquaresVector (selectedDesignMatrix A S) b-b)‖^2 ≤
  (Real.sqrt (1-(leastSquaresOverlap A b)^2)+
    ‖stateVector (coordinateTail S (leastSquaresVector A b))‖)^2 ∧
∃ hφ : Normalized b,
  3/4 ≤ (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (histogramSampleLaw b hφ 15)
    (fun l => missedSelectionMass b l.toFinset ≤ 1/2)).toReal ∧
  ‖stateVector (coordinateTail S b)‖^2 ≤ ‖stateVector b‖^2*(2*(1/2)+0) := by
  (try dsimp only)
  let b : QState (Fin 2) := fun _ => (1/Real.sqrt 2 : ℂ)
  have hb : Normalized b := by
    simp [Normalized, b]
  have hpinv : matrixPseudoinverse (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa using! matrixPseudoinverse_of_isometry (A := (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (by simp [IsIsometry])
  have hx : leastSquaresVector (1 : Matrix (Fin 2) (Fin 2) ℂ) b = b := by
    simp [leastSquaresVector, hpinv]
  have hover : leastSquaresOverlap (1 : Matrix (Fin 2) (Fin 2) ℂ) b = 1 := by
    simpa [leastSquaresOverlap, hpinv] using! (normalized_iff_stateVector_norm b).mp hb
  have hmass : missedSelectionMass b ({0} : Finset (Fin 2)) ≤ 1/2 := by
    simp [missedSelectionMass, BornProb, b, Finset.card_compl]
  have herr : ‖stateVector b - NormedSpace.normalize
      (stateVector (leastSquaresVector (1 : Matrix (Fin 2) (Fin 2) ℂ) b))‖ ≤ 0 := by
    rw [hx,
        NormedSpace.normalize_eq_self_of_norm_eq_one ((normalized_iff_stateVector_norm b).mp hb)]
    simp
  have hres := conciseFit_selected_residual_bounds (1 : Matrix (Fin 2) (Fin 2) ℂ) b {0}
    hb (by simp)
  refine ⟨hb, hx, hover, sq_nonneg _, hres.2, hb, ?_, ?_⟩
  · have h := conciseFit_histogram_markov b hb 15 (1/2) (by norm_num)
    norm_num at h
    exact h
  · have h := conciseFit_direction_tail_bound (1 : Matrix (Fin 2) (Fin 2) ℂ) b {0} b
      0 (1/2) hb (by norm_num) herr hmass
    rw [hx] at h
    simpa [b] using! h

/-- For the two-dimensional identity design, uniform target, and selection `{0}`, both the
squared selected-fit residual and squared omitted-coordinate norm equal one half. -/
theorem conciseFit_identity_values :
    let A : Matrix (Fin 2) (Fin 2) ℂ := 1
    let b : QState (Fin 2) := fun _ => (1/Real.sqrt 2 : ℂ)
    let S : Finset (Fin 2) := {0}
    ‖stateVector (selectedDesignMatrix A S *ᵥ
      leastSquaresVector (selectedDesignMatrix A S) b - b)‖^2 = 1/2 ∧
    ‖stateVector (coordinateTail S b)‖^2 = 1/2 := by
  (try dsimp only)
  let b : QState (Fin 2) := fun _ => (1/Real.sqrt 2 : ℂ)
  let D : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.diagonal (fun i => if i ∈ ({0} : Finset (Fin 2)) then 1 else 0)
  have hDD : D * D = D := by
    simp [D, Matrix.diagonal_mul_diagonal]
  have hDH : Dᴴ = D := by
    simp [D, Matrix.diagonal_conjTranspose]
  have hpinv : matrixPseudoinverse D = D := by
    symm
    apply matrixPseudoinverse_unique D D
    · rw [hDD, hDD]
    · rw [hDD, hDD]
    · rw [hDD, hDH]
    · rw [hDD, hDH]
  have hAS : selectedDesignMatrix (1 : Matrix (Fin 2) (Fin 2) ℂ) {0} = D := by
    simp [selectedDesignMatrix, D]
  have hout : D *ᵥ (D *ᵥ b) - b = -coordinateTail {0} b := by
    ext i
    fin_cases i <;> simp [D, coordinateTail]
  have ht : ‖stateVector (coordinateTail {0} b)‖^2 = (1/2 : ℝ) := by
    rw [coordinateTail_norm_sq]
    simp [missedSelectionMass, BornProb, b, Finset.card_compl]
  refine ⟨?_, ht⟩
  rw [hAS, leastSquaresVector, hpinv, hout]
  change ‖-stateVector (coordinateTail {0} b)‖^2 = _
  rw [norm_neg, ht]

end Qatlib.Concepts.LinearLearning.ConcisePipeline.ConciseFitSelection
