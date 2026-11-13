/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.FreshEstimateCircuit
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean

/-!
# Median amplification of variable-time estimates

This module defines the median estimate `vtMedianEstimate` and its good outcome set
`vtMedianGood`. It bounds failure under independent amplitude-estimation samples, obtains
arbitrarily high good mass by repetition, and records exactness on the support at zero success
probability for the estimation framework of [Ambainis2012].

## Main statements

* `vt_median_estimate_failure`: exponential failure bound `(8 / 9) ^ r`.
* `vt_median_estimate_good_mass`: existence of a sufficiently reliable median.
* `vt_median_estimate_zero_support`: exact zero estimates on positive-probability records.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sorted median of the amplitude estimates from `2 * r + 1` outcome labels. -/
def vtMedianEstimate (M r : ℕ) (ω : Fin (2*r+1) → Fin M) : ℝ :=
  sortedBlockMedian r (fun i=>aeEstimate M (ω i))

/-- The outcome records whose median estimate differs from `a` by at most `vtEstimateRadius a
M`. -/
def vtMedianGood (M r : ℕ) (a : ℝ) : Finset (Fin (2*r+1) → Fin M) :=
  Finset.univ.filter fun ω=>|vtMedianEstimate M r ω-a| ≤ vtEstimateRadius a M

/-- For unitary preparation and `M ≥ 2`, the probability that the median estimate exceeds the
prescribed error radius is at most `(8 / 9) ^ r`. -/
theorem vt_median_estimate_failure (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) :
    (aeLaw M A j S hA hM).probEvent (fun ω : Fin (2*r+1) → Fin M=>
      vtEstimateRadius (MeasureProb (preparedAAState A j) S) M <
        |vtMedianEstimate M r ω-MeasureProb (preparedAAState A j) S|) ≤ (8/9 : ℝ)^r := by
  let p:=aeLaw M A j S hA hM
  let a:=MeasureProb (preparedAAState A j) S
  have ha:=prepared_aa_good_bad_geometry A j S hA
  have ha0 : 0 ≤ a := ha.2.2.2.2.1
  have hrad : 0 ≤ vtEstimateRadius a M := by unfold vtEstimateRadius;positivity
  have hgood:=vt_prescribed_estimate_success M hM A hA j S
  have hpi : 2/3 ≤ 8/Real.pi^2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hc:=Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
      (fun z=>|aeEstimate M z-a| ≤ vtEstimateRadius a M)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z=>vtEstimateRadius a M < |aeEstimate M z-a|) ≤ 1/3 := by
    change 8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
        (fun z=>|aeEstimate M z-a| ≤ vtEstimateRadius a M) at hgood
    linarith
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure p
      (aeEstimate M) r a (vtEstimateRadius a M) hrad hb

/-- For any positive `δ`, some median repetition count gives good-record mass at least `1 - δ`. -/
theorem vt_median_estimate_good_mass (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ r,1-δ ≤ ∑ ω∈vtMedianGood M r (MeasureProb (preparedAAState A j) S),
      (aeLaw M A j S hA hM).probOf ω := by
  obtain ⟨r,hr⟩:=exists_pow_lt_of_lt_one hδ (by norm_num : (8/9 : ℝ) < 1)
  refine ⟨r,?_⟩
  have hb:=vt_median_estimate_failure M hM r A hA j S
  have ht:= (aeLaw M A j S hA hM).sum_probOf (2*r+1)
  have hc:=Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun ω : Fin (2*r+1) → Fin M=>|vtMedianEstimate M r ω-MeasureProb (preparedAAState A j) S| ≤
      vtEstimateRadius (MeasureProb (preparedAAState A j) S) M)
    (fun ω=>(aeLaw M A j S hA hM).probOf ω)
  simp only [not_le] at hc
  unfold vtMedianGood
  unfold FinDist.probEvent at hb
  linarith

/-- When the prepared success mass is zero, every median outcome record of positive product-law
probability has estimate zero. -/
theorem vt_median_estimate_zero_support (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j) S=0) (ω : Fin (2*r+1) → Fin M)
    (hω : 0 < (aeLaw M A j S hA hM).probOf ω) : vtMedianEstimate M r ω=0 := by
  have he (i : Fin (2*r+1)) : aeEstimate M (ω i)=0 := by
    have hn : (aeLaw M A j S hA hM).prob (ω i)≠0 := by
      intro hz
      have hp : (aeLaw M A j S hA hM).probOf ω=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      linarith
    exact vt_prescribed_estimate_zero_support M hM A hA j S ha (ω i)
      (lt_of_le_of_ne ((aeLaw M A j S hA hM).nonneg _) (Ne.symm hn))
  by_contra hne
  have hmed : 0 < |sortedBlockMedian r (fun i=>aeEstimate M (ω i))-0| := by
    simpa [vtMedianEstimate] using! abs_pos.mpr hne
  have hcount:=heterogeneous_sorted_median_majority_witness r (fun i=>aeEstimate M (ω i)) 0 0
      (by norm_num) hmed
  simp [he] at hcount
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
