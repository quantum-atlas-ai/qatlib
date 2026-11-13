/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

/-!
# Payoff means from prepared distributions

This module relates the Born probabilities of a state-preparation column to a finite
distribution and identifies the marked payoff probability with `sourcePayoffMean`. It derives
amplitude-estimation and median bounds for this mean and records the exact query, gate,
preparation-access, and reflection counts.

The source paper is [WoernerEgger2019].

## Main statements

* `source_born_probability`: If the preparation column has entries √(p.prob i), its Born
  probability at each basis index i is exactly p.prob i.
* `source_payoff_probability_and_ae`: For a unitary preparation with the stated distribution
  column and a payoff in [0, 1], payoff preparation is unitary and its marked probability equals
  the payoff mean. Amplitude estimation lies within the stated mean-dependent error window with
  probability at least 8/π².
* `source_payoff_accesses`: For a unitary preparation and payoff in [0, 1], payoff preparation
  is unitary and 2r + 1 repeated estimation circuits have exactly (2r + 1)(M − 1) queries and
  (2r + 1)(5(M − 1) + 3) gates. The associated access word has 2(M − 1) + 1 input accesses and M
  − 1 source reflections.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open scoped BigOperators

namespace Qatlib.Papers.QRiskWoerner18.PayoffMean

/-- The zero basis index in the register of size 2ⁿ. -/
def sourceZero (n : ℕ) : Fin (2 ^ n) := ⟨0, by positivity⟩

/-- The expectation of a payoff function under the finite distribution p. -/
noncomputable def sourcePayoffMean {n : ℕ} (p : FinDist (Fin (2 ^ n)))
    (f : Fin (2 ^ n) → ℝ) : ℝ := ∑ i, p.prob i * f i

/-- If the preparation column has entries √(p.prob i), its Born probability at each basis index
i is exactly p.prob i [WoernerEgger2019]. -/
theorem source_born_probability (n : ℕ) (p : FinDist (Fin (2 ^ n)))
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ))
    (i : Fin (2 ^ n)) : BornProb (ApplyGate A (Ket (sourceZero n))) i = p.prob i := by
  change ‖ApplyGate A (Ket (sourceZero n)) i‖ ^ 2 = p.prob i
  rw [hcolumn i, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (p.nonneg i)]

/-- For a unitary preparation with the stated distribution column and a payoff in [0, 1], payoff
preparation is unitary and its marked probability equals the payoff mean. Amplitude
estimation lies within the stated mean-dependent error window with probability at least 8/π²
[WoernerEgger2019]. -/
theorem source_payoff_probability_and_ae (n M : ℕ) (hM : 2 ≤ M)
    (p : FinDist (Fin (2 ^ n))) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Fin (2 ^ n) → ℝ) (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    payoffPreparation A f ∈ Matrix.unitaryGroup (Fin (2 ^ n) × Bool) ℂ ∧
    MeasureProb (ApplyGate (payoffPreparation A f) (Ket (sourceZero n, false)))
      (Finset.univ.filter (fun q => q.2 = true)) = sourcePayoffMean p f ∧
    (∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      |aeEstimate M z - sourcePayoffMean p f| ≤
        2 * Real.pi * Real.sqrt (sourcePayoffMean p f * (1 - sourcePayoffMean p f)) /
          (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2),
      (meanLaw M A (sourceZero n) f hA hf hM).prob z) ≥ 8 / Real.pi ^ 2 := by
  have hBorn := source_born_probability n p A hcolumn
  have hprep := payoff_actual_rotation_and_mean A (sourceZero n) f hA hf
  refine ⟨hprep.1, ?_, ?_⟩
  · simpa only [sourcePayoffMean, hBorn] using! hprep.2
  · simpa only [sourcePayoffMean, hBorn] using!
      quantum_mean_actual_ae_accuracy M hM A (sourceZero n) f hA hf

/-- For the stated unitary preparation and bounded payoff, the probability that the median of 2r
+ 1 estimates exceeds the amplitude-estimation error tolerance is at most 2^(2r + 1)(1 −
8/π²)^(r + 1) [WoernerEgger2019]. -/
theorem source_payoff_median (n M r : ℕ) (hM : 2 ≤ M)
    (p : FinDist (Fin (2 ^ n))) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (f : Fin (2 ^ n) → ℝ) (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (hcolumn : ∀ i, ApplyGate A (Ket (sourceZero n)) i = (Real.sqrt (p.prob i) : ℂ)) :
    (meanLaw M A (sourceZero n) f hA hf hM).probEvent (fun records =>
      2 * Real.pi * Real.sqrt (sourcePayoffMean p f * (1 - sourcePayoffMean p f)) /
          (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 <
        |meanMedian r M records - sourcePayoffMean p f|) ≤
      (2 : ℝ) ^ (2 * r + 1) * (1 - 8 / Real.pi ^ 2) ^ (r + 1) := by
  have hBorn := source_born_probability n p A hcolumn
  simpa only [sourcePayoffMean, hBorn] using!
    quantum_mean_sorted_median_amplification M r hM A (sourceZero n) f hA hf

/-- For a unitary preparation and payoff in [0, 1], payoff preparation is unitary and 2r + 1
repeated estimation circuits have exactly (2r + 1)(M − 1) queries and (2r + 1)(5(M − 1) + 3)
gates. The associated access word has 2(M − 1) + 1 input accesses and M − 1 source
reflections [WoernerEgger2019]. -/
theorem source_payoff_accesses (n M r : ℕ) (hM : 2 ≤ M)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (f : Fin (2 ^ n) → ℝ)
    (hA : A ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) :
    payoffPreparation A f ∈ Matrix.unitaryGroup (Fin (2 ^ n) × Bool) ℂ ∧
    QueryCount (RepeatCircuit (countedAECircuit M (payoffPreparation A f)
      (sourceZero n, false)) (2 * r + 1)) = (2 * r + 1) * (M - 1) ∧
    GateCount (RepeatCircuit (countedAECircuit M (payoffPreparation A f)
      (sourceZero n, false)) (2 * r + 1)) = (2 * r + 1) * (5 * (M - 1) + 3) ∧
    aeInputAccesses (aeAccessWord (I := Fin (2 ^ n) × Bool) M) = 2 * (M - 1) + 1 ∧
    aeSourceReflections (aeAccessWord (I := Fin (2 ^ n) × Bool) M) = M - 1 := by
  have hrepeat := quantum_mean_repeated_actual_accesses M r hM A (sourceZero n) f
  have hsingle := prepared_ae_access_ledger M (by omega : 0 < M)
    (payoffPreparation A f) (sourceZero n, false)
  exact ⟨payoffPreparation_mem_unitaryGroup A f hA hf,
    hrepeat.1, hrepeat.2, hsingle.2.2.1, hsingle.2.2.2⟩

end Qatlib.Papers.QRiskWoerner18.PayoffMean
