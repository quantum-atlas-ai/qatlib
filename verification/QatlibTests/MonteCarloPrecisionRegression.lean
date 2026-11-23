module

public import Qatlib.Papers.MCMontanaro15.MonteCarlo.VariancePrecision
public import Qatlib.Papers.MCMontanaro15.MonteCarlo.LayeredScaledMean
public import Qatlib.Papers.MCMontanaro15.MonteCarlo.MedianAmplification

@[expose] public section

/-!
# Consumer regression for the Montanaro precision increment

The Hadamard gate on input `false` prepares a fair bit. Its two payoffs `1 / 4` and `1` give a
positive variance and a Euclidean norm with two nonzero coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Tests.MonteCarloPrecisionRegression

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Papers.MCMontanaro15.MonteCarlo
open scoped BigOperators

/-- The payoff takes a distinct positive value on each of the two outcomes. -/
private noncomputable def bitPayoff (b : Bool) : ℝ := if b then 1 else 1 / 4

/-- Each payoff belongs to the amplitude-encoding domain. -/
private theorem bitPayoff_mem_unit (b : Bool) : bitPayoff b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [bitPayoff]

/-- The Hadamard-prepared source has probability one half on each outcome. -/
private theorem fairBit (b : Bool) : BornProb (ApplyGate Hadamard (Ket false)) b = 1 / 2 := by
  simp only [BornProb, applyGate_hadamard_ket_false, Plus, hadamard_apply_false, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private noncomputable def bitMean : ℝ :=
  ∑ i, BornProb (ApplyGate Hadamard (Ket false)) i * bitPayoff i

/-- The fair-bit payoff has variance `9 / 64`, so the variance bound is nonvacuous. -/
private theorem bitVariance :
    (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i * (bitPayoff i - bitMean) ^ 2)
      = 9 / 64 := by
  norm_num [bitMean, Fintype.sum_bool, fairBit, bitPayoff]

/-- Theorem 5 gives additive error `1 / 4` with success at least `2 / 3`. -/
example :
    ∃ k : ℕ, 4 ≤ k ∧
      (∑ ω with |signedMeanEstimate k bitPayoff 1 ω - bitMean| ≤ 1 / 4,
        (signedMeanLaw k Hadamard false bitPayoff 1 hadamard_unitary).prob ω) ≥ 2 / 3 := by
  obtain ⟨k, hk, h⟩ := theorem5_additive_variance_guarantee 1 (1 / 4) (by norm_num) (by norm_num)
  refine ⟨k, hk, h Hadamard false bitPayoff hadamard_unitary ?_⟩
  change (∑ i, BornProb (ApplyGate Hadamard (Ket false)) i * (bitPayoff i - bitMean) ^ 2) ≤ _
  rw [bitVariance]
  norm_num

/-- Lemma 4 applies at layer count `3` with the Born-weighted Euclidean norm. -/
example :
    let L := ‖bornPayoffVector (ApplyGate Hadamard (Ket false)) bitPayoff‖
    (∑ ω with |(L + 1) * layerEstimate 3 ω - bitMean| ≤ (1 / 8) * (L + 1) ^ 2,
      (layerLaw 3 Hadamard false (fun i => bitPayoff i / (L + 1)) hadamard_unitary
        (fun i => div_nonneg (bitPayoff_mem_unit i).1 (by positivity))).prob ω) ≥ 4 / 5 := by
  exact layered_source_l2_scale_guarantee 3 Hadamard false bitPayoff hadamard_unitary
    (fun i => (bitPayoff_mem_unit i).1) (1 / 8) (by norm_num) (by norm_num) (by norm_num)

/-- Theorem 3 bounds the median failure probability at grid size `32` and confidence `1 / 4`. -/
example :
    ∃ r : ℕ, 1 ≤ r ∧
      (meanLaw 32 Hadamard false bitPayoff hadamard_unitary bitPayoff_mem_unit
        (by norm_num)).probEvent
        (fun ω => 2 * Real.pi * Real.sqrt (bitMean * (1 - bitMean)) / 32
          + Real.pi ^ 2 / (32 : ℝ) ^ 2 < |meanMedian r 32 ω - bitMean|) ≤ 1 / 4 := by
  obtain ⟨r, hr, h⟩ := exists_median_count_for_delta (1 / 4) (by norm_num) (by norm_num)
  exact ⟨r, hr, h 32 (by norm_num) Hadamard false bitPayoff hadamard_unitary bitPayoff_mem_unit⟩

end Tests.MonteCarloPrecisionRegression
