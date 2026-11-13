/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.PathModelTrace
import Qatlib.Papers.JonesPoly05.MainResults.EstimatorTail

/-!
# Conditional trace-closure estimation

For bounded real and imaginary observations with means equal to `markovTrace`, this module
establishes a complex estimation guarantee. The definition `traceClosureOutput` incorporates the
writhe and strand normalization, and `theorem31_trace_closure_algorithm` transfers the guarantee
to `jonesTrace`. See [AharonovJonesLandau2009].

## Main statements

* `claim37_hadamard_estimator`: Bounded observations with means equal to the real and imaginary
  parts of `markovTrace` possess a positive sample count with error probability at most δ at any
  positive threshold ε.
* `theorem31_trace_closure_algorithm`: For nonzero d and ‖A‖ = 1, bounded observations with the
  specified Markov-trace means yield a positive sample count with Jones state-sum error
  probability at most δ at threshold ε‖d^(n − 1)‖.

## References

* [Aharonov et al., 2009][AharonovJonesLandau2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.JonesPoly05.MainResults.TraceAlgorithm

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.JonesPoly05.MainResults.Kauffman
open Qatlib.Papers.JonesPoly05.MainResults.Estimator

/-- Bounded observations with means equal to the real and imaginary parts of `markovTrace`
possess a positive sample count with error probability at most δ at any positive threshold
ε; see [AharonovJonesLandau2009]. -/
theorem claim37_hadamard_estimator
    {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (B : BraidWord n)
    (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (re im : X → ℝ)
    (hre : ∀ x, re x ∈ Set.Icc (-1) 1) (him : ∀ x, im x ∈ Set.Icc (-1) 1)
    (hre_mean : p.expect re = (markovTrace A d B).re)
    (him_mean : p.expect im = (markovTrace A d B).im)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ L : ℕ, 0 < L ∧
      p.probEvent (fun ω : Fin L → X =>
        ε ≤ ‖complexEstimate re im ω - markovTrace A d B‖) ≤ δ := by
  obtain ⟨L, hL, hbudget⟩ :=
    exists_sample_budget (B := 1) (ε := ε) (δ := δ) (by norm_num) hε hδ
  refine ⟨L, hL, ?_⟩
  have htarget : ((↑(p.expect re) : ℂ) + (↑(p.expect im) : ℂ) * Complex.I) =
      markovTrace A d B := by
    apply Complex.ext <;> simp [hre_mean, him_mean]
  have hsub : ∀ ω : Fin L → X,
      complexEstimate re im ω - markovTrace A d B = complexDeviation p re im ω := by
    intro ω
    rw [← htarget, complexEstimate_sub p re im ω]
  have hfun : (fun ω : Fin L → X => ε ≤ ‖complexEstimate re im ω - markovTrace A d B‖) =
      (fun ω : Fin L → X => ε ≤ ‖complexDeviation p re im ω‖) := by
    funext ω
    rw [hsub ω]
  have htail := complex_estimator_tail (B := 1) p re im L hL (by norm_num) hε hre him
  have hprob : p.probEvent (fun ω : Fin L → X => ε ≤ ‖complexDeviation p re im ω‖) ≤ δ :=
    htail.trans (by simpa using hbudget)
  simpa only [hfun] using hprob

/-- The complex empirical estimate multiplied by the writhe correction and strand factor d^(n −
1). -/
def traceClosureOutput {X : Type} {L : ℕ} {n : ℕ} (A d : ℂ) (B : BraidWord n)
    (re im : X → ℝ) (ω : Fin L → X) : ℂ :=
  (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) * complexEstimate re im ω

/-- For nonzero d and ‖A‖ = 1, bounded observations with the specified Markov-trace means yield
a positive sample count with Jones state-sum error probability at most δ at threshold ε‖d^(n
− 1)‖; see [AharonovJonesLandau2009]. -/
theorem theorem31_trace_closure_algorithm
    {n : ℕ} {A d : ℂ} (hd : d ≠ 0) (hA : ‖A‖ = 1) (B : BraidWord n)
    (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (re im : X → ℝ)
    (hre : ∀ x, re x ∈ Set.Icc (-1) 1) (him : ∀ x, im x ∈ Set.Icc (-1) 1)
    (hre_mean : p.expect re = (markovTrace A d B).re)
    (him_mean : p.expect im = (markovTrace A d B).im)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ L : ℕ, 0 < L ∧
      p.probEvent (fun ω : Fin L → X =>
        ε * ‖d ^ ((n : ℤ) - 1)‖ ≤
          ‖traceClosureOutput A d B re im ω - jonesTrace A d B‖) ≤ δ := by
  obtain ⟨L, hL, hprob⟩ :=
    claim37_hadamard_estimator hd B X p re im hre him hre_mean him_mean hε hδ
  refine ⟨L, hL, ?_⟩
  have hnormA : ‖(-A : ℂ) ^ (3 * writhe B : ℤ)‖ = 1 := by
    rw [Complex.norm_zpow, norm_neg, hA, one_zpow]
  have hcpos : 0 < ‖d ^ ((n : ℤ) - 1)‖ := by
    rw [norm_pos_iff]
    exact zpow_ne_zero _ hd
  have hkey : ∀ ω : Fin L → X,
      ε * ‖d ^ ((n : ℤ) - 1)‖ ≤
        ‖traceClosureOutput A d B re im ω - jonesTrace A d B‖ →
      ε ≤ ‖complexEstimate re im ω - markovTrace A d B‖ := by
    intro ω hω
    have hsplit : traceClosureOutput A d B re im ω - jonesTrace A d B =
        (-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) *
          (complexEstimate re im ω - markovTrace A d B) := by
      unfold traceClosureOutput
      rw [jonesTrace_eq_markovTrace hd B]
      ring
    rw [hsplit] at hω
    have hnorm : ‖(-A) ^ (3 * writhe B : ℤ) * d ^ ((n : ℤ) - 1) *
          (complexEstimate re im ω - markovTrace A d B)‖ =
        ‖d ^ ((n : ℤ) - 1)‖ *
          ‖complexEstimate re im ω - markovTrace A d B‖ := by
      rw [norm_mul, norm_mul, hnormA]
      ring
    rw [hnorm] at hω
    have hεc : ‖d ^ ((n : ℤ) - 1)‖ * ε ≤
        ‖d ^ ((n : ℤ) - 1)‖ * ‖complexEstimate re im ω - markovTrace A d B‖ := by
      rw [mul_comm (‖d ^ ((n : ℤ) - 1)‖) ε]
      exact hω
    exact le_of_mul_le_mul_left hεc hcpos
  exact (probEvent_mono p hkey).trans hprob

end Qatlib.Papers.JonesPoly05.MainResults.TraceAlgorithm
