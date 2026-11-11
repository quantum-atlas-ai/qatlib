/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.TraceAlgorithm

/-!
# Scaled estimation for plat expectations

`platOutput` scales a complex empirical mean by κ. Given bounded observations with the
prescribed complex expectation and an identity expressing the target as κ times that
expectation, `theorem32_plat_closure_algorithm` supplies a positive sample budget for any
positive error and failure parameters. See [AharonovJonesLandau2009].

## Main statements

* `plat_jones_eq_scaled_trace`: If `vPl` equals `jonesTrace` and d is nonzero, it equals the
  Markov state sum times the writhe and strand normalization factors.
* `theorem32_plat_closure_algorithm`: If `vPl` is κ times the specified expectation with ‖κ‖
  positive, bounded observations with those means yield some positive sample count whose error
  probability at threshold acc is at most δ.

## References

* [Aharonov et al., 2009][AharonovJonesLandau2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.JonesPoly05.MainResults.PlatAlgorithm

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.JonesPoly05.MainResults.Kauffman
open Qatlib.Papers.JonesPoly05.MainResults.Estimator

/-- The complex empirical estimate multiplied by the scale κ. -/
def platOutput {X : Type} {L : ℕ} (κ : ℂ) (re im : X → ℝ) (ω : Fin L → X) : ℂ :=
  κ * complexEstimate re im ω

/-- If `vPl` equals `jonesTrace` and d is nonzero, it equals the Markov state sum times the
writhe and strand normalization factors; see [AharonovJonesLandau2009]. -/
theorem plat_jones_eq_scaled_trace
    {nC : ℕ} {A d : ℂ} (hd : d ≠ 0) (C : BraidWord nC) (vPl : ℂ)
    (hV : vPl = jonesTrace A d C) :
    vPl = (-A) ^ (3 * writhe C : ℤ) * d ^ ((nC : ℤ) - 1) * markovTrace A d C := by
  rw [hV, jonesTrace_eq_markovTrace hd C]

/-- If `vPl` is κ times the specified expectation with ‖κ‖ positive, bounded observations with
those means yield some positive sample count whose error probability at threshold acc is at
most δ; see [AharonovJonesLandau2009]. -/
theorem theorem32_plat_closure_algorithm
    (κ platExpectation vPl : ℂ)
    (hV : vPl = κ * platExpectation) (hκ : 0 < ‖κ‖)
    (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (re im : X → ℝ)
    (hre : ∀ x, re x ∈ Set.Icc (-1) 1) (him : ∀ x, im x ∈ Set.Icc (-1) 1)
    (hre_mean : p.expect re = platExpectation.re)
    (him_mean : p.expect im = platExpectation.im)
    {acc δ : ℝ} (hacc : 0 < acc) (hδ : 0 < δ) :
    ∃ L : ℕ, 0 < L ∧
      p.probEvent (fun ω : Fin L → X =>
        acc ≤ ‖platOutput κ re im ω - vPl‖) ≤ δ := by
  have htarget : ((↑(p.expect re) : ℂ) + (↑(p.expect im) : ℂ) * Complex.I) =
      platExpectation := by
    apply Complex.ext <;> simp [hre_mean, him_mean]
  have hscale : 0 < acc / ‖κ‖ := div_pos hacc hκ
  obtain ⟨L, hL, hbudget⟩ :=
    exists_sample_budget (B := 1) (ε := acc / ‖κ‖) (δ := δ) (by norm_num) hscale hδ
  refine ⟨L, hL, ?_⟩
  have htail := complex_estimator_tail (B := 1) p re im L hL (by norm_num) hscale hre him
  refine (probEvent_mono p ?_).trans (htail.trans ?_)
  · intro ω hω
    have hbase : complexEstimate re im ω -
        ((↑(p.expect re) : ℂ) + (↑(p.expect im) : ℂ) * Complex.I) =
        complexDeviation p re im ω := complexEstimate_sub p re im ω
    have hsplit : platOutput κ re im ω - vPl = κ * complexDeviation p re im ω := by
      unfold platOutput
      rw [hV, ← htarget, ← mul_sub, hbase]
    rw [hsplit, norm_mul] at hω
    rw [div_le_iff₀ hκ]
    calc acc ≤ ‖κ‖ * ‖complexDeviation p re im ω‖ := hω
      _ = ‖complexDeviation p re im ω‖ * ‖κ‖ := by ring
  · simpa using hbudget

end Qatlib.Papers.JonesPoly05.MainResults.PlatAlgorithm
