/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PEPSObs16.MainResults.QuantumSampling

@[expose] public section

/-!
# Explicit repetition budget for bounded measurements

The finite product-law tail bound and the explicit repetition count
combine to give a half-probability bound for estimating the observable mean.
-/

set_option autoImplicit false

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators
open Qatlib.Papers.PEPSObs16.MainResults
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-- The explicit sample count controls the tail about the product-law mean. -/
theorem budget_tail {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) B) :
    let n := sampleCount B ε
    eventMass (independent (fun _ : Fin n => p))
      (fun ω => ε ≤ |weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f) ω -
        (independent (fun _ : Fin n => p)).expect
          (weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f))|) ≤ 1 / 2 := by
  obtain ⟨hn, hslack, _⟩ := sampleCount_spec B ε hB hε
  exact samples_sufficient p f B ε hB hε (sampleCount B ε) hn hf hslack

/-- The same budget estimates the one-measurement expectation with failure probability at most one half. -/
theorem mean_tail {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) B) :
    eventMass (independent (fun _ : Fin (sampleCount B ε) => p))
      (fun ω => ε ≤ |sampleMean f ω - p.expect f|) ≤ 1 / 2 := by
  let n := sampleCount B ε
  have hn : 1 ≤ n := (sampleCount_spec B ε hB hε).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hexpect :
      (independent (fun _ : Fin n => p)).expect
        (weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f)) = p.expect f := by
    rw [ProbabilityInterfaces.independent_weighted_expectation, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  have h := budget_tail p f B ε hB hε hf
  change eventMass (independent (fun _ : Fin n => p))
    (fun ω => ε ≤ |weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f) ω -
      (independent (fun _ : Fin n => p)).expect
        (weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f))|) ≤ 1 / 2 at h
  simpa only [hexpect, sampleMean_eq_weightedSum] using h

end Qatlib.Papers.PEPSObs16.MainResults
