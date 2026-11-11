/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Mathlib.Tactic

/-!
# PEPSObs16 — quantum sampling cost of Theorem 1 (p. 3)

Fixed source: arXiv:1606.06301v2, Theorem 1 and its proof sketch (p. 3,
"the quantum algorithm ... time `Õ(ℓ^d/ε²)`"): the expectation
`⟨ω|O_X|ω⟩/⟨ω|ω⟩` is estimated by averaging `n` independent measurement
outcomes of a bounded local observable (`O(‖O_X‖²/ε²)` samples).

This file formalises the *statistical* part of that statement on the Finite
probability API of the Frozen library: a two-sided Hoeffding tail for the
sample mean of `n` independent bounded measurements, and the explicit sample
count `⌈‖O_X‖² ln 4 / (2ε²)⌉ + 1` that makes the tail at most `1/2`. The
coherent quantum part (amplitude estimation achieving `O(polylog)`
depth) is not modelled at the paper layer and is not asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PEPSObs16.MainResults

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

/-- The sample mean of `n` independent measurements `f (ω 0), …, f (ω (n-1))`. -/
def sampleMean {n : ℕ} {X : Type*} (f : X → ℝ) (ω : Fin n → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (ω i)

/-- The sample mean is the weighted sum with equal weights `1/n`. -/
theorem sampleMean_eq_weightedSum {n : ℕ} {X : Type*} (f : X → ℝ) (ω : Fin n → X) :
    sampleMean f ω =
      weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f) ω := by
  unfold sampleMean weightedSum
  rw [Finset.mul_sum]

/-- Sum of the per-sample Hoeffding variances: with equal weights `1/n` and
values in `[0, B]`, `∑ i, (1/n)² (B - 0)² = B²/n`. -/
theorem hoeffding_variance_sum (n : ℕ) (B : ℝ) (hn : 1 ≤ n) :
    ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2 * (B - 0) ^ 2 = B ^ 2 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Quantum sampling tail (Theorem 1, p. 3).** For `n` independent
measurements of a local observable with spectrum in `[0, B]`, the probability
that the sample mean deviates from its expectation by at least `ε` is at most
`2 e^{-2 n ε² / B²}`. This is the two-sided weighted Hoeffding bound of the
Frozen probability API instantiated with equal weights. -/
theorem sample_mean_tail {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (hn : 1 ≤ n) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) B) :
    eventMass (independent (fun _ : Fin n => p))
      (fun ω => ε ≤ |weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f) ω -
        (independent (fun _ : Fin n => p)).expect
          (weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f))|)
      ≤ 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / B ^ 2) := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hS_eq := hoeffding_variance_sum n B hn
  have hSpos : 0 < ∑ i : Fin n, ((n : ℝ)⁻¹) ^ 2 * (B - 0) ^ 2 := by
    rw [hS_eq]
    positivity
  have hmain := independent_weighted_hoeffding
    (fun _ : Fin n => p) (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f)
    (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => B) ε
    (fun _ => hB.le) (fun _ x => hf x) hε hSpos
  rw [hS_eq] at hmain
  refine hmain.trans (le_of_eq ?_)
  congr 1
  field_simp [hB.ne', hnpos.ne', pow_ne_zero 2 hB.ne']

/-- **`O(1/ε²)` samples suffice (Theorem 1, p. 3).** If the sample count obeys
`ln 4 ≤ 2 n ε² / ‖O_X‖²`, the sample-mean error tail is at most `1/2`. -/
theorem samples_sufficient {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) B)
    (hslack : Real.log 4 ≤ 2 * (n : ℝ) * ε ^ 2 / B ^ 2) :
    eventMass (independent (fun _ : Fin n => p))
      (fun ω => ε ≤ |weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f) ω -
        (independent (fun _ : Fin n => p)).expect
          (weightedSum (fun _ : Fin n => (n : ℝ)⁻¹) (fun _ => f))|)
      ≤ 1 / 2 := by
  classical
  refine (sample_mean_tail p f B ε hB hε hn hf).trans ?_
  have hexp : Real.exp (-2 * (n : ℝ) * ε ^ 2 / B ^ 2) ≤ 4⁻¹ := by
    have hB2 : (0 : ℝ) < B ^ 2 := by positivity
    have hkey : -2 * (n : ℝ) * ε ^ 2 / B ^ 2 ≤ Real.log 4⁻¹ := by
      have hsl := hslack
      rw [le_div_iff₀ hB2] at hsl
      rw [Real.log_inv, div_le_iff₀ hB2]
      linarith
    calc
      Real.exp (-2 * (n : ℝ) * ε ^ 2 / B ^ 2)
          ≤ Real.exp (Real.log 4⁻¹) := Real.exp_le_exp_of_le hkey
      _ = 4⁻¹ := Real.exp_log (by norm_num)
  calc
    2 * Real.exp (-2 * (n : ℝ) * ε ^ 2 / B ^ 2) ≤ 2 * 4⁻¹ :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 1 / 2 := by norm_num

/-- The explicit sample count of the quantum subroutine:
`⌈‖O_X‖² ln 4 / (2ε²)⌉ + 1`, i.e. `O(‖O_X‖²/ε²)` samples. -/
def sampleCount (B ε : ℝ) : ℕ :=
  Nat.ceil (B ^ 2 * Real.log 4 / (2 * ε ^ 2)) + 1

/-- **Sample-count guarantee (Theorem 1, p. 3).** The explicit count
`⌈‖O_X‖² ln 4 / (2ε²)⌉ + 1` is at least the `2 ln 4`-factor of `‖O_X‖²/ε²`
needed for a constant `1/2` failure probability, and is bounded by
`‖O_X‖² ln 4 / (2ε²) + 2`. -/
theorem sampleCount_spec (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    1 ≤ sampleCount B ε ∧
      Real.log 4 ≤ 2 * (sampleCount B ε : ℝ) * ε ^ 2 / B ^ 2 ∧
      (sampleCount B ε : ℝ) ≤ B ^ 2 * Real.log 4 / (2 * ε ^ 2) + 2 := by
  have hB2 : (0 : ℝ) < B ^ 2 := by positivity
  have hε2 : (0 : ℝ) < 2 * ε ^ 2 := by positivity
  have hx0 : 0 ≤ B ^ 2 * Real.log 4 / (2 * ε ^ 2) := by positivity
  have hle := Nat.le_ceil (B ^ 2 * Real.log 4 / (2 * ε ^ 2))
  have hlt := Nat.ceil_lt_add_one hx0
  refine ⟨?_, ?_, ?_⟩
  · unfold sampleCount
    omega
  · have hn : (B ^ 2 * Real.log 4 / (2 * ε ^ 2)) < (sampleCount B ε : ℝ) := by
      unfold sampleCount
      push_cast
      linarith
    rw [div_lt_iff₀ hε2] at hn
    rw [le_div_iff₀ hB2]
    nlinarith [hn]
  · unfold sampleCount
    push_cast
    linarith

end Qatlib.Papers.PEPSObs16.MainResults
