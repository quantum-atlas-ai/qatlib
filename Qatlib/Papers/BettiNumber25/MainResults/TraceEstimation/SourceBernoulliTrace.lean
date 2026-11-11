/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation.SourceTracePower

set_option backward.isDefEq.respectTransparency false

/-!
# TraceEstimation — Bernoulli trace estimation and the Hoeffding bridge

Fixed source: arXiv:2408.16934v3 (Quantum 9, 1901, 2025), PDF SHA-256
`dcf534a47e98fb6bb6bc34039e64bac6e7ba07fdb7d9b17f781dae1a01fe7848`.

* Source Lemma 3.1 (p. 4, "Hoeffding") is the two-sided Hoeffding bound.  It is
  reused from the frozen library as
  `QuantumAlgorithm.Foundations.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_hoeffding`
  and specialised to `q` i.i.d. `{0,1}`-valued records below
  (`lemma_3_1_hoeffding_iid`).
* Source Lemma 3.3 (p. 7): each sample `s_i` of Algorithm 2 is Bernoulli with
  expectation `(1/N) tr(M^d)`.

The probability component is genuine: the Bernoulli law is an actual `FinDist`
and the expectation identity is proved from the trace-power law of
`SourceTracePower`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

namespace Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation

/-- The `{0,1}`-valued indicator of a Boolean sample. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Sum over `Bool` as an explicit two-term sum. -/
theorem bool_sum (f : Bool → ℝ) : ∑ b, f b = f true + f false := by
  rw [Fintype.univ_bool, Finset.sum_pair (by decide)]

/-- The Bernoulli law with success probability `p ∈ [0,1]`. -/
def bernoulliLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    by_cases hb : b
    · simp [hb, hp0]
    · simp [hb]; linarith
  sum_one := by
    rw [bool_sum]
    simp

/-- The expectation of the indicator of a Bernoulli law is its parameter. -/
theorem bernoulli_expect_indicator (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw p hp0 hp1).expect boolIndicator = p := by
  rw [FinDist.expect, bool_sum]
  simp [bernoulliLaw, boolIndicator]

/-- **Source Lemma 3.3.**  If the per-sample success probability is the uniform
average of `‖D^(d) |x⟩‖²`, i.e. `(1/N)` times the trace of `M^d`, then the sample
variable `s_i` is Bernoulli with expectation exactly that normalised trace. -/
theorem lemma_3_3_bernoulli_trace {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (d : ℕ) (hd : 0 < d)
    (hN : 0 < N) (p : ℝ)
    (hp : p = (∑ x, vecNormSq (colVec (Dpow D d) x)) / (N : ℝ))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw p hp0 hp1).expect boolIndicator
      = (((Dᴴ * D) ^ d).trace).re / (N : ℝ) := by
  rw [bernoulli_expect_indicator, hp, lemma_3_2_normalised D d hd hN]

/-- A plain average over `L` records equals the frozen library's weighted sum
with uniform weights `1/L` (for `L > 0`). -/
theorem avg_eq_weightedSum {L : ℕ} (hL : 0 < L) (f : Bool → ℝ) (ω : Fin L → Bool) :
    (∑ k, f (ω k)) / (L : ℝ)
      = weightedSum (I := Fin L) (X := fun _ => Bool) (fun _ => (L : ℝ)⁻¹)
          (fun _ b => f b) ω := by
  rw [weightedSum, ← Finset.mul_sum]
  have hLne : (L : ℝ) ≠ 0 := by positivity
  field_simp

/-- The uniform-weight sum has expectation `p` under `L` Bernoulli samples. -/
theorem bernoulli_uniformExpect (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {L : ℕ} (hL : 0 < L) :
    (independent (I := Fin L) (fun _ => bernoulliLaw p hp0 hp1)).expect
        (weightedSum (I := Fin L) (X := fun _ => Bool)
          (fun _ => (L : ℝ)⁻¹) (fun _ b => boolIndicator b)) = p := by
  rw [ProbabilityInterfaces.independent_weighted_expectation]
  have hsum : (∑ _i : Fin L, (L : ℝ)⁻¹ * p) = p := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  calc (∑ _i : Fin L, (L : ℝ)⁻¹ *
        (bernoulliLaw p hp0 hp1).expect boolIndicator)
      = ∑ _i : Fin L, (L : ℝ)⁻¹ * p := by
        exact Finset.sum_congr rfl fun i _ => by rw [bernoulli_expect_indicator]
    _ = p := hsum

/-- **Source Lemma 3.1 specialised to `L` i.i.d. Bernoulli samples, centred at
the true probability.**  This is the tail bound used verbatim in the proofs of
Theorems 4.4, 5.2, 5.6 and 6.2. -/
theorem lemma_3_1_hoeffding_iid (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {L : ℕ} (hL : 0 < L) (u : ℝ) (hu : 0 < u) :
    eventMass (independent (I := Fin L) (fun _ => bernoulliLaw p hp0 hp1))
        (fun ω => u ≤ |weightedSum (I := Fin L) (X := fun _ => Bool)
          (fun _ => (L : ℝ)⁻¹) (fun _ b => boolIndicator b) ω - p|)
      ≤ 2 * Real.exp (-(2 * u ^ 2 * (L : ℝ))) := by
  have hterm : ∀ i : Fin L, ((L : ℝ)⁻¹) ^ 2 * ((1 : ℝ) - 0) ^ 2 = ((L : ℝ) ^ 2)⁻¹ := by
    intro i
    rw [sub_zero, one_pow, mul_one]
    field_simp
  have hS : 0 < ∑ i : Fin L, ((L : ℝ)⁻¹) ^ 2 * ((1 : ℝ) - 0) ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact Finset.sum_pos (fun i _ => by positivity) ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  have h := independent_weighted_hoeffding (I := Fin L) (X := fun _ => Bool)
    (fun _ => bernoulliLaw p hp0 hp1) (fun _ => (L : ℝ)⁻¹)
    (fun _ b => boolIndicator b) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) u
    (fun _ => by norm_num) (fun _ b => by
      cases b <;> simp [boolIndicator]) hu hS
  rw [bernoulli_uniformExpect p hp0 hp1 hL] at h
  have hsum : (∑ i : Fin L, ((L : ℝ)⁻¹) ^ 2 * ((1 : ℝ) - 0) ^ 2) = (L : ℝ)⁻¹ := by
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum] at h
  have harg : -2 * u ^ 2 / (L : ℝ)⁻¹ = -(2 * u ^ 2 * (L : ℝ)) := by
    field_simp
  rw [harg] at h
  exact h

end Qatlib.Papers.BettiNumber25.MainResults.TraceEstimation
