/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteLikelihoodConcentration
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-distribution sampling bounds for the Hadamard test

Defines the sign observable `spin` and the Boolean distribution `rademacherDist` with prescribed
mean `μ ∈ [-1, 1]`. Expectation identities and finite-event probability inequalities support the
sampling analysis of the Hadamard test in [AradLandau2010].

The theorem `hadamard_test_bias_bound` bounds the probability of empirical-mean error at least
`ε` by one quarter when `N * ε² ≥ 16`, with positive sample count and tolerance.

## Main statements

* `expect_spin`: computes the sign expectation as the prescribed mean.
* `probEvent_or_le`: gives a union bound for finite-sample events.
* `hadamard_test_bias_bound`: proves the empirical-mean error bound.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

namespace Qatlib.Papers.TensorNetwork08.MainResults.HadamardTest

open scoped Classical BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLikelihoodConcentration

noncomputable section

/-- The real sign observable taking value one on true and negative one on false. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The sign observable takes values in the interval `[-1, 1]`. -/
theorem spin_mem_range (b : Bool) : spin b ∈ Set.Icc (-1 : ℝ) 1 := by
  cases b <;> simp [spin]

/-- The negative sign observable takes values in the interval `[-1, 1]`. -/
theorem neg_spin_mem_range (b : Bool) : (fun b => - spin b) b ∈ Set.Icc (-1 : ℝ) 1 := by
  have := spin_mem_range b
  simp only [Set.mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- The Boolean distribution assigning probabilities `(1 + μ) / 2` to true and `(1 - μ) / 2` to
false. -/
def rademacherDist (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1) : FinDist Bool where
  prob b := if b then (1 + μ) / 2 else (1 - μ) / 2
  nonneg := by
    intro b
    cases b
    · simp only [Bool.false_eq_true, if_false]
      linarith [hμ.2]
    · simp only [if_true]
      linarith [hμ.1]
  sum_one := by
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring

/-- The expectation of `spin` under `rademacherDist μ hμ` equals `μ`. See [AradLandau2010]. -/
theorem expect_spin (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1) :
    (rademacherDist μ hμ).expect spin = μ := by
  unfold FinDist.expect
  rw [Fintype.sum_bool]
  simp only [rademacherDist, spin, if_true, Bool.false_eq_true, if_false]
  ring

/-- The expectation of the negative sign observable under `rademacherDist μ hμ` equals `-μ`. -/
theorem expect_neg_spin (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1) :
    (rademacherDist μ hμ).expect (fun b => - spin b) = -μ := by
  unfold FinDist.expect
  rw [Fintype.sum_bool]
  simp only [rademacherDist, spin, if_true, Bool.false_eq_true, if_false]
  ring

/-- The empirical average of the negative sign observable equals the negative empirical average
of `spin`. -/
theorem avg_neg_spin {N : ℕ} (ω : Fin N → Bool) :
    FinDist.avg (fun b => - spin b) ω = - FinDist.avg spin ω := by
  unfold FinDist.avg
  rw [Finset.sum_neg_distrib, neg_div]

/-- Inclusion of finite-sample events implies the corresponding inequality of their
probabilities. -/
theorem probEvent_mono {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) {N : ℕ}
    {E F : (Fin N → X) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : p.probEvent E ≤ p.probEvent F := by
  rw [FinDist.probEvent, FinDist.probEvent]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h w (Finset.mem_filter.mp hw).2⟩
  · intro w _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- The probability of the union of two finite-sample events is at most the sum of their
probabilities. -/
theorem probEvent_or_le {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X) {N : ℕ}
    (E F : (Fin N → X) → Prop) [DecidablePred E] [DecidablePred F] :
    p.probEvent (fun ω => E ω ∨ F ω) ≤ p.probEvent E + p.probEvent F := by
  have key : ∀ {G : (Fin N → X) → Prop} [DecidablePred G],
      p.probEvent G = ∑ ω, p.probOf ω * (if G ω then (1 : ℝ) else 0) := by
    intro G _
    rw [FinDist.probEvent, Finset.sum_filter]
    exact Finset.sum_congr rfl fun ω _ => by by_cases h : G ω <;> simp [h]
  rw [key, key, key, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hpω : 0 ≤ p.probOf ω := Finset.prod_nonneg fun i _ => p.nonneg _
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF] <;> nlinarith

/-- For positive `N` and `ε` with `N * ε² ≥ 16`, the probability that the empirical sign mean
differs from `μ` by at least `ε` is at most one quarter. See [AradLandau2010]. -/
theorem hadamard_test_bias_bound
    (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (hNε : (16 : ℝ) ≤ (N : ℝ) * ε ^ 2) :
    (rademacherDist μ hμ).probEvent
      (fun ω : Fin N → Bool => ε ≤ |FinDist.avg spin ω - μ|) ≤ 1 / 4 := by
  classical

  have hupper :
      (rademacherDist μ hμ).probEvent
          (fun ω : Fin N → Bool => μ + ε ≤ FinDist.avg spin ω)
        ≤ Real.exp (-2 * (N : ℝ) * ε ^ 2 / ((1 : ℝ) - (-1)) ^ 2) := by
    have := average_upper (rademacherDist μ hμ) spin N (-1) 1 ε hN (by norm_num) hε
      (fun x => spin_mem_range x)
    rwa [expect_spin] at this
  have hlower :
      (rademacherDist μ hμ).probEvent
          (fun ω : Fin N → Bool => -μ + ε ≤ FinDist.avg (fun b => - spin b) ω)
        ≤ Real.exp (-2 * (N : ℝ) * ε ^ 2 / ((1 : ℝ) - (-1)) ^ 2) := by
    have h := average_upper (rademacherDist μ hμ) (fun b => - spin b) N (-1) 1 ε hN
      (by norm_num) hε (fun x => neg_spin_mem_range x)
    rwa [expect_neg_spin] at h

  have hden : ((1 : ℝ) - (-1)) ^ 2 = 4 := by norm_num
  have hexp_eq : -2 * (N : ℝ) * ε ^ 2 / 4 = -((N : ℝ) * ε ^ 2 / 2) := by ring
  rw [hden, hexp_eq] at hupper hlower
  have hmono :
      (rademacherDist μ hμ).probEvent
          (fun ω : Fin N → Bool => ε ≤ |FinDist.avg spin ω - μ|)
        ≤ (rademacherDist μ hμ).probEvent
            (fun ω : Fin N → Bool =>
              (μ + ε ≤ FinDist.avg spin ω) ∨
                (-μ + ε ≤ FinDist.avg (fun b => - spin b) ω)) := by
    refine probEvent_mono _ fun ω hω => ?_
    rcases le_total 0 (FinDist.avg spin ω - μ) with hpos | hneg
    · left
      rw [abs_of_nonneg hpos] at hω
      linarith
    · right
      rw [abs_of_nonpos hneg] at hω
      rw [avg_neg_spin]
      nlinarith [hω]
  have hor :
      (rademacherDist μ hμ).probEvent
          (fun ω : Fin N → Bool =>
            (μ + ε ≤ FinDist.avg spin ω) ∨
              (-μ + ε ≤ FinDist.avg (fun b => - spin b) ω))
        ≤ (rademacherDist μ hμ).probEvent
            (fun ω : Fin N → Bool => μ + ε ≤ FinDist.avg spin ω)
          + (rademacherDist μ hμ).probEvent
              (fun ω : Fin N → Bool => -μ + ε ≤ FinDist.avg (fun b => - spin b) ω) :=
    probEvent_or_le _ _ _

  have hexp_le : Real.exp (-((N : ℝ) * ε ^ 2 / 2)) ≤ 1 / 8 := by
    have harg : -((N : ℝ) * ε ^ 2 / 2) ≤ -8 := by nlinarith
    have hstep : Real.exp (-((N : ℝ) * ε ^ 2 / 2)) ≤ Real.exp (-8) :=
      Real.exp_le_exp.mpr harg
    refine le_trans hstep ?_
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by
      have := Real.add_one_le_exp (8 : ℝ)
      linarith
    have : Real.exp (-8) = (Real.exp 8)⁻¹ := Real.exp_neg 8
    rw [this]
    have hle : (Real.exp 8)⁻¹ ≤ (8 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos 8) (by norm_num)).mpr h8
    have h8inv : ((8 : ℝ))⁻¹ = 1 / 8 := by norm_num
    rwa [h8inv] at hle
  calc
    (rademacherDist μ hμ).probEvent
        (fun ω : Fin N → Bool => ε ≤ |FinDist.avg spin ω - μ|)
        ≤ (rademacherDist μ hμ).probEvent
            (fun ω : Fin N → Bool => μ + ε ≤ FinDist.avg spin ω)
          + (rademacherDist μ hμ).probEvent
              (fun ω : Fin N → Bool => -μ + ε ≤ FinDist.avg (fun b => - spin b) ω) :=
        le_trans hmono hor
    _ ≤ Real.exp (-((N : ℝ) * ε ^ 2 / 2)) + Real.exp (-((N : ℝ) * ε ^ 2 / 2)) := by
        linarith [hupper, hlower]
    _ ≤ 1 / 8 + 1 / 8 := by linarith [hexp_le]
    _ = 1 / 4 := by norm_num

end

end Qatlib.Papers.TensorNetwork08.MainResults.HadamardTest
