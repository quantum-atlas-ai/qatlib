/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Runway eigenfunctions and tail summability

This module studies real-valued exponential and cosine eigenfunctions of the discrete line
Laplacian `lineH`. It locates their energies relative to the band `[0, 4]`, proves summability
of the squared negative-half-line exponential tails for positive parameters, and gives a
nonsummable cosine-tail example.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `lineH_alphaState`: computes the energy of the alternating exponential state.
* `runwayEnergy_mem_band`: bounds the cosine-wave energy between zero and four.
* `alphaTail_summable`: proves summability of the decaying alternating exponential tail.
* `planeTail_not_summable`: proves nonsummability at angle `π / 2`.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators Real Topology

namespace Qatlib.Papers.DecisionTrees97.MainResults

/-- The discrete line Laplacian given by twice the value at a site minus the values at its two
neighbors. -/
def lineH (ψ : ℤ → ℝ) (j : ℤ) : ℝ := 2 * ψ j - ψ (j + 1) - ψ (j - 1)

/-- The alternating exponential sequence `(-1) ^ j * exp (α * j)` on integer sites. -/
def alphaState (α : ℝ) (j : ℤ) : ℝ := (-1 : ℝ) ^ j * Real.exp (α * (j : ℝ))

/-- The exponential sequence `exp (β * j)` on integer sites. -/
def betaState (β : ℝ) (j : ℤ) : ℝ := Real.exp (β * (j : ℝ))

/-- The real cosine wave `cos (θ * j)` on integer sites. -/
def planeWave (θ : ℝ) (j : ℤ) : ℝ := Real.cos (θ * (j : ℝ))

/-- The cosine-wave energy `2 - 2 * cos θ`. -/
def runwayEnergy (θ : ℝ) : ℝ := 2 - 2 * Real.cos θ

/-- An even natural power of minus one equals one. -/
theorem neg_one_pow_two_mul (m : ℕ) : (-1 : ℝ) ^ (2 * m) = 1 := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ih]
      norm_num

/-- The square of any natural power of minus one equals one. -/
theorem sq_neg_one_pow (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [pow_two, ← pow_add, show m + m = 2 * m by ring, neg_one_pow_two_mul]

/-- The square of any integer power of minus one equals one. -/
theorem sq_neg_one_zpow (j : ℤ) : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
  rw [pow_two]
  have hsum : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (j + j) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  rw [hsum, show j + j = (2 : ℤ) * j by ring, zpow_mul]
  norm_num

/-- The alternating exponential sequence is an eigenfunction of `lineH` with eigenvalue `2 + 2 *
cosh α`. See [FarhiGutmann1998]. -/
theorem lineH_alphaState (α : ℝ) (j : ℤ) :
    lineH (alphaState α) j = (2 + 2 * Real.cosh α) * alphaState α j := by
  unfold lineH alphaState
  have h1 : (-1 : ℝ) ^ (j + 1) = -((-1 : ℝ) ^ j) := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    ring
  have h2 : (-1 : ℝ) ^ (j - 1) = -((-1 : ℝ) ^ j) := by
    have := zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0) j
    rw [this]; ring
  have e1 : Real.exp (α * ((j + 1 : ℤ) : ℝ)) = Real.exp (α * (j : ℝ)) * Real.exp α := by
    rw [show α * ((j + 1 : ℤ) : ℝ) = α * (j : ℝ) + α by push_cast; ring, Real.exp_add]
  have e2 : Real.exp (α * ((j - 1 : ℤ) : ℝ)) = Real.exp (α * (j : ℝ)) * Real.exp (-α) := by
    rw [show α * ((j - 1 : ℤ) : ℝ) = α * (j : ℝ) + (-α) by push_cast; ring, Real.exp_add]
  rw [h1, h2, e1, e2]
  have hcosh : Real.cosh α = (Real.exp α + Real.exp (-α)) / 2 := Real.cosh_eq α
  rw [hcosh]; ring

/-- The exponential sequence is an eigenfunction of `lineH` with eigenvalue `2 - 2 * cosh β`.
See [FarhiGutmann1998]. -/
theorem lineH_betaState (β : ℝ) (j : ℤ) :
    lineH (betaState β) j = (2 - 2 * Real.cosh β) * betaState β j := by
  unfold lineH betaState
  have e1 : Real.exp (β * ((j + 1 : ℤ) : ℝ)) = Real.exp (β * (j : ℝ)) * Real.exp β := by
    rw [show β * ((j + 1 : ℤ) : ℝ) = β * (j : ℝ) + β by push_cast; ring, Real.exp_add]
  have e2 : Real.exp (β * ((j - 1 : ℤ) : ℝ)) = Real.exp (β * (j : ℝ)) * Real.exp (-β) := by
    rw [show β * ((j - 1 : ℤ) : ℝ) = β * (j : ℝ) + (-β) by push_cast; ring, Real.exp_add]
  rw [e1, e2]
  have hcosh : Real.cosh β = (Real.exp β + Real.exp (-β)) / 2 := Real.cosh_eq β
  rw [hcosh]; ring

/-- The cosine sequence is an eigenfunction of `lineH` with eigenvalue `runwayEnergy θ`. -/
theorem lineH_planeWave (θ : ℝ) (j : ℤ) :
    lineH (planeWave θ) j = runwayEnergy θ * planeWave θ j := by
  unfold lineH planeWave runwayEnergy
  have e1 : Real.cos (θ * ((j + 1 : ℤ) : ℝ)) =
      Real.cos (θ * (j : ℝ)) * Real.cos θ - Real.sin (θ * (j : ℝ)) * Real.sin θ := by
    rw [show θ * ((j + 1 : ℤ) : ℝ) = θ * (j : ℝ) + θ by push_cast; ring, Real.cos_add]
  have e2 : Real.cos (θ * ((j - 1 : ℤ) : ℝ)) =
      Real.cos (θ * (j : ℝ)) * Real.cos θ + Real.sin (θ * (j : ℝ)) * Real.sin θ := by
    rw [show θ * ((j - 1 : ℤ) : ℝ) = θ * (j : ℝ) + (-θ) by push_cast; ring, Real.cos_add,
      Real.cos_neg, Real.sin_neg]
    ring
  rw [e1, e2]; ring

/-- The hyperbolic cosine of every real number is at least one. -/
theorem one_le_cosh (α : ℝ) : 1 ≤ Real.cosh α := by
  have hu : 0 < Real.exp α := Real.exp_pos α
  have hinv : Real.exp α * Real.exp (-α) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [Real.cosh_eq]
  have hsq : 0 ≤ (Real.exp α - 1) ^ 2 := sq_nonneg _
  nlinarith [hu, hinv]

/-- The hyperbolic cosine of a nonzero real number is strictly greater than one. -/
theorem one_lt_cosh_of_ne {β : ℝ} (hβ : β ≠ 0) : 1 < Real.cosh β := by
  have hu : 0 < Real.exp β := Real.exp_pos β
  have hinv : Real.exp β * Real.exp (-β) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hne : Real.exp β ≠ 1 := by
    intro h
    rw [Real.exp_eq_one_iff] at h
    exact hβ h
  rw [Real.cosh_eq]
  have hsq : 0 < (Real.exp β - 1) ^ 2 := by
    apply sq_pos_of_ne_zero
    exact sub_ne_zero.mpr hne
  nlinarith [hu, hinv]

/-- The alternating exponential energy is at least four. -/
theorem alpha_energy_ge_four (α : ℝ) : 4 ≤ 2 + 2 * Real.cosh α := by
  have h : 1 ≤ Real.cosh α := one_le_cosh α
  linarith

/-- The alternating exponential energy lies between four and six exactly when `cosh α ≤ 2`. -/
theorem alpha_energy_mem_window (α : ℝ) :
    4 ≤ 2 + 2 * Real.cosh α ∧ 2 + 2 * Real.cosh α ≤ 6 ↔ Real.cosh α ≤ 2 := by
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    refine ⟨alpha_energy_ge_four α, by linarith⟩

/-- For positive `β`, the exponential-state energy `2 - 2 * cosh β` is negative. See
[FarhiGutmann1998]. -/
theorem beta_energy_negative {β : ℝ} (hβ : 0 < β) :
    2 - 2 * Real.cosh β < 0 := by
  have h : 1 < Real.cosh β := one_lt_cosh_of_ne (ne_of_gt hβ)
  linarith

/-- The cosine-wave energy lies between zero and four. See [FarhiGutmann1998]. -/
theorem runwayEnergy_mem_band (θ : ℝ) :
    0 ≤ runwayEnergy θ ∧ runwayEnergy θ ≤ 4 := by
  constructor
  · unfold runwayEnergy
    have := Real.cos_le_one θ
    linarith
  · unfold runwayEnergy
    have h : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    linarith

/-- The cosine-wave energy equals `4 * sin (θ / 2) ^ 2`. -/
theorem runwayEnergy_eq_four_sin_sq (θ : ℝ) :
    runwayEnergy θ = 4 * Real.sin (θ / 2) ^ 2 := by
  unfold runwayEnergy
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have := Real.cos_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at this
  have hs : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [hc]; nlinarith

/-- The squared alternating exponential state evaluated at the negative integer site `-n`. -/
def alphaTailSq (α : ℝ) (n : ℕ) : ℝ := (alphaState α (-(n : ℤ))) ^ 2

/-- The squared alternating exponential tail equals `exp (-2 * α * n)`. -/
theorem alphaTailSq_eq (α : ℝ) (n : ℕ) :
    alphaTailSq α n = Real.exp (-2 * α * (n : ℝ)) := by
  unfold alphaTailSq alphaState
  rw [mul_pow, sq_neg_one_zpow, one_mul]
  rw [show α * ((-(n : ℤ) : ℤ) : ℝ) = (n : ℝ) * (-2 * α) / 2 by push_cast; ring]
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- For positive `α`, the squared alternating exponential tail on negative integer sites is
summable. See [FarhiGutmann1998]. -/
theorem alphaTail_summable {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => alphaTailSq α n) := by
  have hr : ‖Real.exp (-2 * α)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ => (Real.exp (-2 * α)) ^ n) :=
    summable_geometric_of_norm_lt_one hr
  refine hgeom.congr ?_
  intro n
  rw [alphaTailSq_eq, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The squared exponential state evaluated at the negative integer site `-n`. -/
def betaTailSq (β : ℝ) (n : ℕ) : ℝ := (betaState β (-(n : ℤ))) ^ 2

/-- The squared exponential tail equals `exp (-2 * β * n)`. -/
theorem betaTailSq_eq (β : ℝ) (n : ℕ) :
    betaTailSq β n = Real.exp (-2 * β * (n : ℝ)) := by
  unfold betaTailSq betaState
  rw [pow_two, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- For positive `β`, the squared exponential tail on negative integer sites is summable. -/
theorem betaTail_summable {β : ℝ} (hβ : 0 < β) :
    Summable (fun n : ℕ => betaTailSq β n) := by
  have hr : ‖Real.exp (-2 * β)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable (fun n : ℕ => (Real.exp (-2 * β)) ^ n) :=
    summable_geometric_of_norm_lt_one hr
  refine hgeom.congr ?_
  intro n
  rw [betaTailSq_eq, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The squared cosine wave evaluated at the negative integer site `-n`. -/
def planeTailSq (θ : ℝ) (n : ℕ) : ℝ := (planeWave θ (-(n : ℤ))) ^ 2

/-- At angle `π / 2`, every even-indexed squared cosine-tail value is one. -/
theorem planeTail_even (m : ℕ) : planeTailSq (π / 2) (2 * m) = 1 := by
  unfold planeTailSq planeWave
  have harg : (π / 2) * ((-((2 * m : ℕ) : ℤ) : ℤ) : ℝ) = -((m : ℝ) * π) := by
    push_cast; ring
  rw [harg, Real.cos_neg, Real.cos_nat_mul_pi]
  exact sq_neg_one_pow m

/-- The squared cosine tail at angle `π / 2` is not summable. See [FarhiGutmann1998]. -/
theorem planeTail_not_summable : ¬ Summable (planeTailSq (π / 2)) := by
  intro hs
  have hzero : Tendsto (planeTailSq (π / 2)) atTop (𝓝 0) := hs.tendsto_atTop_zero
  have hlt : ∀ᶠ n : ℕ in atTop, planeTailSq (π / 2) n < 1 / 2 :=
    hzero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlt
  have := hN (2 * N) (by omega)
  rw [planeTail_even N] at this
  norm_num at this

end Qatlib.Papers.DecisionTrees97.MainResults
