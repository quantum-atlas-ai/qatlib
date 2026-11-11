/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# GEQS gradient-sampling cost (Theorem 1)

Source: "Quantum Deep Learning", arXiv:1412.3489v2, Theorem 1, pp.12-13
(eqs. B1-B2) and its proof.

Algorithm 3 (GEQS) prepares Gibbs samples by rejection sampling (Lemma 2) and
estimates the log-likelihood gradient from `N_train` samples. The paper's proof
establishes the success-probability lower bound (eq. B2)

  `min( Z/(κ Z_Q),  min_v Z_v/(κ_v Z_{v,Q}) ) ≥ 1/(κ + max_v κ_v)`,

then notes that the mean number of geometric-distribution repetitions `1/p` is at
most `κ + max_v κ_v`, which amplitude amplification (`√(κ+max_v κ_v)`) reduces, so
the operation count is `Õ(N_train · E · (√κ + √max_v κ_v))` for a connected graph
with `E` edges (cost `Õ(E)` per state preparation).

The quantum subroutines are the paper's granted primitives; here we prove the
quantitative core: (B2), the geometric-repetition bound, and the amplification
cost algebra `√(κ+max) ≤ √κ + √max`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QDeepLearn14.MainResults.GradientSampling

/-- Mean number of repetitions of a geometric distribution with success
probability `p` (eq. B1 of arXiv:1412.3489): `1/p`. -/
def expectedRepetitions (p : ℝ) : ℝ := 1 / p

/-- Eq. B2 of arXiv:1412.3489: for the unclamped instance with `Z_Q ≤ Z`, the
success probability `Z/(κ Z_Q)` dominates `1/(κ + max_v κ_v)`. -/
theorem gibbsSuccess_lowerBound
    (Z κ ZQ maxκ : ℝ) (hZQpos : 0 < ZQ) (hκ : 0 < κ) (hmaxκ : 0 ≤ maxκ)
    (hZQleZ : ZQ ≤ Z) :
    1 / (κ + maxκ) ≤ Z / (κ * ZQ) := by
  have hZpos : 0 < Z := lt_of_lt_of_le hZQpos hZQleZ
  have hkm : (0:ℝ) < κ + maxκ := by linarith
  -- `1/κ ≤ Z/(κ Z_Q)` since `Z_Q ≤ Z`.
  have h1 : (1:ℝ) ≤ Z / ZQ := (one_le_div hZQpos).mpr hZQleZ
  have h2 : (1:ℝ) / κ ≤ Z / (κ * ZQ) := by
    rw [show Z / (κ * ZQ) = (Z / ZQ) / κ by field_simp]
    exact (div_le_div_iff_of_pos_right hκ).mpr h1
  -- `1/(κ+max) ≤ 1/κ`.
  have h3 : (1:ℝ) / (κ + maxκ) ≤ 1 / κ :=
    one_div_le_one_div_of_le hκ (by linarith [hmaxκ])
  exact le_trans h3 h2

/-- Clamped form of eq. B2 of arXiv:1412.3489: for every clamped configuration
`v` with `Z_{v,Q} ≤ Z_v` and `κ_v ≤ max_v κ_v`, the clamped success probability
`Z_v/(κ_v Z_{v,Q})` dominates `1/(κ + max_v κ_v)`. -/
theorem clampedSuccess_lowerBound
    {V : Type*} [Fintype V] [Nonempty V]
    (Zx κx ZxQ : V → ℝ) (κ maxκ : ℝ)
    (hZxQ : ∀ v, 0 < ZxQ v) (hκx : ∀ v, 0 < κx v)
    (hκxmax : ∀ v, κx v ≤ maxκ) (hκ : 0 < κ) (hmaxκ : 0 ≤ maxκ)
    (hZxle : ∀ v, ZxQ v ≤ Zx v) :
    ∀ v, 1 / (κ + maxκ) ≤ Zx v / (κx v * ZxQ v) := by
  intro v
  have hZxpos : 0 < Zx v := lt_of_lt_of_le (hZxQ v) (hZxle v)
  have h1 : (1:ℝ) ≤ Zx v / ZxQ v := (one_le_div (hZxQ v)).mpr (hZxle v)
  have h2 : (1:ℝ) / (κx v) ≤ Zx v / (κx v * ZxQ v) := by
    rw [show Zx v / (κx v * ZxQ v) = (Zx v / ZxQ v) / (κx v) by field_simp]
    exact (div_le_div_iff_of_pos_right (hκx v)).mpr h1
  have h3 : (1:ℝ) / (κ + maxκ) ≤ 1 / (κx v) :=
    one_div_le_one_div_of_le (hκx v) (by linarith [hmaxκ, hκxmax v])
  exact le_trans h3 h2

/-- **Theorem 1 (success-probability core)**, eq. B2 of arXiv:1412.3489 p.13:
the minimum of the unclamped and all clamped success probabilities is at least
`1/(κ + max_v κ_v)`. -/
theorem theorem1_successLowerBound
    {V : Type*} [Fintype V] [Nonempty V]
    (Z κ ZQ maxκ : ℝ) (Zx κx ZxQ : V → ℝ)
    (hZQpos : 0 < ZQ) (hκ : 0 < κ) (hmaxκ : 0 ≤ maxκ)
    (hZQleZ : ZQ ≤ Z)
    (hZxQ : ∀ v, 0 < ZxQ v) (hκx : ∀ v, 0 < κx v)
    (hκxmax : ∀ v, κx v ≤ maxκ) (hZxle : ∀ v, ZxQ v ≤ Zx v) :
    (1 / (κ + maxκ) ≤ Z / (κ * ZQ)) ∧
      (∀ v, 1 / (κ + maxκ) ≤ Zx v / (κx v * ZxQ v)) :=
  ⟨gibbsSuccess_lowerBound Z κ ZQ maxκ hZQpos hκ hmaxκ hZQleZ,
    clampedSuccess_lowerBound Zx κx ZxQ κ maxκ hZxQ hκx hκxmax hκ hmaxκ hZxle⟩

/-- The mean geometric number of repetitions needed for success probability `p`
is at most `κ + max_v κ_v` once `p ≥ 1/(κ + max_v κ_v)` (eq. B1). -/
theorem expectedRepetitions_le
    (p κ maxκ : ℝ) (hp : 0 < p) (hκ : 0 < κ) (hmaxκ : 0 ≤ maxκ)
    (hpge : 1 / (κ + maxκ) ≤ p) :
    expectedRepetitions p ≤ κ + maxκ := by
  have hkm : (0:ℝ) < κ + maxκ := by linarith
  unfold expectedRepetitions
  have hp' : (1:ℝ) ≤ (κ + maxκ) * p := by
    have := (div_le_iff₀ hkm).mp hpge
    linarith [this]
  rw [div_le_iff₀ hp]
  nlinarith [hp']

/-- Amplification cost algebra (eq. B2 proof): `√(κ + max) ≤ √κ + √max`. -/
theorem sqrt_add_le_sqrt_add_sqrt
    (κ maxκ : ℝ) (hκ : 0 ≤ κ) (hmaxκ : 0 ≤ maxκ) :
    Real.sqrt (κ + maxκ) ≤ Real.sqrt κ + Real.sqrt maxκ := by
  have hy : (0:ℝ) ≤ Real.sqrt κ + Real.sqrt maxκ := by positivity
  have hsq : κ + maxκ ≤ (Real.sqrt κ + Real.sqrt maxκ) ^ 2 := by
    nlinarith [Real.sq_sqrt hκ, Real.sq_sqrt hmaxκ,
      Real.sqrt_nonneg κ, Real.sqrt_nonneg maxκ]
  exact (Real.sqrt_le_left hy).mpr hsq

/-- **Theorem 1 (operation-count core)** of arXiv:1412.3489 p.13: with `N_train`
samples and per-preparation cost `E` (connected graph, `E` edges), the amplified
operation count `N_train · E · √(κ + max_v κ_v)` is bounded by the paper's
`Õ`-expression `N_train · E · (√κ + √max_v κ_v)` (up to polylogarithmic factors,
which are not modelled). -/
theorem theorem1_operationCost
    (Ntrain E κ maxκ : ℝ) (hN : 0 ≤ Ntrain) (hE : 0 ≤ E)
    (hκ : 0 ≤ κ) (hmaxκ : 0 ≤ maxκ) :
    Ntrain * E * Real.sqrt (κ + maxκ) ≤
      Ntrain * E * (Real.sqrt κ + Real.sqrt maxκ) := by
  exact mul_le_mul_of_nonneg_left
    (sqrt_add_le_sqrt_add_sqrt κ maxκ hκ hmaxκ) (mul_nonneg hN hE)

end Qatlib.Papers.QDeepLearn14.MainResults.GradientSampling
