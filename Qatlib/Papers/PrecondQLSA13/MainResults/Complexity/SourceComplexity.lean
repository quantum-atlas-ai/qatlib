/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Complexity — source interface for the overall complexity of PrecondQLSA13

Clader--Jacobs--Sprouse, *Preconditioned quantum linear system algorithm*,
fixed arXiv:1301.2340v4 (2013-05-07). Source location: p. 3 (right column,
Hamiltonian-simulation and preconditioner costs) and p. 4 ("Combining all
steps").

The paper composes the following costs:

* creating `M|b>`: `O(d^2)` oracle queries and `O(d^3)` operations;
* Hamiltonian simulation (Berry et al.), with `m = 6 d^2` one-sparse
  submatrices and `τ = κ‖A‖/ε`, uses
  `N_exp ≤ 2 m^2 τ exp(2 ln 5 sqrt(ln(m τ / ε)))` exponential-operator
  applications;
* amplitude estimation of `sin^2 φ_x`, `P_1110`, `P_1111` to accuracy `ε`
  needs `O(1/ε)` iterations, and `τ = O(κ/ε)`;
* the QLSA dependence on the matrix size is `log N`.

Combining them gives the paper's headline bound `Õ(d^7 κ log N / ε^2)`, where
the tilde absorbs the Suzuki-integrator factor. This module formalises the
composition exactly (with `‖A‖ = 1` as the paper's scaling convention, so that
`τ = κ/ε`): the product of the stated component costs is
`72 · d^7 κ log N / ε^2 · F`. It also records the `κ² → κ` improvement obtained
by removing the post-selection step of Eq. (4).

Boundary: this is the algebraic cost composition and the κ-improvement
inequality; hidden constants and the asymptotic convention `Õ` are explicit
here (72 and `F`). Oracle construction costs of the SPAI are the paper's
standard-model premise, not re-derived.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PrecondQLSA13.MainResults.Complexity

/-- Berry et al. Suzuki-integrator factor
`F = exp(2 ln 5 sqrt(ln(m τ / ε)))` multiplying `2 m^2 τ` in `N_exp`
(arXiv:1301.2340v4, p. 3). -/
noncomputable def suzukiFactor (m τ ε : ℝ) : ℝ :=
  Real.exp (2 * Real.log 5 * Real.sqrt (Real.log (m * τ / ε)))

/-- Number of one-sparse submatrices in the Berry et al. decomposition,
`m = 6 d^2` (arXiv:1301.2340v4, p. 3). -/
def subMatrixCount (d : ℝ) : ℝ := 6 * d ^ 2

/-- The composed cost model of arXiv:1301.2340v4, pp. 3--4:
SPAI preconditioner `d^3` × Hamiltonian simulation `2 m^2 τ F` with `τ = κ/ε`
× amplitude estimation `1/ε` × QLSA size dependence `log N`. -/
noncomputable def totalCost (d κ N ε : ℝ) : ℝ :=
  d ^ 3 *
    (2 * (subMatrixCount d) ^ 2 * (κ / ε)
      * suzukiFactor (subMatrixCount d) (κ / ε) ε) *
    (1 / ε) * Real.log N

/-- The Suzuki factor is positive. -/
theorem suzukiFactor_pos (m τ ε : ℝ) : 0 < suzukiFactor m τ ε :=
  Real.exp_pos _

/-- Fixed arXiv:1301.2340v4, pp. 3--4 ("Combining all steps, the overall
quantum algorithm has Õ(d^7 κ log N / ε^2) complexity"): substituting
`m = 6 d^2`, `τ = κ/ε` and multiplying the component costs gives exactly
`72 · d^7 κ log N / ε^2 · F`, i.e. the paper's `Õ(d^7 κ log N / ε^2)` with the
tilde equal to the explicit Suzuki factor `F`. -/
theorem totalCost_eq_tilde (d κ N ε : ℝ) (hd : d ≠ 0) (hε : ε ≠ 0) :
    totalCost d κ N ε =
      72 * d ^ 7 * κ * Real.log N / ε ^ 2
        * suzukiFactor (subMatrixCount d) (κ / ε) ε := by
  unfold totalCost subMatrixCount
  field_simp
  ring

/-- Fixed arXiv:1301.2340v4, pp. 3--4: the leading `d^7 κ log N / ε^2` factor is
positive for positive `d`, `κ`, `ε` and `N > 1`, so the composed cost is
positive. -/
theorem totalCost_pos (d κ N ε : ℝ) (hd : 0 < d) (hκ : 0 < κ)
    (hN : 1 < N) (hε : 0 < ε) : 0 < totalCost d κ N ε := by
  unfold totalCost
  have hm : 0 < subMatrixCount d := by
    unfold subMatrixCount
    positivity
  have hm2 : 0 < (subMatrixCount d) ^ 2 := pow_pos hm 2
  have hτ : 0 < κ / ε := by positivity
  have hF : 0 < suzukiFactor (subMatrixCount d) (κ / ε) ε := suzukiFactor_pos _ _ _
  have h1 : 0 < d ^ 3 := by positivity
  have h2 : 0 < 2 * (subMatrixCount d) ^ 2 * (κ / ε)
      * suzukiFactor (subMatrixCount d) (κ / ε) ε := by
    have h2m : 0 < 2 * (subMatrixCount d) ^ 2 := by positivity
    exact mul_pos (mul_pos h2m hτ) hF
  have h3 : 0 < 1 / ε := by positivity
  have h4 : 0 < Real.log N := Real.log_pos hN
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-- Removing the post-selection step of Eq. (4) (arXiv:1301.2340v4, p. 2 and
p. 4) replaces the post-selection repetition factor `1/p` by the amplitude-
amplification factor `1/sqrt(p)`. With the HHL success probability
`p ≥ 1/κ^2`, the post-selected algorithm needs `κ^2` repetitions while the
unitary/amplitude-amplified version needs only `κ`: the paper's statement that
the implementation is "quadratically better in κ than in the original QLSA". -/
theorem postselection_vs_amplification (κ p : ℝ) (hκ : 1 ≤ κ) (hp : 0 < p)
    (hpκ : 1 / κ ^ 2 ≤ p) :
    (1 / p ≤ κ ^ 2) ∧ (1 / Real.sqrt p ≤ κ) := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hκ2pos : 0 < κ ^ 2 := by positivity
  have h1κpos : 0 < 1 / κ := by positivity
  constructor
  · rw [div_le_iff₀ hp]
    have hmul : κ ^ 2 * (1 / κ ^ 2) ≤ κ ^ 2 * p :=
      mul_le_mul_of_nonneg_left hpκ hκ2pos.le
    rw [mul_one_div, div_self hκ2pos.ne'] at hmul
    linarith
  · have hsq : (1 / κ) ^ 2 ≤ p := by
      simpa [div_pow] using hpκ
    have hsqrt : 1 / κ ≤ Real.sqrt p := by
      calc 1 / κ = Real.sqrt ((1 / κ) ^ 2) := (Real.sqrt_sq h1κpos.le).symm
        _ ≤ Real.sqrt p := Real.sqrt_le_sqrt hsq
    calc 1 / Real.sqrt p ≤ 1 / (1 / κ) :=
          one_div_le_one_div_of_le h1κpos hsqrt
      _ = κ := by field_simp

/-- The paper's κ-improvement, stated as costs: post-selection needs `κ^2`
repetitions, amplitude amplification needs `κ` (arXiv:1301.2340v4, p. 4). -/
def postSelectionRepetitions (κ : ℝ) : ℝ := κ ^ 2

/-- Number of amplitude-amplification repetitions for success probability
`1/κ^2`. -/
def amplificationRepetitions (κ : ℝ) : ℝ := κ

/-- Fixed arXiv:1301.2340v4, p. 4: amplitude amplification is quadratically
better in the condition number than post-selection. -/
theorem kappa_squared_improvement (κ : ℝ) (hκ : 1 ≤ κ) :
    amplificationRepetitions κ ≤ postSelectionRepetitions κ := by
  unfold amplificationRepetitions postSelectionRepetitions
  nlinarith

end Qatlib.Papers.PrecondQLSA13.MainResults.Complexity
