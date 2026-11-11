/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIOptim24.MainResults.Source.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4.1: the asymptotic optimal fraction

Fixed paper version: arXiv:2408.08292v5 (`Optimization by Decoded Quantum
Interferometry`), Theorem 4.1 and equation (9), page 11.

The theorem combines two ingredients proved in §9:

* Lemma 9.2 (equation (69), page 26): for finite `m, ℓ` the expected number of
  satisfied constraints of the optimal DQI state is
  `⟨s⟩ = m r / p + (√(r(p-r))/p) · wᵀ A^(m,ℓ,d) w`;
* Lemma 9.3 (equation (113), page 32): the maximum eigenvalue of `A^(m,ℓ,d)`
  satisfies `λ_max / m → μ d + 2√(μ(1-μ))` as `m, ℓ → ∞` with `ℓ/m = μ`.

Substituting `d = (1 - 2ρ)/√(ρ(1-ρ))` with `ρ = r/p` gives equation (9). The
statement below isolates exactly this algebraic substitution: it is the step
that turns the eigenvalue asymptotics into the closed form of Theorem 4.1.
-/

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIOptim24.MainResults

open Qatlib.Papers.DQIOptim24.MainResults.Source

/-- Theorem 4.1 (page 11), equation (9).  With `μ = ℓ/m` and `ρ = r/p`, the
optimal expected fraction `⟨s⟩/m` of satisfied max-LINSAT constraints equals
`ρ + √(ρ(1-ρ)) · (μ d + 2√(μ(1-μ)))` with `d = (1-2ρ)/√(ρ(1-ρ))`, which is the
closed form `(√(μ(1-ρ)) + √(ρ(1-μ)))²` when `ρ ≤ 1 - μ` and `1` otherwise.

This is the passage from equations (69) and (113) to equation (9); the finite-
size expectation value itself is Lemma 9.2 (see `LocalExpectation.lean`). -/
theorem theorem41_asymptotic_fraction
    (mu rho : ℝ) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hle : rho ≤ 1 - mu) :
    rho + Real.sqrt (rho * (1 - rho)) *
        ((1 - 2 * rho) / Real.sqrt (rho * (1 - rho)) * mu +
          2 * Real.sqrt (mu * (1 - mu)))
      = optimalFraction mu rho := by
  unfold optimalFraction
  rw [if_pos hle]
  have hpos : 0 < rho * (1 - rho) := by nlinarith
  have hne : Real.sqrt (rho * (1 - rho)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hA : Real.sqrt (rho * (1 - rho)) *
      ((1 - 2 * rho) / Real.sqrt (rho * (1 - rho))) = 1 - 2 * rho := by
    exact mul_div_cancel₀ (1 - 2 * rho) hne
  have h1 : Real.sqrt (rho * (1 - rho)) *
      ((1 - 2 * rho) / Real.sqrt (rho * (1 - rho)) * mu) = (1 - 2 * rho) * mu := by
    rw [← mul_assoc, hA]
  have h2 : Real.sqrt (rho * (1 - rho)) * (2 * Real.sqrt (mu * (1 - mu))) =
      2 * (Real.sqrt (rho * (1 - rho)) * Real.sqrt (mu * (1 - mu))) := by
    ring
  have hsq1 : (Real.sqrt (mu * (1 - rho))) ^ 2 = mu * (1 - rho) :=
    Real.sq_sqrt (by nlinarith)
  have hsq2 : (Real.sqrt (rho * (1 - mu))) ^ 2 = rho * (1 - mu) :=
    Real.sq_sqrt (by nlinarith)
  have hcross : Real.sqrt (mu * (1 - rho)) * Real.sqrt (rho * (1 - mu)) =
      Real.sqrt (rho * (1 - rho)) * Real.sqrt (mu * (1 - mu)) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ rho * (1 - rho) by nlinarith),
        ← Real.sqrt_mul (show (0 : ℝ) ≤ mu * (1 - rho) by nlinarith)]
    congr 1
    ring
  have hexp : (Real.sqrt (mu * (1 - rho)) + Real.sqrt (rho * (1 - mu))) ^ 2 =
      mu * (1 - rho) + rho * (1 - mu) +
        2 * (Real.sqrt (rho * (1 - rho)) * Real.sqrt (mu * (1 - mu))) := by
    nlinarith [hsq1, hsq2, hcross]
  rw [hexp, mul_add, h1, h2]
  ring

end Qatlib.Papers.DQIOptim24.MainResults
