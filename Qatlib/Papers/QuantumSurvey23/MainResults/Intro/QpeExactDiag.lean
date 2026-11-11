/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c001 — Quantum phase estimation vs. exact diagonalization

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 1.1 (arXiv source lines 768–772).

Source conclusion: phase estimation solves eigenvalue problems with circuit
size polynomial in `M` (number of lattice sites) and `1/ΔE` (inverse precision),
whereas exact diagonalization needs exponential time in `M` (or in `1/ΔE`).

Formalization notes: the paper's "poly(M/ΔE)" and "exp(M)" are cost models.  We
instantiate the shared vocabulary of `MainResults.Scaling.CostScaling`:

* `qpeCost runs M invAcc = runs * (M+1)^2 * (invAcc+1)`, where `runs` counts
  repetitions of the phase-estimation circuit; the paper assumes the ground
  state has polynomial overlap, so `runs` is itself `M+1` at worst;
* `exactDiagCost M = 2^M`.

The load-bearing arithmetic content is `exactDiag_not_polynomial`: no fixed
polynomial bounds `2^M`.  That is exactly the statement that exact
diagonalization is not polynomial-time.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Intro

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Cost of phase estimation: `runs` repetitions of a degree-2 circuit in the
system size `M` and the inverse accuracy `invAccuracy = 1/ΔE`. -/
def qpeCost (runs M invAccuracy : ℕ) : ℕ := runs * (M + 1) ^ 2 * (invAccuracy + 1)

/-- Exact diagonalization of an `M`-site / `M`-qubit Hamiltonian costs `2^M`. -/
def exactDiagCost (M : ℕ) : ℕ := 2 ^ M

/-- **c001a (Section 1.1).** Under polynomial overlap (`runs ≤ M+1`, the
paper's assumption), the phase-estimation cost is bounded by a single cubic in
`M` times a linear factor in `1/ΔE` — i.e. polynomial in `M` and `1/ΔE`. -/
theorem qpe_cost_polynomial (runs M invAccuracy : ℕ) (hOverlap : runs ≤ M + 1) :
    qpeCost runs M invAccuracy ≤ (M + 1) ^ 3 * (invAccuracy + 1) := by
  unfold qpeCost
  have h : runs * (M + 1) ^ 2 ≤ (M + 1) ^ 3 := by
    calc runs * (M + 1) ^ 2 ≤ (M + 1) * (M + 1) ^ 2 :=
          Nat.mul_le_mul_right _ hOverlap
      _ = (M + 1) ^ 3 := by ring
  exact Nat.mul_le_mul_right _ h

/-- **c001b (Section 1.1).** Exact diagonalization is not polynomially
bounded in the number of sites: for every constant `C` and degree `d` there is
an `M` with `C*(M+1)^d < 2^M`.  Hence there is no polynomial-time exact
diagonalization. -/
theorem exactDiag_not_polynomial (C d : ℕ) :
    ∃ M : ℕ, polyCost C d M < exactDiagCost M := by
  obtain ⟨N, hN⟩ := expCost_dominates_poly C d
  exact ⟨N, hN N le_rfl⟩

/-- **c001b' (Section 1.1).** The same exponential separation holds in the
inverse-accuracy variable `1/ΔE`: `2^(1/ΔE)` also eventually exceeds any fixed
polynomial. -/
theorem exactDiag_not_polynomial_in_accuracy (C d : ℕ) :
    ∃ K : ℕ, polyCost C d K < 2 ^ K := by
  obtain ⟨N, hN⟩ := expCost_dominates_poly C d
  exact ⟨N, hN N le_rfl⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Intro
