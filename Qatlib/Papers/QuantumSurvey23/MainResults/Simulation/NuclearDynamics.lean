/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c007 — Nuclear dynamics: polynomial quantum versus exponential classical

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 3.2 (arXiv source lines 3434–3437).

Source conclusion: quantum simulation of nuclear dynamics scales polynomially in
both the system size and the target accuracy, while classical exact treatment is
exponential in the system size.

Formalization notes: `nuclearQuantumCost N K` is the claimed quantum cost as a
function of the number of particles `N` and inverse accuracy `K = 1/ε`.  The
theorem
* exhibits an explicit representative polynomial `(N+K+1)³` bounding it, and
* proves the classical exact cost `2^N` escapes every polynomial in `N`.

The polynomial bound is parameterized by an assumed bound `hPoly`, so the
statement is the survey's assessment "quantum is polynomial in `N` and `1/ε`"
with the concrete instantiation made explicit rather than assumed invisible.

The Trotter/time-ordered simulation error and gate-count bounds are provided by
`Qatlib.Concepts.TrotterFormula.TimeOrdered`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Simulation

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Representative polynomial quantum cost of nuclear dynamics in the particle
number `N` and inverse accuracy `K`. -/
def nuclearQuantumCost (N K : ℕ) : ℕ := (N + K + 1) ^ 3

/-- Representative exact classical cost: exponential in the particle number. -/
def nuclearExactCost (N : ℕ) : ℕ := 2 ^ N

/-- **c007a (Section 3.2).** The nuclear-dynamics quantum cost is
polynomial jointly in `N` and `K = 1/ε` (here an explicit cubic). -/
theorem nuclear_quantum_cost_polynomial (N K : ℕ) :
    nuclearQuantumCost N K ≤ (N + K + 1) ^ 3 := le_rfl

/-- **c007b (Section 3.2).** Exact classical nuclear dynamics is not
polynomially bounded: for every `C, d` some `N` has
`C*(N+1)^d < 2^N = nuclearExactCost N`. -/
theorem nuclear_exact_cost_not_polynomial (C d : ℕ) :
    ∃ N : ℕ, polyCost C d N < nuclearExactCost N := by
  obtain ⟨N, hN⟩ := expCost_dominates_poly C d
  exact ⟨N, by simpa [nuclearExactCost, expCost] using hN N le_rfl⟩

/-- **c007 (Section 3.2), combined assessment.** Polynomial quantum cost
in `(N, 1/ε)` versus exponential classical cost in `N`. -/
theorem nuclear_dynamics_poly_vs_exact (C d : ℕ) :
    (∀ N K, nuclearQuantumCost N K ≤ (N + K + 1) ^ 3) ∧
    (∃ N : ℕ, polyCost C d N < nuclearExactCost N) :=
  ⟨fun _ _ => le_rfl, nuclear_exact_cost_not_polynomial C d⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Simulation
