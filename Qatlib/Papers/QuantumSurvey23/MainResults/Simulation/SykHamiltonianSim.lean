/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c006 — SYK Hamiltonian simulation: polynomial versus exponential

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 1.3 (SYK model / quantum
simulation) (arXiv source lines 1585–1589).

Source conclusion: Trotter-based quantum simulation of the `N`-site SYK
Hamiltonian runs in `poly(N)` time, while exact classical diagonalization is
exponential `~2^N`.  The survey stresses a caveat: the exponential quantum
advantage persists only if the relevant initial states (in particular the
thermal purification / thermofield-double states) can themselves be prepared in
`poly(N)` time.

Formalization notes: `sykSimCost` and `sykPrepCost` are arbitrary `ℕ → ℕ`
functions representing the two claimed polynomial costs.  The theorem records
(a) that their sum is again polynomially bounded, and (b) the exponential
classical lower scale `2^N`.  The hypothesis `hPrep` *is* the survey's caveat:
if state preparation is not polynomial the sum claim fails, so the survey's
conclusion is exactly this conditional statement.

Reusable dependency (Dev bind `TrotterFormula.TimeOrdered`):
`QuantumAlgorithm.Concepts.TrotterFormula.TimeOrdered` supplies the
time-ordered/Trotter product-formula error bounds underlying the `poly(N)`
simulation cost.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Simulation

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- **c006 (Section 1.3).** If both the Trotter simulation and the
initial-state preparation are `poly(N)`, so is their total, while exact
classical diagonalization is unbounded by any polynomial.  The `hPrep`
hypothesis is the survey's explicit caveat on preparing the initial state. -/
theorem syk_simulation_poly_vs_exact
    (simCost prepCost : ℕ → ℕ)
    (hSim : ∃ C d, ∀ N, simCost N ≤ C * (N + 1) ^ d)
    (hPrep : ∃ C d, ∀ N, prepCost N ≤ C * (N + 1) ^ d) :
    (∃ C d, ∀ N, simCost N + prepCost N ≤ C * (N + 1) ^ d) ∧
    (∀ C d, ∃ N, polyCost C d N < expCost N) := by
  refine ⟨?_, fun C d => ?_⟩
  · obtain ⟨C₁, d₁, h₁⟩ := hSim
    obtain ⟨C₂, d₂, h₂⟩ := hPrep
    exact ⟨C₁ + C₂, max d₁ d₂, polySum_bound h₁ h₂⟩
  · obtain ⟨N, hN⟩ := expCost_dominates_poly C d
    exact ⟨N, hN N le_rfl⟩

/-- **c006 (Section 1.3), separated form.** The simulation cost alone is
polynomial, and exact diagonalization escapes every polynomial in `N`. -/
theorem syk_polynomial_versus_exponential
    (simCost : ℕ → ℕ) (hSim : ∃ C d, ∀ N, simCost N ≤ C * (N + 1) ^ d) :
    (∃ C d, ∀ N, simCost N ≤ C * (N + 1) ^ d) ∧
    (∀ C d, ∃ N, polyCost C d N < 2 ^ N) := by
  refine ⟨hSim, fun C d => ?_⟩
  obtain ⟨N, hN⟩ := expCost_dominates_poly C d
  exact ⟨N, by simpa [expCost] using hN N le_rfl⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Simulation
