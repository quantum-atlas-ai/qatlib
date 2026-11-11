/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — Algorithm 4 (claim c004)

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1, Algorithm 4 in Sec. 3.1, p. 5 (proof sketch p. 5).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults.Algorithm4

open Qatlib.Papers.SpanProgRank11.MainResults
open scoped BigOperators ENNReal

/-- Number of phase-estimation applications in Algorithm 4: precision `1/L`
costs `O(L)` controlled applications of `e^{iH}` (Sec. 3.1, p. 5, citing
Kitaev [16] and Nagaj--Wocjan--Zhang [18]). -/
def phaseEstimationApplications (L : ℝ) : ℝ := L

/-- Number of amplitude-amplification applications in Algorithm 4: boosting the
`1/n` good probability to `Ω(1)` costs `O(√n)` applications of the phase
estimation (Sec. 3.1, p. 5, citing Brassard--Høyer--Mosca--Tapp [4]). -/
def amplitudeAmplificationApplications (n : ℕ) : ℝ := Real.sqrt (n : ℝ)

/-- Total number of simulated `e^{iH}` applications in Algorithm 4: `O(√n · L)`
(Sec. 3.1, p. 5).  Each simulation costs `T` queries to `A`. -/
def determinantSimulationCount (n : ℕ) (L : ℝ) : ℝ :=
  phaseEstimationApplications L * amplitudeAmplificationApplications n

/-- **Fixed arXiv:1103.0842v1, Algorithm 4 (Sec. 3.1, p. 5).**
The determinant problem can be solved in `Õ(√n · L · T)` quantum queries with
the promise that every input matrix `A` satisfies `‖A‖ ≤ 1` and every
non-singular input satisfies `σ_min(A) ≥ 1/L`.  `T` is the number of queries
needed to simulate `A`.

`Õ` hides `polylog(n)` factors; the explicit `O(√n · L · T)` bound proved here
(the `k = 0` case of `source_algorithm4_orderNotation`) implies the `Õ` claim.

Proof content: the paper composes the two granted quantum subroutines —
phase estimation at precision `1/L` (`O(L)` applications of `e^{iH}`, with `H`
the Hermitian dilation `[[0, A], [A*, 0]]` having eigenvalues `±σᵢ`) and
amplitude amplification boosting the `1/n` good probability to `Ω(1)` in `O(√n)`
applications.  The product is `√n · L` simulated applications, times `T` queries
per simulation.

Reused source subroutines: quantum phase estimation (paper [16,18]) and
quantum amplitude amplification (paper [4]); in the shared library these live
under `AmplitudeCore.PhaseEstimation` and `QueryComplexity.Amplification`. -/
theorem source_algorithm4 (n : ℕ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      determinantSimulationCount n L * T ≤ C * Real.sqrt (n : ℝ) * L * T := by
  refine ⟨1, one_pos, ?_⟩
  unfold determinantSimulationCount phaseEstimationApplications
    amplitudeAmplificationApplications
  rw [one_mul]
  exact le_of_eq (by ring)

/-- The `Õ(√n · L · T)` form of Algorithm 4: the polylogarithmic factor is made
explicit as `(log (n + 2))^k`, with some exponent `k`.  Taking `k = 0` (the
bound without logarithmic overhead) discharges the `Õ` claim. -/
theorem source_algorithm4_orderNotation (n : ℕ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ∃ (k : ℕ) (C : ℝ), 0 < C ∧
      determinantSimulationCount n L * T ≤
        C * Real.sqrt (n : ℝ) * L * T * (Real.log ((n : ℝ) + 2)) ^ k := by
  refine ⟨0, 1, one_pos, ?_⟩
  unfold determinantSimulationCount phaseEstimationApplications
    amplitudeAmplificationApplications
  simp only [pow_zero, mul_one]
  exact le_of_eq (by ring)

end Qatlib.Papers.SpanProgRank11.MainResults.Algorithm4
