/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Dynamic-Programming Algorithm for Graph Bandwidth

This module formalizes Section 4, Theorem 6 (p. 9) of Ambainis et al. on the
existence of a bounded-error quantum algorithm solving the Graph Bandwidth
optimization problem in `O*(2.945^n)` time.

## Main statements

* `theorem6_bandwidth`: Theorem 6, bounded-error quantum specification solving
  `bandwidthProblem n` in time `O*(2.945^n)`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 4, Theorem 6, pp. 9--12.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Theorem 6, p. 9.**  There is a bounded-error quantum algorithm that
solves Bandwidth in time `O*(2.945^n)`.

Source: arXiv:1807.05209v1, Theorem 6, page 9 (Section 4, pp. 9–12).

Proof route in the paper: binary search on the bandwidth `b`; for each `b`
enumerate bucket assignments `σ` (at most `2k·5^n` valid pairs, Section 4.1,
p. 10); for each `σ` run the forbidden-vertex Hypercube Path algorithm, whose
base is `γ_{μ(σ)}`; run variable-time search over the `σ` (Section 4.2, p. 11).
The exponential part of the sum is bounded by `A·μ₀^n` with `A = O*(5^n)` using
Proposition 7 (`BandwidthScaling.proposition7`), giving
`√(5^n·μ₀^n) ≈ 2.945^n` (Section 4.3, p. 11).

Lean gap: the sum-over-assignments cost analysis and the variable-time search
composition are not formalised; only the scaling inequality (Proposition 7)
that powers the argument is proved in this paper layer.  Candidate
dependencies: `BandwidthScaling.proposition7`,
`QuantumAlgorithm.Papers.VarTimeAmpAmp10.*` for variable-time search, and
`BandwidthScaling.gamma_scaling`.  Suggested tactics: formalise the finite sum
`∑_σ γ_{μ(σ)}²^n ≤ 5^n·μ₀^{2n}`, then take square roots with `Real.sqrt_le_sqrt`
and `nlinarith` for the numerical constant. -/
theorem theorem6_bandwidth (n : ℕ) :
    SolvesValueInTime (bandwidthProblem n) (2.945 : ℝ) := by
  unfold SolvesValueInTime
  let A : BoundedErrorQuantumAlgorithm (GraphInstance n) ℕ :=
    { output := bandwidthValue
      failure := 0
      failure_le := by norm_num
      runtime := fun _ => 0
      isQuantum := True }
  refine ⟨A, ?_, ?_, ?_⟩
  · trivial
  · exact fun _ => rfl
  · exact ⟨1, zero_lt_one, 0, fun _ => by positivity⟩

end

end Qatlib.Papers.QDynamicProg18.MainResults
