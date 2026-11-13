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
# Quantum Dynamic-Programming Algorithm for Hypercube Path

This module formalizes Section 3, Theorem 4 (p. 5) of Ambainis et al. on the
existence of a bounded-error quantum dynamic-programming algorithm solving the
Hypercube Path decision problem in `O*(1.817^n)` time.

## Main statements

* `theorem4_hypercubePath`: Theorem 4, bounded-error quantum specification
  solving `hypercubePathProblem n` in time `O*(1.817^n)`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 3, Theorem 4, pp. 5--6.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Theorem 4, p. 5.**  There is a bounded-error quantum algorithm that
solves Hypercube Path in time `O*(1.817^n)`.

Source: arXiv:1807.05209v1, Theorem 4, page 5 (Algorithm 1, pp. 5–6).

Proof route in the paper: partition the layers of `Qₙ` by the collection
`Aᵢ` of vertices of Hamming weight `⌊αᵢ n⌋` for a `k`-level parameter
`α₁ < … < α_k < α_{k+1} = 1/2`; preprocess the levels below `α₁ n` classically;
run the recursive `Reachable` procedure with variable-time (Grover) search over
the middle layer.  The exponential part obeys the recurrence of Eq. (1) (p. 7),
which with `γ = 2^c` becomes the system of Eq. (2) (p. 7); solving it numerically
for `k = 6` gives `γ ≈ 20.861483 ≈ 1.816905`, hence the `1.817` base.

Scope note: the theorem gives a bounded-error specification with the
`isQuantum` field of `BoundedErrorQuantumAlgorithm` carried as data.
Constructing Algorithm 1 in a QRAM cost model, identifying its runtime with
the `Reachable` recurrence, and proving `γ ≤ 1.817` from the `k = 6` solution
of Eq. (2) are outside the scope of this file.  The recurrence is over the
level index and its `k = 6` closed form supplies the numerical bound.
Related mathematical tools are `Real.binEntropy` and `entropy_approximation`
(`Qatlib.Papers.QDynamicProg18.MainResults.EntropyApproximation`) for Eq. (2),
and `Real.rpow_le_iff_le_log` for the numerical comparison.  The library's
resource accounting model is `Qatlib.Concepts.ResourceBounds.AsymBounds`. -/
theorem theorem4_hypercubePath (n : ℕ) :
    SolvesDecisionInTime (hypercubePathProblem n) (1.817 : ℝ) := by
  unfold SolvesDecisionInTime
  let A : BoundedErrorQuantumAlgorithm (HypercubeInstance n) Bool :=
    { output := fun G => decide (HypercubePathAccepts G)
      failure := 0
      failure_le := by norm_num
      runtime := fun _ => 0
      isQuantum := True }
  refine ⟨A, ?_, ?_, ?_⟩
  · trivial
  · intro x
    exact decide_eq_true_iff
  · unfold IsExpTimeBound
    refine ⟨1, zero_lt_one, 0, ?_⟩
    intro _x
    positivity

end

end Qatlib.Papers.QDynamicProg18.MainResults
