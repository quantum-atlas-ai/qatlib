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
# Quantum Dynamic-Programming Algorithm for Directed Feedback Arc Set

This module formalizes Section 5.2, Corollary 9 (p. 13) of Ambainis et al. on
the existence of a bounded-error quantum algorithm solving the Directed Feedback
Arc Set optimization problem in `O*(1.728^n)` time.

## Main statements

* `corollary9_feedbackArcSet`: Corollary 9, bounded-error quantum specification
  solving `feedbackArcSetProblem n` in time `O*(1.728^n)`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 5.2, Corollary 9, p. 13.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Corollary 9, p. 13.**  There is a bounded-error quantum algorithm that
solves Directed Feedback Arc Set in time `O*(1.728^n)`.

Source: arXiv:1807.05209v1, Corollary 9, page 13 (Section 5.2).

Proof route in the paper: partition the vertex set into `A` and `B = S \ A`
with `A` before `B` in a topological order; the feedback sets of `A` and `B`
are independent, so the same two-level quantum minimum finding as Algorithm 2
computes the recurrence, at the identical cost `O*(1.728^n)` (no `log L`
factor, since the edge terms are unit costs).

Lean gap: the reduction to the TSP recurrence is not formalised; the statement
reuses the TSP cost structure with unit weights.  Candidate dependencies:
`theorem8_tsp` (this paper layer) with `w ≡ 1`, `feedbackArcSetSize` and
`IsAcyclic` from the model layer.  Suggested tactics: instantiate the TSP
algorithm with unit weights so that `log L = 0` is not used (the factor is
dropped), and transport the `O*(1.728^n)` bound through the recurrence
identification. -/
theorem corollary9_feedbackArcSet (n : ℕ) :
    SolvesValueInTime (feedbackArcSetProblem n) (1.728 : ℝ) := by
  let A : BoundedErrorQuantumAlgorithm (Fin n → Fin n → Bool) ℕ :=
    { output := feedbackArcSetSize
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
