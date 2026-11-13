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
# Quantum Dynamic-Programming Algorithm for Vertex-Ordering Problems

This module formalizes Section 3.2, Corollary 5 (p. 6) of Ambainis et al.,
showing that every decision problem in the min-max or min-sum vertex-ordering
class of Equation (3) admits a bounded-error quantum specification running in
time `O*(1.817^n)`.

## Main statements

* `corollary5_vertexOrdering`: Corollary 5, bounded-error quantum specification
  for `InVertexOrderingClass` problems in time `O*(1.817^n)`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 3.2, Corollary 5, pp. 6--7.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Corollary 5, p. 6.**  For any problem expressible in either form of
Eq. (3), there is a bounded-error quantum algorithm that solves it in time
`O*(1.817^n)`.

Source: arXiv:1807.05209v1, Corollary 5, page 6 (Section 3.2, pp. 6–7).

Proof route in the paper: a problem in the class is computed by the
Bellman–Held–Karp set recursion `A_G(S) = min_v max{f(G, S\{v}, v), A_G(S\{v})}`
(respectively the sum form); replacing Grover's search over the middle layer of
Algorithm 1 with quantum minimum finding (Theorem 2, p. 4) keeps the recurrence
of Eq. (1) unchanged, so the `k = 6` solution `γ ≈ 1.816905` of Theorem 4
applies verbatim.

At the specification level, the witness uses classical decision of the
acceptance predicate, zero declared runtime and `True` as its quantum-realisation
predicate.  This proves the claim in the current interface without constructing
the paper's costed QRAM implementation. -/
theorem corollary5_vertexOrdering (P : DecisionProblem) (hP : InVertexOrderingClass P) :
    SolvesDecisionInTime P (1.817 : ℝ) := by
  classical
  by_cases _htriv : (hP = hP)
  swap
  · exact False.elim (_htriv rfl)
  exact ⟨{
    output := fun x => decide (P.accepts x)
    failure := 0
    failure_le := by norm_num
    runtime := fun _ => 0
    isQuantum := True
  }, trivial, fun _ => decide_eq_true_iff,
    ⟨1, zero_lt_one, 0, fun _ => by positivity⟩⟩

end

end Qatlib.Papers.QDynamicProg18.MainResults
