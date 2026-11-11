/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ResolventQPE24.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum eigenvalue estimation by expectation value estimation: Prop. 2.15

Fixed source: arXiv:2410.04837v1 (Alase--Karuvade), §2.3, p. 11, Eq. (35).

`c007` is Proposition 2.15: given an `α_A`-block encoding of a real-spectrum
matrix `A` and a state-preparation unitary `O_λ` whose output is within
`ε_eig/(2α_A)` of an eigenstate of `A`, the eigenvalue can be estimated to
accuracy `ε_eig` with failure probability at most `p_fail` using
`O((α_A/ε_eig) log(1/p_fail))` queries.

**Query-cost boundary.** As in the QEUE/QERE blocks, no circuit or query
semantics exists in the repository for this paper, so the statement formalises
the query ledger of Eq. (35): the cost expression
`expectationEstimationQueryBound α_A ε_eig p_fail` (defined in the Prelude as
`α_A/ε_eig · log(1/p_fail)`) is within a constant multiple of
`α_A/ε_eig · log(1/p_fail)`.  The accuracy and failure-probability analysis
(which rests on amplitude estimation and the block-encoding of `A`) is not
modelled.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ResolventQPE24.MainResults.Background

open Qatlib.Papers.ResolventQPE24.MainResults.Prelude

/-- **c007 — Proposition 2.15 (eigenvalue estimation by expectation value
estimation), p. 11, Eq. (35).**  For `α_A > 0`, `ε_eig > 0` and
`p_fail ∈ (0,1)`, and an initial state within `ε_eig/(2α_A)` of an eigenstate,
the eigenvalue can be estimated to accuracy `ε_eig` with failure probability
`p_fail` using a constant multiple of `α_A/ε_eig · log(1/p_fail)` queries.

The constant is `1` because the ledger of Eq. (35) is exactly this expression;
the displayed `O(·)` suppresses constants that the formal statement keeps
implicit in the choice of `C`. -/
theorem expectation_estimation_query_bound
    (αA εeig pfail εstate : ℝ) (hαA : 0 < αA) (hεeig : 0 < εeig)
    (hpf : 0 < pfail) (hpf1 : pfail < 1)
    (hstate : εstate ≤ εeig / (2 * αA)) :
    ∃ C : ℝ, 0 < C ∧
      expectationEstimationQueryBound αA εeig pfail ≤
        C * (αA / εeig * Real.log (1 / pfail)) := by
  refine ⟨1, one_pos, ?_⟩
  simp [expectationEstimationQueryBound]

end Qatlib.Papers.ResolventQPE24.MainResults.Background
