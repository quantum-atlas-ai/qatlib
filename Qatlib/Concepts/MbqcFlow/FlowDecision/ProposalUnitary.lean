/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs

/-!
# Unitarity identities for proposal operators

Proves the adjoint-times-operator identities for both fields of `ProposalOracle`. The stored
unitarity of the proposal and its inverse gives the identities used in subsequent Kraus-operator
calculations.

Proposal and reversal operations appear in quantum Metropolis sampling; see [TemmeEtAl2011].

## Main statements

* `ProposalOracle.unitary_KK`: the proposal adjoint times the proposal is the identity.
* `ProposalOracle.inverse_KK`: the inverse adjoint times the inverse is the identity.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS

open Matrix

/-- The adjoint of a proposal oracle's unitary multiplied by that unitary equals the identity. -/
theorem ProposalOracle.unitary_KK
    {D : ℕ} (Q : ProposalOracle D) :
    Q.unitaryᴴ * Q.unitary = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 Q.unitary_mem
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

/-- The adjoint of a proposal oracle's inverse multiplied by that inverse equals the identity. -/
theorem ProposalOracle.inverse_KK
    {D : ℕ} (Q : ProposalOracle D) :
    Q.inverseᴴ * Q.inverse = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 Q.inverse_mem
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

end Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS
