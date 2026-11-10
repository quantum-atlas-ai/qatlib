/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS

open Matrix

theorem ProposalOracle.unitary_KK
    {D : ℕ} (Q : ProposalOracle D) :
    Q.unitaryᴴ * Q.unitary = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 Q.unitary_mem
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

theorem ProposalOracle.inverse_KK
    {D : ℕ} (Q : ProposalOracle D) :
    Q.inverseᴴ * Q.inverse = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').1 Q.inverse_mem
  rw [Matrix.star_eq_conjTranspose] at h
  exact h

end Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS
