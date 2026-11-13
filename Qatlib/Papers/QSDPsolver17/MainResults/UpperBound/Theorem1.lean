/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem1

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QSDPsolver17.MainResults
open scoped Classical

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `theorem1_quantum_sdp_solver`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def theorem1_quantum_sdp_solver_statement : Prop :=
    ∃ solver : QuantumSdpSolver,
      ∀ {n m : ℕ} (P : SdpData n m) (s : ℕ) (R r ε : ℝ) (hm : 0 < m),
        P.instanceAssumptions s R hm → P.traceBound R → P.dualL1Bound r →
        0 < ε →
        P.dualEpsOptimal (solver.output P ε) ε ∧
        (2 : ℝ) / 3 ≤ solver.successProb P ε ∧
        IsSoftO (solver.queryCost P ε)
          (Real.sqrt ((n : ℝ) * (m : ℝ)) * (s : ℝ) ^ 2 * (R * r / ε) ^ 8)
          ((n : ℝ) + (m : ℝ) + (s : ℝ) + R * r / ε) ∧
        IsSoftO (solver.gateCost P ε)
          (Real.sqrt ((n : ℝ) * (m : ℝ)) * (s : ℝ) ^ 2 * (R * r / ε) ^ 8)
          ((n : ℝ) + (m : ℝ) + (s : ℝ) + R * r / ε)

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
