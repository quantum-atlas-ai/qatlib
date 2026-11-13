/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# proposition3.2 output-error and resource specification

Corresponds to Cornelissen and Jerbi, arXiv:2111.09787.
**Statement only — not proved in Qatlib.** This module defines
`proposition3_2_statement`, parameterized by a predicate certifying a candidate's
oracle implementation and its resource accounting. It supplies no circuit,
sampling procedure, or proof that a qualifying candidate exists.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- **Statement only — not proved in Qatlib.**
Output-error and resource specification corresponding to proposition3.2.
`Implemented` must certify an oracle implementation of the candidate, including
its output semantics and recorded resource usage. No such implementation or
existence proof is supplied here; the legacy records alone do not restrict access
to the full input. -/
def proposition3_2_statement {d : ℕ} (hd : 0 < d) (L2 α ε : ℝ) (m : ℕ)
    (hL2 : 0 < L2) (hL2' : L2 ≤ 1) (hm : 1 / L2 ≤ (m : ℝ))
    (hα : 0 < α) (hα' : α < 1) (hε : 0 < ε) (hε' : ε < 1)
    (r : FinRV d) (hbound : r.BoundedL2) (hmean : r.expectedNorm ≤ L2)
    (Implemented : PhaseEncoding d → Prop) : Prop :=
    ∃ PE : PhaseEncoding d,
      Implemented PE ∧
      1 - α / 2 ≤ gridProb d m (fun u =>
        stateDistSq (PE.state u)
          (targetPhaseState PE.N ((m : ℝ) * r.truncatedDirectionalMean α u)) ≤ ε ^ 2) ∧
      SoftOLeLogSq (PE.experiments : ℝ) ((m : ℝ) * Real.sqrt L2) (1 / ε) ∧
      SoftOLeLogSq (PE.queries : ℝ) ((m : ℝ) * Real.sqrt L2) (1 / ε)

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
