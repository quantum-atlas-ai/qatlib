/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# lemma4.2 output-error and resource specification

Corresponds to Cornelissen and Jerbi, arXiv:2111.09787.
**Statement only — not proved in Qatlib.** This module defines
`lemma4_2_statement`, parameterized by a predicate certifying a candidate's
oracle implementation and its resource accounting. It supplies no circuit,
sampling procedure, or proof that a qualifying candidate exists.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- **Statement only — not proved in Qatlib.**
Output-error and resource specification corresponding to lemma4.2.
`Implemented` must certify an oracle implementation of the candidate, including
its output semantics and recorded resource usage. No such implementation or
existence proof is supplied here; the legacy records alone do not restrict access
to the full input. -/
def lemma4_2_statement {d : ℕ} (hd : 0 < d) (ε η : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hη : 0 < η) (hη' : η < 1) (m : ℕ)
    (hm : ε / (6 * Real.sqrt (d : ℝ)) ≤ (m : ℝ))
    (r : FinRV d) (hbox : r.InBox (1 / 4))
    (Implemented : PhaseEncoding d → Prop) : Prop :=
    ∃ PE : PhaseEncoding d,
      Implemented PE ∧
      1 - η / 2 ≤ gridProb d m (fun u =>
        stateDistSq (PE.state u)
          (targetPhaseState PE.N ((m : ℝ) * ∑ i, u i * r.mean i)) ≤ ε ^ 2) ∧
      SoftOLeLogSq (PE.experiments : ℝ) (Real.sqrt ((d : ℝ) * (m : ℝ))) (1 / (ε * η)) ∧
      SoftOLePow (PE.queries : ℝ) ((d : ℝ) * (m : ℝ)) (1 / (ε * η)) 4

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
