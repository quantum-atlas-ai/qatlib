/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# lemma4.1 output-error and resource specification

Corresponds to Cornelissen and Jerbi, arXiv:2111.09787.
**Statement only — not proved in Qatlib.** This module defines
`lemma4_1_statement`, parameterized by a predicate certifying a candidate's
oracle implementation and its resource accounting. It supplies no circuit,
sampling procedure, or proof that a qualifying candidate exists.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- **Statement only — not proved in Qatlib.**
Output-error and resource specification corresponding to lemma4.1.
`Implemented` must certify an oracle implementation of the candidate, including
its output semantics and recorded resource usage. No such implementation or
existence proof is supplied here; the legacy records alone do not restrict access
to the full input. -/
def lemma4_1_statement {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (m : ℕ)
    (r : FinRV d) (hbox : r.InBox (1 / 4))
    (Implemented : SamplePhaseEncoding d r.Ω → Prop) : Prop :=
    ∃ L : SamplePhaseEncoding d r.Ω,
      Implemented L ∧
      (∀ (ω : r.Ω) (u : Vec d),
        stateDistSq (L.state ω u)
          (targetPhaseState L.N ((m : ℝ) / (d : ℝ) * ∑ i, u i * r.X ω i)) ≤ ε ^ 2) ∧
      SoftOLe (L.queries : ℝ) ((m : ℝ) + Real.log (1 / ε)) (m / ε)

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
