/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# theorem3.4 output-error and resource specification

Corresponds to Cornelissen and Jerbi, arXiv:2111.09787.
**Statement only — not proved in Qatlib.** This module defines
`theorem3_4_statement`, parameterized by a predicate certifying a candidate's
oracle implementation and its resource accounting. It supplies no circuit,
sampling procedure, or proof that a qualifying candidate exists.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
open Qatlib.Papers.MultivarMean21.MainResults


/-- **Statement only — not proved in Qatlib.**
Output-error and resource specification corresponding to theorem3.4.
`Implemented` must certify an oracle implementation of the candidate, including
its output semantics and recorded resource usage. No such implementation or
existence proof is supplied here; the legacy records alone do not restrict access
to the full input. -/
def theorem3_4_statement (d : ℕ)
    (Implemented : Estimator d SampleParams → Prop) : Prop :=
    ∃ E : Estimator d SampleParams,
      Implemented E ∧
      ∀ (p : SampleParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → Real.log ((d : ℝ) / p.δ) ≤ (p.n : ℝ) →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              Real.sqrt (r.trCov * Real.log ((d : ℝ) / p.δ) / (p.n : ℝ))) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ)

end Qatlib.Papers.MultivarMean21.MainResults.BoundedBinary
