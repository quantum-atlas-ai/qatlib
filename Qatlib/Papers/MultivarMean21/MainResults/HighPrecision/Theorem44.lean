/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultivarMean21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# theorem4.4 output-error and resource specification

Corresponds to Cornelissen and Jerbi, arXiv:2111.09787.
**Statement only — not proved in Qatlib.** This module defines
`theorem4_4_statement`, parameterized by a predicate certifying a candidate's
oracle implementation and its resource accounting. It supplies no circuit,
sampling procedure, or proof that a qualifying candidate exists.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
open Qatlib.Papers.MultivarMean21.MainResults


/-- **Statement only — not proved in Qatlib.**
Output-error and resource specification corresponding to theorem4.4.
`Implemented` must certify an oracle implementation of the candidate, including
its output semantics and recorded resource usage. No such implementation or
existence proof is supplied here; the legacy records alone do not restrict access
to the full input. -/
def theorem4_4_statement (d : ℕ)
    (Implemented : Estimator d PhaseParams → Prop) : Prop :=
    ∃ E : Estimator d PhaseParams,
      Implemented E ∧
      ∀ (p : PhaseParams) (r : FinRV d),
        0 < p.δ → p.δ < 1 → Real.log ((d : ℝ) / p.δ) ≤ (p.n : ℝ) →
        Real.sqrt (d : ℝ) * Real.log ((d : ℝ) / p.δ) ≤ (p.n' : ℝ) →
        r.InBox (1 / 4) →
        E.failProb r p (fun v =>
            linfErr v r.mean ≤
              max (1 / Real.sqrt (p.n : ℝ)) ((d : ℝ) / (p.n' : ℝ)) *
                Real.log ((d : ℝ) / p.δ)) ≤ p.δ ∧
        SoftOLe ((E.cost p).experiments : ℝ) (p.n : ℝ) ((d : ℝ) / p.δ) ∧
        SoftOLe ((E.cost p).queries : ℝ) (p.n' : ℝ) ((d : ℝ) / p.δ)

end Qatlib.Papers.MultivarMean21.MainResults.HighPrecision
