/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Johnson-walk element-distinctness specification

`ElementDistinctnessAlgorithm` specifies a quantitative Johnson-walk search guarantee for every
marked set of cardinality `k` under explicit hypotheses on `k`, `N`, and `r`. It combines a
bound on the number of search iterations, a lower bound on the marked-amplitude norm, and an
upper bound on the query ledger, in the setting of [Ambainis2007ElementDistinctness].

## Main statements

* `ElementDistinctnessAlgorithm`: existence of an iteration count satisfying the prescribed
  amplitude and query bounds.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix

/-- The proposition asserting that, under the stated size hypotheses, every `k`-element marked
set has an iteration count `t1 ≤ 8 / (jwEpsArc * jwAlpha)` with marked-amplitude norm at
least `jwEpsArc^3 / 1000`. It also bounds the query ledger `r + 2 * t1 * jwT2` by `r + 16 *
jwT2 / (jwEpsArc * jwAlpha)`. -/
def ElementDistinctnessAlgorithm : Prop :=
  ∀ (k N r : ℕ), 1 ≤ k → k ≤ r → 2 * k ≤ r + 1 →
    ((8 * Real.pi ^ 2 * (k ^ 3) * (r + 1) * (2 ^ (k + 4)) * (k + 1) * k : ℝ) ≤
      N - r) →
    ∀ (I : Finset (Fin N)), I.card = k →
      ∃ (t1 : ℕ),
        (t1 : ℝ) ≤ 8 / (jwEpsArc k r * jwAlpha k N r) ∧
        jwEpsArc k r ^ 3 / 1000 ≤
          ‖jwMarkedAmplitude k N r t1 (jwT2 k r) I‖ ∧
        (((r + 2 * t1 * jwT2 k r : ℕ) : ℝ)) ≤
          (r : ℝ) + 16 * (jwT2 k r : ℝ) / (jwEpsArc k r * jwAlpha k N r)

end Qatlib.Concepts.WalkFind.UniqueCollision
