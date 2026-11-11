/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem6HeuristicAuxiliary

/-!
# Heuristic-search cost specification

`Theorem6HeuristicSpec.expected` states the distributional square-root cost bound for heuristic
search in [BrassardEtAl2002]. Its hypothesis requires a positive number of successful seeds on
every input in the support of the input law.

## Main statements

* `Theorem6HeuristicSpec.expected`: the average-cost specification for quantum heuristic search.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh6

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem6HeuristicSpec
/-- Specifies that the distributional quantum search cost is at most `400` times the square root
of the classical average time when every supported input has a successful seed. -/
def expected : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (G : (Fin n → Bool) → Fin n → Fin n)
    (D : PMF (Fin n → Bool)) (T : ℕ),
    (∀ f ∈ D.support, 0 < BHMTTh6.heuristicGoodCount n G f) →
    BHMTTh6.heuristicQuantumChiCost hn G D T ≤
      ENNReal.ofReal (400 * Real.sqrt (BHMTTh6.heuristicClassicalTime n G D))
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem6HeuristicSpec
