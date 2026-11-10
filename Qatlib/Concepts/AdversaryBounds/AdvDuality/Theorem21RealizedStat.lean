/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped BigOperators Matrix.Norms.L2Operator

def Theorem21Realized : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (C : Circuit ((Fin 6 × Bool) × W))
    (psi : QState ((Fin 6 × Bool) × W)) (E : Finset ((Fin 6 × Bool) × W)) (eps : ℝ),
    IsUnitaryCircuit C → Normalized psi → 0 ≤ eps → eps ≤ 1 / 2 →
    (∀ x : Fin 20, 1 - eps ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (kushilevitzInputW x)) C psi)
        (if kushilevitzFunW x = true then E else Eᶜ)) →
    (2 + 3 * Real.sqrt 5 / 5) * (1 - 2 * Real.sqrt (eps * (1 - eps))) / 2 ≤ QueryCount C

end Qatlib.Concepts.AdversaryBounds.AdvDuality
