/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical

noncomputable def observedDecodedMass {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (decode : ℕ → I → Option J) (o : Option J) : ℝ :=
  (((observedTraces O P ψ).zipIdx).map fun t =>
    MeasureProb t.1.state (Finset.univ.filter fun z => decode t.2 z = o)).sum

end Qatlib.Concepts.AdversaryBounds.AdvDuality
