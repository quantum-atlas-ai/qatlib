/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveQueryPurification
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds

/-!
# Decoded branch output mass

`observedDecodedMass` sums the measurement masses of observed execution branches after decoding
a basis element together with its branch index. The optional output type includes an undecoded
outcome, and the definition does not require normalized input states. The measurement
interpretation follows [NielsenChuang2010].

## Main statements

* `observedDecodedMass`: Total mass assigned to an optional decoded output across indexed
  branches.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical

/-- Sums the measurement masses for an optional output over observed traces, using a decoder
that depends on the branch index and basis element. -/
noncomputable def observedDecodedMass {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    (O : Matrix I I ℂ) (P : ObservedCircuit I) (ψ : QState I)
    (decode : ℕ → I → Option J) (o : Option J) : ℝ :=
  (((observedTraces O P ψ).zipIdx).map fun t =>
    MeasureProb t.1.state (Finset.univ.filter fun z => decode t.2 z = o)).sum

end Qatlib.Concepts.AdversaryBounds.AdvDuality
