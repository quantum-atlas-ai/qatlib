/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection

/-!
# Basic data for Boolean witness conversion

Defines the padded Boolean input and the clean tagged embedding used in witness conversion
circuits. The extra input address carries the false symbol, and the embedding initializes the
query and scratch registers to zero.

The precision factor `conversionPrecisionPrice` records the inverse-square error and logarithmic
repetition dependence used in the state conversion construction of [LeeEtAl2011].

## Main definitions

* `conversionPaddedInput`: appends a false input coordinate.
* `conversionCleanEmbed`: initializes query and scratch registers around a tagged state.
* `conversionPrecisionPrice`: records the precision-dependent integer cost.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib

/-- Extends a Boolean input by a false symbol at its additional padded address. -/
def conversionPaddedInput {X : Type} {n : ℕ} (input : X → Fin n → Bool)
    (x : X) (j : Fin (n+1)) : Bool :=
  if h : j.val < n then input x ⟨j.val,h⟩ else false

/-- Embeds a state with Boolean tag `b` into the padded bit-query space, initializing the query
address, query answer, and scratch registers to zero. -/
noncomputable def conversionCleanEmbed (n r : ℕ) (hr : 0 < r)
    {H : Type} [Fintype H] [DecidableEq H] (b : Bool) (ψ : QState H) :
    QState ((Fin (n+1) × Bool) × ((Bool × H) × Fin r)) :=
  TensorState (Ket (0,false)) (TensorState (TensorState (Ket b) ψ) (Ket ⟨0,hr⟩))

/-- The integer precision factor `Nat.ceil (1/ε^2) * (Nat.ceil (Real.log (2/ε)) + 1)`. -/
noncomputable def conversionPrecisionPrice (ε : ℝ) : ℕ :=
  Nat.ceil (1 / ε^2) * (Nat.ceil (Real.log (2 / ε)) + 1)

end Qatlib.Concepts.GramQueryCore.LowerBoundTools
