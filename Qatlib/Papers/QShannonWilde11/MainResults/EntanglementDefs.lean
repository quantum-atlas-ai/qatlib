/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy
import Qatlib.Concepts.Entanglement.Separability.EntanglementSeparability

/-!
# Entanglement witness expectations

This module defines `witnessExpectation` as the real part of the trace pairing of an operator
with a bipartite matrix. This scalar quantity provides the expectation notation for the
entanglement criteria developed in the setting of [Wilde2017].

## Main statements

* `witnessExpectation`: Returns the real part of trace(Wρ).

## References

* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.QShannonWilde11.MainResults

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The real part of trace(Wρ), used as the expectation of a bipartite witness operator W
against ρ. -/
noncomputable def witnessExpectation {D E : ℕ}
    (W : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (Matrix.trace (W * ρ)).re

end Qatlib.Papers.QShannonWilde11.MainResults
