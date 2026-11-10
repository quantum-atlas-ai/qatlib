/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.EntanglementEntropy
import Qatlib.Concepts.Entanglement.Separability.EntanglementSeparability
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Papers.QShannonWilde11.MainResults

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable def witnessExpectation {D E : ℕ}
    (W : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) : ℝ :=
  (Matrix.trace (W * ρ)).re

end Qatlib.Papers.QShannonWilde11.MainResults
