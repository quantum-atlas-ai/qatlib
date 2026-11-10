/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix

open Qatlib.Concepts.LocalCircuits.LocalGateCosts

namespace Qatlib.Papers.QCircApprox95.MainResults

theorem lemma_annex_one (n m : ℕ) (X Y : Matrix (Fin n) (Fin m) ℂ)
    (hXY : Xᴴ * X = Yᴴ * Y) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ U * X = Y :=
  Qatlib.Concepts.GramQueryCore.GramRealization.gram_equal_actual_unitary_transport
    (Fin n) (Fin m) X Y hXY

end Qatlib.Papers.QCircApprox95.MainResults
