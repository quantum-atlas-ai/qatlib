/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.LocalGateCosts.Costs
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization

/-!
# Unitary extension from equal Gram matrices

The module proves that two rectangular complex matrices with the same column Gram matrix differ
by left multiplication by a unitary matrix. `lemma_annex_one` packages this finite-dimensional
extension principle for the approximation arguments. See [Knill1995].

## Main statements

* `lemma_annex_one`: extends equality of Gram matrices to a unitary relation between the
  matrices.

## References

* [Knill, 1995][Knill1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix

open Qatlib.Concepts.LocalCircuits.LocalGateCosts

namespace Qatlib.Papers.QCircApprox95.MainResults

/-- If `Xᴴ * X = Yᴴ * Y`, there is a unitary matrix `U` with `U * X = Y`. This is the equal-Gram
extension statement of Lemma A.1 in [Knill1995]. -/
theorem lemma_annex_one (n m : ℕ) (X Y : Matrix (Fin n) (Fin m) ℂ)
    (hXY : Xᴴ * X = Yᴴ * Y) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ U * X = Y :=
  Qatlib.Concepts.GramQueryCore.GramRealization.gram_equal_actual_unitary_transport
    (Fin n) (Fin m) X Y hXY

end Qatlib.Papers.QCircApprox95.MainResults
