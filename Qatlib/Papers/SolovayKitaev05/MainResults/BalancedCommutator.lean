/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CommutatorDecomposition

/-!
# Exact balanced commutators in SU(2)

This module proves `balanced_commutator_su2_exact`: every determinant-one unitary matrix of size
two is an exact group commutator of determinant-one unitaries. Both factors lie within `sqrt 2 *
sqrt ‖U - 1‖` of the identity, giving the balanced decomposition used in the Solovay–Kitaev
construction of [DawsonNielsen2006].

## Main statements

* `balanced_commutator_su2_exact`: Every matrix in SU(2) is an exact commutator of two SU(2)
  matrices, each at distance at most `sqrt 2 * sqrt ‖U - 1‖` from the identity, as used in
  [DawsonNielsen2006].

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

namespace Qatlib.Papers.SolovayKitaev05.MainResults.BalancedCommutator

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- Every matrix in SU(2) is an exact commutator of two SU(2) matrices, each at distance at most
`sqrt 2 * sqrt ‖U - 1‖` from the identity, as used in [DawsonNielsen2006]. -/
theorem balanced_commutator_su2_exact {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : U.det = 1) :
    ∃ V W : Matrix (Fin 2) (Fin 2) ℂ,
      V ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ W ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧
      V.det = 1 ∧ W.det = 1 ∧
      U = V * W * star V * star W ∧
      ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ ∧
      ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ :=
  Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2.exists_commutator_of_det_one
    hU hdet

end Qatlib.Papers.SolovayKitaev05.MainResults.BalancedCommutator
