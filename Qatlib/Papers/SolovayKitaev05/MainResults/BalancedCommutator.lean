/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CommutatorDecomposition
set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.BalancedCommutator

open Matrix
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

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
