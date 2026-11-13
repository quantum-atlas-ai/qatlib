/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CellularAuto96.MainResults.ActualEvolution
import Qatlib.Concepts.QcaDynamics.PeriodicNoGo.RadiusBound

/-!
# A coordinatewise finite-lattice no-go theorem

This module states a finite periodic version of the scalar cellular-automaton no-go result
associated with [Meyer1996]. A neighborhood radius bound together with the coordinatewise size
condition `4 * r < n i` forces a unitary quotient kernel to act as a translation multiplied by a
unit-modulus scalar.

## Main statements

* `noGo_corrected_finite`: proves the translation conclusion under the coordinatewise periodic
  size hypotheses.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
open Qatlib.Concepts.QcaDynamics.PeriodicNoGo
namespace Qatlib.Papers.CellularAuto96.MainResults

/-- If integer-lattice weights lie within coordinate radius `r`, each period exceeds `4 * r`,
and the quotient kernel is unitary, its action is a translation multiplied by a unit-modulus
original weight. This states the finite periodic no-go conclusion with the coordinatewise
size hypotheses used here in connection with [Meyer1996]. -/
theorem noGo_corrected_finite (d r : ℕ) (n : Fin d → ℕ)
    [∀ i, NeZero (n i)] (hn : ∀ i, 4*r<n i) (A : Weights (Fin d → ℤ))
    (hA : ∀ e ∈ A.neighborhood, ∀ i, -(r:ℤ) ≤ e i ∧ e i ≤ r)
    (hU : finiteKernel (quotientWeights (residueHom d n) A).weight ∈
      Matrix.unitaryGroup (∀ i, ZMod (n i)) ℂ) :
    ∃ (e₀ : Fin d → ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      ∀ (φ : (∀ i, ZMod (n i)) → ℂ) x,
        (finiteKernel (quotientWeights (residueHom d n) A).weight *ᵥ φ) x =
          c * φ (x + residueHom d n e₀) :=
  periodic_radius_matrix_noGo d r n hn A hA hU

end Qatlib.Papers.CellularAuto96.MainResults
