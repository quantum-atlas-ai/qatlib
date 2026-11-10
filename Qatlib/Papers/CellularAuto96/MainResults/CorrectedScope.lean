/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CellularAuto96.MainResults.ActualEvolution
import Qatlib.Concepts.QcaDynamics.PeriodicNoGo.RadiusBound
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
open Qatlib.Concepts.QcaDynamics.PeriodicNoGo
namespace Qatlib.Papers.CellularAuto96.MainResults

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
