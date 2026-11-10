/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped ENNReal ComplexOrder

def CoherentValueFeasibleBoundary : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (input : X → Fin n → Bool)
    (δ : ℝ) (ρ σ : Matrix X X ℂ), 0 ≤ δ →
    stateConversionSDP input δ ρ σ =
      ⨅ σ' : {M : Matrix X X ℂ // M.PosSemidef ∧
        filteredGamma2 (M - σ) (fun _ : Fin 1 => gramFilterAllOnes) ≤ ENNReal.ofReal δ},
        filteredGamma2 (ρ - σ'.1) (gramFilterDelta input)

end Qatlib.Concepts.GramQueryCore.ModelSemantics
