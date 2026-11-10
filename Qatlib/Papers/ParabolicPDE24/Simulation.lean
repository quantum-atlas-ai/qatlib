/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.FourierModel.FiberGenerator
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.ParabolicPDE24.Simulation
open Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection

theorem heat_eta_weight_constant {E : Type} [Fintype E] [DecidableEq E]
    (k ε ω : ℝ) (η : E→ℝ) (ρ : Matrix (Fin 2×E) (Fin 2×E) ℂ) (t : ℝ) :
    (positive (I:=Fin 2) η*(evolution (heatA₁ ε ω) (heatA₂ k ε) η t*ρ*
      (evolution (heatA₁ ε ω) (heatA₂ k ε) η t)ᴴ)).trace=
        (positive (I:=Fin 2) η*ρ).trace :=
  positive_weight_constant _ _ (heatA₁_hermitian ε ω) (heatA₂_hermitian k ε) η ρ t
end Qatlib.Papers.ParabolicPDE24.Simulation
