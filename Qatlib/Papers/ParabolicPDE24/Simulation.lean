/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.FourierModel.FiberGenerator

/-!
# Conservation of lifted heat weights

The lifted evolution built from the Hermitian heat matrices preserves the trace weighted by
`positive`. `heat_eta_weight_constant` specializes the general conservation identity to the heat
fiber model used in [JinLiu2024] for any input matrix and auxiliary parameter function.

## Main statements

* `heat_eta_weight_constant`: the positive-weighted trace is constant under the lifted heat
  evolution.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
namespace Qatlib.Papers.ParabolicPDE24.Simulation
open Qatlib.Papers.ParabolicPDE24.FourierDefs
open Qatlib.Concepts.ChannelTheory.Naimark.EtaProjection

/-- For every input matrix `ρ`, the trace of `positive η` times the matrix evolved by
conjugation with the lifted heat evolution equals the initial weighted trace. See
[JinLiu2024]. -/
theorem heat_eta_weight_constant {E : Type} [Fintype E] [DecidableEq E]
    (k ε ω : ℝ) (η : E→ℝ) (ρ : Matrix (Fin 2×E) (Fin 2×E) ℂ) (t : ℝ) :
    (positive (I:=Fin 2) η*(evolution (heatA₁ ε ω) (heatA₂ k ε) η t*ρ*
      (evolution (heatA₁ ε ω) (heatA₂ k ε) η t)ᴴ)).trace=
        (positive (I:=Fin 2) η*ρ).trace :=
  positive_weight_constant _ _ (heatA₁_hermitian ε ω) (heatA₂_hermitian k ε) η ρ t
end Qatlib.Papers.ParabolicPDE24.Simulation
