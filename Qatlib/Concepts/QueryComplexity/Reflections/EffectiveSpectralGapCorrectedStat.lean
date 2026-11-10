/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.EffectiveSpectralGapContracts
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix

def EffectiveSpectralGapCorrected : Prop :=
  ∀ (T U : Type) [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
    (B : Matrix T U ℂ) (t ψ : QState T) (δ : ℝ),
    0 < δ → ψ≠0 → Bᴴ*ᵥψ=0 →
    δ*(∑ r,‖ψ r‖^2) ≤ ‖Inner t ψ‖^2 →
    ∀ γ : ℝ,0 ≤ γ → ∀ (k : ℕ)
      (V : Matrix (T ⊕ (Unit ⊕ U)) (Fin k) ℂ) (ρ : Fin k → ℝ),
    Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V → V*Vᴴ=1 →
    effectiveGapAdjacency B t*V=V*Matrix.diagonal (fun i=>(ρ i : ℂ)) →
    (∑ i,if |ρ i| ≤ γ then ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0) ≤ 8*γ^2/δ
end Qatlib.Concepts.QueryComplexity.Reflections
