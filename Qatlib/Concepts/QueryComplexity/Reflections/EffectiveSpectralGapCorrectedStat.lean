/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.EffectiveSpectralGapContracts
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Nonzero-witness effective-gap contract

Defines `EffectiveSpectralGapCorrected`, requiring a nonzero vector annihilated by `Bᴴ` and a
positive lower bound on its squared target overlap relative to its squared norm. Every complete
orthonormal eigenframe then satisfies the asserted low-energy root-mass estimate.

This proposition records the corrected witness hypothesis for the effective-gap argument of
[Reichardt2011].

## Main statements

* `EffectiveSpectralGapCorrected`: states the root spectral-mass bound `8 * γ^2 / δ` with a
  nonzero kernel witness.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix

/-- The effective spectral-gap contract with a nonzero witness in the kernel of `Bᴴ`, bounding
root mass at energies at most `γ` by `8 * γ^2 / δ`. -/
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
