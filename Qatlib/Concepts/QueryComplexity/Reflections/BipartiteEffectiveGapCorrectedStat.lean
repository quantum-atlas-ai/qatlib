/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.SpanProgram
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Corrected bipartite gap contract

Defines `BipartiteEffectiveGapCorrected` for source dual-feasible witness data with `W ≥ 1`. The
positive-input clause requires a nonzero column-supported kernel vector with root mass at least
nine tenths of its squared norm; the negative-input clause bounds root spectral mass below
energy `c/W`.

The proposition records the complement-marked graph formulation associated with [Reichardt2011].

## Main statements

* `BipartiteEffectiveGapCorrected`: packages the nonzero positive witness and the bound `72 * (1
  + 1/W) * c^2` on negative low-energy mass.

## References

* [Reichardt, 2011][Reichardt2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix

/-- The source dual-feasible contract requiring a nonzero positive-input kernel witness with
root mass at least `9/10`, and negative-input spectral mass at energies at most `c/W`
bounded by `72 * (1 + 1/W) * c^2`. -/
def BipartiteEffectiveGapCorrected : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n m : ℕ)
    (input : X → Fin n → Bool) (f : X → Bool) (v : X → Fin n → Fin m → ℂ) (W : ℝ),
    SourceDualFeasible input f v W → 1 ≤ W →
    (∀ x,f x=true → ∃ ψ : QState (ColLab X f n m),ψ≠0 ∧
      sourceMarkedAdjacency input f v W x*ᵥSum.elim 0 ψ=0 ∧
      (9/10 : ℝ)*(∑ c,‖ψ c‖^2) ≤ ‖ψ (Sum.inl ())‖^2) ∧
    (∀ x,f x=false → ∀ c : ℝ,0 ≤ c → ∀ (k : ℕ)
      (V : Matrix (RowLab X f n m ⊕ ColLab X f n m) (Fin k) ℂ) (ρ : Fin k → ℝ),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V → V*Vᴴ=1 →
      sourceMarkedAdjacency input f v W x*V=V*Matrix.diagonal (fun i=>(ρ i : ℂ)) →
      (∑ i,if |ρ i| ≤ c/W then ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0) ≤ 72*(1+1/W)*c^2)
end Qatlib.Concepts.QueryComplexity.Reflections
