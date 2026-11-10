/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.QueryComplexity.StateConversion
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def OptimizedConversionEndpoints : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<ε → ε ≤ 1/3 →
    let R := gramStateMatrix ρ
    let S := gramStateMatrix σ
    sourceQDelta input (2*Real.sqrt (2*ε)) R S ≤ c*sourceCoherentQ input ρ σ ε ∧
    sourceCoherentQ input ρ σ ε ≤ c*ENNReal.ofReal (Real.log (1/ε)/ε^2)*
      sourceQDelta input (ε^4/16) R S ∧
    sourceQNoncoherentDelta input (2*Real.sqrt (2*ε)) R S ≤ c*sourceNoncoherentQ input ρ σ ε ∧
    sourceNoncoherentQ input ρ σ ε ≤ c*ENNReal.ofReal (Real.log (1/ε)/ε^2)*
      sourceQNoncoherentDelta input (ε^4/16) R S
end Qatlib.Concepts.QueryComplexity.StateConversion
