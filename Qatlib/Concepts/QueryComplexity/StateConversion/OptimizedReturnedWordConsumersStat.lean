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

def OptimizedReturnedWordConsumers : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (ε W : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<ε → ε ≤ 1/3 → 0 ≤ W →
    (sourceQDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) ≤ ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W*Real.log (1/ε)/ε^2) ∧
        ∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
          sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥
            Real.sqrt (1-ε)) ∧
    (sourceQNoncoherentDelta input (ε^4/16) (gramStateMatrix ρ) (gramStateMatrix σ) ≤
        ENNReal.ofReal W →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*W*Real.log (1/ε)/ε^2) ∧
        ∀ x, ∃ ξ : QState ((Fin (n+1) × Fin (q+1)) × (Bool × Fin r)),
          Normalized ξ ∧ ‖∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
            sourceClean n q r hr false (ρ x)) p)*sourceGarbageTarget n q r (σ x) ξ p‖ ≥
              Real.sqrt (1-ε))
end Qatlib.Concepts.QueryComplexity.StateConversion
