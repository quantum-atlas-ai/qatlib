/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Alphabet phase word assembly specification

Defines `AlphabetPhaseWordAssembly`, the requirement that legal words using the controlled
witness walk can be implemented in a padded alphabet oracle space. The encoding is isometric,
preserves the action on every encoded state, and uses at most twice the original query count.

This is the word assembly component of the state conversion framework in [LeeEtAl2011].

## Main statements

* `AlphabetPhaseWordAssembly`: specifies isometric simulation of controlled walk words by
  alphabet queries.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The proposition that every legal controlled witness walk word has an isometric alphabet
oracle simulation with positive workspace size and at most twice its oracle call count. -/
def AlphabetPhaseWordAssembly : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q m b : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u : X → Fin n → QState (Fin m)) (W ε : ℝ), 0<q →
    ∀ C : SourceWord ((Bool × SourceGeometry n q m H) × Fin (2^b)), sourceWordLegal C →
    ∃ (r : ℕ) (_hr : 0<r)
      (F : Matrix (SourceSpace n q H r) ((Bool × SourceGeometry n q m H) × Fin (2^b)) ℂ)
      (D : SourceWord (SourceSpace n q H r)),
      Fᴴ * F=1 ∧ sourceWordLegal D ∧ sourceWordCalls D ≤ 2*sourceWordCalls C ∧
      ∀ (x : X) (ψ : QState ((Bool × SourceGeometry n q m H) × Fin (2^b))),
        sourceWordMatrix (sourceAlphabetOracle input x) D *ᵥ (F *ᵥ ψ)=
          F *ᵥ (sourceWordMatrix (sourceControlledU (2^b)
            (ReflectionAbout (sourceKeep input x) *
              ReflectionAbout (sourceComplement input ρ σ u W ε))) C *ᵥ ψ)
end Qatlib.Concepts.GramQueryCore.LowerBoundTools
