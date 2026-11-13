/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Real-budget conversion specification

`RealBudgetConversionAlgorithm` specifies a uniform legal source-word construction from a real
alphabet-filtered Gram-matrix budget. It records a ceiling-based query bound, a real-overlap
guarantee, zero queries in degenerate cases, and a stronger distance estimate when the error is
at most the budget.

The mathematical background is described in [LeeEtAl2011].

## Main statements

* `RealBudgetConversionAlgorithm`: the real-budget state-conversion interface.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.QueryComplexity.StateConversion
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The existence of one positive constant controlling legal conversion words from real filtered
budgets, with the stated call, overlap, degenerate-case, and distance guarantees. -/
def RealBudgetConversionAlgorithm : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (X H : Type) [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] [Nonempty H] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ W →
    sourceRectValue (gramStateMatrix ρ-gramStateMatrix σ) (sourceAlphabetDelta input) ≤
      ENNReal.ofReal W → 0<ε → ε ≤ 1/3 →
    ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace n q H r)),
      sourceWordLegal C ∧
      sourceWordCalls C ≤ c*Nat.ceil (W*Real.log (2/ε)/ε^2) ∧
      ((W=0 ∨ n=0 ∨ q=0) → sourceWordCalls C=0) ∧
      (∀ x, (∑ p, star ((sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p)*sourceClean n q r hr true (σ x) p).re ≥
          Real.sqrt (1-ε)) ∧
      (ε ≤ W → ∀ x, ‖toEuclidean_fromVec (sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)-sourceClean n q r hr true (σ x))‖ < 4*ε)
end Qatlib.Concepts.QueryComplexity.StateConversion
