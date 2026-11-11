/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Query direct-sum specification

`QueryDirectSumConsumer` specifies a universal constant comparing the query complexity of
independent function evaluations with the copy count times the single-instance complexity. It
also requires a legal word computing the full output tuple with success probability at least
`2/3` under an explicit real query budget.

This is the direct-sum framework of [LeeEtAl2011].

## Main statements

* `QueryDirectSumConsumer`: the two-sided direct-sum comparison and budgeted evaluation-word
  specification.

## References

* [Lee et al., 2011, Corollary 5.3][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The existence of a universal positive constant comparing the query cost of `m` independent
function evaluations with `m` times the single-instance cost in both directions, together
with legal tuple-evaluation words using at most `ceil (c*m*Q)` calls and succeeding with
probability at least `2/3` for every nonnegative single-instance budget `Q`. -/
def QueryDirectSumConsumer : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (X E : Type) [Fintype X] [DecidableEq X]
    [Fintype E] [DecidableEq E] (n m q : ℕ)
    (input : X → Fin n → Fin (q+1)) (f : X → E),
    let many := fun xs : Fin m → X => fun j => f (xs j)
    let allInput := sourceIndependentInput input m
    (m : ℝ≥0∞)*sourceFunctionQ input f ≤ c*sourceFunctionQ allInput many ∧
    sourceFunctionQ allInput many ≤ c*(m : ℝ≥0∞)*sourceFunctionQ input f ∧
    (∀ Q : ℝ, 0 ≤ Q → sourceFunctionQ input f ≤ ENNReal.ofReal Q →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace (m*n) q (Option (Fin m → E)) r)),
        sourceWordLegal C ∧ sourceWordCalls C ≤ Nat.ceil (c*m*Q) ∧ ∀ xs,
        MeasureProb (sourceWordMatrix (sourceAlphabetOracle allInput xs) C *ᵥ
          sourceClean (m*n) q r hr false (Ket none))
          (Finset.univ.filter (fun p => p.2.1.2=some (many xs))) ≥ 2/3)
end Qatlib.Concepts.ConversionCore.WitnessCompile
