/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutator
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCore
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterOrderedCommutatorAthe
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrectedAthe
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCombinatorics
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorMultiplicative
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorNormGibbs
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefutations
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorWords

/-!
# Ordered derivative levels and raw segment selectors

This module defines the derivative-level terms and grouped integral levels used to describe
ordered conjugation remainders. The quantities `orderedLevelTerm` and `groupedIntegralLevel`
organize the prefix, active generator, and suffix contributions in the commutator-scaling
setting [ChildsEtAl2021Trotter].

The definitions `rawTrotterBudgetFactor` and `rawTrotterSegments` provide a tolerance-scaled raw
commutator budget and its ceiling-based positive segment selector.

## Main statements

* `orderedLevelTerm`: one ordered contribution to the conjugation derivative.
* `orderedLevelSum`: sum of all derivative-level contributions.
* `groupedIntegralLevel`: grouped remainder contribution at a fixed level.
* `rawTrotterSegments`: ceiling-based raw-budget segment selector.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false


open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open Qatlib
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The derivative contribution from the generator at position `k`, with the suffix-conjugated
seed commuted with that generator and then conjugated by it and the prefix. -/
noncomputable def orderedLevelTerm (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (k : ℕ) (τ : ℝ) : Matrix I I ℂ :=
  pfConjWord (xs.take k)
    (pfConjExp (xs.getD k 0)
      (pfComm (xs.getD k 0) (pfConjWord (xs.drop (k + 1)) B τ)) τ) τ

/-- The sum of the ordered derivative-level terms over all generator positions. -/
noncomputable def orderedLevelSum (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ)
    (τ : ℝ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range xs.length, orderedLevelTerm xs B k τ

/-- The generator at position `k`, with zero as the default for an out-of-range lookup. -/
def orderedLevelGenerator (xs : List (Matrix I I ℂ)) (k : ℕ) : Matrix I I ℂ :=
  xs.getD k 0

/-- The sum of grouped integral terms over all grouped compositions of order `p` and length `k`. -/
noncomputable def groupedIntegralLevel {I : Type} [Fintype I]
    (xs : List (Matrix I I ℂ)) (B : Matrix I I ℂ) (p k : ℕ) (t : ℝ) :
    Matrix I I ℂ :=
  ∑ q ∈ groupedCompositions p k, groupedIntegralTerm xs B p q t

/-- The raw commutator error numerator divided by the requested tolerance, namely `p! *
pfCommAlphaSelf xs (p+1) * |t|^(p+1) / (p+1)! / ε`. -/
noncomputable def rawTrotterBudgetFactor (xs : List (Matrix I I ℂ)) (p : ℕ)
    (t ε : ℝ) : ℝ :=
  (p.factorial : ℝ) * pfCommAlphaSelf xs (p + 1) * |t| ^ (p + 1) /
    ((p + 1).factorial : ℝ) / ε

/-- The ceiling of `rawTrotterBudgetFactor`, bounded below by one. -/
noncomputable def rawTrotterSegments (xs : List (Matrix I I ℂ)) (p : ℕ)
    (t ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (rawTrotterBudgetFactor xs p t ε))

end

end Qatlib.Concepts.TrotterFormula.GeneralOrder
