/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Defs

/-!
# A discriminant singular-value specification

This module defines `Proposition3Spec.expected`, a proposition about the singular values of
`mnrsDiscriminant`. Its hypotheses specify a finite nonempty index type, an irreducible
row-sum-one real matrix with positive diagonal, and nonnegative normalized stationary weights;
the conclusion requires a unique singular-value index with value one. The discriminant
construction comes from quantum-walk search [MagniezNayakRolandSantha2011].

## Main declarations

* `Proposition3Spec.expected`: the quantified singular-value specification.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped BigOperators

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Spec
/-- The proposition that an irreducible row-sum-one real matrix with positive diagonal and
nonnegative normalized stationary weights has exactly one singular-value index of
`mnrsDiscriminant` equal to one [MagniezNayakRolandSantha2011]. -/
def expected : Prop :=
  (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X]
  (P : Matrix X X ℝ) (π : X → ℝ),
  P.IsIrreducible →
  (∀ x, ∑ y, P x y = 1) →
  (∀ x, 0 < P x x) →
  (∀ x, 0 ≤ π x) →
  (∑ x, π x) = 1 →
  (∀ y, ∑ x, π x * P x y = π y) →
  ∃! k : ℕ,
    (Matrix.toEuclideanLin (mnrsDiscriminant P π)).singularValues k = 1)
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Spec
