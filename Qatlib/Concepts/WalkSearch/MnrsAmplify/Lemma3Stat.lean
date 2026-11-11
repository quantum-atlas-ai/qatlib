/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Relation

/-!
# Discriminant singular-value specification

Defines `Lemma3WalkSpec.expected`, the unit-interval singular-value contract for the
stationary-distribution discriminant of a finite irreducible chain. This is the spectral bound
used by MNRS quantum walk search [MagniezNayakRolandSantha2011].

## Main statements

* `expected`: The assertion that every dimension-indexed singular value of the discriminant of a
  finite irreducible stochastic matrix with a normalized positive stationary distribution lies
  in `[0, 1]` [Magniez et al., Lemma 3][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma3WalkSpec
/-- The assertion that every dimension-indexed singular value of the discriminant of a finite
irreducible stochastic matrix with a normalized positive stationary distribution lies in
`[0, 1]` [Magniez et al., Lemma 3][MagniezNayakRolandSantha2011]. -/
def expected : Prop :=
  (∀ (X : Type*) [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ),
  (∀ x y, 0 ≤ P x y) →
  (∀ x, (∑ y : X, P x y) = 1) →
  (∀ x y, Relation.ReflTransGen (fun a b : X => 0 < P a b) x y) →
  (∀ x, 0 < π x) →
  (∑ x : X, π x) = 1 →
  (∀ y, (∑ x : X, π x * P x y) = π y) →
  let PC : Matrix X X ℂ := fun x y => (P x y : ℂ);
  let D : Matrix X X ℂ :=
    Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)) * PC *
      Matrix.diagonal (fun x => (Real.sqrt (π x) : ℂ)⁻¹);
  ∀ i : Fin (Fintype.card X),
    (Matrix.toEuclideanLin D).singularValues i.val ∈ Set.Icc (0 : ℝ) 1)
end Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma3WalkSpec
