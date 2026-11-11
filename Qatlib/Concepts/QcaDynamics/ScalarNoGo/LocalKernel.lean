/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic

/-!
# Finite neighborhood scalar kernel models

Defines finite-neighborhood complex weights, their translation invariant update `step`, and the
autocorrelation equations `Unitary`. The predicate `evolveByTranslation` records equality of
this update with a single weighted translation for every input field, setting up the scalar
dynamics of [Meyer1996].

## Main statements

* `Weights`: bundles weights with a finite neighborhood containing their support.
* `Unitary`: states normalized delta autocorrelation.
* `evolveByTranslation`: specifies a weighted translation update.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.QcaDynamics.ScalarNoGo

open Finset
open scoped BigOperators

/-- Complex weights together with a finite neighborhood containing every point with nonzero
weight. -/
structure Weights (V : Type*) where

  neighborhood : Finset V

  weight : V → ℂ

  support : ∀ v, weight v ≠ 0 → v ∈ neighborhood

variable {V : Type*}

/-- The scalar update obtained by summing the weighted translates `φ (x + e)` over the
neighborhood. -/
def step [Add V] (A : Weights V) (φ : V → ℂ) : V → ℂ :=
  fun x => ∑ e ∈ A.neighborhood, A.weight e * φ (x + e)

/-- The autocorrelation equations requiring normalization at zero displacement and vanishing
correlation at every nonzero displacement. -/
def Unitary [Sub V] [Zero V] (A : Weights V) : Prop :=
  (∑ e ∈ A.neighborhood, A.weight e * star (A.weight e)) = 1 ∧
    ∀ d : V, d ≠ 0 → (∑ e ∈ A.neighborhood,
      A.weight e * star (A.weight (e - d))) = 0

/-- The property that `step A` acts on every input field as translation by `e₀` multiplied by
`c`. -/
def evolveByTranslation [Add V] (A : Weights V) (e₀ : V) (c : ℂ) : Prop :=
  ∀ (φ : V → ℂ) (x : V), step A φ x = c * φ (x + e₀)

end Qatlib.Concepts.QcaDynamics.ScalarNoGo
