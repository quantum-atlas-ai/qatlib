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

set_option autoImplicit false

namespace Qatlib.Concepts.QcaDynamics.ScalarNoGo

open Finset
open scoped BigOperators

structure Weights (V : Type*) where

  neighborhood : Finset V

  weight : V → ℂ

  support : ∀ v, weight v ≠ 0 → v ∈ neighborhood

variable {V : Type*}

def step [Add V] (A : Weights V) (φ : V → ℂ) : V → ℂ :=
  fun x => ∑ e ∈ A.neighborhood, A.weight e * φ (x + e)

def Unitary [Sub V] [Zero V] (A : Weights V) : Prop :=
  (∑ e ∈ A.neighborhood, A.weight e * star (A.weight e)) = 1 ∧
    ∀ d : V, d ≠ 0 → (∑ e ∈ A.neighborhood,
      A.weight e * star (A.weight (e - d))) = 0

def evolveByTranslation [Add V] (A : Weights V) (e₀ : V) (c : ℂ) : Prop :=
  ∀ (φ : V → ℂ) (x : V), step A φ x = c * φ (x + e₀)

end Qatlib.Concepts.QcaDynamics.ScalarNoGo
