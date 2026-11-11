/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Data.Complex.Basic

/-!
# Matrix feasibility for query computations

`bssE` and `bssDelta` encode query signs and output selectors for finite input and output types.
`bssFamilyFeasible` collects positive semidefinite matrix constraints, `bssFeasible` quantifies
over their witnesses, and `IsBssSymmetry` specifies compatible permutations. These definitions
provide matrix feasibility vocabulary for the ordered-search semidefinite programming setting of
[ChildsLandahlParrilo2007].

## Main statements

* `bssFamilyFeasible`: positivity, initialization, transition, finalization, and output success
  constraints.
* `bssFeasible`: existence of a feasible matrix family.
* `IsBssSymmetry`: compatibility of input, query-index, and output permutations.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open scoped BigOperators ComplexOrder

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The query sign matrix whose entry is one when the two inputs agree at query index `i`, and
minus one otherwise. -/
def bssE {m : ℕ} (bit : X → Fin m → Bool) (i : Fin m) : Matrix X X ℂ :=
  Matrix.of fun x x' => if bit x i = bit x' i then 1 else -1

/-- The diagonal selector matrix for inputs whose value under `f` equals the specified output
`y`. -/
def bssDelta (f : X → Y) (y : Y) : Matrix X X ℂ :=
  Matrix.of fun x x' => if f x = y ∧ x = x' then 1 else 0

/-- The positive semidefinite matrix constraints for a specified query family: initialization,
intermediate query transitions, final output decomposition when `k > 0`, and output success
inequalities with error parameter `epsilon`. -/
def bssFamilyFeasible {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y) (k : ℕ) (ε : ℝ)
    (M : Fin m → ℕ → Matrix X X ℂ) (N : ℕ → Matrix X X ℂ) (Γ : Y → Matrix X X ℂ) :
    Prop :=
  (∀ i t, (M i t).PosSemidef) ∧ (∀ t, (N t).PosSemidef) ∧ (∀ y, (Γ y).PosSemidef) ∧
  (∀ x x', (∑ i, M i 0 x x') + N 0 x x' = 1) ∧
  (∀ t, t + 1 < k → ∀ x x',
      (∑ i, Matrix.hadamard (bssE bit i) (M i t) x x') + N t x x'
        = (∑ i, M i (t + 1) x x') + N (t + 1) x x') ∧
  (0 < k → ∀ x x',
      (∑ i, Matrix.hadamard (bssE bit i) (M i (k - 1)) x x') + N (k - 1) x x'
        = ∑ y, Γ y x x') ∧
  (∀ y, (Matrix.hadamard (bssDelta f y) (Γ y)
      - ((1 - ε : ℂ)) • (bssDelta f y)).PosSemidef)

/-- Existence of matrix families `M`, `N`, and `Gamma` satisfying `bssFamilyFeasible` for the
given query bits, output function, query count, and error parameter. -/
def bssFeasible {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ M : Fin m → ℕ → Matrix X X ℂ, ∃ N : ℕ → Matrix X X ℂ, ∃ Γ : Y → Matrix X X ℂ,
    bssFamilyFeasible bit f k ε M N Γ

/-- Compatibility of input, query-index, and output permutations with the query sign matrices
and output function. -/
def IsBssSymmetry {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (π : X ≃ X) (ρ : Fin m ≃ Fin m) (σ : Y ≃ Y) : Prop :=
  (∀ i x x', bssE bit (ρ i) x x' = bssE bit i (π x) (π x')) ∧
  (∀ x, σ (f x) = f (π x))

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
