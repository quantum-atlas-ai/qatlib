/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Defs
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition1Defs

/-!
# Classical spectral-gap search specification

Defines `Proposition1WalkSpec.expected`, the finite-path formulation of the classical MNRS
search comparison [MagniezNayakRolandSantha2011]. It specifies strided and every-step scans,
success at least `1 / 2`, and explicit resource bounds in terms of the absolute gap and
marked-density lower bound.

## Main statements

* `expected`: The classical search contract for a primitive symmetric stochastic matrix with
  positive absolute gap `δ` and marked-density lower bound `ε`, giving the prescribed scan
  lengths, success at least `1 / 2`, and both trace-cost estimates [Magniez et al., Proposition
  1][MagniezNayakRolandSantha2011].

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open scoped BigOperators

open Qatlib.Concepts.WalkSearch.MnrsAmplify

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition1WalkSpec
/-- The classical search contract for a primitive symmetric stochastic matrix with positive
absolute gap `δ` and marked-density lower bound `ε`, giving the prescribed scan lengths,
success at least `1 / 2`, and both trace-cost estimates [Magniez et al., Proposition
1][MagniezNayakRolandSantha2011]. -/
def expected : Prop :=
  (∀ (δ ε : ℝ),
  0 < δ → 0 < ε →
  let t₁ : ℕ := Nat.ceil (1 / δ);
  let t₂ : ℕ := if ε ≤ 1 then Nat.ceil (4 / ε) else 0;
  let t : ℕ := t₁ * t₂;
  ∀ (X : Type*) [Fintype X] [Nonempty X] [DecidableEq X]
    (P : Matrix X X ℝ) (M : Finset X),
    P ∈ Matrix.rowStochastic ℝ X →
    P.IsPrimitive →
    P.IsSymm →
    mnrsAbsoluteGap P δ →
    (M.Nonempty → ε ≤ (M.card : ℝ) / (Fintype.card X : ℝ)) →
    (t₁ : ℝ) ≤ 2 / δ ∧
    (t₂ : ℝ) ≤ 5 / ε ∧
    (t : ℝ) ≤ 10 / (δ * ε) ∧
    mnrsSearchGuarantee P M t₁ t₂ (1 / 2) ∧
    mnrsSearchGuarantee P M 1 t (1 / 2) ∧
    (∀ (S U C : ℝ), 0 ≤ S → 0 ≤ U → 0 ≤ C →
      (∀ path : Fin (t₂ + 1) → X,
        mnrsTraceCost M t₁ t₂ path S U C ≤
          10 * (S + (1 / ε) * ((1 / δ) * U + C))) ∧
      (∀ path : Fin (t + 1) → X,
        mnrsTraceCost M 1 t path S U C ≤
          10 * (S + (1 / (δ * ε)) * (U + C)))))
end Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition1WalkSpec
