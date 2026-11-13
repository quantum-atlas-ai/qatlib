/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedQuan
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Specification of known-success amplification

`Theorem2RestrictedSpec.expected` packages the good-mass guarantee for a unitary prepared state
when its initial success angle is known. The chosen number of iterations is `Nat.floor (π / (4 *
θ))`. For background, see [BrassardHoyerTapp1998Counting].

## Main statements

* `expected`: The proposition that the prescribed iteration count gives good squared mass at
  least `max (1 - a) a` for a unitary preparation with positive initial mass `a = sin² θ` and `0
  ≤ θ ≤ π/2`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2RestrictedSpec
/-- The proposition that the prescribed iteration count gives good squared mass at least `max (1
- a) a` for a unitary preparation with positive initial mass `a = sin² θ` and `0 ≤ θ ≤ π/2`. -/
def expected : Prop :=
  (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool),
  A * A.conjTranspose = 1 →
  let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
  let a : ℝ := ∑ i, Complex.normSq (RankOneReflection.goodPart g ψ i);
  ∀ (θ : ℝ),
    0 ≤ θ → θ ≤ Real.pi / 2 →
    Real.sin θ ^ 2 = a →
    0 < a →
    let m : ℕ := Nat.floor (Real.pi / (4 * θ));
    let v : Fin (n + 1) → ℂ :=
      ((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec ψ;
    max (1 - a) a ≤
      ∑ i, Complex.normSq (RankOneReflection.goodPart g v i))
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2RestrictedSpec
