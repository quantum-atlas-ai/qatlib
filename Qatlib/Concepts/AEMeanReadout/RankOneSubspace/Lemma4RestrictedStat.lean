/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Specification of the rank-one sign action

`Lemma4RestrictedSpec.expected` records the two-dimensional action of the sign-phase iterate on
the prepared good and bad components, together with the identity relating their squared masses.
For background, see [BrassardHoyerTapp1998Counting].

## Main statements

* `expected`: The proposition that the rank-one sign-phase iterate has the specified good and
  bad component formulas, with bad mass equal to one minus good mass.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedSpec
/-- The proposition that the rank-one sign-phase iterate has the specified good and bad
component formulas, with bad mass equal to one minus good mass. -/
def expected : Prop :=
  (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool),
  A * A.conjTranspose = 1 →
  let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
  let ψa := RankOneReflection.goodPart g ψ;
  let ψb := RankOneReflection.badPart g ψ;
  let a : ℝ := ∑ i, Complex.normSq (ψa i);
  let b : ℝ := ∑ i, Complex.normSq (ψb i);
  (RankOneReflection.iterate A g (-1) (-1)).mulVec ψa =
    (1 - 2 * (a : ℂ)) • ψa - (2 * (a : ℂ)) • ψb ∧
  (RankOneReflection.iterate A g (-1) (-1)).mulVec ψb =
    (1 - 2 * (a : ℂ)) • ψb + (2 * (b : ℂ)) • ψa ∧
  b = 1 - a)
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedSpec
