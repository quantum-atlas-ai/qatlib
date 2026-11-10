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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2RestrictedSpec
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
