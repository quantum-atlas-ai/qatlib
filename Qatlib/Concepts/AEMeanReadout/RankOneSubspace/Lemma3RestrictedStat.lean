/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedQuan
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open scoped BigOperators

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedSpec
def expected : Prop :=
  (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (φ ϕ : ℂ),
  A * A.conjTranspose = 1 →
  ‖φ‖ = 1 → ‖ϕ‖ = 1 →
  let ψ : Fin (n + 1) → ℂ := fun i => A i 0;
  let ψa := RankOneReflection.goodPart g ψ;
  let ψb := RankOneReflection.badPart g ψ;
  let a : ℝ := ∑ i, Complex.normSq (ψa i);
  (RankOneReflection.iterate A g φ ϕ).mulVec ψa =
    (ϕ * ((1 - φ) * (a : ℂ) - 1)) • ψa +
      (ϕ * (1 - φ) * (a : ℂ)) • ψb ∧
  (RankOneReflection.iterate A g φ ϕ).mulVec ψb =
    (-((1 - φ) * (a : ℂ) + φ)) • ψb +
      ((1 - φ) * (1 - (a : ℂ))) • ψa)
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedSpec
