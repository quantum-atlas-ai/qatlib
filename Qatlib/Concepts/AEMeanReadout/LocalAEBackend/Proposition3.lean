/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Defs
open scoped BigOperators

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3Spec
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
