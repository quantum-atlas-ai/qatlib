/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Rank-one phase conjugation specification

`Lemma1RestrictedSpec.expected` states the rank-one phase-conjugation identity for a finite
complex matrix satisfying `A * A.conjTranspose = 1`. The formulation uses the zero-coordinate
projector and the outer product of the first column, as in [BrassardHoyerTapp1998Counting].

## Main statements

* `Lemma1RestrictedSpec.expected`: the rank-one conjugation contract.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedSpec
/-- Specifies that conjugating the zero-coordinate phase update by `A` yields the same update on
the outer product of its first column when `A * A.conjTranspose = 1`. -/
def expected : Prop :=
  (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (φ : ℂ),
  A * A.conjTranspose = 1 →
  A * (1 + (φ - 1) • Matrix.single 0 0 (1 : ℂ)) * A.conjTranspose =
    1 + (φ - 1) • Matrix.vecMulVec (fun i => A i 0) (fun j => star (A j 0)))
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedSpec
