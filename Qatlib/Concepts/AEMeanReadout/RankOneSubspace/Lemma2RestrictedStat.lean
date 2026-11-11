/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Diagonal
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedQuan
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Rank-one phase iterates and component specifications

`RankOneReflection.goodPart` and `RankOneReflection.badPart` restrict a vector to marked and
unmarked coordinates. `RankOneReflection.iterate` combines a conjugated zero-coordinate phase
update with the marked phase diagonal, and `Lemma2RestrictedSpec.expected` states its component
formulas from [BrassardHoyerTapp1998Counting].

## Main statements

* `RankOneReflection.iterate`: the rank-one phase-amplification matrix.
* `Lemma2RestrictedSpec.expected`: the good and bad component action contract.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open scoped BigOperators
namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
/-- The vector equal to `v` on coordinates marked by `g` and zero on all other coordinates. -/
noncomputable def goodPart {n : ℕ} (g : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun i => if g i then v i else 0
/-- The vector equal to `v` on unmarked coordinates and zero on coordinates marked by `g`. -/
noncomputable def badPart {n : ℕ} (g : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun i => if g i then 0 else v i
/-- The negative product of the conjugated zero-coordinate phase update with the diagonal phase
update on marked coordinates. -/
noncomputable def iterate {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (φ ϕ : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  -(A * (1 + (φ - 1) • Matrix.single 0 0 (1 : ℂ)) * A.conjTranspose *
    Matrix.diagonal (fun i => if g i then ϕ else 1))
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedSpec
/-- Specifies the first-column correction formulas for the phase iterate on the good and bad
components of any vector under `A * A.conjTranspose = 1`. -/
def expected : Prop :=
  (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (φ ϕ : ℂ) (v : Fin (n + 1) → ℂ),
  A * A.conjTranspose = 1 →
  (RankOneReflection.iterate A g φ ϕ).mulVec (RankOneReflection.goodPart g v) =
    (-ϕ) • RankOneReflection.goodPart g v +
      (ϕ * (1 - φ) * (∑ i, star (A i 0) * RankOneReflection.goodPart g v i)) • (fun i => A i 0) ∧
  (RankOneReflection.iterate A g φ ϕ).mulVec (RankOneReflection.badPart g v) =
    -RankOneReflection.badPart g v +
      ((1 - φ) * (∑ i, star (A i 0) * RankOneReflection.badPart g v i)) • (fun i => A i 0))
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedSpec
