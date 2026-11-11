/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Commuting projector constraints and postselection

This module defines projector families, satisfaction predicates, and scalar parameters for the
commuting-projector setting of [SattathArad2015]. A `QSatFamily` carries a finite family of
positive semidefinite idempotent matrices, while `CommutingFamily` expresses pairwise
commutation.

The operation `zeroPostselect` multiplies a matrix by the complement of a constraint projector
on both sides. It enforces its own zero constraint and preserves other zero constraints in a
commuting family.

## Main statements

* `zeroPostselect_satisfies_own`: A zero postselection enforces the selected constraint.
* `zeroPostselect_preserves`: Commutation preserves previously satisfied constraints.
* `zeroSweep_preserves`: A finite sweep preserves simultaneous satisfaction.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped BigOperators Matrix ComplexOrder
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.Defs

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The predicate that a complex matrix is positive semidefinite and idempotent. -/
def IsProjector (P : Matrix D D ℂ) : Prop := P.PosSemidef ∧ P * P = P

/-- The predicate that the matrix rank of `P` is at most the natural number `r`. -/
def rankAtMost (P : Matrix D D ℂ) (r : ℕ) : Prop := Matrix.rank P ≤ r

/-- Natural parameters `n`, `m`, `k`, `r`, and `g` for the quantum satisfiability estimates,
together with the requirement `r > 0`. -/
structure QSatParams where

  n : ℕ

  m : ℕ

  k : ℕ

  r : ℕ

  g : ℕ

  hr : 0 < r

/-- A family of `m` complex constraint matrices indexed by `Fin m`, each positive semidefinite
and idempotent. -/
structure QSatFamily (D : Type) [Fintype D] [DecidableEq D] (m : ℕ) where

  P : Fin m → Matrix D D ℂ

  isProj : ∀ i, IsProjector (P i)

/-- The predicate that every pair of constraint matrices in a `QSatFamily` commutes. -/
def CommutingFamily {m : ℕ} (F : QSatFamily D m) : Prop :=
  ∀ i j, F.P i * F.P j = F.P j * F.P i

/-- The predicate that every constraint projector annihilates the matrix `M` on the left. -/
def SatisfiesMat {m : ℕ} (M : Matrix D D ℂ) (F : QSatFamily D m) : Prop :=
  ∀ i, F.P i * M = 0

/-- The satisfaction predicate for a density matrix, requiring every constraint projector to
annihilate its underlying matrix on the left. -/
def Satisfies {m : ℕ} (ρ : Density D) (F : QSatFamily D m) : Prop :=
  SatisfiesMat ρ.val F

/-- The natural-logarithm parameter `1 / (δ * (k - log(g * r * exp 1)))`. -/
noncomputable def etaNatural (δ k r g : ℝ) : ℝ :=
  1 / (δ * (k - Real.log (g * r * Real.exp 1)))

/-- The natural-number ceiling of `4 * m * η * log(η + 2)`, using the natural logarithm. -/
noncomputable def thresholdNatural (m : ℕ) (η : ℝ) : ℕ :=
  Nat.ceil (4 * (m : ℝ) * η * Real.log (η + 2))

/-- The unnormalized zero-outcome postselection `(1 - F.P i0) * M * (1 - F.P i0)` for constraint
`i0`. -/
def zeroPostselect {m : ℕ} (F : QSatFamily D m) (i0 : Fin m) (M : Matrix D D ℂ) :
    Matrix D D ℂ :=
  (1 - F.P i0) * M * (1 - F.P i0)

/-- Zero-outcome postselection makes the selected constraint projector annihilate the resulting
matrix on the left. -/
theorem zeroPostselect_satisfies_own {m : ℕ} (F : QSatFamily D m) (i0 : Fin m)
    (M : Matrix D D ℂ) :
    F.P i0 * zeroPostselect F i0 M = 0 := by
  have hsq : F.P i0 * F.P i0 = F.P i0 := (F.isProj i0).2
  have h1 : F.P i0 * (1 - F.P i0) = 0 := by
    rw [Matrix.mul_sub, mul_one, hsq, sub_self]
  calc F.P i0 * zeroPostselect F i0 M
      = (F.P i0 * (1 - F.P i0)) * M * (1 - F.P i0) := by
        simp only [zeroPostselect]
        noncomm_ring
    _ = 0 := by rw [h1]; simp

/-- In a commuting family, zero-outcome postselection at `i0` preserves left-annihilation by any
constraint projector `F.P j` that already annihilates `M`. -/
theorem zeroPostselect_preserves {m : ℕ} (F : QSatFamily D m) (hcomm : CommutingFamily F)
    (i0 j : Fin m) (M : Matrix D D ℂ) (hM : F.P j * M = 0) :
    F.P j * zeroPostselect F i0 M = 0 := by
  have hc : F.P j * (1 - F.P i0) = (1 - F.P i0) * F.P j := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, one_mul, hcomm j i0]
  calc F.P j * zeroPostselect F i0 M
      = (F.P j * (1 - F.P i0)) * M * (1 - F.P i0) := by
        simp only [zeroPostselect]
        noncomm_ring
    _ = ((1 - F.P i0) * F.P j) * M * (1 - F.P i0) := by rw [hc]
    _ = (1 - F.P i0) * (F.P j * M) * (1 - F.P i0) := by noncomm_ring
    _ = 0 := by rw [hM]; simp

/-- For a commuting family, folding zero-outcome postselection over any finite list preserves
satisfaction of every constraint when the input already satisfies the family. -/
theorem zeroSweep_preserves {m : ℕ} (F : QSatFamily D m) (hcomm : CommutingFamily F)
    (l : List (Fin m)) (M : Matrix D D ℂ) (hM : SatisfiesMat M F) :
    SatisfiesMat (l.foldr (zeroPostselect F) M) F := by
  induction l with
  | nil => exact hM
  | cons i0 rest ih =>
    simp only [List.foldr_cons]
    intro j
    exact zeroPostselect_preserves F hcomm i0 j (rest.foldr (zeroPostselect F) M) (ih j)

end Qatlib.Papers.CommutingLLL13.MainResults.Defs
