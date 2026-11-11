/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lattice search indices and time scales

This module defines the square lattice site type, Boolean marking oracles, and the unique-mark
condition. It also records query and move accounting and the two real time scales `sqrt (N * log
N)` and `sqrt N * log N`, where `N` is the lattice size.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `card_site`: the number of sites equals `latticeSize`.
* `sqrt_latticeSize`: the square root of the lattice size equals its side length.
* `sqrtNLatticeLog_eq`: side-length expression for the improved time scale.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

/-- The sites of an `n` by `n` square lattice, indexed by a pair of elements of `Fin n`. -/
abbrev Site (n : ℕ) : Type := Fin n × Fin n

/-- The number `n * n` of sites in the square lattice. -/
def latticeSize (n : ℕ) : ℕ := n * n

/-- A Boolean marking function on lattice sites. -/
abbrev Oracle (n : ℕ) : Type := Site n → Bool

/-- The condition that exactly one lattice site is marked `true` by the oracle. -/
def UniqueMarked {n : ℕ} (f : Oracle n) : Prop := ∃! s : Site n, f s = true

/-- The two kinds of lattice-search steps: examining a site and moving. -/
inductive StepKind where

  | examine

  | move
deriving DecidableEq, Repr

/-- Natural-number counts of total steps, queries, and moves, with total steps equal to queries
plus moves. -/
structure TimeAccount where

  steps : ℕ

  queries : ℕ

  moves : ℕ

  steps_eq : steps = queries + moves

/-- The real time scale `sqrt (N * log N)` for lattice size `N = latticeSize n`. -/
def sqrtNLatticeLog (n : ℕ) : ℝ :=
  Real.sqrt ((latticeSize n : ℝ) * Real.log (latticeSize n : ℝ))

/-- The real time scale `sqrt N * log N` for lattice size `N = latticeSize n`. -/
def sqrtNLogLattice (n : ℕ) : ℝ :=
  Real.sqrt (latticeSize n : ℝ) * Real.log (latticeSize n : ℝ)

/-- The cardinality of the lattice site type equals `latticeSize n`. -/
theorem card_site (n : ℕ) : Fintype.card (Site n) = latticeSize n := by
  simp [Site, latticeSize]

/-- A positive lattice side length gives a positive lattice size. -/
theorem latticeSize_pos {n : ℕ} (hn : 0 < n) : 0 < latticeSize n := by
  unfold latticeSize
  exact Nat.mul_pos hn hn

/-- The real square root of the lattice size equals the natural side length cast to the reals. -/
theorem sqrt_latticeSize (n : ℕ) : Real.sqrt (latticeSize n) = (n : ℝ) := by
  have h : (latticeSize n : ℝ) = (n : ℝ) ^ 2 := by
    simp [latticeSize, Nat.cast_mul, pow_two]
  rw [h, Real.sqrt_sq (Nat.cast_nonneg n)]

/-- The scale `sqrtNLatticeLog n` equals `n * sqrt (log (latticeSize n))` over the reals. -/
theorem sqrtNLatticeLog_eq (n : ℕ) :
    sqrtNLatticeLog n = (n : ℝ) * Real.sqrt (Real.log (latticeSize n : ℝ)) := by
  have hN : (latticeSize n : ℝ) = (n : ℝ) ^ 2 := by
    simp [latticeSize, Nat.cast_mul, pow_two]
  unfold sqrtNLatticeLog
  rw [hN, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)]

/-- The lattice size equals the square of its side length. -/
theorem latticeSize_eq_sq (n : ℕ) : latticeSize n = n ^ 2 := by
  simp [latticeSize, pow_two]

end Qatlib.Papers.WalkSpatial08.MainResults
