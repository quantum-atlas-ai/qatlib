/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

abbrev Site (n : ℕ) : Type := Fin n × Fin n

def latticeSize (n : ℕ) : ℕ := n * n

abbrev Oracle (n : ℕ) : Type := Site n → Bool

def UniqueMarked {n : ℕ} (f : Oracle n) : Prop := ∃! s : Site n, f s = true

inductive StepKind where

  | examine

  | move
deriving DecidableEq, Repr

structure TimeAccount where

  steps : ℕ

  queries : ℕ

  moves : ℕ

  steps_eq : steps = queries + moves

def sqrtNLatticeLog (n : ℕ) : ℝ :=
  Real.sqrt ((latticeSize n : ℝ) * Real.log (latticeSize n : ℝ))

def sqrtNLogLattice (n : ℕ) : ℝ :=
  Real.sqrt (latticeSize n : ℝ) * Real.log (latticeSize n : ℝ)

theorem card_site (n : ℕ) : Fintype.card (Site n) = latticeSize n := by
  simp [Site, latticeSize]

theorem latticeSize_pos {n : ℕ} (hn : 0 < n) : 0 < latticeSize n := by
  unfold latticeSize
  exact Nat.mul_pos hn hn

theorem sqrt_latticeSize (n : ℕ) : Real.sqrt (latticeSize n) = (n : ℝ) := by
  have h : (latticeSize n : ℝ) = (n : ℝ) ^ 2 := by
    simp [latticeSize, Nat.cast_mul, pow_two]
  rw [h, Real.sqrt_sq (Nat.cast_nonneg n)]

theorem sqrtNLatticeLog_eq (n : ℕ) :
    sqrtNLatticeLog n = (n : ℝ) * Real.sqrt (Real.log (latticeSize n : ℝ)) := by
  have hN : (latticeSize n : ℝ) = (n : ℝ) ^ 2 := by
    simp [latticeSize, Nat.cast_mul, pow_two]
  unfold sqrtNLatticeLog
  rw [hN, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)]

theorem latticeSize_eq_sq (n : ℕ) : latticeSize n = n ^ 2 := by
  simp [latticeSize, pow_two]

end Qatlib.Papers.WalkSpatial08.MainResults
