/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AndersonLoc09.MainResults

def twoLevel (E1 E2 V : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![E1, V; V, E2]

theorem twoLevel_sub_scalar (E1 E2 V lam : ℝ) :
    twoLevel E1 E2 V - Matrix.scalar (Fin 2) lam
      = !![E1 - lam, V; V, E2 - lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoLevel, Matrix.sub_apply, Matrix.scalar_apply]

theorem twoLevel_det_sub (E1 E2 V lam : ℝ) :
    (twoLevel E1 E2 V - Matrix.scalar (Fin 2) lam).det
      = (E1 - lam) * (E2 - lam) - V ^ 2 := by
  rw [twoLevel_sub_scalar, Matrix.det_fin_two_of]
  ring

def upperEigen (E1 E2 V : ℝ) : ℝ :=
  (E1 + E2) / 2 + Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2)

def lowerEigen (E1 E2 V : ℝ) : ℝ :=
  (E1 + E2) / 2 - Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2)

theorem upperEigen_charpoly (E1 E2 V : ℝ) :
    (twoLevel E1 E2 V - Matrix.scalar (Fin 2) (upperEigen E1 E2 V)).det = 0 := by
  rw [twoLevel_det_sub]
  unfold upperEigen
  have h : Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2) ^ 2 = ((E1 - E2) / 2) ^ 2 + V ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [h]

theorem lowerEigen_charpoly (E1 E2 V : ℝ) :
    (twoLevel E1 E2 V - Matrix.scalar (Fin 2) (lowerEigen E1 E2 V)).det = 0 := by
  rw [twoLevel_det_sub]
  unfold lowerEigen
  have h : Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2) ^ 2 = ((E1 - E2) / 2) ^ 2 + V ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [h]

def levelGap (E1 E2 V : ℝ) : ℝ := Real.sqrt ((E1 - E2) ^ 2 + 4 * V ^ 2)

theorem eigen_gap (E1 E2 V : ℝ) :
    upperEigen E1 E2 V - lowerEigen E1 E2 V = levelGap E1 E2 V := by
  unfold upperEigen lowerEigen levelGap
  have hs : 0 ≤ ((E1 - E2) / 2) ^ 2 + V ^ 2 := by positivity
  have hsq : (2 * Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2)) ^ 2
      = (E1 - E2) ^ 2 + 4 * V ^ 2 := by
    rw [show (2 * Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2)) ^ 2
          = 4 * Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2) ^ 2 by ring,
      Real.sq_sqrt hs]
    ring
  have hnonneg : 0 ≤ 2 * Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2) := by positivity
  have hgap : Real.sqrt ((E1 - E2) ^ 2 + 4 * V ^ 2)
      = 2 * Real.sqrt (((E1 - E2) / 2) ^ 2 + V ^ 2) :=
    (Real.sqrt_eq_iff_eq_sq (by positivity) hnonneg).mpr hsq.symm
  rw [hgap]
  ring

def paperGap (E1 E2 V12 : ℝ) : ℝ := Real.sqrt ((E1 - E2) ^ 2 + V12 ^ 2)

theorem paperGap_eq_levelGap (E1 E2 V12 : ℝ) :
    paperGap E1 E2 V12 = levelGap E1 E2 (V12 / 2) := by
  unfold paperGap levelGap
  congr 1
  ring

theorem paperGap_ge_abs (E1 E2 V12 : ℝ) : |V12| ≤ paperGap E1 E2 V12 := by
  unfold paperGap
  have h : V12 ^ 2 ≤ (E1 - E2) ^ 2 + V12 ^ 2 := by nlinarith [sq_nonneg (E1 - E2)]
  calc |V12| = Real.sqrt (V12 ^ 2) := (Real.sqrt_sq_eq_abs V12).symm
    _ ≤ Real.sqrt ((E1 - E2) ^ 2 + V12 ^ 2) := Real.sqrt_le_sqrt h

theorem paperGap_eq_abs_iff (E1 E2 V12 : ℝ) :
    paperGap E1 E2 V12 = |V12| ↔ E1 = E2 := by
  constructor
  · intro h
    unfold paperGap at h
    have hsq : (E1 - E2) ^ 2 + V12 ^ 2 = V12 ^ 2 := by
      have h2 : Real.sqrt ((E1 - E2) ^ 2 + V12 ^ 2) ^ 2 = |V12| ^ 2 := by rw [h]
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (E1 - E2) ^ 2 + V12 ^ 2),
        sq_abs] at h2
      exact h2
    have hzero : (E1 - E2) ^ 2 = 0 := by nlinarith
    have := sq_eq_zero_iff.mp hzero
    linarith
  · intro h
    unfold paperGap
    rw [h]
    simp [Real.sqrt_sq_eq_abs]

theorem paperGap_eq_zero_iff (E1 E2 V12 : ℝ) :
    paperGap E1 E2 V12 = 0 ↔ E1 = E2 ∧ V12 = 0 := by
  unfold paperGap
  rw [Real.sqrt_eq_zero (by positivity)]
  constructor
  · intro h
    have h1 : (E1 - E2) ^ 2 = 0 := by nlinarith [sq_nonneg V12]
    have h2 : V12 ^ 2 = 0 := by nlinarith [sq_nonneg (E1 - E2)]
    exact ⟨by linarith [sq_eq_zero_iff.mp h1], sq_eq_zero_iff.mp h2⟩
  · rintro ⟨h1, h2⟩
    subst h1
    subst h2
    ring

theorem paperGap_pos_iff (E1 E2 V12 : ℝ) :
    0 < paperGap E1 E2 V12 ↔ E1 ≠ E2 ∨ V12 ≠ 0 := by
  have hnonneg : 0 ≤ paperGap E1 E2 V12 := Real.sqrt_nonneg _
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hzero := (paperGap_eq_zero_iff E1 E2 V12).mpr ⟨hc.1, hc.2⟩
    linarith
  · intro h
    have hzero : paperGap E1 E2 V12 ≠ 0 := by
      intro hz
      obtain ⟨h1, h2⟩ := (paperGap_eq_zero_iff E1 E2 V12).mp hz
      exact h.elim (fun hne => hne h1) (fun hne => hne h2)
    exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

end Qatlib.Papers.AndersonLoc09.MainResults
