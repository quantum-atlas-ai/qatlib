/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Finite clock matrices and an explicit history inverse

The shift `clockShift` and its Kronecker product `lowerBlock` encode propagation along a finite
clock. Nilpotence gives a finite geometric-series inverse `historyInverse` for `historyMatrix`,
yielding a direct solution formula for the block history systems used in [LloydEtAl2020].

## Main statements

* `clockShift_nilpotent`: The clock shift on `N` clock values has zero `N`th power.
* `historyInverse_left`: The finite geometric sum is a left inverse of the history matrix.
* `history_solution_iff`: A vector solves the history system exactly when it is the history
  inverse applied to the right-hand side.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace Qatlib.Papers.NonlinearDE20.HistorySystem.History

/-- The finite clock shift with entry one immediately below the diagonal and zero elsewhere. -/
def clockShift (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i.val=j.val+1 then 1 else 0

/-- The entry of the `r`th clock-shift power vanishes whenever its row index is less than its
column index plus `r`. -/
theorem clockShift_pow_zero (N r : ℕ) (i j : Fin N) (h : i.val<j.val+r) :
    ((clockShift N)^r) i j=0 := by
  induction r generalizing i j with
  | zero =>
    have hij : i≠j := by intro he;subst j;omega
    simp [hij]
  | succ r ih =>
    rw [pow_succ,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val=j.val+1
    · have hz := ih i k (by omega)
      simp [clockShift,hk,hz]
    · simp [clockShift,hk]

/-- The clock shift on `N` clock values has zero `N`th power. -/
theorem clockShift_nilpotent (N : ℕ) : (clockShift N)^N=0 := by
  ext i j
  exact clockShift_pow_zero N N i j (by omega)

/-- The Kronecker product of the finite clock shift with the system propagator `K`. -/
def lowerBlock {I : Type} (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  clockShift N ⊗ₖ K

/-- Powers of the lower propagation block are Kronecker products of the corresponding
clock-shift and propagator powers. -/
theorem lowerBlock_pow {I : Type} [Fintype I] [DecidableEq I] (N r : ℕ) (K : Matrix I I ℂ) :
    (lowerBlock N K)^r=((clockShift N)^r) ⊗ₖ (K^r) := by
  induction r with
  | zero => simp [lowerBlock]
  | succ r ih =>
    rw [pow_succ,ih,pow_succ,pow_succ,Matrix.mul_kronecker_mul]
    rfl

/-- The lower propagation block on `N` clock values has zero `N`th power. -/
theorem lowerBlock_nilpotent {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    (lowerBlock N K)^N=0 := by
  rw [lowerBlock_pow,clockShift_nilpotent,Matrix.zero_kronecker]

/-- The block history matrix given by the identity minus the lower propagation block. -/
def historyMatrix {I : Type} [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  1-lowerBlock N K

/-- The finite geometric sum of lower propagation block powers from zero through `N - 1`. -/
def historyInverse {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  ∑ r∈Finset.range N,(lowerBlock N K)^r

/-- The finite geometric sum is a left inverse of the history matrix [LloydEtAl2020]. -/
theorem historyInverse_left {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    historyInverse N K*historyMatrix N K=1 := by
  rw [historyInverse,historyMatrix,geom_sum_mul_neg,lowerBlock_nilpotent,sub_zero]

/-- The finite geometric sum is a right inverse of the history matrix [LloydEtAl2020]. -/
theorem historyInverse_right {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    historyMatrix N K*historyInverse N K=1 := by
  rw [historyInverse,historyMatrix,mul_neg_geom_sum,lowerBlock_nilpotent,sub_zero]

/-- A vector solves the history system exactly when it is the history inverse applied to the
right-hand side. -/
theorem history_solution_iff {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ)
    (X B : Fin N×I→ℂ) : historyMatrix N K*ᵥ X=B ↔ X=historyInverse N K*ᵥ B := by
  constructor
  · intro h
    have hh := congrArg (fun v=>historyInverse N K*ᵥ v) h
    try dsimp only at hh
    rw [Matrix.mulVec_mulVec,historyInverse_left,Matrix.one_mulVec] at hh
    exact hh
  · intro h
    rw [h,Matrix.mulVec_mulVec,historyInverse_right,Matrix.one_mulVec]

end Qatlib.Papers.NonlinearDE20.HistorySystem.History
