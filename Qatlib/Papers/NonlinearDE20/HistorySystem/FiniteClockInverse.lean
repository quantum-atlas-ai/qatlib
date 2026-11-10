/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace Qatlib.Papers.NonlinearDE20.HistorySystem.History

def clockShift (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i.val=j.val+1 then 1 else 0

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

theorem clockShift_nilpotent (N : ℕ) : (clockShift N)^N=0 := by
  ext i j
  exact clockShift_pow_zero N N i j (by omega)

def lowerBlock {I : Type} (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  clockShift N ⊗ₖ K

theorem lowerBlock_pow {I : Type} [Fintype I] [DecidableEq I] (N r : ℕ) (K : Matrix I I ℂ) :
    (lowerBlock N K)^r=((clockShift N)^r) ⊗ₖ (K^r) := by
  induction r with
  | zero => simp [lowerBlock]
  | succ r ih =>
    rw [pow_succ,ih,pow_succ,pow_succ,Matrix.mul_kronecker_mul]
    rfl

theorem lowerBlock_nilpotent {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    (lowerBlock N K)^N=0 := by
  rw [lowerBlock_pow,clockShift_nilpotent,Matrix.zero_kronecker]

def historyMatrix {I : Type} [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  1-lowerBlock N K

def historyInverse {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) : Matrix (Fin N×I) (Fin N×I) ℂ :=
  ∑ r∈Finset.range N,(lowerBlock N K)^r

theorem historyInverse_left {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    historyInverse N K*historyMatrix N K=1 := by
  rw [historyInverse,historyMatrix,geom_sum_mul_neg,lowerBlock_nilpotent,sub_zero]

theorem historyInverse_right {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (K : Matrix I I ℂ) :
    historyMatrix N K*historyInverse N K=1 := by
  rw [historyInverse,historyMatrix,mul_neg_geom_sum,lowerBlock_nilpotent,sub_zero]

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
