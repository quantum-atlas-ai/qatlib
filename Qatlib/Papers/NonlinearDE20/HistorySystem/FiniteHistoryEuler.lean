/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.HistorySystem.FiniteClockInverse

/-!
# Euler recurrence encoded by a finite history system

This module identifies the initial and successor clock blocks of `historyMatrix`. The forced
recurrence `eulerSequence` assembles into `eulerHistory`, which solves the finite block system
and equals the explicit inverse applied to its forcing data, as in the history encoding of
[LloydEtAl2020].

## Main statements

* `historyMatrix_succ`: At a successor clock value, the history matrix returns the current slice
  minus `K` applied to the previous slice.
* `eulerHistory_system`: The Euler history solves the history matrix system with right-hand side
  given by the forcing sequence.
* `eulerHistory_eq_inverse`: The Euler history equals the explicit history inverse applied to
  the clock-indexed forcing data.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace Qatlib.Papers.NonlinearDE20.HistorySystem.History

/-- The lower propagation block contributes zero at the initial clock value. -/
theorem lowerBlock_zero {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (i : I) :
    (lowerBlock (T+1) K*ᵥ X) (0,i)=0 := by
  rw [Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro p _
  simp [lowerBlock,Matrix.kroneckerMap_apply,clockShift]

/-- At a successor clock value, the lower block applies `K` to the preceding system slice. -/
theorem lowerBlock_succ {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (k : Fin T) (i : I) :
    (lowerBlock (T+1) K*ᵥ X) (k.succ,i)=K i ⬝ᵥ (fun j=>X (k.castSucc,j)) := by
  rw [Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k.castSucc]
  · simp [lowerBlock,Matrix.kroneckerMap_apply,clockShift,dotProduct]
  · intro l _ hl
    have hn : k.val≠l.val := by
      intro he
      apply hl
      apply Fin.ext
      simpa only [Fin.val_castSucc] using he.symm
    simp [lowerBlock,Matrix.kroneckerMap_apply,clockShift,hn]
  · simp

/-- At the initial clock value, the history matrix returns the input vector slice unchanged. -/
theorem historyMatrix_zero {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (i : I) :
    (historyMatrix (T+1) K*ᵥ X) (0,i)=X (0,i) := by
  simp only [historyMatrix,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,lowerBlock_zero,sub_zero]

/-- At a successor clock value, the history matrix returns the current slice minus `K` applied
to the previous slice. -/
theorem historyMatrix_succ {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (k : Fin T) (i : I) :
    (historyMatrix (T+1) K*ᵥ X) (k.succ,i)=X (k.succ,i)-K i ⬝ᵥ (fun j=>X (k.castSucc,j)) := by
  simp only [historyMatrix,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,lowerBlock_succ]

/-- The forced linear recurrence starting at `g 0` and updating by `K` followed by addition of
the next forcing vector. -/
def eulerSequence {I : Type} [Fintype I] (K : Matrix I I ℂ) (g : ℕ→I→ℂ) : ℕ→I→ℂ
  | 0=>g 0
  | k+1=>K*ᵥ eulerSequence K g k+g (k+1)

/-- The finite clock-indexed vector containing the first `T + 1` values of `eulerSequence`. -/
def eulerHistory {I : Type} [Fintype I] (T : ℕ) (K : Matrix I I ℂ) (g : ℕ→I→ℂ) : Fin (T+1)×I→ℂ :=
  fun p=>eulerSequence K g p.1.val p.2

/-- The Euler history solves the history matrix system with right-hand side given by the forcing
sequence. -/
theorem eulerHistory_system {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ) (g : ℕ→I→ℂ) :
    historyMatrix (T+1) K*ᵥ eulerHistory T K g=(fun p=>g p.1.val p.2) := by
  funext p
  rcases p with ⟨k,i⟩
  refine Fin.cases ?_ (fun l=>?_) k
  · rw [historyMatrix_zero]
    rfl
  · rw [historyMatrix_succ]
    change (K*ᵥ eulerSequence K g l.val+g (l.val+1)) i-
      (K*ᵥ eulerSequence K g l.val) i=g (l.val+1) i
    simp

/-- The Euler history equals the explicit history inverse applied to the clock-indexed forcing
data [LloydEtAl2020]. -/
theorem eulerHistory_eq_inverse {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ) (g : ℕ→I→ℂ) :
    eulerHistory T K g=historyInverse (T+1) K*ᵥ (fun p=>g p.1.val p.2) :=
  (history_solution_iff (T+1) K _ _).mp (eulerHistory_system T K g)

end Qatlib.Papers.NonlinearDE20.HistorySystem.History
