/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.HistorySystem.FiniteClockInverse
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace Qatlib.Papers.NonlinearDE20.HistorySystem.History

theorem lowerBlock_zero {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (i : I) :
    (lowerBlock (T+1) K*ᵥ X) (0,i)=0 := by
  rw [Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro p _
  simp [lowerBlock,Matrix.kroneckerMap_apply,clockShift]

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

theorem historyMatrix_zero {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (i : I) :
    (historyMatrix (T+1) K*ᵥ X) (0,i)=X (0,i) := by
  simp only [historyMatrix,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,lowerBlock_zero,sub_zero]

theorem historyMatrix_succ {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ)
    (X : Fin (T+1)×I→ℂ) (k : Fin T) (i : I) :
    (historyMatrix (T+1) K*ᵥ X) (k.succ,i)=X (k.succ,i)-K i ⬝ᵥ (fun j=>X (k.castSucc,j)) := by
  simp only [historyMatrix,Matrix.sub_mulVec,Matrix.one_mulVec,Pi.sub_apply,lowerBlock_succ]

def eulerSequence {I : Type} [Fintype I] (K : Matrix I I ℂ) (g : ℕ→I→ℂ) : ℕ→I→ℂ
  | 0=>g 0
  | k+1=>K*ᵥ eulerSequence K g k+g (k+1)

def eulerHistory {I : Type} [Fintype I] (T : ℕ) (K : Matrix I I ℂ) (g : ℕ→I→ℂ) : Fin (T+1)×I→ℂ :=
  fun p=>eulerSequence K g p.1.val p.2

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

theorem eulerHistory_eq_inverse {I : Type} [Fintype I] [DecidableEq I] (T : ℕ) (K : Matrix I I ℂ) (g : ℕ→I→ℂ) :
    eulerHistory T K g=historyInverse (T+1) K*ᵥ (fun p=>g p.1.val p.2) :=
  (history_solution_iff (T+1) K _ _).mp (eulerHistory_system T K g)

end Qatlib.Papers.NonlinearDE20.HistorySystem.History
