/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.DysonError.SeriesSteps

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.DysonError
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {n : ℕ}

def historyOperator (V : Fin n → E →L[𝕜] E) (x : Fin (n+1) → E) : Fin (n+1) → E :=
  Fin.cases (x 0) (fun i => x i.succ - V i (x i.castSucc))

def extendedStep (V : Fin n → E →L[𝕜] E) (k : ℕ) : E → E :=
  if h : k < n then V ⟨k,h⟩ else id

def extendedDriving (rhs : Fin (n+1) → E) (k : ℕ) : E :=
  if h : k < n then rhs ⟨k+1,Nat.succ_lt_succ h⟩ else 0

def solveHistory (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) : Fin (n+1) → E :=
  fun i => affineTrajectory (extendedStep V) (extendedDriving rhs) (rhs 0) i.val

theorem solveHistory_zero (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) :
    solveHistory V rhs 0=rhs 0 := rfl

theorem solveHistory_succ (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) (i : Fin n) :
    solveHistory V rhs i.succ=V i (solveHistory V rhs i.castSucc)+rhs i.succ := by
  simp only [solveHistory,Fin.val_succ,Fin.val_castSucc,affineTrajectory,extendedStep,extendedDriving,dif_pos i.isLt]
  congr 2

theorem history_solve_right (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) :
    historyOperator V (solveHistory V rhs)=rhs := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [historyOperator,solveHistory_succ]

theorem history_solve_left (V : Fin n → E →L[𝕜] E) (x : Fin (n+1) → E) :
    solveHistory V (historyOperator V x)=x := by
  funext i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [solveHistory_succ,ih]
    simp [historyOperator]

theorem history_unique (V : Fin n → E →L[𝕜] E) (rhs x : Fin (n+1) → E)
    (hx : historyOperator V x=rhs) : x=solveHistory V rhs := by
  rw [← hx,history_solve_left]

theorem historyOperator_add (V : Fin n → E →L[𝕜] E) (x y : Fin (n+1) → E) :
    historyOperator V (x+y)=historyOperator V x+historyOperator V y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [historyOperator,Fin.cases_succ,Pi.add_apply,map_add]
    abel
end Qatlib.Foundations.TimeEvolution.DysonError
