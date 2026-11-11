/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.DysonError.SeriesSteps

/-!
# Solving finite linear history recurrences

This module defines `historyOperator`, which records an initial value followed by the residuals
of a finite sequence of linear evolution steps. The forward recurrence `solveHistory` inverts
this operator on both sides, proving existence and uniqueness for every prescribed driving
sequence.

The mathematical background is discussed in [BerryCosta2024].

## Main statements

* `solveHistory_succ`: the forward recurrence defining the history solution.
* `history_solve_right` and `history_solve_left`: the two inverse identities.
* `history_unique`: uniqueness of the finite history solution.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.DysonError
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {n : ℕ}

/-- The history residual sequence consisting of `x 0` and the successive differences `x (i + 1)
- V i (x i)`. -/
def historyOperator (V : Fin n → E →L[𝕜] E) (x : Fin (n+1) → E) : Fin (n+1) → E :=
  Fin.cases (x 0) (fun i => x i.succ - V i (x i.castSucc))

/-- Extend a finite sequence of linear steps to natural indices by using the identity beyond its
last step. -/
def extendedStep (V : Fin n → E →L[𝕜] E) (k : ℕ) : E → E :=
  if h : k < n then V ⟨k,h⟩ else id

/-- Extend the successor entries of a finite driving sequence to natural indices by zero beyond
the last step. -/
def extendedDriving (rhs : Fin (n+1) → E) (k : ℕ) : E :=
  if h : k < n then rhs ⟨k+1,Nat.succ_lt_succ h⟩ else 0

/-- Solve the finite history recurrence by starting at `rhs 0` and applying each linear step
followed by its driving term. -/
def solveHistory (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) : Fin (n+1) → E :=
  fun i => affineTrajectory (extendedStep V) (extendedDriving rhs) (rhs 0) i.val

/-- The history solution starts at the initial driving value `rhs 0`. -/
theorem solveHistory_zero (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) :
    solveHistory V rhs 0=rhs 0 := rfl

/-- Each successive history value is its predecessor acted on by `V i`, plus the next driving
value. -/
theorem solveHistory_succ (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) (i : Fin n) :
    solveHistory V rhs i.succ=V i (solveHistory V rhs i.castSucc)+rhs i.succ := by
  simp only [solveHistory,Fin.val_succ,Fin.val_castSucc,affineTrajectory,extendedStep,extendedDriving,dif_pos i.isLt]
  congr 2

/-- Applying the history operator to its forward solution recovers the driving sequence. -/
theorem history_solve_right (V : Fin n → E →L[𝕜] E) (rhs : Fin (n+1) → E) :
    historyOperator V (solveHistory V rhs)=rhs := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [historyOperator,solveHistory_succ]

/-- Solving the residual sequence of a history recovers the original history. -/
theorem history_solve_left (V : Fin n → E →L[𝕜] E) (x : Fin (n+1) → E) :
    solveHistory V (historyOperator V x)=x := by
  funext i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [solveHistory_succ,ih]
    simp [historyOperator]

/-- Every history with residual sequence `rhs` equals `solveHistory V rhs`. -/
theorem history_unique (V : Fin n → E →L[𝕜] E) (rhs x : Fin (n+1) → E)
    (hx : historyOperator V x=rhs) : x=solveHistory V rhs := by
  rw [← hx,history_solve_left]

/-- The history operator preserves pointwise addition of histories. -/
theorem historyOperator_add (V : Fin n → E →L[𝕜] E) (x y : Fin (n+1) → E) :
    historyOperator V (x+y)=historyOperator V x+historyOperator V y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [historyOperator,Fin.cases_succ,Pi.add_apply,map_add]
    abel
end Qatlib.Foundations.TimeEvolution.DysonError
