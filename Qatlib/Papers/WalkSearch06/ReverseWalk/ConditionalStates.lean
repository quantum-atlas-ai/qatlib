/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.WalkSearch06.ReverseWalk.ConditionalStates

open Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def liftA (P : Matrix X X ℝ) (x : X) : X × X → ℂ :=
  fun p => if p.1 = x then (Real.sqrt (P x p.2) : ℂ) else 0

noncomputable def liftB (P : Matrix X X ℝ) (π : X → ℝ) (y : X) : X × X → ℂ :=
  fun p => if p.2 = y then (Real.sqrt (timeReversal P π y p.1) : ℂ) else 0

theorem gram_liftA_liftB (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) :
    (∑ p : X × X, liftA P x p * liftB P π y p)
      = (Real.sqrt (P x y * timeReversal P π y x) : ℂ) := by
  classical
  rw [Finset.sum_eq_single (x, y)]
  · simp only [liftA, liftB, ↓reduceIte]
    rw [← Complex.ofReal_mul, Real.sqrt_mul (hP x y)]
  · intro p _ hp
    rcases p with ⟨p1, p2⟩
    have hp' : ¬ (p1 = x ∧ p2 = y) := by simpa [Prod.mk.injEq] using hp
    by_cases h1 : p1 = x
    · have h2 : p2 ≠ y := by
        intro h2
        exact hp' ⟨h1, h2⟩
      simp [liftA, liftB, h1, h2]
    · simp [liftA, liftB, h1]
  · intro hmem
    exact absurd (Finset.mem_univ (x, y)) hmem

theorem gram_entry_eq_discriminant (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (x y : X) :
    (∑ p : X × X, liftA P x p * liftB P π y p)
      = (discriminant P π x y : ℂ) := by
  rw [gram_liftA_liftB P π hP x y]
  rfl

noncomputable def swapVec {X : Type*} (v : X × X → ℂ) : X × X → ℂ :=
  fun p => v (p.2, p.1)

theorem liftB_eq_swap_liftA_of_reversible (P : Matrix X X ℝ) (π : X → ℝ)
    (hπ : ∀ x, 0 < π x)
    (hdb : ∀ x y, π x * P x y = π y * P y x) (y : X) :
    liftB P π y = swapVec (liftA P y) := by
  have hPr : timeReversal P π = P := timeReversal_eq_of_detailedBalance P π hπ hdb
  funext p
  rcases p with ⟨p1, p2⟩
  simp only [liftB, liftA, swapVec, hPr]

noncomputable def exampleP : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 1 ∧ j = 2 then 1
    else if i = 2 ∧ j = 0 then 1 else 0

noncomputable def examplePi : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

theorem examplePi_stationary : ∀ y, ∑ x, examplePi x * exampleP x y = examplePi y := by
  intro y
  fin_cases y <;> simp [examplePi, exampleP]

theorem examplePi_pos : ∀ x, 0 < examplePi x := by
  intro x
  fin_cases x <;> norm_num [examplePi]

theorem example_not_reversible : timeReversal exampleP examplePi ≠ exampleP := by
  intro h
  have hentry := congrFun (congrFun h 0) 2
  simp [timeReversal, exampleP, examplePi] at hentry

end Qatlib.Papers.WalkSearch06.ReverseWalk.ConditionalStates
