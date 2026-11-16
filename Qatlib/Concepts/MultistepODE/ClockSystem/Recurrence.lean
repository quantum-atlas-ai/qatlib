/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MultistepODE.ClockSystem.Basic

@[expose] public section


/-! # Exact finite clock system and its source recurrence

The matrix equation is equivalent to the initial condition, actual Euler
startup, given multistep recurrence, and constant tail. These are exact
algebraic statements and do not assume numerical stability or a solver.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix

namespace Qatlib.Concepts.MultistepODE.ClockSystem

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The explicit source recurrence, independently stated in terms of spatial vectors. -/
def Recurs {N : ℕ} (k : ℕ) (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) (initial forcing : I → ℂ)
    (x : Fin (N+1) → I → ℂ) : Prop :=
  x 0 = initial ∧
  (∀ t : Fin (N+1), 0 < t.val → t.val < k →
    x t = (1 + h • A) *ᵥ x (previous t) + h • forcing) ∧
  (∀ (t : Fin (N+1)) (ht : k ≤ t.val), t.val ≤ N/2 →
    ∑ ell, (alpha ell • x (termTime t ht ell) -
      (h * beta ell) • (A *ᵥ x (termTime t ht ell))) =
        (h * ∑ ell, beta ell) • forcing) ∧
  (∀ t : Fin (N+1), N/2 < t.val → x t = x (previous t))

/-- The actual clock equation is equivalent to all four independent source recurrences. -/
theorem systemIff {N k : ℕ} (hk : 0 < k) (hkL : k ≤ N/2)
    (alpha beta : Fin (k+1) → ℂ) (h : ℂ) (A : Matrix I I ℂ)
    (initial forcing : I → ℂ) (x : Fin (N+1) → I → ℂ) :
    clockMatrix k alpha beta h A *ᵥ flatVec x = flatVec (rhs k beta h initial forcing) ↔
      Recurs k alpha beta h A initial forcing x := by
  constructor
  · intro heq
    have row (t : Fin (N+1)) (i : I) := congrFun heq (t,i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext i
      simpa [startRow alpha beta h A x 0 hk, flatVec, rhs] using row 0 i
    · intro t hz ht
      funext i
      have hr := row t i
      rw [startRow alpha beta h A x t ht] at hr
      simpa [flatVec, rhs, hz.ne', ht, hz, sub_eq_iff_eq_add, add_comm] using hr
    · intro t ht hL
      funext i
      have hr := row t i
      rw [mainRow alpha beta h A x t ht hL] at hr
      have hz : t.val ≠ 0 := by omega
      simpa [flatVec, rhs, hz, show ¬t.val < k by omega, hL,
        Matrix.sub_mulVec, Matrix.smul_mulVec, Finset.sum_apply] using hr
    · intro t ht
      funext i
      have hr := row t i
      rw [tailRow alpha beta h A x t hkL ht] at hr
      have hz : t.val ≠ 0 := by omega
      simpa [flatVec, rhs, hz, show ¬t.val < k by omega,
        show ¬t.val ≤ N/2 by omega, sub_eq_zero] using hr
  · rintro ⟨hinit, hstart, hmain, htail⟩
    funext u
    rcases u with ⟨t,i⟩
    change (clockMatrix k alpha beta h A *ᵥ flatVec x) (t,i) =
      rhs k beta h initial forcing t i
    by_cases hz : t.val = 0
    · have ht0 : t = 0 := Fin.ext hz
      subst t
      rw [startRow alpha beta h A x 0 hk]
      simp [rhs, hinit]
    · by_cases ht : t.val < k
      · rw [startRow alpha beta h A x t ht]
        have hpos : 0 < t.val := by omega
        have hs := congrFun (hstart t hpos ht) i
        simpa [rhs, hz, ht, hpos, sub_eq_iff_eq_add, add_comm] using hs
      · by_cases hL : t.val ≤ N/2
        · rw [mainRow alpha beta h A x t (by omega) hL]
          simpa [rhs, hz, ht, hL, Matrix.sub_mulVec, Matrix.smul_mulVec,
            Finset.sum_apply] using congrFun (hmain t (by omega) hL) i
        · rw [tailRow alpha beta h A x t hkL (by omega)]
          simp [rhs, hz, ht, hL, htail t (by omega)]

omit [Fintype I] [DecidableEq I] in
/-- Every padding value equals the actual final-time value, by finite induction. -/
theorem constantTail {N : ℕ} (x : Fin (N+1) → I → ℂ)
    (htail : ∀ t : Fin (N+1), N/2 < t.val → x t = x (previous t))
    (t : Fin (N+1)) (ht : N/2 ≤ t.val) :
    x t = x ⟨N/2, by omega⟩ := by
  have step : ∀ j : ℕ, ∀ hj : j < N+1, N/2 ≤ j →
      x ⟨j,hj⟩ = x ⟨N/2, by omega⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hL
      by_cases heq : j = N/2
      · subst j
        rfl
      · have hgt : N/2 < j := by omega
        rw [htail ⟨j,hj⟩ hgt]
        exact ih (j-1) (by omega) (by omega) (by omega)
  exact step t.val t.isLt ht

/-- A solution of the actual matrix equation has a constant final-time padding region. -/
theorem solutionTail {N k : ℕ} (hk : 0 < k) (hkL : k ≤ N/2)
    (alpha beta : Fin (k+1) → ℂ) (h : ℂ) (A : Matrix I I ℂ)
    (initial forcing : I → ℂ) (x : Fin (N+1) → I → ℂ)
    (hsol : clockMatrix k alpha beta h A *ᵥ flatVec x =
      flatVec (rhs k beta h initial forcing))
    (t : Fin (N+1)) (ht : N/2 ≤ t.val) :
    x t = x ⟨N/2, by omega⟩ :=
  constantTail x ((systemIff hk hkL alpha beta h A initial forcing x).mp hsol).2.2.2 t ht

end Qatlib.Concepts.MultistepODE.ClockSystem
