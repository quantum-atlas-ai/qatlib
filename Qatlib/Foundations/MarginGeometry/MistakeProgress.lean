/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace Qatlib.Foundations.MarginGeometry.MistakeProgress
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_prefix (w a : ℕ → E) (M : ℕ) (hw0 : w 0=0)
    (hstep : ∀ n<M, w (n+1)=w n+a n)
    (hunit : ∀ n<M, ‖a n‖≤1) (hmis : ∀ n<M, ⟪w n,a n⟫_ℝ≤0) :
    ∀ n≤M, ‖w n‖^2≤(n:ℝ) := by
  intro n
  induction n with
  | zero => simp [hw0]
  | succ n ih =>
    intro hn
    have hnM : n<M := by omega
    have hi := ih (by omega)
    have ha := hunit n hnM
    have hs : ‖a n‖^2≤1 := by nlinarith [norm_nonneg (a n)]
    rw [hstep n hnM,norm_add_sq_real]
    push_cast
    nlinarith [hmis n hnM]

theorem margin_prefix (u : E) (w a : ℕ → E) (M : ℕ) (γ : ℝ) (hw0 : w 0=0)
    (hstep : ∀ n<M, w (n+1)=w n+a n)
    (hmargin : ∀ n<M, γ≤⟪u,a n⟫_ℝ) :
    ∀ n≤M, (n:ℝ)*γ≤⟪u,w n⟫_ℝ := by
  intro n
  induction n with
  | zero => simp [hw0]
  | succ n ih =>
    intro hn
    have hnM : n<M := by omega
    have hi := ih (by omega)
    rw [hstep n hnM,inner_add_right]
    push_cast
    linarith [hmargin n hnM]

theorem mistake_prefix_bound (u : E) (hu : ‖u‖=1) (w a : ℕ → E) (M : ℕ) (γ : ℝ)
    (hγ : 0<γ) (hw0 : w 0=0) (hstep : ∀ n<M, w (n+1)=w n+a n)
    (hunit : ∀ n<M, ‖a n‖≤1) (hmis : ∀ n<M, ⟪w n,a n⟫_ℝ≤0)
    (hmargin : ∀ n<M, γ≤⟪u,a n⟫_ℝ) : γ^2*(M:ℝ)≤1 := by
  by_cases hM : M=0
  · simp [hM]
  have hn := norm_sq_prefix w a M hw0 hstep hunit hmis M le_rfl
  have hm := margin_prefix u w a M γ hw0 hstep hmargin M le_rfl
  have hcs : ⟪u,w M⟫_ℝ≤‖w M‖ := by
    have hh := norm_inner_le_norm (𝕜:=ℝ) u (w M)
    rw [hu,one_mul,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh
  have hnonneg : 0≤(M:ℝ)*γ := mul_nonneg (Nat.cast_nonneg _) hγ.le
  have hs : ((M:ℝ)*γ)^2≤(M:ℝ) := by
    have hsq := pow_le_pow_left₀ hnonneg (hm.trans hcs) 2
    exact hsq.trans hn
  have hpos : 0<(M:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hp : (M:ℝ)*(γ^2*(M:ℝ))≤(M:ℝ)*1 := by nlinarith [hs]
  exact le_of_mul_le_mul_left hp hpos

end Qatlib.Foundations.MarginGeometry.MistakeProgress
