/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Conditional

variable {I : Type*} [Fintype I] [DecidableEq I]

def tensorPower (ψ : I → ℂ) (n : ℕ) : (Fin n → I) → ℂ :=
  fun v => ∏ j : Fin n, ψ (v j)

def productState (ψ : I → ℂ) (n : ℕ) : I × (Fin n → I) → ℂ :=
  fun p => ψ p.1 * tensorPower ψ n p.2

omit [Fintype I] [DecidableEq I] in

theorem productState_apply (ψ : I → ℂ) (n : ℕ) (a : I) (r : Fin n → I) :
    productState ψ n (a, r) = ψ a * ∏ j : Fin n, ψ (r j) := rfl

def reducedFirst (n : ℕ) (Ψ : I × (Fin n → I) → ℂ) (a b : I) : ℂ :=
  ∑ r : Fin n → I, Ψ (a, r) * star (Ψ (b, r))

omit [DecidableEq I] in

theorem sum_prod_univ_pow (g : I → ℂ) (n : ℕ) :
    (∑ r : Fin n → I, ∏ j : Fin n, g (r j)) = (∑ i, g i) ^ n := by
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => I)
    (t := fun _ => (Finset.univ : Finset I)) (f := fun _ i => g i)
  rw [Fintype.piFinset_univ] at h
  have hL : (∏ _i : Fin n, ∑ j : I, g j) = (∑ j : I, g j) ^ n := by
    simp [Finset.prod_const, Fintype.card_fin]
  rw [hL] at h
  exact h.symm

omit [DecidableEq I] in

theorem product_marginal_eq_outerProduct (ψ : I → ℂ) (n : ℕ)
    (hψ : (∑ i, (Complex.normSq (ψ i) : ℂ)) = 1) (a b : I) :
    reducedFirst n (productState ψ n) a b = ψ a * star (ψ b) := by
  show (∑ r : Fin n → I, (ψ a * ∏ j : Fin n, ψ (r j)) *
      star ((ψ b * ∏ j : Fin n, ψ (r j)))) = ψ a * star (ψ b)
  have hterm : ∀ r : Fin n → I,
      (ψ a * ∏ j : Fin n, ψ (r j)) * star ((ψ b * ∏ j : Fin n, ψ (r j)))
        = ψ a * star (ψ b) * ∏ j : Fin n, (Complex.normSq (ψ (r j)) : ℂ) := by
    intro r
    set P : ℂ := ∏ j : Fin n, ψ (r j) with hPdef
    have hstar : star P = ∏ j : Fin n, star (ψ (r j)) := by
      rw [hPdef, star_prod]
    have hnorm : P * star P = ∏ j : Fin n, (Complex.normSq (ψ (r j)) : ℂ) := by
      rw [hPdef]
      rw [hstar, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => Complex.mul_conj _)
    rw [star_mul]
    calc (ψ a * P) * (star P * star (ψ b))
        = ψ a * star (ψ b) * (P * star P) := by ring
      _ = ψ a * star (ψ b) * ∏ j : Fin n, (Complex.normSq (ψ (r j)) : ℂ) := by rw [hnorm]
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [← Finset.mul_sum]
  have hsum : (∑ r : Fin n → I, ∏ j : Fin n, (Complex.normSq (ψ (r j)) : ℂ))
      = (∑ i, (Complex.normSq (ψ i) : ℂ)) ^ n :=
    sum_prod_univ_pow (g := fun i => (Complex.normSq (ψ i) : ℂ)) n
  rw [hsum, hψ, one_pow, mul_one]

theorem accumulated_error_le (T : ℕ) {e : ℕ → ℝ} {γ : ℝ}
    (h0 : e 0 = 0) (hstep : ∀ k < T, e (k + 1) ≤ e k + γ) :
    e T ≤ (T : ℝ) * γ := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
      have h1 : e (T + 1) ≤ e T + γ := hstep T (Nat.lt_succ_self T)
      have ih' : e T ≤ (T : ℝ) * γ :=
        ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self T)))
      calc e (T + 1) ≤ e T + γ := h1
        _ ≤ (T : ℝ) * γ + γ := by linarith
        _ = ((T : ℝ) + 1) * γ := by ring
        _ = ((T + 1 : ℕ) : ℝ) * γ := by push_cast; ring

theorem conditional_step_budget (T : ℕ) (E2 Δt m n : ℝ) (e : ℕ → ℝ)
    (h0 : e 0 = 0)
    (hstep : ∀ k < T, e (k + 1) ≤ e k + E2 * Δt ^ 2 * m ^ 2 / n) :
    e T ≤ E2 * (T : ℝ) * Δt ^ 2 * m ^ 2 / n := by
  have h := accumulated_error_le T h0 hstep
  calc e T ≤ (T : ℝ) * (E2 * Δt ^ 2 * m ^ 2 / n) := h
    _ = E2 * (T : ℝ) * Δt ^ 2 * m ^ 2 / n := by ring

theorem conditional_time_budget (T : ℕ) (E2 Δt t m n : ℝ) (e : ℕ → ℝ)
    (h0 : e 0 = 0)
    (hstep : ∀ k < T, e (k + 1) ≤ e k + E2 * Δt ^ 2 * m ^ 2 / n)
    (hT : (T : ℝ) * Δt = t) :
    e T ≤ E2 * t * Δt * m ^ 2 / n := by
  have h := conditional_step_budget T E2 Δt m n e h0 hstep
  calc e T ≤ E2 * (T : ℝ) * Δt ^ 2 * m ^ 2 / n := h
    _ = E2 * ((T : ℝ) * Δt) * Δt * m ^ 2 / n := by ring
    _ = E2 * t * Δt * m ^ 2 / n := by rw [hT]

end Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Conditional
