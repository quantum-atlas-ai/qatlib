/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Product marginals and conditional error accumulation

Computes the first-system reduced matrix of an identical normalized product state, obtaining its
single-factor outer product. Separately, scalar recurrence bounds propagate an assumed per-step
error estimate to step-count and total-time budgets. See [LloydEtAl2020].

## Main statements

* `product_marginal_eq_outerProduct`: a normalized product state has the expected one-system
  marginal.
* `conditional_step_budget`: assumed one-step errors accumulate linearly in the number of steps.
* `conditional_time_budget`: the bound can be expressed using TΔt = t.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Conditional

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coordinate amplitudes of the `n`-fold tensor power of `ψ`. -/
def tensorPower (ψ : I → ℂ) (n : ℕ) : (Fin n → I) → ℂ :=
  fun v => ∏ j : Fin n, ψ (v j)

/-- The product amplitude with one distinguished factor `ψ` and `n` further identical factors. -/
def productState (ψ : I → ℂ) (n : ℕ) : I × (Fin n → I) → ℂ :=
  fun p => ψ p.1 * tensorPower ψ n p.2

omit [Fintype I] [DecidableEq I] in

/-- The product-state amplitude at `(a, r)` is `ψ a` times the product of the amplitudes at the
remaining coordinates. -/
theorem productState_apply (ψ : I → ℂ) (n : ℕ) (a : I) (r : Fin n → I) :
    productState ψ n (a, r) = ψ a * ∏ j : Fin n, ψ (r j) := rfl

/-- The first-system reduced matrix entry obtained by summing the product of an amplitude and a
conjugate amplitude over all remaining indices. -/
def reducedFirst (n : ℕ) (Ψ : I × (Fin n → I) → ℂ) (a b : I) : ℂ :=
  ∑ r : Fin n → I, Ψ (a, r) * star (Ψ (b, r))

omit [DecidableEq I] in

/-- Summing the product of `g` over all length-`n` index tuples equals the `n`th power of the
sum of `g`. -/
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

/-- For a normalized factor `ψ`, the reduced first-system matrix of its identical product state
has entry `ψ a * star (ψ b)`. See [LloydEtAl2020]. -/
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

/-- If an error sequence starts at zero and increases by at most `γ` at each of the first `T`
steps, its value at `T` is at most `T * γ`. -/
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

/-- An error sequence starting at zero and satisfying the assumed increment bound `E2 * Δt ^ 2 *
m ^ 2 / n` has total error at most `E2 * T * Δt ^ 2 * m ^ 2 / n`. -/
theorem conditional_step_budget (T : ℕ) (E2 Δt m n : ℝ) (e : ℕ → ℝ)
    (h0 : e 0 = 0)
    (hstep : ∀ k < T, e (k + 1) ≤ e k + E2 * Δt ^ 2 * m ^ 2 / n) :
    e T ≤ E2 * (T : ℝ) * Δt ^ 2 * m ^ 2 / n := by
  have h := accumulated_error_le T h0 hstep
  calc e T ≤ (T : ℝ) * (E2 * Δt ^ 2 * m ^ 2 / n) := h
    _ = E2 * (T : ℝ) * Δt ^ 2 * m ^ 2 / n := by ring

/-- Under the assumed per-step increment bound and `T * Δt = t`, the total error is at most `E2
* t * Δt * m ^ 2 / n`. See [LloydEtAl2020]. -/
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
