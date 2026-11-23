/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterError19.MainResults.Appendices.AppendixB
import Mathlib.Tactic

@[expose] public section

/-!
# Monomial order bounds and explicit integrals

Closed forms for one and two adjacent integration variables in Lemma B.2 of
[ChildsEtAl2021Trotter]. The power bound uses the library's order condition,
so it can be combined with the addition and multiplication rules of
Proposition B.3.
-/

set_option autoImplicit false

open Qatlib.Papers.TrotterError19.MainResults (OrderCondition)

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

/-- A pure power times a fixed vector satisfies its own order condition:
`τ ↦ τ ^ p • X` is `O(τ ^ p)`, with constant `‖X‖ + 1`. -/
theorem pow_smul_orderCondition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : E) (p : ℕ) :
    OrderCondition (fun τ : ℝ => τ ^ p • X) p := by
  refine ⟨‖X‖ + 1, 1, by positivity, one_pos, fun τ _ => ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  calc |τ| ^ p * ‖X‖ ≤ |τ| ^ p * (‖X‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg X])
          (pow_nonneg (abs_nonneg τ) p)
    _ = (‖X‖ + 1) * |τ| ^ p := mul_comm _ _

/-- Integration of a monomial over `[0, t]` (Lemma B.2 with one variable):
`∫₀ᵗ s ^ p ds = t ^ (p + 1) / (p + 1)`. -/
theorem monomial_integral_eq (p : ℕ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, s ^ p) = t ^ (p + 1) / (p + 1 : ℝ) := by
  simp

/-- Iterated integration of a monomial (Lemma B.2 with two variables):
integrating `τ₂ ^ q` from `0` to `τ₁` and then `τ₁ ^ p` from `0` to `t`
gives exactly `t ^ (p + q + 2) / ((q + 1) * (p + q + 2))`, so the constant
in `O(t ^ (p + q + 2))` is `1 / ((q + 1) * (p + q + 2))`. -/
theorem iterated_monomial_integral_eq (p q : ℕ) (t : ℝ) :
    (∫ τ₁ in (0 : ℝ)..t, τ₁ ^ p * (∫ τ₂ in (0 : ℝ)..τ₁, τ₂ ^ q))
      = t ^ (p + q + 2) / (((q : ℝ) + 1) * ((p : ℝ) + q + 2)) := by
  have hinner : ∀ τ₁ : ℝ, (∫ τ₂ in (0 : ℝ)..τ₁, τ₂ ^ q)
      = τ₁ ^ (q + 1) / (q + 1 : ℝ) := fun τ₁ => monomial_integral_eq q τ₁
  rw [intervalIntegral.integral_congr (fun τ₁ _ => by rw [hinner τ₁])]
  have hform : (∫ τ₁ in (0 : ℝ)..t, τ₁ ^ p * (τ₁ ^ (q + 1) / (q + 1 : ℝ)))
      = (∫ τ₁ in (0 : ℝ)..t, τ₁ ^ (p + q + 1)) / (q + 1 : ℝ) := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun τ₁ _ => by
      rw [← mul_div_assoc, ← pow_add, show p + (q + 1) = p + q + 1 by omega]
  rw [hform, monomial_integral_eq (p + q + 1) t, div_div]
  have e1 : (p + q + 1) + 1 = p + q + 2 := by omega
  have e2 : ((p + q + 1 : ℕ) : ℝ) + 1 = (p : ℝ) + q + 2 := by push_cast; ring
  rw [e1, e2, mul_comm]

/-- The iterated monomial integral is `O(t ^ (p + q + 2))` with the exact
constant of `iterated_monomial_integral_eq` (Lemma B.2). -/
theorem iterated_monomial_orderCondition (p q : ℕ) :
    OrderCondition
      (fun t : ℝ => ∫ τ₁ in (0 : ℝ)..t, τ₁ ^ p * (∫ τ₂ in (0 : ℝ)..τ₁, τ₂ ^ q))
      (p + q + 2) := by
  have hden : (0 : ℝ) < ((q : ℝ) + 1) * ((p : ℝ) + q + 2) := by positivity
  refine ⟨1 / (((q : ℝ) + 1) * ((p : ℝ) + q + 2)), 1, by positivity, one_pos,
    fun t _ => ?_⟩
  dsimp only
  rw [iterated_monomial_integral_eq, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos hden, one_div]
  exact le_of_eq (by rw [div_eq_mul_inv]; ring)

end Qatlib.Papers.TrotterError19.MainResults.Appendices
