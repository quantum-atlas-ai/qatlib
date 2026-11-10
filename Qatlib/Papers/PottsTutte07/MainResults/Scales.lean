/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

def algScale (numV : ℕ) (d : ℝ) (opNorms : List ℝ) : ℝ :=
  d ^ numV * opNorms.prod

def hardScale {E : Type*} [Fintype E] (numV : ℕ) (Eodd : Finset E) (q : ℂ) (v : E → ℂ) : ℂ :=
  q ^ (numV - Eodd.card) * Eodd.prod (fun e => v e)

def grpScale (numV : ℕ) (d : ℝ) (groupNorms : List ℝ) : ℝ :=
  d ^ numV * groupNorms.prod

theorem list_prod_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.prod_cons]
      exact mul_nonneg (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem algScale_nonneg (numV : ℕ) (d : ℝ) (hd : 0 ≤ d) (opNorms : List ℝ)
    (hn : ∀ x ∈ opNorms, 0 ≤ x) : 0 ≤ algScale numV d opNorms := by
  unfold algScale
  exact mul_nonneg (pow_nonneg hd numV) (list_prod_nonneg opNorms hn)

theorem norm_hardScale {E : Type*} [Fintype E] (numV : ℕ) (Eodd : Finset E) (q : ℂ)
    (v : E → ℂ) :
    ‖hardScale numV Eodd q v‖ = ‖q‖ ^ (numV - Eodd.card) * ∏ e ∈ Eodd, ‖v e‖ := by
  unfold hardScale
  rw [norm_mul, norm_pow, norm_prod]

theorem hardScale_eq_zero_iff {E : Type*} [Fintype E] (numV : ℕ) (Eodd : Finset E) (q : ℂ)
    (v : E → ℂ) (hq : q ≠ 0) :
    hardScale numV Eodd q v = 0 ↔ ∃ e ∈ Eodd, v e = 0 := by
  unfold hardScale
  rw [mul_eq_zero, Finset.prod_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (pow_ne_zero _ hq)
    · exact h
  · intro h
    exact Or.inr h

end Qatlib.Papers.PottsTutte07.MainResults
