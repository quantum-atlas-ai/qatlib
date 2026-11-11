/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions

/-!
# Approximation scales for Tutte partition expressions

The definitions `algScale`, `hardScale`, and `grpScale` record the scalar normalizations used by
the approximation statements. The module proves nonnegativity of the real algorithmic scale, the
multiplicative norm formula for the complex hardness scale, and its zero criterion
[AharonovEtAl2007].

## Main statements

* `algScale_nonneg`: Nonnegative input factors give a nonnegative algorithmic scale.
* `norm_hardScale`: The norm factors into the power of the parameter norm and selected weight
  norms.
* `hardScale_eq_zero_iff`: For nonzero q, the scale vanishes exactly when a selected weight
  vanishes.

## References

* [Aharonov et al., 2007][AharonovEtAl2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

/-- The real scale `d ^ numV` times the product of the supplied operator norms. -/
def algScale (numV : ℕ) (d : ℝ) (opNorms : List ℝ) : ℝ :=
  d ^ numV * opNorms.prod

/-- The complex scale `q ^ (numV - card Eodd)` times the product of weights on `Eodd`. -/
def hardScale {E : Type*} [Fintype E] (numV : ℕ) (Eodd : Finset E) (q : ℂ) (v : E → ℂ) : ℂ :=
  q ^ (numV - Eodd.card) * Eodd.prod (fun e => v e)

/-- The real scale `d ^ numV` times the product of the supplied grouped norms. -/
def grpScale (numV : ℕ) (d : ℝ) (groupNorms : List ℝ) : ℝ :=
  d ^ numV * groupNorms.prod

/-- A finite list of nonnegative real numbers has nonnegative product. -/
theorem list_prod_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.prod_cons]
      exact mul_nonneg (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- The algorithmic scale is nonnegative when `d` and all supplied operator norms are
nonnegative. -/
theorem algScale_nonneg (numV : ℕ) (d : ℝ) (hd : 0 ≤ d) (opNorms : List ℝ)
    (hn : ∀ x ∈ opNorms, 0 ≤ x) : 0 ≤ algScale numV d opNorms := by
  unfold algScale
  exact mul_nonneg (pow_nonneg hd numV) (list_prod_nonneg opNorms hn)

/-- The norm of the hardness scale is `‖q‖ ^ (numV - card Eodd)` times the product of the
selected weight norms. -/
theorem norm_hardScale {E : Type*} [Fintype E] (numV : ℕ) (Eodd : Finset E) (q : ℂ)
    (v : E → ℂ) :
    ‖hardScale numV Eodd q v‖ = ‖q‖ ^ (numV - Eodd.card) * ∏ e ∈ Eodd, ‖v e‖ := by
  unfold hardScale
  rw [norm_mul, norm_pow, norm_prod]

/-- For nonzero `q`, the hardness scale is zero exactly when some weight on an odd edge is zero. -/
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
