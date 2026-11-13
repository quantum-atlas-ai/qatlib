/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedOpExp08.MainResults.Defs

/-!
# Perturbation bounds for matrix products

Controls the effect of perturbing each factor in a matrix product, assuming that the unperturbed
factors have norm at most one. These estimates support the product-noise analysis in
[WiebeEtAl2010].

## Main statements

* `lemma4_product_perturbation`: bounds the total error by `2 * δ` when each factor error is at
  most `δ / length`.

## References

* [Wiebe et al., 2010][WiebeEtAl2010]
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.OrderedOpExp08.MainResults

/-- For equal-length lists with contractive unperturbed factors and factor errors at most `e ≥
0`, bounds the product difference by `V.length * e * (1 + e) ^ V.length`. -/
theorem list_prod_diff_le {I : Type} [Fintype I] [DecidableEq I]
    (V W : List (Matrix I I ℂ)) (e : ℝ) (he : 0 ≤ e)
    (hlen : V.length = W.length)
    (hV : ∀ X ∈ V, ‖X‖ ≤ 1)
    (hnoise : ∀ j : ℕ, j < V.length → ‖V.getD j 0 - W.getD j 0‖ ≤ e) :
    ‖V.prod - W.prod‖ ≤ (V.length : ℝ) * e * (1 + e) ^ V.length := by
  induction V generalizing W with
  | nil =>
    have hW : W = [] := List.length_eq_zero_iff.mp hlen.symm
    subst W
    simp
  | cons X xs ih =>
    cases W with
    | nil => simp at hlen
    | cons Y ys =>
      have hlen' : xs.length = ys.length := by simpa using! hlen
      have hVxs : ∀ Z ∈ xs, ‖Z‖ ≤ 1 := fun Z hZ => hV Z (by simp [hZ])
      have hnoise' : ∀ j : ℕ, j < xs.length → ‖xs.getD j 0 - ys.getD j 0‖ ≤ e := by
        intro j hj
        simpa using! hnoise (j + 1) (by simpa using! hj)
      have hih := ih ys hlen' hVxs hnoise'
      have hh : ‖X - Y‖ ≤ e := by simpa using! hnoise 0 (by simp)
      have hxn : ‖xs.prod‖ ≤ 1 := list_prod_norm_le_one xs hVxs
      have hYeq : X - (X - Y) = Y := by abel
      have hYn : ‖Y‖ ≤ 1 + e := by
        calc
          ‖Y‖ = ‖X - (X - Y)‖ := by rw [hYeq]
          _ ≤ ‖X‖ + ‖X - Y‖ := norm_sub_le _ _
          _ ≤ 1 + e := add_le_add (hV X (by simp)) hh
      have hex : X * xs.prod - Y * ys.prod =
          (X - Y) * xs.prod + Y * (xs.prod - ys.prod) := by noncomm_ring
      have hbound : ‖(X - Y) * xs.prod + Y * (xs.prod - ys.prod)‖ ≤
          e + (1 + e) * ((xs.length : ℝ) * e * (1 + e) ^ xs.length) := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · have h1 : ‖(X - Y) * xs.prod‖ ≤ e * 1 :=
            (norm_mul_le _ _).trans (mul_le_mul hh hxn (norm_nonneg _) he)
          simpa using! h1
        · exact (norm_mul_le _ _).trans
            (mul_le_mul hYn hih (norm_nonneg _) (by linarith))
      have hstep : e + (1 + e) * ((xs.length : ℝ) * e * (1 + e) ^ xs.length) ≤
          ((xs.length : ℝ) + 1) * e * (1 + e) ^ (xs.length + 1) := by
        have hpow : (1 : ℝ) ≤ (1 + e) ^ (xs.length + 1) := one_le_pow₀ (by linarith)
        have hfac : 1 + (xs.length : ℝ) * (1 + e) ^ (xs.length + 1) ≤
            ((xs.length : ℝ) + 1) * (1 + e) ^ (xs.length + 1) := by linarith
        have hmul := mul_le_mul_of_nonneg_left hfac he
        calc
          e + (1 + e) * ((xs.length : ℝ) * e * (1 + e) ^ xs.length) =
              e * (1 + (xs.length : ℝ) * (1 + e) ^ (xs.length + 1)) := by
            rw [pow_succ]
            ring
          _ ≤ e * (((xs.length : ℝ) + 1) * (1 + e) ^ (xs.length + 1)) := hmul
          _ = ((xs.length : ℝ) + 1) * e * (1 + e) ^ (xs.length + 1) := by ring
      rw [List.prod_cons, List.prod_cons, hex]
      simpa using! hbound.trans hstep

/-- For nonempty equal-length lists, contractive unperturbed factors, and `0 ≤ δ < 1 / 2`,
factor errors at most `δ / A.length` give product error at most `2 * δ` [WiebeEtAl2010]. -/
theorem lemma4_product_perturbation {I : Type} [Fintype I] [DecidableEq I]
    (A B : List (Matrix I I ℂ)) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 2)
    (hne : 0 < A.length)
    (hlen : A.length = B.length)
    (hA : ∀ X ∈ A, ‖X‖ ≤ 1)
    (hnoise : ∀ p : ℕ, p < A.length → ‖A.getD p 0 - B.getD p 0‖ ≤ δ / (A.length : ℝ)) :
    ‖A.prod - B.prod‖ ≤ 2 * δ := by
  have hP : (0 : ℝ) < (A.length : ℝ) := by exact_mod_cast hne
  have he : 0 ≤ δ / (A.length : ℝ) := div_nonneg hδ0 (by positivity)
  have hmain := list_prod_diff_le A B (δ / (A.length : ℝ)) he hlen hA hnoise
  have hpre : (A.length : ℝ) * (δ / (A.length : ℝ)) = δ := by
    field_simp
  have hmain' : ‖A.prod - B.prod‖ ≤ δ * (1 + δ / (A.length : ℝ)) ^ A.length := by
    calc
      ‖A.prod - B.prod‖ ≤
          (A.length : ℝ) * (δ / (A.length : ℝ)) * (1 + δ / (A.length : ℝ)) ^ A.length := hmain
      _ = δ * (1 + δ / (A.length : ℝ)) ^ A.length := by rw [hpre]
  have hexp_half : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    nlinarith
  have hpow : (1 + δ / (A.length : ℝ)) ^ A.length ≤ 2 := by
    have hx : 0 ≤ 1 + δ / (A.length : ℝ) := by positivity
    have hle_exp : 1 + δ / (A.length : ℝ) ≤ Real.exp (δ / (A.length : ℝ)) := by
      simpa [add_comm] using! Real.add_one_le_exp (δ / (A.length : ℝ))
    have hpow_le : (1 + δ / (A.length : ℝ)) ^ A.length ≤
        (Real.exp (δ / (A.length : ℝ))) ^ A.length :=
      pow_le_pow_left₀ hx hle_exp _
    have hexp_eq : (Real.exp (δ / (A.length : ℝ))) ^ A.length =
        Real.exp ((A.length : ℝ) * (δ / (A.length : ℝ))) := by
      rw [Real.exp_nat_mul]
    have hstep : (A.length : ℝ) * (δ / (A.length : ℝ)) ≤ 1 / 2 := by
      have heq : (A.length : ℝ) * (δ / (A.length : ℝ)) = δ := hpre
      rw [heq]
      exact le_of_lt hδ
    have hexp_le : Real.exp ((A.length : ℝ) * (δ / (A.length : ℝ))) ≤
        Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hstep
    calc
      (1 + δ / (A.length : ℝ)) ^ A.length ≤
          (Real.exp (δ / (A.length : ℝ))) ^ A.length := hpow_le
      _ = Real.exp ((A.length : ℝ) * (δ / (A.length : ℝ))) := hexp_eq
      _ ≤ Real.exp (1 / 2 : ℝ) := hexp_le
      _ ≤ 2 := le_of_lt hexp_half
  have := mul_le_mul_of_nonneg_left hpow hδ0
  linarith

end Qatlib.Papers.OrderedOpExp08.MainResults
