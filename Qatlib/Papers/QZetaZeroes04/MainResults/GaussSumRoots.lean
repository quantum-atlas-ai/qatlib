/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs

/-!
# Gauss products and the zeta-root circle

This module establishes the complex norm identities needed for the Gauss-product expression
`gaussProductRoot` associated with diagonal hypersurfaces in [VanDam2004]. A nontrivial
multiplicative character paired with a primitive additive character has Gauss-sum norm equal to
the square root of the field cardinality, while character values at nonzero coefficients have
norm one.

The product of `n + 1` such Gauss sums, scaled by the signed inverse `n`th power of the field
cardinality and divided by the coefficient character values, is nonzero. For `n ≥ 1`, its norm
is the inverse of `rootRadius`, matching the radius of the reciprocal roots.

## Main statements

* `gaussSum_conj`: conjugation inverts both characters.
* `gaussSum_norm`: the square-root cardinality norm of a nontrivial Gauss sum.
* `gaussProductRoot_ne_zero`: nonvanishing of the scaled Gauss product.
* `gaussProductRoot_norm_eq_radius_inv`: the reciprocal-root circle formula.

## References

* [van Dam, 2004][VanDam2004]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.GaussSumRoots

open Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in

/-- Complex conjugation of a Gauss sum gives the Gauss sum formed from the inverse
multiplicative and additive characters. -/
theorem gaussSum_conj (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ :=
  star_gaussSum_eq χ ψ

omit [DecidableEq F] in

/-- For a nontrivial multiplicative character and a primitive additive character on a finite
field, the squared complex norm of their Gauss sum equals the field cardinality. -/
theorem gaussSum_norm_sq (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : AddChar.IsPrimitive ψ) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by

  have hmul : gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card F : ℂ) := by
    rw [gaussSum_conj, gaussSum_mul_gaussSum_eq_card hχ hψ]

  have hnorm :
      gaussSum χ ψ * star (gaussSum χ ψ) = (((‖gaussSum χ ψ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm] at hmul
  exact_mod_cast hmul

omit [DecidableEq F] in

/-- For a nontrivial multiplicative character and a primitive additive character, the Gauss-sum
norm is the square root of the field cardinality. -/
theorem gaussSum_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : AddChar.IsPrimitive ψ) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hsq := gaussSum_norm_sq χ hχ ψ hψ
  have hnn : 0 ≤ ‖gaussSum χ ψ‖ := norm_nonneg _
  rw [← hsq, Real.sqrt_sq hnn]

/-- A complex multiplicative character on a finite field has norm one at every nonzero field
element. -/
theorem mulChar_norm_apply (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    ‖χ a‖ = 1 := by
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr ha
  obtain ⟨u, rfl⟩ := hunit
  have hpow : (χ (u : F)) ^ (Fintype.card Fˣ) = 1 := by
    have h := MulChar.pow_card_eq_one χ
    have h' := congrArg (fun f : MulChar F ℂ => f (u : F)) h
    simpa [MulChar.pow_apply_coe, MulChar.one_apply_coe] using h'
  have hcard : 0 < Fintype.card Fˣ := Fintype.card_pos_iff.mpr ⟨1⟩
  exact Complex.norm_eq_one_of_pow_eq_one hpow (Nat.pos_iff_ne_zero.mp hcard)

/-- The signed product of `n + 1` Gauss sums divided by the corresponding coefficient character
values and by the `n`th power of the field cardinality. -/
def gaussProductRoot (n : ℕ) (χs : Fin (n + 1) → MulChar F ℂ) (ψ : AddChar F ℂ)
    (cs : Fin (n + 1) → F) : ℂ :=
  (-1 : ℂ) ^ (n - 1) / (Fintype.card F : ℂ) ^ n *
    ((∏ i, gaussSum (χs i) ψ) / (∏ i, χs i (cs i)))

omit [DecidableEq F] in

/-- The scaled Gauss-product expression is nonzero when all multiplicative characters are
nontrivial, the additive character is primitive, and all coefficients are nonzero. -/
theorem gaussProductRoot_ne_zero (n : ℕ) (χs : Fin (n + 1) → MulChar F ℂ)
    (hχs : ∀ i, χs i ≠ 1) (ψ : AddChar F ℂ) (hψ : AddChar.IsPrimitive ψ)
    (cs : Fin (n + 1) → F) (hcs : ∀ i, cs i ≠ 0) :
    gaussProductRoot n χs ψ cs ≠ 0 := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by
    have : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hg : ∀ i, gaussSum (χs i) ψ ≠ 0 := by
    intro i
    have h := gaussSum_norm (χs i) (hχs i) ψ hψ
    have hpos : (0 : ℝ) < Real.sqrt (Fintype.card F : ℝ) := by
      have hc : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
      have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hc
      exact Real.sqrt_pos.mpr hqR
    have hnorm : 0 < ‖gaussSum (χs i) ψ‖ := by rw [h]; exact hpos
    intro hzero
    rw [hzero, norm_zero] at hnorm
    exact lt_irrefl 0 hnorm
  have hc : ∀ i, χs i (cs i) ≠ 0 := by
    intro i
    exact IsUnit.ne_zero (IsUnit.map (χs i) (isUnit_iff_ne_zero.mpr (hcs i)))
  unfold gaussProductRoot
  refine mul_ne_zero (div_ne_zero ?_ (pow_ne_zero _ hq)) (div_ne_zero ?_ ?_)
  · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hg i)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)

/-- For `n ≥ 1`, nontrivial multiplicative characters, a primitive additive character, and
nonzero coefficients, the Gauss-product norm is the inverse square root of the field
cardinality raised to `n - 1`. This is the Gauss-product radius calculation associated with
Theorem 3 of [VanDam2004]. -/
theorem gaussProductRoot_norm (n : ℕ) (hn : 1 ≤ n)
    (χs : Fin (n + 1) → MulChar F ℂ) (hχs : ∀ i, χs i ≠ 1)
    (ψ : AddChar F ℂ) (hψ : AddChar.IsPrimitive ψ)
    (cs : Fin (n + 1) → F) (hcs : ∀ i, cs i ≠ 0) :
    ‖gaussProductRoot n χs ψ cs‖ =
      (Real.sqrt (Fintype.card F : ℝ))⁻¹ ^ (n - 1) := by
  have hqpos : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hqpos
  have hqsqrt : 0 < Real.sqrt (Fintype.card F : ℝ) := Real.sqrt_pos.mpr hqR

  have hg : ∀ i, ‖gaussSum (χs i) ψ‖ = Real.sqrt (Fintype.card F : ℝ) :=
    fun i => gaussSum_norm (χs i) (hχs i) ψ hψ

  have hc : ∀ i, ‖χs i (cs i)‖ = 1 := fun i => mulChar_norm_apply (χs i) (hcs i)
  have hnum : ‖(∏ i, gaussSum (χs i) ψ)‖ =
      (Real.sqrt (Fintype.card F : ℝ)) ^ (n + 1) := by
    rw [norm_prod]
    simp only [hg]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hden : ‖(∏ i, χs i (cs i))‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one (fun i _ => hc i)
  have hsign : ‖(-1 : ℂ) ^ (n - 1)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  unfold gaussProductRoot
  rw [norm_mul, norm_div, norm_div, hsign, hnum, hden, norm_pow,
    Complex.norm_natCast, div_one, one_div, inv_pow]

  have hqne : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hqsqrt
  have hsq : (Real.sqrt (Fintype.card F : ℝ)) ^ 2 = (Fintype.card F : ℝ) :=
    Real.sq_sqrt hqR.le
  have hkey : (Real.sqrt (Fintype.card F : ℝ)) ^ (n + 1) *
      (Real.sqrt (Fintype.card F : ℝ)) ^ (n - 1) = ((Fintype.card F : ℝ)) ^ n := by
    rw [← pow_add]
    have hexp : n + 1 + (n - 1) = 2 * n := by omega
    rw [hexp, pow_mul, hsq]
  rw [← hkey, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hqne), mul_one]

/-- Under the nontriviality, primitivity, nonzero-coefficient, and `n ≥ 1` hypotheses, the
Gauss-product norm equals the inverse of `rootRadius (Fintype.card F) n`. This expresses the
reciprocal-root circle used in the Theorem 3 setting of [VanDam2004]. -/
theorem gaussProductRoot_norm_eq_radius_inv (n : ℕ) (hn : 1 ≤ n)
    (χs : Fin (n + 1) → MulChar F ℂ) (hχs : ∀ i, χs i ≠ 1)
    (ψ : AddChar F ℂ) (hψ : AddChar.IsPrimitive ψ)
    (cs : Fin (n + 1) → F) (hcs : ∀ i, cs i ≠ 0) :
    ‖gaussProductRoot n χs ψ cs‖ = (rootRadius (Fintype.card F) n)⁻¹ := by
  rw [gaussProductRoot_norm n hn χs hχs ψ hψ cs hcs]
  unfold rootRadius
  have hsp : ∀ k : ℕ, (Real.sqrt (Fintype.card F : ℝ)) ^ k =
      Real.sqrt ((Fintype.card F : ℝ) ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (Real.sqrt (Fintype.card F : ℝ)) ^ (k + 1)
            = (Real.sqrt (Fintype.card F : ℝ)) ^ k *
                Real.sqrt (Fintype.card F : ℝ) := pow_succ _ _
          _ = Real.sqrt ((Fintype.card F : ℝ) ^ k) *
                Real.sqrt (Fintype.card F : ℝ) := by rw [ih]
          _ = Real.sqrt ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ)) := by
                rw [← Real.sqrt_mul (by positivity)]
          _ = Real.sqrt ((Fintype.card F : ℝ) ^ (k + 1)) := by rw [pow_succ]
  rw [← hsp (n - 1), inv_pow]

end Qatlib.Papers.QZetaZeroes04.MainResults.GaussSumRoots
