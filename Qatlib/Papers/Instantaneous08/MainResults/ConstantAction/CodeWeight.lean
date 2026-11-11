/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ConstantAction.Bias

/-!
# Code weights and constant-action biases

This module expresses the bias of a constant-action X-program in terms of the rows selected by a
direction `s`. The signed action sum `actSum`, the selected-row count `nSub`, and the induced
`codeWeight` give the cosine and cosine-squared formulas of Theorem 1 in [ShepherdBremner2009].

## Main statements

* `actSum_shift`: computes the change of the signed action under translation.
* `bias_eq_codeWeight`: expresses the bias as a uniform average of squared cosines.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.XProgram

attribute [local instance] Classical.propDecidable

/-- The real sign associated with a Boolean value, equal to `1` for true and `-1` for false. -/
def rSign (b : Bool) : ℝ := if b then 1 else -1

/-- An element of `ZMod 2` is nonzero if and only if it equals `1`. -/
theorem zmod2_ne_zero_iff_eq_one (z : ZMod 2) : z ≠ 0 ↔ z = 1 := by
  constructor
  · intro h
    rcases ClassicalApprox.zmod2_eq_zero_or_one z with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h h0; rw [h] at h0; exact absurd h0 (by norm_num)

/-- The complex sign `signBit b` is the complex coercion of the real sign `rSign b`. -/
theorem signBit_eq_rSign (b : Bool) : signBit b = (rSign b : ℂ) := by
  cases b <;> simp [signBit, rSign]

/-- The sum of the real signs of the row dot products with `a`, with sign `1` for zero dot
product. -/
def actSum {n k : ℕ} (p : Fin k → F2Vec n) (a : F2Vec n) : ℝ :=
  ∑ i, rSign (dot (p i) a = 0)

/-- Expresses the constant-action phase as the exponential of `I * θ * actSum p a`. -/
theorem expAction_eq_exp_actSum {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ)
    (a : F2Vec n) :
    expAction p θ a = Complex.exp (Complex.I * (θ : ℂ) * (actSum p a : ℂ)) := by
  unfold expAction actSum
  rw [Complex.ofReal_sum]
  rw [show (∑ i : Fin k, signBit (dot (p i) a = 0)) =
      ∑ i : Fin k, ((rSign (dot (p i) a = 0) : ℂ)) from
    Finset.sum_congr rfl (fun i _ => signBit_eq_rSign _)]

/-- The indices of rows of `p` whose dot product with `s` equals `1`. -/
def subRowSet {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) : Finset (Fin k) :=
  Finset.univ.filter (fun i => dot (p i) s = 1)

/-- The number of rows selected by `subRowSet p s`. -/
def nSub {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) : ℕ :=
  (subRowSet p s).card

/-- The number of selected rows whose dot product with `a` equals `1`. -/
def codeWeight {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) (a : F2Vec n) : ℕ :=
  ((subRowSet p s).filter (fun i => dot (p i) a = 1)).card

/-- Translating `a` by `s` reverses the row sign exactly when the row has dot product `1` with
`s`. -/
theorem rSign_shift {n : ℕ} (q a s : F2Vec n) :
    rSign (dot q (a + s) = 0) =
      rSign (dot q a = 0) -
        2 * (if dot q s = 1 then rSign (dot q a = 0) else 0) := by
  have hsplit : dot q (a + s) = dot q a + dot q s := by
    change q ⬝ᵥ (a + s) = q ⬝ᵥ a + q ⬝ᵥ s
    rw [dotProduct_add]
  have hcases : ∀ x y : ZMod 2, rSign (x + y = 0) =
      rSign (x = 0) - 2 * (if y = 1 then rSign (x = 0) else 0) := by
    intro x y
    rcases ClassicalApprox.zmod2_eq_zero_or_one x with rfl | rfl <;>
      rcases ClassicalApprox.zmod2_eq_zero_or_one y with rfl | rfl
    · norm_num [rSign]
    · norm_num [rSign]
    · norm_num [rSign]
    · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11]
      norm_num [rSign]
  rw [hsplit]
  exact hcases _ _

/-- The sum of signs over the selected rows equals their number minus twice `codeWeight p s a`. -/
theorem sum_sign_subRow {n k : ℕ} (p : Fin k → F2Vec n) (s a : F2Vec n) :
    (∑ i ∈ subRowSet p s, rSign (dot (p i) a = 0)) =
      (nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ) := by
  have hsign : ∀ i ∈ subRowSet p s, rSign (dot (p i) a = 0) =
      (1 : ℝ) - 2 * (if dot (p i) a = 1 then 1 else 0) := by
    intro i _
    rcases ClassicalApprox.zmod2_eq_zero_or_one (dot (p i) a) with h0 | h0
    · norm_num [rSign, h0]
    · norm_num [rSign, h0]
  rw [Finset.sum_congr rfl hsign]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_boole, Finset.sum_const]
  rw [codeWeight, nSub]
  simp only [nsmul_eq_mul, mul_one]

/-- Expresses the change in `actSum` under translation by `s` through the selected-row count and
code weight. -/
theorem actSum_shift {n k : ℕ} (p : Fin k → F2Vec n) (s a : F2Vec n) :
    actSum p (a + s) = actSum p a -
      2 * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) := by
  have hterm : ∀ i : Fin k,
      rSign (dot (p i) (a + s) = 0) =
        rSign (dot (p i) a = 0) -
          2 * (if dot (p i) s = 1 then rSign (dot (p i) a = 0) else 0) :=
    fun i => rSign_shift _ _ _
  simp only [actSum, hterm]
  rw [Finset.sum_sub_distrib]
  have h2 : (∑ i : Fin k,
      2 * (if dot (p i) s = 1 then rSign (dot (p i) a = 0) else 0)) =
      2 * ∑ i : Fin k,
        (if dot (p i) s = 1 then rSign (dot (p i) a = 0) else 0) := by
    rw [Finset.mul_sum]
  rw [h2]
  have hfilter : (∑ i : Fin k,
        (if dot (p i) s = 1 then rSign (dot (p i) a = 0) else 0)) =
      ∑ i ∈ subRowSet p s, rSign (dot (p i) a = 0) := by
    rw [subRowSet, Finset.sum_filter]
  rw [hfilter, sum_sign_subRow]

/-- The real part of the conjugated phase product is the cosine of the difference of signed
actions multiplied by `θ`. -/
theorem kernel_re {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (a s : F2Vec n) :
    ((starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + s)).re =
      Real.cos (θ * (actSum p (a + s) - actSum p a)) := by
  have hexp : ∀ b : F2Vec n,
      expAction p θ b = Complex.exp (Complex.I * ((θ * actSum p b : ℝ) : ℂ)) := by
    intro b
    rw [expAction_eq_exp_actSum]
    congr 1
    push_cast
    ring
  rw [hexp a, hexp (a + s)]
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * ((θ * actSum p a : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((θ * actSum p a : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj, ← Complex.exp_add]
  have hsum : -(Complex.I * ((θ * actSum p a : ℝ) : ℂ)) +
        Complex.I * ((θ * actSum p (a + s) : ℝ) : ℂ) =
      Complex.I * ((θ * (actSum p (a + s) - actSum p a) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum]
  rw [show Complex.I * ((θ * (actSum p (a + s) - actSum p a) : ℝ) : ℂ) =
      ((θ * (actSum p (a + s) - actSum p a)) : ℝ) * Complex.I by
    rw [mul_comm]]
  rw [Complex.exp_ofReal_mul_I_re]

/-- Expresses the bias in direction `s` as one half times one plus a uniform cosine average, as
in [Shepherd and Bremner, Theorem 1][ShepherdBremner2009]. -/
theorem bias_eq_cos {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (s : F2Vec n) :
    (∑ x : F2Vec n, (if dot x s = 0 then prob p (fun _ => θ) x else 0)) =
      (1 / 2) * (1 + ((Fintype.card (F2Vec n) : ℝ))⁻¹ *
        ∑ a : F2Vec n,
          Real.cos (2 * θ *
            ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)))) := by
  have hcast : ((∑ x : F2Vec n,
        (if dot x s = 0 then prob p (fun _ => θ) x else 0) : ℝ) : ℂ) =
      (∑ x : F2Vec n,
        (if dot x s = 0 then (prob p (fun _ => θ) x : ℂ) else 0)) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : dot x s = 0 <;> simp [h]
  have h := bias_eq_fourier p θ s
  rw [← hcast] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have hR : ((1 / 2 : ℂ) * (1 + ((Fintype.card (F2Vec n) : ℂ))⁻¹ *
        ∑ a : F2Vec n,
          (starRingEnd ℂ) (expAction p θ a) * expAction p θ (a + s))).re =
      (1 / 2) * (1 + ((Fintype.card (F2Vec n) : ℝ))⁻¹ *
        ∑ a : F2Vec n,
          Real.cos (2 * θ *
            ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)))) := by
    have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have hNin : ((Fintype.card (F2Vec n) : ℂ))⁻¹.im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    have hNre : ((Fintype.card (F2Vec n) : ℂ))⁻¹.re =
        ((Fintype.card (F2Vec n) : ℝ))⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [h12, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.add_re, Complex.one_re, Complex.mul_re, hNre, hNin,
      zero_mul, sub_zero]
    rw [Complex.re_sum]
    have hsum : (∑ x : F2Vec n,
          ((starRingEnd ℂ) (expAction p θ x) * expAction p θ (x + s)).re) =
        ∑ x : F2Vec n, Real.cos (2 * θ *
          ((nSub p s : ℝ) - 2 * (codeWeight p s x : ℝ))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [kernel_re]
      have harg : θ * (actSum p (x + s) - actSum p x) =
          -(2 * θ * ((nSub p s : ℝ) - 2 * (codeWeight p s x : ℝ))) := by
        rw [actSum_shift]; ring
      rw [harg, Real.cos_neg]
    rw [hsum]
  exact hR

/-- Expresses the bias in direction `s` as the uniform average of `cos (θ * (nSub p s - 2 *
codeWeight p s a)) ^ 2`, as in [Shepherd and Bremner, Theorem 1][ShepherdBremner2009]. -/
theorem bias_eq_codeWeight {n k : ℕ} (p : Fin k → F2Vec n) (θ : ℝ) (s : F2Vec n) :
    (∑ x : F2Vec n, (if dot x s = 0 then prob p (fun _ => θ) x else 0)) =
      ((Fintype.card (F2Vec n) : ℝ))⁻¹ *
        ∑ a : F2Vec n,
          Real.cos (θ * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) ^ 2 := by
  rw [bias_eq_cos]
  have hcos : ∀ a : F2Vec n,
      Real.cos (2 * θ *
        ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) =
        2 * Real.cos (θ *
          ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) ^ 2 - 1 := by
    intro a
    rw [Real.cos_sq]
    have : 2 * (θ * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) =
        2 * θ * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ)) := by ring
    rw [this]
    ring
  simp only [hcos]
  have hS : (∑ a : F2Vec n,
        (2 * Real.cos (θ * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) ^ 2 - 1)) =
      2 * (∑ a : F2Vec n,
        Real.cos (θ * ((nSub p s : ℝ) - 2 * (codeWeight p s a : ℝ))) ^ 2) -
        (Fintype.card (F2Vec n) : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ]
    simp
  rw [hS]
  have hN : (Fintype.card (F2Vec n) : ℝ) ≠ 0 := by
    rw [ClassicalApprox.card_f2vec]; positivity
  field_simp
  ring

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
