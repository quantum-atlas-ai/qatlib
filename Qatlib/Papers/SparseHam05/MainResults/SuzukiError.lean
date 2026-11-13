/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SparseHam05.MainResults.Defs

/-!
# Recursive Suzuki product-formula error

This module proves unitarity and norm identities for the paper-normalized Suzuki words and
bounds their scalar remainder terms. `source_lemma1_recursive_suzuki_error` derives the error
estimate of Lemma 1 in [BerryEtAl2007Sparse] for finite Hermitian matrix lists satisfying
`PaperLemma1Conditions` and the stated norm bounds.

## Main statements

* `paperSuzukiWord_unitary`: For a Hermitian Hamiltonian list and positive repetition count, the
  product of the paper Suzuki word is unitary.
* `source_lemma1_recursive_suzuki_error`: Under the stated Hermiticity, norm, positivity, and
  `PaperLemma1Conditions` hypotheses, the norm error between the Suzuki word product and the
  exact generator exponential is at most `paperSuzukiError hs.length k (‖hs.sum‖ * t) r`.

## References

* [Berry et al., 2007][BerryEtAl2007Sparse]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.SparseHam05.MainResults

/-- The pair of scalar step-size and remainder inequalities required for the paper's Suzuki
error bound. -/
def PaperLemma1Conditions (m k : ℕ) (τ : ℝ) (r : ℕ) : Prop :=
  4 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * τ / (r : ℝ) ≤ 1 ∧
    (16 / 3) * (2 * (5 : ℝ) ^ (k - 1) * (m : ℝ) * τ) ^ (2 * k + 1) /
        (r : ℝ) ^ (2 * k) ≤ 1

/-- For a Hermitian Hamiltonian list and positive repetition count, the product of the paper
Suzuki word is unitary. -/
theorem paperSuzukiWord_unitary {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hh : ∀ X ∈ hs, Xᴴ = X) (hr : 0 < r) :
    (paperSuzukiWord hs k t r).prod ∈ Matrix.unitaryGroup I ℂ := by
  have h := (recursive_suzuki_actual_simulation_and_cost I (paperAntiHermitian hs)
    (k - 1) r t (paperAntiHermitian_antiHermitian hs hh) hr).1
  simpa [paperSuzukiWord] using! h

/-- Multiplying all matrices by `-I` leaves `suzukiMass` unchanged. -/
theorem suzukiMass_paperAntiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) :
    suzukiMass (paperAntiHermitian hs) = suzukiMass hs := by
  unfold suzukiMass paperAntiHermitian
  simp only [List.map_map]
  have hfun : (norm ∘ (fun H : Matrix I I ℂ => (-Complex.I) • H)) = norm := by
    funext H
    simp only [Function.comp_apply]
    rw [norm_smul]
    simp
  rw [hfun]

/-- Summing a matrix list after multiplication by a common scalar equals that scalar times the
original sum. -/
theorem list_sum_map_smul {I : Type} [Fintype I] [DecidableEq I]
    (a : ℂ) (xs : List (Matrix I I ℂ)) :
    (xs.map (fun H => a • H)).sum = a • xs.sum := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, smul_add]

/-- The sum of the generator list equals `-I` times the sum of the Hamiltonian list. -/
theorem sum_paperAntiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) :
    (paperAntiHermitian hs).sum = (-Complex.I) • hs.sum :=
  list_sum_map_smul (-Complex.I) hs

/-- The sum of the generator list and the sum of the Hamiltonian list have the same norm. -/
theorem norm_sum_paperAntiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) :
    ‖(paperAntiHermitian hs).sum‖ = ‖hs.sum‖ := by
  rw [sum_paperAntiHermitian, norm_smul]
  simp [Complex.norm_I]

/-- The Suzuki mass of a matrix list is nonnegative. -/
theorem suzukiMass_nonneg {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : 0 ≤ suzukiMass xs := by
  unfold suzukiMass
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg Y)

/-- If every matrix in the list has norm at most `Λ`, its Suzuki mass is at most the list length
times `Λ`. -/
theorem suzukiMass_le_length_mul_norm {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (Λ : ℝ) (h : ∀ X ∈ hs, ‖X‖ ≤ Λ) :
    suzukiMass hs ≤ (hs.length : ℝ) * Λ := by
  induction hs with
  | nil => simp [suzukiMass]
  | cons X xs ih =>
    have hX : ‖X‖ ≤ Λ := h X (by simp)
    have hxs : ∀ Y ∈ xs, ‖Y‖ ≤ Λ := fun Y hY => h Y (by simp [hY])
    have hih : (List.map norm xs).sum ≤ (xs.length : ℝ) * Λ := ih hxs
    simp only [suzukiMass, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    nlinarith [hX, hih]

/-- For positive integer `k`, the real quantity `3^(k-1) + 1` is at most `2 * 5^(k-1)`. -/
theorem three_pow_add_one_le_two_five_pow (k : ℕ) (_hk : 1 ≤ k) :
    (3 : ℝ) ^ (k - 1) + 1 ≤ 2 * (5 : ℝ) ^ (k - 1) := by
  have h35 : (3 : ℝ) ^ (k - 1) ≤ (5 : ℝ) ^ (k - 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h1 : (1 : ℝ) ≤ (5 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
  linarith

/-- If `0 ≤ x ≤ 1/2`, then `exp x ≤ 2`. -/
theorem exp_le_two_of_le_half {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp x ≤ 2 := by
  have h1 : Real.exp x ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hx
  have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    rw [Real.exp_neg] at h
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    have hmul : (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) ≤ 1 := by
      have h' := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
      have hcoef : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
      rw [hcoef, inv_mul_cancel₀ (ne_of_gt hpos)] at h'
      exact h'
    nlinarith
  exact h1.trans h2

/-- For nonnegative `x` and `B` with `x ≤ B/r ≤ 1/2` and positive `r`, the stated exponential
Taylor remainder is at most `5 * B^(2*k+1) / r^(2*k)`. -/
theorem paper_remainder_bound (k r : ℕ) (_hk : 1 ≤ k) (hr : 0 < r)
    {x B : ℝ} (hx0 : 0 ≤ x) (hB0 : 0 ≤ B)
    (hx : x ≤ B / (r : ℝ)) (hBr : B / (r : ℝ) ≤ 1 / 2) :
    2 * (r : ℝ) * Real.exp x * x ^ (2 * k + 1) /
        (((2 * k + 1).factorial : ℕ) : ℝ) ≤
      5 * B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hxle : x ≤ 1 / 2 := hx.trans hBr
  have hexp : Real.exp x ≤ 2 := exp_le_two_of_le_half hx0 hxle
  have hfact : (1 : ℝ) ≤ (((2 * k + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfactpos : (0 : ℝ) < (((2 * k + 1).factorial : ℕ) : ℝ) := by positivity
  have hxpow : x ^ (2 * k + 1) ≤ (B / (r : ℝ)) ^ (2 * k + 1) :=
    pow_le_pow_left₀ hx0 hx _
  have hnum_nonneg : 0 ≤ 2 * (r : ℝ) * Real.exp x * x ^ (2 * k + 1) := by positivity
  have hA : 2 * (r : ℝ) * Real.exp x * x ^ (2 * k + 1) /
        (((2 * k + 1).factorial : ℕ) : ℝ)
      ≤ 2 * (r : ℝ) * Real.exp x * x ^ (2 * k + 1) := by
    rw [div_le_iff₀ hfactpos]
    nlinarith [hnum_nonneg, hfact]
  have hB : 2 * (r : ℝ) * Real.exp x * x ^ (2 * k + 1)
      ≤ 2 * (r : ℝ) * 2 * (B / (r : ℝ)) ^ (2 * k + 1) := by
    have hxpow0 : 0 ≤ x ^ (2 * k + 1) := pow_nonneg hx0 _
    have hexp0 : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
    have hprod : Real.exp x * x ^ (2 * k + 1)
        ≤ 2 * (B / (r : ℝ)) ^ (2 * k + 1) :=
      mul_le_mul hexp hxpow hxpow0 (by positivity)
    have hr2 : (0 : ℝ) ≤ 2 * (r : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hprod hr2
    nlinarith [this]
  have hC : 2 * (r : ℝ) * 2 * (B / (r : ℝ)) ^ (2 * k + 1)
      = 4 * B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k) := by
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
    have hden : (r : ℝ) ^ (2 * k + 1) = (r : ℝ) * (r : ℝ) ^ (2 * k) := by
      rw [pow_succ']
    rw [div_pow, hden]
    field_simp
    ring
  refine hA.trans (hB.trans ?_)
  rw [hC]
  have hpos : 0 ≤ B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k) := by positivity
  calc 4 * B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k)
      = 4 * (B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k)) := by ring
    _ ≤ 5 * (B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k)) := by linarith
    _ = 5 * B ^ (2 * k + 1) / (r : ℝ) ^ (2 * k) := by ring

/-- Under the stated Hermiticity, norm, positivity, and `PaperLemma1Conditions` hypotheses, the
norm error between the Suzuki word product and the exact generator exponential is at most
`paperSuzukiError hs.length k (‖hs.sum‖ * t) r`. See [BerryEtAl2007Sparse]. -/
theorem source_lemma1_recursive_suzuki_error {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k r : ℕ) (t : ℝ)
    (hh : ∀ X ∈ hs, Xᴴ = X) (hk : 1 ≤ k) (hr : 0 < r) (ht : 0 ≤ t)
    (hm : 0 < hs.length) (hbound : ∀ X ∈ hs, ‖X‖ ≤ ‖hs.sum‖)
    (hcond : PaperLemma1Conditions hs.length k (‖hs.sum‖ * t) r) :
    ‖(paperSuzukiWord hs k t r).prod -
        NormedSpace.exp (t • (paperAntiHermitian hs).sum)‖ ≤
      paperSuzukiError hs.length k (‖hs.sum‖ * t) r := by
  have he := (recursive_suzuki_actual_simulation_and_cost I (paperAntiHermitian hs)
    (k - 1) r t (paperAntiHermitian_antiHermitian hs hh) hr).2.2
  have hexp : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hkey : recursiveSuzukiError (paperAntiHermitian hs) (k - 1) t r ≤
      paperSuzukiError hs.length k (‖hs.sum‖ * t) r := by
    simp only [recursiveSuzukiError, paperSuzukiError]
    rw [hexp]
    have htabs : |t / (r : ℝ)| = t / (r : ℝ) :=
      abs_of_nonneg (div_nonneg ht (le_of_lt hrR))
    rw [htabs]
    have hmass_nonneg : 0 ≤ suzukiMass (paperAntiHermitian hs) :=
      suzukiMass_nonneg _
    have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (k - 1) := by positivity
    have hLam0 : (0 : ℝ) ≤ ‖hs.sum‖ := norm_nonneg _
    have hL0 : 0 ≤ (3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
        ‖(paperAntiHermitian hs).sum‖ :=
      add_nonneg (mul_nonneg hpow3 hmass_nonneg) (norm_nonneg _)
    have hmass_le : suzukiMass (paperAntiHermitian hs) ≤
        (hs.length : ℝ) * ‖hs.sum‖ := by
      rw [suzukiMass_paperAntiHermitian]
      exact suzukiMass_le_length_mul_norm hs ‖hs.sum‖ hbound
    have hsum_norm : ‖(paperAntiHermitian hs).sum‖ = ‖hs.sum‖ :=
      norm_sum_paperAntiHermitian hs
    have hm1 : (1 : ℝ) ≤ (hs.length : ℝ) := by exact_mod_cast hm
    have hL_le : (3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
        ‖(paperAntiHermitian hs).sum‖
        ≤ 2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * ‖hs.sum‖ := by
      rw [hsum_norm]
      have h35 := three_pow_add_one_le_two_five_pow k hk
      have hmLam : (0 : ℝ) ≤ (hs.length : ℝ) * ‖hs.sum‖ :=
        mul_nonneg (by positivity) hLam0
      have hstep1 : (3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs)
          ≤ (3 : ℝ) ^ (k - 1) * ((hs.length : ℝ) * ‖hs.sum‖) :=
        mul_le_mul_of_nonneg_left hmass_le hpow3
      have hstep2 : (1 : ℝ) * ‖hs.sum‖ ≤ (hs.length : ℝ) * ‖hs.sum‖ := by
        have := mul_le_mul_of_nonneg_right hm1 hLam0
        simpa using! this
      have hstep3 : ((3 : ℝ) ^ (k - 1) + 1) * ((hs.length : ℝ) * ‖hs.sum‖)
          ≤ (2 * (5 : ℝ) ^ (k - 1)) * ((hs.length : ℝ) * ‖hs.sum‖) :=
        mul_le_mul_of_nonneg_right h35 hmLam
      nlinarith [hstep1, hstep2, hstep3]
    have hB0 : (0 : ℝ) ≤ 2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t) :=
      by positivity
    have hx_le : ((3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
        ‖(paperAntiHermitian hs).sum‖) * (t / (r : ℝ))
        ≤ (2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t)) / (r : ℝ) := by
      have hLt : ((3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
          ‖(paperAntiHermitian hs).sum‖) * t
          ≤ (2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * ‖hs.sum‖) * t :=
        mul_le_mul_of_nonneg_right hL_le ht
      have hrew : (2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * ‖hs.sum‖) * t
          = 2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t) := by ring
      rw [hrew] at hLt
      calc ((3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
            ‖(paperAntiHermitian hs).sum‖) * (t / (r : ℝ))
          = (((3 : ℝ) ^ (k - 1) * suzukiMass (paperAntiHermitian hs) +
              ‖(paperAntiHermitian hs).sum‖) * t) / (r : ℝ) := by ring
        _ ≤ (2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t)) / (r : ℝ) :=
            (div_le_div_iff_of_pos_right hrR).mpr hLt
    have hBr : (2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t)) / (r : ℝ) ≤
        1 / 2 := by
      have hc := hcond.1
      have hrew2 : 2 * (5 : ℝ) ^ (k - 1) * (hs.length : ℝ) * (‖hs.sum‖ * t) / (r : ℝ)
          = (4 * (hs.length : ℝ) * (5 : ℝ) ^ (k - 1) * (‖hs.sum‖ * t) / (r : ℝ)) / 2 := by
        ring
      rw [hrew2]
      linarith
    exact paper_remainder_bound k r hk hr
      (mul_nonneg hL0 (div_nonneg ht (le_of_lt hrR))) hB0 hx_le hBr
  exact he.trans hkey

end Qatlib.Papers.SparseHam05.MainResults
