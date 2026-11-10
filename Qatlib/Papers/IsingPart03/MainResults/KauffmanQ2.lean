/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPart03.MainResults.SpinGlass
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def isingSpin : Fin 2 → ℂ
  | 0 => 1
  | 1 => -1

lemma potts_two_state_separation (s t : Fin 2) :
    ((if s = t then (1 : ℂ) else 0)) = (isingSpin s * isingSpin t + 1) / 2 := by
  fin_cases s <;> fin_cases t <;> norm_num [isingSpin]

lemma potts_two_state_weight (K : ℂ) (s t : Fin 2) :
    Complex.exp (K * (if s = t then (1 : ℂ) else 0))
      = Complex.exp (K / 2) *
          Complex.exp ((K / 2) * (isingSpin s * isingSpin t)) := by
  rw [potts_two_state_separation]
  have h : K * ((isingSpin s * isingSpin t + 1) / 2)
      = K / 2 + (K / 2) * (isingSpin s * isingSpin t) := by ring
  rw [h, Complex.exp_add]

theorem kauffman_q2_eighth_power (A : ℂ) (hA : A ≠ 0)
    (hq : (A ^ 2 + (A ^ 2)⁻¹) ^ 2 = 2) : A ^ 8 = -1 := by
  have h : (A ^ 2) ^ 4 = -1 := by
    set v := A ^ 2 with hv
    set w := v + v⁻¹ with hw
    have hv0 : v ≠ 0 := pow_ne_zero 2 hA
    have hwv : w * v = v ^ 2 + 1 := by
      rw [hw, add_mul, inv_mul_cancel₀ hv0]
      ring
    have hsq : v ^ 2 = w * v - 1 := by
      rw [hwv]
      ring
    have hw2 : w ^ 2 = 2 := hq
    calc v ^ 4 = (w * v - 1) ^ 2 := by
          rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, hsq]
      _ = w ^ 2 * v ^ 2 - 2 * (w * v) + 1 := by ring
      _ = 2 * v ^ 2 - 2 * (w * v) + 1 := by rw [hw2]
      _ = 2 * (w * v - 1) - 2 * (w * v) + 1 := by rw [hsq]
      _ = -1 := by ring
  rw [show A ^ 8 = (A ^ 2) ^ 4 by ring]
  exact h

theorem kauffman_q2_fourth_power (A : ℂ) (hA : A ≠ 0)
    (hq : (A ^ 2 + (A ^ 2)⁻¹) ^ 2 = 2) :
    A ^ 4 = Complex.I ∨ A ^ 4 = -Complex.I := by
  have h8 : (A ^ 4) ^ 2 = -1 := by
    rw [show (A ^ 4) ^ 2 = A ^ 8 by ring]
    exact kauffman_q2_eighth_power A hA hq
  have hfac : (A ^ 4 - Complex.I) * (A ^ 4 + Complex.I) = 0 := by
    calc (A ^ 4 - Complex.I) * (A ^ 4 + Complex.I) = (A ^ 4) ^ 2 - Complex.I * Complex.I := by
          ring
      _ = (A ^ 4) ^ 2 + 1 := by rw [Complex.I_mul_I]; ring
      _ = 0 := by rw [h8]; ring
  rcases mul_eq_zero.mp hfac with h | h
  · left
    linear_combination h
  · right
    linear_combination h

theorem kauffman_q2_boltzmann_factor (A : ℂ) (b : ℤ) (hb : b = 1 ∨ b = -1)
    (h4 : A ^ 4 = Complex.I ∨ A ^ 4 = -Complex.I) :
    -(A ^ (-(4 * b))) = Complex.I ∨ -(A ^ (-(4 * b))) = -Complex.I := by
  have hpow : A ^ (-(4 * b)) = (A ^ 4) ^ (-b) := by
    rw [show (-(4 * b) : ℤ) = 4 * (-b) by ring, zpow_mul]
    rfl
  rcases hb with hb | hb <;> subst hb
  · rw [hpow, show (-(1 : ℤ)) = -1 by rfl, zpow_neg_one]
    rcases h4 with h | h <;> rw [h]
    · left
      rw [Complex.inv_I]
      norm_num
    · right
      rw [inv_neg, Complex.inv_I]
      ring
  · rw [hpow, show (-(-1 : ℤ)) = 1 by rfl, zpow_one]
    rcases h4 with h | h <;> rw [h]
    · right
      norm_num
    · left
      norm_num

lemma kauffman_q2_lambda_of_factor (z : ℂ) (hz : z = Complex.I ∨ z = -Complex.I) :
    (z - 1) / (z + 1) = Complex.I ∨ (z - 1) / (z + 1) = -Complex.I := by
  have hI2 : Complex.I ^ 2 = -1 := by rw [sq, Complex.I_mul_I]
  have hI1 : Complex.I + 1 ≠ 0 := by
    intro hcon
    have := congrArg Complex.re hcon
    simp at this
  have hI1' : -Complex.I + 1 ≠ 0 := by
    intro hcon
    have := congrArg Complex.re hcon
    simp at this
  rcases hz with hz | hz <;> subst hz
  · left
    rw [div_eq_iff hI1]
    ring_nf
    rw [hI2]
    ring
  · right
    rw [div_eq_iff hI1']
    ring_nf
    rw [hI2]
    ring

theorem kauffman_q2_lambda_complex (A : ℂ) (b : ℤ) (hA : A ≠ 0)
    (hq : (A ^ 2 + (A ^ 2)⁻¹) ^ 2 = 2) (hb : b = 1 ∨ b = -1) :
    ((-(A ^ (-(4 * b))) - 1) / (-(A ^ (-(4 * b))) + 1) = Complex.I) ∨
      ((-(A ^ (-(4 * b))) - 1) / (-(A ^ (-(4 * b))) + 1) = -Complex.I) := by
  exact kauffman_q2_lambda_of_factor _
    (kauffman_q2_boltzmann_factor A b hb (kauffman_q2_fourth_power A hA hq))

theorem kauffman_q2_lambda_im (A : ℂ) (b : ℤ) (hA : A ≠ 0)
    (hq : (A ^ 2 + (A ^ 2)⁻¹) ^ 2 = 2) (hb : b = 1 ∨ b = -1) :
    ((-(A ^ (-(4 * b))) - 1) / (-(A ^ (-(4 * b))) + 1)).im = 1 ∨
      ((-(A ^ (-(4 * b))) - 1) / (-(A ^ (-(4 * b))) + 1)).im = -1 := by
  rcases kauffman_q2_lambda_complex A b hA hq hb with h | h
  · left; rw [h]; exact Complex.I_im
  · right; rw [h]; rw [Complex.neg_im, Complex.I_im]

omit [DecidableEq V] [DecidableEq E] in

theorem source_prop2_q2_factor_ne_zero (μ c E0 : ℂ) (hc : c ≠ 0) (hE0 : E0 ≠ 0)
    (hμ : μ ≠ 0) :
    c * E0 * ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E) ≠ 0 := by
  have h2 : ((2 : ℂ) ^ Fintype.card V) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hμE : μ ^ Fintype.card E ≠ 0 := pow_ne_zero _ hμ
  exact mul_ne_zero (mul_ne_zero hc hE0) (div_ne_zero h2 hμE)

theorem source_prop2_q2_qwgt_reduction (ends : E → V × V)
    (hLoop : ∀ e, (ends e).1 ≠ (ends e).2) (w : E → ZMod 2)
    (Θ μ c E0 Kvalue lam : ℂ)
    (hNechaev : Kvalue = c * (E0 * partition ends w Θ lam))
    (hΘ : Θ * μ ^ Fintype.card E = 1) (hμ : μ ≠ 0) :
    Kvalue = c * E0 * ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E) *
      qwgt (incidence ends) (dg w) lam 1 := by
  have hthm : μ ^ Fintype.card E / (2 : ℂ) ^ Fintype.card V * partition ends w Θ lam
      = qwgt (incidence ends) (dg w) lam 1 := source_theorem2_qwgt ends hLoop w Θ lam μ hΘ
  have hpart : partition ends w Θ lam
      = ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E) * qwgt (incidence ends) (dg w) lam 1 := by
    rw [← hthm]
    field_simp
  rw [hNechaev, hpart]
  ring

end Qatlib.Papers.IsingPart03.MainResults
