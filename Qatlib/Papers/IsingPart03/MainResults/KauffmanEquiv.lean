/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPart03.MainResults.KauffmanQ2
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.IsingPart03.MainResults

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in

theorem potts_q2_partition_separates (ends : E → V × V) (K : E → ℂ) :
    (∑ s : V → Fin 2,
        ∏ e : E, Complex.exp (K e * (if s (ends e).1 = s (ends e).2 then (1 : ℂ) else 0)))
      = Complex.exp (∑ e : E, K e / 2) *
          ∑ s : V → Fin 2,
            ∏ e : E,
              Complex.exp ((K e / 2) * (isingSpin (s (ends e).1) * isingSpin (s (ends e).2))) := by
  classical
  have hpoint : ∀ s : V → Fin 2,
      (∏ e : E, Complex.exp (K e * (if s (ends e).1 = s (ends e).2 then (1 : ℂ) else 0)))
        = Complex.exp (∑ e : E, K e / 2) *
            ∏ e : E,
              Complex.exp ((K e / 2) * (isingSpin (s (ends e).1) * isingSpin (s (ends e).2))) := by
    intro s
    rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl
      (fun e _ => potts_two_state_weight (K e) (s (ends e).1) (s (ends e).2))
  rw [Finset.sum_congr rfl (fun s _ => hpoint s), ← Finset.mul_sum]

theorem kauffman_lambda_inverse (z lam : ℂ) (hz : z ≠ -1)
    (hlam : lam = (z - 1) / (z + 1)) :
    (1 + lam) / (1 - lam) = z := by
  subst hlam
  have hz1 : z + 1 ≠ 0 := by
    intro h
    exact hz (by linear_combination h)
  have h2 : (1 : ℂ) - (z - 1) / (z + 1) ≠ 0 := by
    have hnum : (1 : ℂ) - (z - 1) / (z + 1) = 2 / (z + 1) := by
      field_simp
      ring
    rw [hnum]
    exact div_ne_zero (by norm_num) hz1
  field_simp [hz1, h2]
  ring

theorem kauffman_q2_inverse_factor_pos :
    (1 + Complex.I) / (1 - Complex.I) = Complex.I := by
  have h2 : (1 : ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [div_eq_iff h2]
  linear_combination Complex.I_mul_I

theorem kauffman_q2_inverse_factor_neg :
    (1 + (-Complex.I)) / (1 - (-Complex.I)) = -Complex.I := by
  have h2 : (1 : ℂ) - (-Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [div_eq_iff h2]
  linear_combination Complex.I_mul_I

theorem kauffman_q2_lambda_sq (lam : ℂ) (h : lam = Complex.I ∨ lam = -Complex.I) :
    lam ^ 2 = -1 := by
  rcases h with h | h
  · rw [h, sq, Complex.I_mul_I]
  · rw [h, sq]
    rw [show (-Complex.I) * (-Complex.I) = Complex.I * Complex.I by ring]
    rw [Complex.I_mul_I]

theorem kauffman_q2_lambda_not_real (lam : ℂ) (h : lam = Complex.I ∨ lam = -Complex.I) :
    lam.im ≠ 0 := by
  rcases h with h | h
  · rw [h, Complex.I_im]; norm_num
  · rw [h, Complex.neg_im, Complex.I_im]; norm_num

theorem kauffman_q2_lambda_sq_of_params (A : ℂ) (b : ℤ) (hA : A ≠ 0)
    (hq : (A ^ 2 + (A ^ 2)⁻¹) ^ 2 = 2) (hb : b = 1 ∨ b = -1) :
    (((-(A ^ (-(4 * b))) - 1) / (-(A ^ (-(4 * b))) + 1)) ^ 2 = -1) :=
  kauffman_q2_lambda_sq _ (kauffman_q2_lambda_complex A b hA hq hb)

theorem source_prop2_q2_equivalent (ends : E → V × V)
    (hLoop : ∀ e, (ends e).1 ≠ (ends e).2) (w : E → ZMod 2)
    (Θ μ c E0 Kvalue lam : ℂ)
    (hNechaev : Kvalue = c * (E0 * partition ends w Θ lam))
    (hΘ : Θ * μ ^ Fintype.card E = 1) (hμ : μ ≠ 0)
    (hfactor : c * E0 * ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E) ≠ 0) :
    Kvalue = c * E0 * ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E) *
        qwgt (incidence ends) (dg w) lam 1
      ∧ qwgt (incidence ends) (dg w) lam 1
        = (c * E0 * ((2 : ℂ) ^ Fintype.card V / μ ^ Fintype.card E))⁻¹ * Kvalue := by
  have hred := source_prop2_q2_qwgt_reduction ends hLoop w Θ μ c E0 Kvalue lam hNechaev hΘ hμ
  constructor
  · exact hred
  · rw [hred]
    exact (inv_mul_cancel_left₀ hfactor
      (qwgt (incidence ends) (dg w) lam 1)).symm

end Qatlib.Papers.IsingPart03.MainResults
