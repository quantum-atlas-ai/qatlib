/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.BornMetrics.EventProbability

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measureProb_mono (ψ : QState I) {S T : Finset I} (h : S ⊆ T) :
    MeasureProb ψ S ≤ MeasureProb ψ T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => bornProb_nonneg ψ i)

theorem measureProb_le_one {ψ : QState I} (hψ : Normalized ψ) (S : Finset I) :
    MeasureProb ψ S ≤ 1 := by
  calc
    MeasureProb ψ S ≤ MeasureProb ψ Finset.univ :=
      measureProb_mono ψ (Finset.subset_univ S)
    _ = 1 := measureProb_univ hψ

omit [Fintype I] in

theorem measureProb_union (ψ : QState I) {S T : Finset I} (h : Disjoint S T) :
    MeasureProb ψ (S ∪ T) = MeasureProb ψ S + MeasureProb ψ T :=
  Finset.sum_union h

omit [Fintype I] [DecidableEq I] in

theorem measureProb_smul (c : ℂ) (ψ : QState I) (S : Finset I) :
    MeasureProb (c • ψ) S = ‖c‖ ^ 2 * MeasureProb ψ S := by
  simp only [MeasureProb, BornProb, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    Finset.mul_sum]

omit [DecidableEq I] in

theorem bornProb_uniform (i : I) : BornProb (Uniform I) i = (Fintype.card I : ℝ)⁻¹ := by
  simp only [BornProb, Uniform, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    inv_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I))]

omit [DecidableEq I] in

theorem measureProb_uniform (S : Finset I) :
    MeasureProb (Uniform I) S = (S.card : ℝ) / Fintype.card I := by
  simp [MeasureProb, bornProb_uniform, div_eq_mul_inv]

end Qatlib.Foundations.BornMetrics.EventProbability

open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.BornMetrics.EventProbability

theorem measureProb_smul_ket {c : ℂ} (hc : ‖c‖ = 1) (x : I) (S : Finset I) :
    MeasureProb (c • Ket x) S = if x ∈ S then 1 else 0 := by
  by_cases hxS : x ∈ S
  · rw [if_pos hxS]
    have hpoint : ∀ y ∈ S, ‖c * Ket x y‖ ^ 2 = if y = x then 1 else 0 := by
      intro y _
      by_cases h : y = x
      · subst h
        simp [ket_self, mul_one, hc]
      · simp [Ket, h]
    unfold MeasureProb BornProb
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_ite_eq' S x (fun _ => (1 : ℝ))]
    simp [hxS]
  · rw [if_neg hxS]
    unfold MeasureProb BornProb
    simp only [Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro y _
    have hyx : y ≠ x := fun e => hxS (by rw [← e]; exact ‹y ∈ S›)
    simp [Ket, hyx]
end Qatlib.Foundations.BornMetrics.EventProbability
