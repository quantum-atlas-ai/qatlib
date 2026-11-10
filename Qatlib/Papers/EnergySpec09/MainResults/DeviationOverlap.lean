/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.SuccessProbability
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inner_add_right (ψ φ₁ φ₂ : QState I) :
    Inner ψ (φ₁ + φ₂) = Inner ψ φ₁ + Inner ψ φ₂ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem inner_zero_right (ψ : QState I) : Inner ψ (0 : QState I) = 0 := by
  rw [inner_apply]
  simp

theorem overlap_deviation_decomp {ψ0 ψdev ψp : QState I} :
    Inner ψ0 (ψ0 + ψdev + ψp) = Inner ψ0 ψ0 + Inner ψ0 ψdev + Inner ψ0 ψp := by
  rw [inner_add_right, inner_add_right]

theorem overlap_eq_one_add_deviation {ψ0 ψdev ψp : QState I}
    (hnorm : Normalized ψ0) :
    Inner ψ0 (ψ0 + ψdev + ψp) = 1 + Inner ψ0 ψdev + Inner ψ0 ψp := by
  rw [overlap_deviation_decomp, (normalized_iff_inner_self ψ0).mp hnorm]

theorem success_prob_deviation_form {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) {ψdev ψp : QState I}
    (htrial : (∑ i, c i • φ i) = φ n + ψdev + ψp) (hnorm : Normalized (φ n)) :
    MeasureProb (qpeOutput M U (∑ i, c i • φ i))
        ({k n} ×ˢ (Finset.univ : Finset I))
      = ‖1 + Inner (φ n) ψdev + Inner (φ n) ψp‖ ^ 2 := by
  rw [qpe_success_prob_eq_overlap_sq hM U c φ k hOr heig hk n, htrial,
    overlap_eq_one_add_deviation hnorm]

theorem overlap_eq_one_of_no_deviation {ψ0 ψp : QState I}
    (hnorm : Normalized ψ0) (hp : Inner ψ0 ψp = 0) :
    Inner ψ0 (ψ0 + 0 + ψp) = 1 := by
  rw [overlap_eq_one_add_deviation hnorm, inner_zero_right, hp]
  ring

theorem exact_guess_success_prob_one {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) (hc : ∀ i, c i = if i = n then 1 else 0) :
    MeasureProb (qpeOutput M U (∑ i, c i • φ i))
        ({k n} ×ˢ (Finset.univ : Finset I)) = 1 := by
  unfold qpeOutput
  rw [tensorState_sum, qpe_success_prob_eq_coeff_sq hM U c φ k hOr heig hk n, hc n,
    if_pos rfl]
  norm_num

end Qatlib.Papers.EnergySpec09.MainResults
