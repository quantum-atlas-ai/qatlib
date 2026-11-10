/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Matrix
open scoped Matrix

structure LinearSystemProblem (I : Type*) [Fintype I] [DecidableEq I] where

  A : Matrix I I ℂ

  herm : Aᴴ = A

  b : QState I

  hb : Normalized b

  eigval : I → ℝ

  eigvec : I → QState I

  eigvec_norm : ∀ i, Normalized (eigvec i)

  eigvec_eig : ∀ i, A *ᵥ (eigvec i) = ((eigval i : ℂ)) • (eigvec i)

  eigvec_orth : ∀ i i', i ≠ i' → Inner (eigvec i) (eigvec i') = 0

  b_decomp : ∃ β : I → ℂ, b = ∑ i, β i • (eigvec i)

  κ : ℝ

  hκ : ∀ i, 1 ≤ |eigval i| ∧ |eigval i| ≤ κ

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem inner_sum_smul_left (β : I → ℂ) (v : I → QState I) (φ : QState I) :
    Inner (∑ i, β i • v i) φ = ∑ i, (starRingEnd ℂ) (β i) * Inner (v i) φ := by
  simp only [inner_apply]
  have step : ∀ x : I, (starRingEnd ℂ) ((∑ i, β i • v i) x) * φ x
      = ∑ i, (starRingEnd ℂ) (β i) * ((starRingEnd ℂ) (v i x) * φ x) := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]

theorem inner_sum_smul_right (ψ : QState I) (β : I → ℂ) (v : I → QState I) :
    Inner ψ (∑ i, β i • v i) = ∑ i, β i * Inner ψ (v i) := by
  simp only [inner_apply]
  have step : ∀ x : I, (starRingEnd ℂ) (ψ x) * ((∑ i, β i • v i) x)
      = ∑ i, β i * ((starRingEnd ℂ) (ψ x) * v i x) := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]

namespace LinearSystemProblem

theorem eigval_ne_zero (p : LinearSystemProblem I) (i : I) : p.eigval i ≠ 0 :=
  abs_pos.mp (zero_lt_one.trans_le (p.hκ i).1)

theorem nonempty (p : LinearSystemProblem I) : Nonempty I := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    have h0 : (∑ i, ‖p.b i‖ ^ 2 : ℝ) = 0 := by
      rw [Finset.univ_eq_empty, Finset.sum_empty]
    have hb' : (∑ i, ‖p.b i‖ ^ 2 : ℝ) = 1 := p.hb
    rw [h0] at hb'
    exact absurd hb' zero_ne_one
  | inr h => exact h

theorem one_le_κ (p : LinearSystemProblem I) : 1 ≤ p.κ := by
  obtain ⟨i₀⟩ := p.nonempty
  exact (p.hκ i₀).1.trans (p.hκ i₀).2

theorem κ_pos (p : LinearSystemProblem I) : 0 < p.κ :=
  zero_lt_one.trans_le p.one_le_κ

theorem b_norm_sq (p : LinearSystemProblem I) {β : I → ℂ}
    (hβ : p.b = ∑ i, β i • p.eigvec i) : ∑ i, ‖β i‖ ^ 2 = 1 := by
  have hbb : Inner p.b p.b = 1 := (normalized_iff_inner_self p.b).mp p.hb
  have hcomp : (∑ i, (starRingEnd ℂ) (β i) * Inner (p.eigvec i) (∑ i', β i' • p.eigvec i'))
      = ∑ i, ((‖β i‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsum : (∑ i', β i' * Inner (p.eigvec i) (p.eigvec i')) = β i := by
      rw [Finset.sum_eq_single i
        (fun i' _ hii' => by rw [p.eigvec_orth i i' hii'.symm, mul_zero])
        (by simp)]
      rw [(normalized_iff_inner_self _).mp (p.eigvec_norm i), mul_one]
    rw [inner_sum_smul_right, hsum, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  rw [hβ, inner_sum_smul_left, hcomp] at hbb
  rw [← Complex.ofReal_sum, ← Complex.ofReal_one] at hbb
  exact Complex.ofReal_injective hbb

theorem inverse_action (p : LinearSystemProblem I) {β : I → ℂ}
    (hβ : p.b = ∑ i, β i • p.eigvec i) :
    p.A *ᵥ (∑ i, (β i / ((p.eigval i : ℂ))) • p.eigvec i) = p.b := by
  rw [Matrix.mulVec_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hβ.symm
  rw [Matrix.mulVec_smul, p.eigvec_eig i, smul_smul,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (p.eigval_ne_zero i))]

theorem accept_mass_lower_bound (p : LinearSystemProblem I) {β : I → ℂ}
    (hβ : p.b = ∑ i, β i • p.eigvec i) :
    1 / p.κ ^ 2 ≤ ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2 := by
  have hterm : ∀ i : I, ‖β i‖ ^ 2 / p.κ ^ 2 ≤ ‖β i / ((p.eigval i : ℂ))‖ ^ 2 := by
    intro i
    have hlam : 0 < |p.eigval i| := zero_lt_one.trans_le (p.hκ i).1
    have hle : |p.eigval i| ^ 2 ≤ p.κ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (p.hκ i).2 2
    have hnorm : ‖β i / ((p.eigval i : ℂ))‖ = ‖β i‖ / |p.eigval i| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, div_pow]
    have h1 : 1 / p.κ ^ 2 ≤ 1 / |p.eigval i| ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hlam) hle
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖β i‖)
    rwa [mul_one_div, mul_one_div] at h2
  have hsum : (∑ i, ‖β i‖ ^ 2 / p.κ ^ 2) = 1 / p.κ ^ 2 := by
    rw [← Finset.sum_div, p.b_norm_sq hβ]
  calc 1 / p.κ ^ 2 = ∑ i, ‖β i‖ ^ 2 / p.κ ^ 2 := hsum.symm
    _ ≤ ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i

theorem accept_mass_pos (p : LinearSystemProblem I) {β : I → ℂ}
    (hβ : p.b = ∑ i, β i • p.eigvec i) :
    0 < ∑ i, ‖β i / ((p.eigval i : ℂ))‖ ^ 2 :=
  lt_of_lt_of_le (one_div_pos.mpr (pow_pos p.κ_pos 2)) (p.accept_mass_lower_bound hβ)

end LinearSystemProblem

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
