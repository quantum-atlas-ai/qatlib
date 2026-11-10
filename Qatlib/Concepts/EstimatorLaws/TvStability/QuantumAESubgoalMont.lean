/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.QuantumAESubgoalStat
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout


namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib
open Matrix

private lemma inner_add_left {I : Type} [Fintype I] [DecidableEq I] (x y z : QState I) :
    Inner (x + y) z = Inner x z + Inner y z := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply, map_add, add_mul]

private lemma inner_add_right {I : Type} [Fintype I] [DecidableEq I] (x y z : QState I) :
    Inner x (y + z) = Inner x y + Inner x z := by
  rw [inner_apply, inner_apply, inner_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.add_apply, mul_add]

private lemma inner_smul_left {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (x y : QState I) :
    Inner (c • x) y = (starRingEnd ℂ) c * Inner x y := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

private lemma inner_smul_right {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (x y : QState I) :
    Inner x (c • y) = c * Inner x y := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

private lemma inner_conj_symm {I : Type} [Fintype I] [DecidableEq I] (x y : QState I) :
    Inner x y = (starRingEnd ℂ) (Inner y x) := by
  rw [inner_apply, inner_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [map_mul, starRingEnd_self_apply]
    ring

private lemma rot_eigen_scalar (c s a b : ℂ) :
    c * a - s * b + Complex.I * (s * a + c * b)
      = (c + Complex.I * s) * (a + Complex.I * b) := by
  linear_combination (-(s * b)) * Complex.I_mul_I

theorem quantumAESubgoal : QuantumAESubgoal := by
  intro M I _ _ W _hW hM ψ₀ ψ₁ hψ₀n hψ₁n hψ01 θ j hW0 hW1 hθj

  have hrot : ((Real.cos (2 * θ) : ℝ) : ℂ) + Complex.I * ((Real.sin (2 * θ) : ℝ) : ℂ)
      = Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    have h := Complex.cos_add_sin_I (((2 * θ : ℝ) : ℂ))
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    linear_combination h

  have hexp : Complex.exp ((2 * θ : ℝ) * Complex.I) = primRoot M ^ ((j.val : ℤ)) := by
    have hcast : ((2 * θ : ℝ) : ℂ) = ((2 * Real.pi * (j.val : ℝ) / M : ℝ) : ℂ) := by
      exact_mod_cast hθj
    have harg : ((2 * θ : ℝ) : ℂ) * Complex.I
        = (j.val : ℂ) * (2 * Real.pi * Complex.I / (M : ℝ)) := by
      rw [hcast]
      push_cast
      ring
    rw [harg, zpow_natCast]
    unfold primRoot
    exact Complex.exp_nat_mul _ _

  have hWsum : W *ᵥ (ψ₀ + Complex.I • ψ₁)
      = Complex.exp ((2 * θ : ℝ) * Complex.I) • (ψ₀ + Complex.I • ψ₁) := by
    rw [← hrot, Matrix.mulVec_add, Matrix.mulVec_smul, hW0, hW1]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact rot_eigen_scalar _ _ _ _

  have h00 : Inner ψ₀ ψ₀ = 1 := (normalized_iff_inner_self ψ₀).mp hψ₀n
  have h11 : Inner ψ₁ ψ₁ = 1 := (normalized_iff_inner_self ψ₁).mp hψ₁n
  have h10 : Inner ψ₁ ψ₀ = 0 := by rw [inner_conj_symm, hψ01, map_zero]
  have hinner : Inner (ψ₀ + Complex.I • ψ₁) (ψ₀ + Complex.I • ψ₁) = 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      h00, h11, hψ01, h10]
    simp only [mul_zero, add_zero, zero_add, mul_one]
    rw [Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg]
    exact one_add_one_eq_two
  have hψn : Normalized (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ψ₀ + Complex.I • ψ₁)) := by
    rw [normalized_iff_inner_self, inner_smul_left, inner_smul_right, hinner]
    have hconj : (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
        = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [hconj, ← mul_assoc, inv_sqrt2_mul_self]
    exact inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)

  have hψeig : W *ᵥ (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ψ₀ + Complex.I • ψ₁))
      = (primRoot M ^ ((j.val : ℤ))) •
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (ψ₀ + Complex.I • ψ₁)) := by
    rw [Matrix.mulVec_smul, hWsum, ← hexp, smul_smul, smul_smul, mul_comm]

  refine ⟨(Qatlib.Concepts.SpectralFilter.PhaseReadout.qpe_exact_readout hM hψn j hψeig).1, ?_⟩
  have h2 : θ = (2 * θ) / 2 := by ring
  have hθeq : Real.pi * (j.val : ℝ) / M = θ := by
    rw [h2, hθj]
    ring
  rw [hθeq]

end Qatlib.Concepts.EstimatorLaws.TvStability
