/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.LatticeDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def spectralVector (U : Matrix ι ι ℂ) (a : ι) : QState ι := fun i => U i a

theorem inner_spectralVector_eq_mulVec (U : Matrix ι ι ℂ) (a : ι) (s : QState ι) :
    Inner (spectralVector U a) s = (Uᴴ *ᵥ s) a := rfl

theorem eq_sum_spectralVector (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (s : QState ι) :
    s = ∑ a, Inner (spectralVector U a) s • spectralVector U a := by
  have hUU : U * Uᴴ = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    simpa [Matrix.star_eq_conjTranspose] using h
  calc s = (1 : Matrix ι ι ℂ) *ᵥ s := by rw [Matrix.one_mulVec]
    _ = (U * Uᴴ) *ᵥ s := by rw [hUU]
    _ = U *ᵥ (Uᴴ *ᵥ s) := by rw [Matrix.mulVec_mulVec]
    _ = U *ᵥ (fun a => Inner (spectralVector U a) s) := by
        rw [show (Uᴴ *ᵥ s) = (fun a => Inner (spectralVector U a) s) from
          funext fun a => (inner_spectralVector_eq_mulVec U a s).symm]
    _ = ∑ a, Inner (spectralVector U a) s • spectralVector U a := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, spectralVector]
        apply Finset.sum_congr rfl
        intro a _
        ring

theorem inner_sum_state (w : QState ι) (f : ι → QState ι) :
    Inner w (∑ a, f a) = ∑ a, Inner w (f a) := by
  unfold Qatlib.Foundations.PureStateMath.Inner
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]

theorem amplitude_expansion
    (U : Matrix ι ι ℂ) (lam : ι → ℝ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (H : Matrix ι ι ℂ) (s w : QState ι) (t : ℝ)
    (hH : H = spectralHamiltonian U lam) :
    Inner w (HamiltonianEvolution H t *ᵥ s) =
      ∑ a, Inner (spectralVector U a) s * Inner w (spectralVector U a) *
        Complex.exp ((-Complex.I * (t : ℂ)) * (lam a : ℂ)) := by
  subst hH
  conv_lhs => rw [eq_sum_spectralVector U hU s]
  rw [Matrix.mulVec_sum, inner_sum_state]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mulVec_smul,
    hamiltonianEvolution_eigenvector (spectralHamiltonian U lam) (spectralVector U a)
      (lam a) t (spectralHamiltonian_eigen U lam a hU),
    inner_smul_state, inner_smul_state]
  ring

theorem amplitude_norm_le_sum
    (U : Matrix ι ι ℂ) (lam : ι → ℝ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (H : Matrix ι ι ℂ) (s w : QState ι) (t : ℝ)
    (hH : H = spectralHamiltonian U lam) :
    ‖Inner w (HamiltonianEvolution H t *ᵥ s)‖ ≤
      ∑ a, ‖Inner (spectralVector U a) s‖ * ‖Inner w (spectralVector U a)‖ := by
  rw [amplitude_expansion U lam hU H s w t hH]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  have hexp (a : ι) :
      ‖Complex.exp ((-Complex.I * (t : ℂ)) * (lam a : ℂ))‖ = 1 := by
    rw [show (-Complex.I * (t : ℂ)) * (lam a : ℂ) =
        Complex.I * ((-(t * lam a) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal]
  have hbank (a : ι) :
      ‖Inner (spectralVector U a) s * Inner w (spectralVector U a) *
        Complex.exp ((-Complex.I * (t : ℂ)) * (lam a : ℂ))‖ =
      ‖Inner (spectralVector U a) s‖ * ‖Inner w (spectralVector U a)‖ := by
    rw [norm_mul, norm_mul, hexp a, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hbank a)]

theorem norm_exp_neg_I_sub_exp_I (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * (θ : ℂ))) - Complex.exp (Complex.I * (θ : ℂ))‖ =
      2 * |Real.sin θ| := by
  have h1 : -(Complex.I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : Complex.I * (θ : ℂ) = ((θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hval : (Real.cos (-θ) + (Real.sin (-θ) : ℂ) * Complex.I) -
      (Real.cos θ + (Real.sin θ : ℂ) * Complex.I) =
      ((-(2 * Real.sin θ) : ℝ) : ℂ) * Complex.I := by
    rw [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hval, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have h2sin : |(-(2 * Real.sin θ) : ℝ)| = 2 * |Real.sin θ| := by
    rw [abs_neg, abs_mul]
    norm_num
  exact h2sin

theorem two_level_amplitude_value
    (N : ℕ) (hN : 0 < N) (E F' t : ℝ) (hE : 0 < E) (hF' : 0 < F') :
    ‖-(((Real.sqrt (N : ℝ) : ℂ))⁻¹) *
        ((-(((E * F' : ℝ) : ℂ)⁻¹)) * Complex.exp (Complex.I * ((t * E : ℝ) : ℂ)) +
          (((E * F' : ℝ) : ℂ)⁻¹) *
            Complex.exp (-(Complex.I * ((t * E : ℝ) : ℂ))))‖ =
      2 / (Real.sqrt (N : ℝ) * E * F') * |Real.sin (E * t)| := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hEF : 0 < E * F' := mul_pos hE hF'
  have hfactor :
      -(((Real.sqrt (N : ℝ) : ℂ))⁻¹) *
        ((-(((E * F' : ℝ) : ℂ)⁻¹)) * Complex.exp (Complex.I * ((t * E : ℝ) : ℂ)) +
          (((E * F' : ℝ) : ℂ)⁻¹) *
            Complex.exp (-(Complex.I * ((t * E : ℝ) : ℂ)))) =
      -(((Real.sqrt (N : ℝ) : ℂ))⁻¹) * (((E * F' : ℝ) : ℂ)⁻¹) *
        (Complex.exp (-(Complex.I * ((t * E : ℝ) : ℂ))) -
          Complex.exp (Complex.I * ((t * E : ℝ) : ℂ))) := by
    ring
  rw [hfactor, norm_mul, norm_mul, norm_neg]
  rw [show ‖(((Real.sqrt (N : ℝ) : ℂ))⁻¹)‖ = (Real.sqrt (N : ℝ))⁻¹ by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]]
  rw [show ‖(((E * F' : ℝ) : ℂ)⁻¹)‖ = (E * F')⁻¹ by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEF.le]]
  rw [norm_exp_neg_I_sub_exp_I]
  field_simp

end Qatlib.Papers.SpatialSearch03.MainResults
