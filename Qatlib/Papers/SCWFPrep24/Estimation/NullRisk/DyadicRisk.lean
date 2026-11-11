/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.OriginalRisk

set_option backward.isDefEq.respectTransparency false

/-!
# Dyadic Risk

The original dyadic mesh has at least four sites and is actually even as soon as r is at least two.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

open Qatlib.Foundations.FiniteStats.BornEstimator
local instance (d N : ℕ) : DecidableEq (Fin d → Fin N) := Classical.decEq _

/-- The original dyadic mesh has at least four sites and is actually even as soon as r is at least two. -/
theorem original_dyadic_mesh_parameters (r : ℕ) (hr : 2 ≤ r) :
    4 ≤ 2^r ∧ 2 ∣ 2^r := by
  constructor
  · calc 4 = 2^2 := by decide
         _ ≤ 2^r := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr
  · exact dvd_pow_self 2 (by omega)

/-- On the original N≥4 periodic meshes and positive lambda, the complete physical loss-gap constant is strictly positive. -/
theorem original_periodic_gap_pos (N : ℕ) (hN : 4 ≤ N) (lam : ℝ) (hlam : 0 < lam) :
    0 < lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2 := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0 : ℝ) < N := by linarith
  have hh : (0 : ℝ) < 2*Real.pi/N := div_pos (by positivity) hnp
  have hlt : (2*Real.pi/N : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hnp]
    nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hh hlt
  exact div_pos (mul_pos (sq_pos_of_pos hlam) (sq_pos_of_pos hs)) (sq_pos_of_pos hh)

/-- On the full original d=2 or 3 dyadic promise, bounded bias below the true physical gap forces an attained zero-full-loss variance floor for arbitrary finite-output two-copy PSD-separable measurements. -/
theorem original_dyadic_bounded_bias_null_variance {O K : Type*} [Fintype O] [Fintype K]
    (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 2 ≤ r)
    (P : POVM O (((Fin d → Fin (2^r)) × Fin 2) × ((Fin d → Fin (2^r)) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin (2^r)) × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (lam p0 beta : ℝ) (hp0 : (Real.sin (2*Real.pi/(2^r : ℕ)))^2/2 ≤ p0)
    (hbeta : 0 ≤ beta)
    (hsmall : beta < lam^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2)
    (y : O → ℝ)
    (hbias : ∀ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ →
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d (2^r) lam ψ| ≤ beta) :
    ∃ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ ∧ originalPeriodicLoss d (2^r) lam ψ = 0 ∧
      (lam^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2-beta)^2/24-beta^2 ≤
        variance (literalFieldOutcome P ψ) y := by
  obtain ⟨h4,heven⟩ := original_dyadic_mesh_parameters r hr
  let : Fact (1 < 2^r) := ⟨by omega⟩
  let j : Fin d := ⟨0,by rcases hd with h|h <;> omega⟩
  obtain ⟨z,hp,hz,hv⟩ := original_periodic_bounded_bias_null_variance d (2^r) heven j
    P E F hE hF hsep lam p0 beta hp0 hbeta hsmall y hbias
  exact ⟨periodicNullInput d (2^r) heven z,hp,hz,hv⟩

/-- The original dyadic physical promise also has the attained zero-full-loss mean-square-error floor, with every hidden-input, full-address Born and public-promise obligation discharged. -/
theorem original_dyadic_bounded_bias_null_mse {O K : Type*} [Fintype O] [Fintype K]
    (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 2 ≤ r)
    (P : POVM O (((Fin d → Fin (2^r)) × Fin 2) × ((Fin d → Fin (2^r)) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin (2^r)) × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (lam p0 beta : ℝ) (hp0 : (Real.sin (2*Real.pi/(2^r : ℕ)))^2/2 ≤ p0)
    (hsmall : beta < lam^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2)
    (y : O → ℝ)
    (hbias : ∀ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ →
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d (2^r) lam ψ| ≤ beta) :
    ∃ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ ∧ originalPeriodicLoss d (2^r) lam ψ = 0 ∧
      (lam^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2-beta)^2/24 ≤
        second (literalFieldOutcome P ψ) y := by
  obtain ⟨h4,heven⟩ := original_dyadic_mesh_parameters r hr
  let : Fact (1 < 2^r) := ⟨by omega⟩
  let j : Fin d := ⟨0,by rcases hd with h|h <;> omega⟩
  obtain ⟨z,hp,hz,hv⟩ := original_periodic_bounded_bias_null_mse d (2^r) heven j
    P E F hE hF hsep lam p0 beta hp0 hsmall y hbias
  exact ⟨periodicNullInput d (2^r) heven z,hp,hz,hv⟩

/-- Exact unbiasedness on all original promised inputs forces the original S²/24 variance lower bound at an actually legal zero-full-loss input, for every positive lambda and every original dyadic mesh. -/
theorem original_dyadic_unbiased_null_variance {O K : Type*} [Fintype O] [Fintype K]
    (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 2 ≤ r)
    (P : POVM O (((Fin d → Fin (2^r)) × Fin 2) × ((Fin d → Fin (2^r)) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin (2^r)) × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (lam p0 : ℝ) (hlam : 0 < lam)
    (hp0 : (Real.sin (2*Real.pi/(2^r : ℕ)))^2/2 ≤ p0)
    (y : O → ℝ)
    (hunbiased : ∀ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ →
      mean (literalFieldOutcome P ψ) y=originalPeriodicLoss d (2^r) lam ψ) :
    ∃ ψ : (Fin d → Fin (2^r)) → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ ∧ originalPeriodicLoss d (2^r) lam ψ = 0 ∧
      (lam^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2)^2/24 ≤
        variance (literalFieldOutcome P ψ) y := by
  have hS := original_periodic_gap_pos (2^r) (original_dyadic_mesh_parameters r hr).1 lam hlam
  have hb (ψ : (Fin d → Fin (2^r)) → Bool → ℂ)
      (hψ : OriginalPeriodicPromise d (2^r) p0 ψ) :
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d (2^r) lam ψ| ≤ 0 := by
    rw [hunbiased ψ hψ, sub_self, abs_zero]
  simpa only [sub_zero, zero_pow (by decide : 2 ≠ 0)] using
    original_dyadic_bounded_bias_null_variance d r hd hr P E F hE hF hsep
      lam p0 0 hp0 le_rfl hS y hb

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
