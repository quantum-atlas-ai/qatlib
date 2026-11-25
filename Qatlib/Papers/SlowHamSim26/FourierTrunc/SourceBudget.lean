/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SlowHamSim26.FourierTrunc.SourceGammaSum

@[expose] public section

/-!
# Source rate and truncation budget for the Floquet space

In arXiv:2608.17653v1, Eq. (4.45) applies `h₂` only to the Fourier tail.
Equation (4.67) uses the product of three powers, or equivalently a
single power of `4ζ` times the logarithmic budget when that budget is
nonnegative.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.SlowHamSim26.FourierTrunc

namespace Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- The transition rate in Eq. (4.45), with separate contributions from
the Fourier tail, the logarithmic term, and the constant term. -/
def sourceBetaRate (ρ ζ A h₂ h₃ h₄ : ℝ) : ℝ :=
  h₂ * (∑' m : ℕ, Real.exp (-(((m : ℝ) + 1) ^ (1 / ρ)) / (2 * ζ))) +
    h₃ * (Real.log ((Nat.ceil (A / Real.pi) : ℝ) - 1) + 1) + h₄

/-- The coefficient `h₂` multiplies exactly the `m ≥ 1` sum in Eq. (4.45). -/
theorem betaRate_eq_source (ρ ζ A h₂ h₃ h₄ : ℝ) :
    sourceBetaRate ρ ζ A h₂ h₃ h₄ =
      h₂ * (∑' m : ℕ, Real.exp (-(((m : ℝ) + 1) ^ (1 / ρ)) / (2 * ζ))) +
        h₃ * (Real.log ((Nat.ceil (A / Real.pi) : ℝ) - 1) + 1) + h₄ :=
  rfl

/-- The source rate is nonnegative when its three coefficients are
nonnegative and the logarithmic contribution is in the source domain. -/
theorem source_betaRate_nonneg (ρ ζ A h₂ h₃ h₄ : ℝ)
    (h₂pos : 0 ≤ h₂) (h₃pos : 0 ≤ h₃) (h₄pos : 0 ≤ h₄) (hA : Real.pi < A) :
    0 ≤ sourceBetaRate ρ ζ A h₂ h₃ h₄ := by
  have hc : (1 : ℝ) < Nat.ceil (A / Real.pi) :=
    ((lt_div_iff₀ Real.pi_pos).mpr (by simpa using hA)).trans_le (Nat.le_ceil _)
  have hcN : 1 < Nat.ceil (A / Real.pi) := by exact_mod_cast hc
  have hc' : 2 ≤ Nat.ceil (A / Real.pi) := hcN
  have hlog : 0 ≤ Real.log ((Nat.ceil (A / Real.pi) : ℝ) - 1) :=
    Real.log_nonneg (by linarith [show (2 : ℝ) ≤ Nat.ceil (A / Real.pi) by exact_mod_cast hc'])
  unfold sourceBetaRate
  exact add_nonneg (add_nonneg (mul_nonneg h₂pos (tsum_nonneg fun _ => (Real.exp_pos _).le))
    (mul_nonneg h₃pos (add_nonneg hlog zero_le_one))) h₄pos

/-- The logarithmic budget appearing in Eq. (4.67). -/
def truncationBudget (β t S ε : ℝ) : ℝ :=
  2 * β * t + Real.log (1 / ε) + Real.log S + Real.log 4

/-- The cutoff from Eq. (4.67), with zero used when the logarithmic
budget is already nonpositive. -/
def chosenTruncationOrder (ρ ζ β t S ε : ℝ) : ℕ :=
  Nat.ceil ((4 * ζ * max 0 (truncationBudget β t S ε)) ^ ρ)

/-- A bound on the base before taking its power suffices for the
error expression in Eq. (4.59). -/
private theorem truncation_error_le (ρ ζ β t S ε : ℝ) (L : ℕ) (hρ : 0 < ρ)
    (hζ : 0 < ζ) (hS : 0 < S) (hε : 0 < ε)
    (hL : (4 * ζ * max 0 (truncationBudget β t S ε)) ^ ρ ≤ (L : ℝ)) :
    4 * S * Real.exp (2 * β * t - (L : ℝ) ^ (1 / ρ) / (4 * ζ)) ≤ ε := by
  let X := truncationBudget β t S ε
  have hbase : 0 ≤ 4 * ζ * max 0 X := mul_nonneg (by positivity) (le_max_left _ _)
  have hinv : ρ * (1 / ρ) = 1 := by field_simp
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hL (by positivity : 0 ≤ 1 / ρ)
  rw [← Real.rpow_mul hbase, hinv, Real.rpow_one] at hr
  have hx : X ≤ (L : ℝ) ^ (1 / ρ) / (4 * ζ) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * ζ)).mpr
    calc X * (4 * ζ) ≤ max 0 X * (4 * ζ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ _ := by rwa [mul_comm]
  have hxexp : 2 * β * t - (L : ℝ) ^ (1 / ρ) / (4 * ζ) ≤
      Real.log (ε / (4 * S)) := by
    rw [Real.log_div hε.ne' (by positivity : (4 * S) ≠ 0),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hS.ne']
    dsimp [X, truncationBudget] at hx
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hε.ne', Real.log_one] at hx
    linarith
  calc
    _ ≤ 4 * S * Real.exp (Real.log (ε / (4 * S))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxexp) (by positivity)
    _ = ε := by rw [Real.exp_log (by positivity)]; field_simp

/-- The tail prefactor in Eq. (4.59) is positive by Lemma 4.3. -/
private theorem sourceTail_pos (ρ ζ : ℝ) (hρ : 1 < ρ) (hζ : 0 < ζ) :
    0 < Ssum ρ (4 * ζ) := by
    have hg := (lemma_four_three_gamma_sum ρ (4 * ζ) hρ (by positivity)).1
    exact (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.rpow_pos_of_pos (by positivity) _)).trans_le hg

/-- The printed product of powers in Eq. (4.67) implies the desired
truncation budget when its logarithmic base is nonnegative. -/
theorem eq467_truncation_order_suffices (ρ ζ β t ε : ℝ) (L : ℕ)
    (hρ : 1 < ρ) (hζ : 0 < ζ) (hε : 0 < ε)
    (hX : 0 ≤ truncationBudget β t (Ssum ρ (4 * ζ)) ε)
    (hL : Nat.ceil ((4 : ℝ) ^ ρ * ζ ^ ρ *
      (truncationBudget β t (Ssum ρ (4 * ζ)) ε) ^ ρ) ≤ L) :
    4 * Ssum ρ (4 * ζ) * Real.exp (2 * β * t - (L : ℝ) ^ (1 / ρ) / (4 * ζ)) ≤ ε := by
  have hS := sourceTail_pos ρ ζ hρ hζ
  apply truncation_error_le ρ ζ β t _ ε L (zero_lt_one.trans hρ) hζ hS hε
  rw [max_eq_right hX, Real.mul_rpow (by positivity : 0 ≤ 4 * ζ) hX,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hζ.le]
  exact (Nat.le_ceil _).trans (by exact_mod_cast hL)

/-- The explicit cutoff also works without a sign assumption on the
logarithmic budget, for any positive tail prefactor. -/
theorem chosenTruncationOrder_suffices (ρ ζ β t S ε : ℝ)
    (hρ : 0 < ρ) (hζ : 0 < ζ) (hS : 0 < S) (hε : 0 < ε) :
    let L := chosenTruncationOrder ρ ζ β t S ε
    4 * S * Real.exp (2 * β * t - (L : ℝ) ^ (1 / ρ) / (4 * ζ)) ≤ ε :=
  truncation_error_le ρ ζ β t S ε _ hρ hζ hS hε (Nat.le_ceil _)

/-- The cutoff computes its budget using the source transition rate and
the actual Fourier tail sum. -/
theorem source_rate_truncation_suffices (ρ ζ A h₂ h₃ h₄ t ε : ℝ)
    (hρ : 1 < ρ) (hζ : 0 < ζ) (hε : 0 < ε) :
    let β := sourceBetaRate ρ ζ A h₂ h₃ h₄
    let S := Ssum ρ (4 * ζ)
    let L := chosenTruncationOrder ρ ζ β t S ε
    4 * S * Real.exp (2 * β * t - (L : ℝ) ^ (1 / ρ) / (4 * ζ)) ≤ ε :=
  chosenTruncationOrder_suffices ρ ζ _ t _ ε (zero_lt_one.trans hρ) hζ
    (sourceTail_pos ρ ζ hρ hζ) hε

end Qatlib.Papers.SlowHamSim26.FourierTrunc
