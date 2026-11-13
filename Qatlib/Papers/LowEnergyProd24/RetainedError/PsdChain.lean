/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedError.CutoffChain

/-!
# Recursive leakage remainders along cutoff chains

This module defines `chainRemainder` by recursively increasing the energy cutoff by a fixed gap.
It proves nonnegativity and bounds compressed nested commutators by the enlarged-cutoff leading
term plus this explicit leakage remainder, as in [HejaziZiniArrazola2024].

## Main statements

* `chainRemainder`: Accumulates exponential leakage errors through the cutoff recursion.
* `actual_psd_cutoff_chain`: Gives the nested-commutator bound for positive semidefinite local
  terms.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The recursive cutoff-chain remainder, initialized at zero and updated by a `2 * (Δ + gap)`
factor and an explicit exponential leakage term. -/
def chainRemainder (L k d : ℕ) (J : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n+1, Δ, gap => 2*(Δ+gap)*chainRemainder L k d J n (Δ+gap) gap +
      2*Real.exp (-2*(1/(2*J*k*d))*gap)*sourceEll L k d J 0*sourceEll L k d J n

/-- The cutoff-chain remainder is nonnegative when `J`, `Δ`, and the cutoff gap are nonnegative. -/
theorem chainRemainder_nonneg (L k d n : ℕ) (J Δ gap : ℝ)
    (hJ : 0 ≤ J) (hΔ : 0 ≤ Δ) (hgap : 0 ≤ gap) : 0 ≤ chainRemainder L k d J n Δ gap := by
  induction n generalizing Δ with
  | zero => rfl
  | succ n ih =>
    rw [chainRemainder]
    exact add_nonneg (mul_nonneg (by positivity) (ih (Δ+gap) (by positivity)))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (sourceEll_nonneg L k d 0 J hJ)) (sourceEll_nonneg L k d n J hJ))

/-- For positive semidefinite local terms, the nested commutator compressed at `Δ` is bounded by
`2 ^ xs.length * (Δ + xs.length * gap) ^ (xs.length + 1)` plus the cutoff-chain remainder. -/
theorem actual_psd_cutoff_chain (h : Hamiltonian N R M k d J)
    (hp : ∀ i, (h.term i).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (L : ℕ) (hL : ∀ m, (h.labels m).card ≤ L) (seed : Fin M) (xs : List (Fin M))
    (Δ gap : ℝ) (hΔ : 0 ≤ Δ) (hgap : 0 ≤ gap) :
    ‖low h.total h.total_hermitian Δ*nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
      2^xs.length*(Δ+xs.length*gap)^(xs.length+1)+chainRemainder L k d J xs.length Δ gap := by
  induction xs generalizing Δ with
  | nil =>
    simpa only [nested, List.length_nil, Nat.cast_zero, zero_mul, add_zero, zero_add,
      pow_zero, one_mul, pow_one, chainRemainder] using h.actual_psd_group_cutoff hp seed Δ hΔ
  | cons a xs ih =>
    have hi := ih (Δ+gap) (by positivity)
    have hs := actual_nested_cutoff_step h hp hJ hk hd L hL a seed xs Δ (Δ+gap)
      (by linarith) (by positivity)
    have hf : (Δ+gap)+(xs.length : ℝ)*gap=Δ+(xs.length+1 : ℕ)*gap := by push_cast; ring
    rw [hf] at hi
    have hlead : 2*(Δ+gap)*(2^xs.length*(Δ+(xs.length+1 : ℕ)*gap)^(xs.length+1)) ≤
        2^(xs.length+1)*(Δ+(xs.length+1 : ℕ)*gap)^(xs.length+1+1) := by
      calc
        _ ≤ 2*(Δ+(xs.length+1 : ℕ)*gap)*(2^xs.length*(Δ+(xs.length+1 : ℕ)*gap)^(xs.length+1)) := by
          gcongr
          push_cast
          nlinarith [mul_nonneg (Nat.cast_nonneg xs.length : (0 : ℝ) ≤ xs.length) hgap]
        _ = _ := by rw [pow_succ, pow_succ]; ring
    calc
      _ ≤ _ := hs
      _ ≤ 2*(Δ+gap)*(2^xs.length*(Δ+(xs.length+1 : ℕ)*gap)^(xs.length+1)+
          chainRemainder L k d J xs.length (Δ+gap) gap)+
          2*Real.exp (-2*(1/(2*J*k*d))*((Δ+gap)-Δ))*sourceEll L k d J 0*sourceEll L k d J xs.length :=
        add_le_add (mul_le_mul_of_nonneg_left hi (by positivity)) le_rfl
      _ ≤ _ := by
        simp only [List.length_cons, chainRemainder]
        rw [add_sub_cancel_left]
        nlinarith only [hlead]
end Qatlib.Papers.LowEnergyProd24.RetainedError
