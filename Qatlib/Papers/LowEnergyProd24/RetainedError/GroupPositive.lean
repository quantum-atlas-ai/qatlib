/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedError.PsdTolerance

/-!
# Retained bounds under positivity of Hamiltonian groups

This module establishes compressed-group and nested-commutator bounds assuming positivity of the
grouped Hamiltonians. The cutoff recursion and tolerance result implement the retained-error
estimates of [HejaziZiniArrazola2024] under this grouped positivity hypothesis.

## Main statements

* `compressed_group`: Bounds a positive group compressed below `Λ` by `Λ`.
* `psd_tolerance_cutoffs`: Chooses a positive cutoff gap making the chain remainder smaller than
  a prescribed tolerance.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedError.GroupPositive
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- If every grouped Hamiltonian is positive semidefinite, a group compressed below a
nonnegative cutoff `Λ` has operator norm at most `Λ`. -/
theorem compressed_group (h : Hamiltonian N R M k d J) (hp : ∀ m, (h.grouped m).PosSemidef)
    (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low h.total h.total_hermitian Λ*h.grouped m*low h.total h.total_hermitian Λ‖ ≤ Λ :=
  psd_group_compression h.grouped hp m Λ hΛ

/-- Under positivity of every group, one nested-commutator step at `Δ` is bounded by a `2 * Λ`
compressed term and explicit exponential leakage for `Δ ≤ Λ`. -/
theorem nested_cutoff_step (h : Hamiltonian N R M k d J)
    (hp : ∀ m, (h.grouped m).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (L : ℕ) (hL : ∀ m, (h.labels m).card ≤ L) (a seed : Fin M) (xs : List (Fin M))
    (Δ Λ : ℝ) (hΔ : Δ ≤ Λ) (hΛ : 0 ≤ Λ) :
    ‖low h.total h.total_hermitian Δ*nested h seed (a::xs)*low h.total h.total_hermitian Δ‖ ≤
      2*Λ*‖low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ‖+
      2*Real.exp (-2*(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J 0*sourceEll L k d J xs.length := by
  have he :=
      nested_cutoff_commutator_norm h.total h.total_hermitian Δ Λ hΔ (h.grouped a)
      (nested h seed xs)
  have hrevA : ‖low h.total h.total_hermitian Δ*h.grouped a*high h.total h.total_hermitian Λ‖ =
      ‖high h.total h.total_hermitian Λ*h.grouped a*low h.total h.total_hermitian Δ‖ :=
    actual_excursion_reverse h a [] Δ Λ
  rw [hrevA, actual_excursion_reverse h seed xs Δ Λ] at he
  have ha := actual_nested_leakage h hJ hk hd L a (hL a) [] Δ Λ
  have hb := actual_nested_leakage h hJ hk hd L seed (hL seed) xs Δ Λ
  change ‖high h.total h.total_hermitian Λ*h.grouped a*low h.total h.total_hermitian Δ‖ ≤
    Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J 0 at ha
  change ‖low h.total h.total_hermitian Δ*nested h seed
      (a::xs)*low h.total h.total_hermitian Δ‖ ≤ _ at he
  calc
    _ ≤ _ := he
    _ ≤ 2*Λ*‖low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ‖+
        (Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J 0)*
          (Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J xs.length)+
        (Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J xs.length)*
          (Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J 0) := by
      have hcut := compressed_group h hp a Λ hΛ
      have hlead := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcut (by norm_num : (0 : ℝ) ≤ 2))
        (norm_nonneg (low h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Λ))
      have hcrossAB := mul_le_mul ha hb (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (sourceEll_nonneg L k d 0 J hJ.le))
      have hcrossBA := mul_le_mul hb ha (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (sourceEll_nonneg L k d xs.length J hJ.le))
      exact add_le_add (add_le_add hlead hcrossAB) hcrossBA
    _ = _ := by
      have hx : Real.exp (-2*(1/(2*J*k*d))*(Λ-Δ)) =
          Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*Real.exp (-(1/(2*J*k*d))*(Λ-Δ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hx]
      ring

/-- Under grouped positivity, the depth-`xs.length` commutator compressed at `Δ` is bounded by
`2 ^ xs.length * (Δ + xs.length * gap) ^ (xs.length + 1)` plus `chainRemainder`. -/
theorem psd_cutoff_chain (h : Hamiltonian N R M k d J)
    (hp : ∀ m, (h.grouped m).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (L : ℕ) (hL : ∀ m, (h.labels m).card ≤ L) (seed : Fin M) (xs : List (Fin M))
    (Δ gap : ℝ) (hΔ : 0 ≤ Δ) (hgap : 0 ≤ gap) :
    ‖low h.total h.total_hermitian Δ*nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
      2^xs.length*(Δ+xs.length*gap)^(xs.length+1)+chainRemainder L k d J xs.length Δ gap := by
  induction xs generalizing Δ with
  | nil =>
    simpa only [nested, List.length_nil, Nat.cast_zero, zero_mul, add_zero, zero_add,
      pow_zero, one_mul, pow_one, chainRemainder] using compressed_group h hp seed Δ hΔ
  | cons a xs ih =>
    have hi := ih (Δ+gap) (by positivity)
    have hs := nested_cutoff_step h hp hJ hk hd L hL a seed xs Δ (Δ+gap)
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

/-- Under grouped positivity, every positive tolerance possesses a positive cutoff gap for which
the compressed nested-commutator norm is bounded by the enlarged-cutoff leading term plus
that tolerance. -/
theorem psd_tolerance_cutoffs (h : Hamiltonian N R M k d J)
    (hp : ∀ m, (h.grouped m).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
    (L : ℕ) (hL : ∀ m, (h.labels m).card ≤ L) (seed : Fin M) (xs : List (Fin M))
    (Δ θ : ℝ) (hΔ : 0 ≤ Δ) (hθ : 0 < θ) :
    ∃ gap : ℝ, 0 < gap ∧
      ‖low h.total h.total_hermitian Δ*nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
        2^xs.length*(Δ+xs.length*gap)^(xs.length+1)+θ := by
  have hdecay := actual_chainRemainder_decay L k d xs.length J hJ hk hd Δ
  have he : ∀ᶠ gap : ℝ in atTop, chainRemainder L k d J xs.length Δ gap < θ :=
    hdecay.eventually (gt_mem_nhds hθ)
  obtain ⟨gap, hrem, hg⟩ := (he.and (eventually_ge_atTop (1 : ℝ))).exists
  have hgap : 0 < gap := lt_of_lt_of_le zero_lt_one hg
  exact ⟨gap, hgap, (psd_cutoff_chain h hp hJ hk hd L hL seed xs Δ gap hΔ hgap.le).trans
    (add_le_add le_rfl hrem.le)⟩

end Qatlib.Papers.LowEnergyProd24.RetainedError.GroupPositive
