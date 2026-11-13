/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.NestedLeakage
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.NestedCutoffs

/-!
# A cutoff step for nested commutators

This module proves the adjoint parity of grouped nested commutators and equality of their
opposite off-diagonal block norms. With positive semidefinite local terms,
`actual_nested_cutoff_step` combines compression at a larger cutoff with exponential leakage
control, as required in [HejaziZiniArrazola2024].

## Main statements

* `actual_nested_star`: Identifies the adjoint sign from the nesting depth.
* `actual_nested_cutoff_step`: Bounds one commutator step using a larger energy cutoff.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

/-- The adjoint of a grouped nested commutator equals the commutator multiplied by `(-1 : ℂ) ^
xs.length`. -/
theorem actual_nested_star (h : Hamiltonian N R M k d J) (seed : Fin M) (xs : List (Fin M)) :
    star (nested h seed xs) = (-1 : ℂ)^xs.length • nested h seed xs := by
  induction xs with
  | nil =>
    simp only [nested, List.length_nil, pow_zero, one_smul]
    exact h.grouped_hermitian seed
  | cons a xs ih =>
    have ha : star (h.grouped a) = h.grouped a := h.grouped_hermitian a
    simp only [nested, star_sub, star_mul, ih, ha, mul_smul_comm, smul_mul_assoc,
      List.length_cons, pow_succ, mul_neg_one, neg_smul, smul_sub]
    module

/-- The two opposite off-diagonal blocks of a grouped nested commutator have equal operator
norms. -/
theorem actual_excursion_reverse (h : Hamiltonian N R M k d J) (seed : Fin M)
    (xs : List (Fin M)) (Δ Λ : ℝ) :
    ‖low h.total h.total_hermitian Δ*nested h seed xs*high h.total h.total_hermitian Λ‖ =
      ‖high h.total h.total_hermitian Λ*nested h seed xs*low h.total h.total_hermitian Δ‖ := by
  let P := low h.total h.total_hermitian Δ
  let Q := high h.total h.total_hermitian Λ
  have hp : star P=P := low_hermitian _ _ _
  have hq : star Q=Q := high_hermitian _ _ _
  change ‖P*nested h seed xs*Q‖ = ‖Q*nested h seed xs*P‖
  calc
    _ = ‖star (P*nested h seed xs*Q)‖ := (norm_star _).symm
    _ = ‖(-1 : ℂ)^xs.length • (Q*nested h seed xs*P)‖ := by
      simp only [star_mul, hp, hq, actual_nested_star, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- For positive semidefinite local terms and `Δ ≤ Λ`, one extra commutator is bounded by `2 *
Λ` times the inner commutator compressed at `Λ`, plus the explicit exponential leakage term. -/
theorem actual_nested_cutoff_step (h : Hamiltonian N R M k d J)
    (hp : ∀ i, (h.term i).PosSemidef) (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d)
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
      have hcut := h.actual_psd_group_cutoff hp a Λ hΛ
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
end Qatlib.Papers.LowEnergyProd24.RetainedError
