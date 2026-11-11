/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

/-!
# Linear adiabatic paths and product-formula step counts

Defines the time-scaled linear path `adiabaticPath` and proves its endpoint identities. For a
finite Hermitian family with bounded commutator sum, `product_formula_step_bound` chooses a
positive number of product-formula steps achieving a prescribed positive error tolerance. See
[VanDamMoscaVazirani2001].

## Main statements

* `adiabaticPath_end`: The path reaches the final Hamiltonian at nonzero total time.
* `product_formula_step_bound`: Provides an explicit upper bound on a sufficient step count.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabPower02.MainResults
namespace Theorem1

open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Foundations.PureStateMath

/-- The time-scaled affine Hamiltonian path `t ↦ (1 - t / T) • H₀ + (t / T) • H_f`. -/
def adiabaticPath {I : Type} [Fintype I] [DecidableEq I]
    (H₀ H_f : Matrix I I ℂ) (T : ℝ) : ℝ → Matrix I I ℂ :=
  fun t => (1 - t / T) • H₀ + (t / T) • H_f

/-- The affine adiabatic path starts at `H₀` at time zero. -/
@[simp] lemma adiabaticPath_zero {I : Type} [Fintype I] [DecidableEq I]
    (H₀ H_f : Matrix I I ℂ) (T : ℝ) : adiabaticPath H₀ H_f T 0 = H₀ := by
  simp [adiabaticPath]

/-- For nonzero total time `T`, the affine adiabatic path equals `H_f` at time `T`. -/
lemma adiabaticPath_end {I : Type} [Fintype I] [DecidableEq I]
    (H₀ H_f : Matrix I I ℂ) {T : ℝ} (hT : T ≠ 0) :
    adiabaticPath H₀ H_f T T = H_f := by
  unfold adiabaticPath
  rw [div_self hT]
  simp

/-- For positive `t`, `K`, and `ε`, a Hermitian family with commutator sum at most `K` has a
positive step count at most `t ^ 2 * K / (2 * ε) + 2` giving product-formula error at most
`ε` [VanDamMoscaVazirani2001]. -/
theorem product_formula_step_bound
    {D m : ℕ} (H : Fin m → Operator D) (t K ε : ℝ)
    (hH : ∀ j, (H j).IsHermitian)
    (ht : 0 < t) (hK : 0 < K) (hcomm : pfCommutatorSum H ≤ K) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧
      (r : ℝ) ≤ t ^ 2 * K / (2 * ε) + 2 ∧
      ‖pfFamily H t r - HamiltonianEvolution (∑ j, H j) t‖ ≤ ε := by
  set x : ℝ := t ^ 2 * K / (2 * ε) with hx
  have hxpos : 0 < x := by positivity
  refine ⟨max 1 ⌈x⌉₊, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  · have hceil_lt : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hxpos)
    have hmax : (max 1 ⌈x⌉₊ : ℕ) ≤ ⌈x⌉₊ + 1 := by
      apply max_le <;> omega
    have hcast : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) + 1 := by
      exact_mod_cast hmax
    linarith
  · have hrpos : 0 < (max 1 ⌈x⌉₊ : ℕ) :=
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    have hrposR : (0 : ℝ) < (max 1 ⌈x⌉₊ : ℕ) := by exact_mod_cast hrpos
    have hrx : x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil x) (by exact_mod_cast le_max_right 1 ⌈x⌉₊)
    have hseg := product_formula_finite_family_segmented D m (max 1 ⌈x⌉₊) H t
      hrpos hH
    have hfrac_nonneg : 0 ≤ t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) := by positivity
    have hstep2 : t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) * pfCommutatorSum H
        ≤ t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) * K :=
      mul_le_mul_of_nonneg_left hcomm hfrac_nonneg
    have hfrac_le : t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) ≤ ε / K := by
      have hrx' : 0 < ((max 1 ⌈x⌉₊ : ℕ) : ℝ) := hrposR
      have hmono : t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) ≤ t ^ 2 / (2 * x) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hrx, sq_nonneg t]
      have heq : t ^ 2 / (2 * x) = ε / K := by
        rw [hx]
        field_simp
      linarith
    calc ‖pfFamily H t (max 1 ⌈x⌉₊) - HamiltonianEvolution (∑ j, H j) t‖
        ≤ t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) * pfCommutatorSum H := hseg
      _ ≤ t ^ 2 / (2 * (max 1 ⌈x⌉₊ : ℕ)) * K := hstep2
      _ ≤ (ε / K) * K := mul_le_mul_of_nonneg_right hfrac_le (le_of_lt hK)
      _ = ε := by field_simp

end Theorem1
end Qatlib.Papers.AdiabPower02.MainResults
