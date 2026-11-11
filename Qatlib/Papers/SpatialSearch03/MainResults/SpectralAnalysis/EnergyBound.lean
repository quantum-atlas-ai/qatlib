/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.TimeBound

/-!
# Lattice energies and Fourier normalization

This module proves elementary energy and normalization estimates for the periodic lattice model
of [ChildsGoldstone2004]. It also supplies the scalar inequality `ground_amplitude_bound`, which
bounds an amplitude prefactor under a lower bound on the secular slope.

## Main statements

* `latticeEnergy_nonneg` and `latticeEnergy_le`: lattice energies lie between zero and `4 * d`.
* `normalized_fourierMode`: Fourier modes are normalized when the lattice side length is
  positive.
* `ground_amplitude_bound`: comparison of the two scalar amplitude bounds.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialSearch03.MainResults

/-- Every periodic lattice energy is nonnegative. -/
theorem latticeEnergy_nonneg (d n : ℕ) (m : LatticeVertex d n) : 0 ≤ latticeEnergy d n m := by
  unfold latticeEnergy
  have hterm : ∀ j : Fin d, 0 ≤ 1 - Real.cos (2 * Real.pi * (m j).val / (n : ℝ)) := by
    intro j
    linarith [Real.cos_le_one (2 * Real.pi * (m j).val / (n : ℝ))]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hterm j)
  linarith

/-- Every periodic lattice energy in dimension `d` is at most `4 * d`. -/
theorem latticeEnergy_le (d n : ℕ) (m : LatticeVertex d n) :
    latticeEnergy d n m ≤ 4 * (d : ℝ) := by
  unfold latticeEnergy
  have hterm : ∀ j : Fin d, 1 - Real.cos (2 * Real.pi * (m j).val / (n : ℝ)) ≤ 2 := by
    intro j
    linarith [Real.neg_one_le_cos (2 * Real.pi * (m j).val / (n : ℝ))]
  have hsum : ∑ j : Fin d, (1 - Real.cos (2 * Real.pi * (m j).val / (n : ℝ))) ≤
      ∑ _j : Fin d, (2 : ℝ) := Finset.sum_le_sum fun j _ => hterm j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- Each entry of a lattice Fourier mode has norm equal to the inverse square root of the number
of lattice vertices. -/
theorem norm_fourierMode_apply (d n : ℕ) (m x : LatticeVertex d n) :
    ‖fourierMode d n m x‖ =
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
  unfold fourierMode
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Complex.norm_exp_I_mul_ofReal, mul_one]

/-- Every lattice Fourier mode is normalized when the side length is positive. -/
theorem normalized_fourierMode (d n : ℕ) (hn : 0 < n) (m : LatticeVertex d n) :
    Normalized (fourierMode d n m) := by
  unfold Normalized
  have hcard : 0 < Fintype.card (LatticeVertex d n) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hn⟩⟩
  have hterm : ∀ x : LatticeVertex d n, ‖fourierMode d n m x‖ ^ 2 =
      (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ ^ 2 := by
    intro x
    rw [norm_fourierMode_apply]
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => hterm x)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hNpos : (0 : ℝ) < Fintype.card (LatticeVertex d n) := by exact_mod_cast hcard
  have hsq : (Real.sqrt (Fintype.card (LatticeVertex d n) : ℝ))⁻¹ ^ 2 =
      ((Fintype.card (LatticeVertex d n) : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hNpos.le]
  rw [hsq]
  exact mul_inv_cancel₀ (ne_of_gt hNpos)

/-- For positive `N`, `E`, and `F'`, the inequality `1 ≤ N * E ^ 2 * F'` implies `2 / (Real.sqrt
N * E * F') ≤ 2 * Real.sqrt N * E`. This scalar estimate supports the amplitude bounds in
[ChildsGoldstone2004]. -/
theorem ground_amplitude_bound {N : ℕ} {E F' : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hF' : 0 < F')
    (hNF : 1 ≤ (N : ℝ) * E ^ 2 * F') :
    2 / (Real.sqrt (N : ℝ) * E * F') ≤ 2 * Real.sqrt (N : ℝ) * E := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNpos.le
  have hpos : 0 < Real.sqrt (N : ℝ) * E * F' :=
    mul_pos (mul_pos hRN hE) hF'
  rw [div_le_iff₀ hpos]
  have hprod : 2 * Real.sqrt (N : ℝ) * E * (Real.sqrt (N : ℝ) * E * F') =
      2 * ((N : ℝ) * E ^ 2 * F') := by
    nlinarith [hsq]
  linarith [hNF, hprod]

end Qatlib.Papers.SpatialSearch03.MainResults
