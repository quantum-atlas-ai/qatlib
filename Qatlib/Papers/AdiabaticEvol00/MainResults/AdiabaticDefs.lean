/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Interpolation, spectral gaps, and runtime inequalities

This module defines linear Hamiltonian interpolation through `interpolate`, the
lowest-eigenvalue separation `instantaneousGap`, and its infimum `minGap` along the
interpolation interval. The predicate `TimeSufficient` records the algebraic criterion `E / g ^
2 ≤ T`, and the remaining estimates convert assumed energy and gap bounds into polynomial bounds
for this ratio. The mathematical context is [FarhiEtAl2000].

## Main statements

* `instantaneousGap_nonneg`: The separation between the two lowest eigenvalues of a Hermitian
  operator is nonnegative.
* `time_bound_power`: For positive `n` and `c`, the bounds `0 ≤ E ≤ C * n ^ a` and `c * n ^ q ≤
  g` imply `E / g ^ 2 ≤ (C / c ^ 2) * n ^ (a - 2 * q)`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {D : ℕ}

/-- The linear interpolation `(1 - s) • HB + s • HP` between the initial and problem
Hamiltonians [FarhiEtAl2000]. -/
def interpolate (HB HP : Operator D) (s : ℝ) : Operator D :=
  (1 - s) • HB + s • HP

/-- At interpolation parameter zero, `interpolate HB HP` equals `HB`. -/
@[simp] theorem interpolate_zero (HB HP : Operator D) : interpolate HB HP 0 = HB := by
  simp [interpolate]

/-- At interpolation parameter one, `interpolate HB HP` equals `HP`. -/
@[simp] theorem interpolate_one (HB HP : Operator D) : interpolate HB HP 1 = HP := by
  simp [interpolate]

/-- Linear Hamiltonian interpolation is continuous in its real parameter. -/
theorem continuous_interpolate (HB HP : Operator D) :
    Continuous (fun s : ℝ => interpolate HB HP s) := by
  unfold interpolate
  fun_prop

/-- Real linear interpolation between Hermitian Hamiltonians is Hermitian. -/
theorem interpolate_isHermitian (HB HP : Operator D)
    (hB : HB.IsHermitian) (hP : HP.IsHermitian) (s : ℝ) :
    (interpolate HB HP s).IsHermitian := by
  unfold interpolate
  exact (hB.smul (k := (1 - s)) (IsSelfAdjoint.all _)).add
    (hP.smul (k := s) (IsSelfAdjoint.all _))

/-- The difference between the second-smallest and smallest eigenvalues of a Hermitian operator
of dimension at least two. -/
def instantaneousGap (hD : 2 ≤ D) (H : Operator D) (hH : H.IsHermitian) : ℝ :=
  hH.eigenvalues₀ ⟨Fintype.card (Fin D) - 2, by rw [Fintype.card_fin]; omega⟩ -
    hH.eigenvalues₀ ⟨Fintype.card (Fin D) - 1, by rw [Fintype.card_fin]; omega⟩

/-- The separation between the two lowest eigenvalues of a Hermitian operator is nonnegative. -/
theorem instantaneousGap_nonneg (hD : 2 ≤ D) (H : Operator D) (hH : H.IsHermitian) :
    0 ≤ instantaneousGap hD H hH := by
  unfold instantaneousGap

  have hidx : (⟨Fintype.card (Fin D) - 2, by rw [Fintype.card_fin]; omega⟩ :
      Fin (Fintype.card (Fin D))) ≤
      ⟨Fintype.card (Fin D) - 1, by rw [Fintype.card_fin]; omega⟩ := by
    simp only [Fin.mk_le_mk]
    have hcard : Fintype.card (Fin D) = D := Fintype.card_fin D
    omega
  exact sub_nonneg.mpr (hH.eigenvalues₀_antitone hidx)

/-- The infimum of the instantaneous spectral gap along the linear interpolation for parameters
in `[0, 1]`. -/
def minGap (hD : 2 ≤ D) (HB HP : Operator D)
    (hB : HB.IsHermitian) (hP : HP.IsHermitian) : ℝ :=
  sInf ((fun s : ℝ => instantaneousGap hD (interpolate HB HP s)
      (interpolate_isHermitian HB HP hB hP s)) '' Set.Icc 0 1)

/-- The algebraic runtime criterion `E / g ^ 2 ≤ T` [FarhiEtAl2000]. -/
def TimeSufficient (T E g : ℝ) : Prop := E / g ^ 2 ≤ T

/-- The inequality `E / g ^ 2 ≤ T` yields `TimeSufficient T E g` for positive `g`. -/
theorem timeSufficient_of_gap (T E g : ℝ) (_hg : 0 < g) (h : E / g ^ 2 ≤ T) :
    TimeSufficient T E g := h

/-- If `0 < g ≤ g'`, a sufficient time for `g'` gives a sufficient time for `g` after
multiplication by `g' ^ 2 / g ^ 2`. -/
theorem timeSufficient_mono_gap {T E g g' : ℝ} (hg : 0 < g) (hgg : g ≤ g')
    (h : TimeSufficient T E g') : TimeSufficient (T * (g' ^ 2 / g ^ 2)) E g := by
  unfold TimeSufficient at *
  have hg2 : 0 < g ^ 2 := by positivity
  have hgg2 : 0 < g' ^ 2 := pow_pos (lt_of_lt_of_le hg hgg) 2
  have h2 : E ≤ T * g' ^ 2 := by rwa [div_le_iff₀ hgg2] at h
  rw [div_le_iff₀ hg2]
  calc E ≤ T * g' ^ 2 := h2
    _ = T * (g' ^ 2 / g ^ 2) * g ^ 2 := by field_simp

/-- For positive `n` and `c`, the bounds `0 ≤ E ≤ C * n` and `c / n ≤ g` imply `E / g ^ 2 ≤ (C /
c ^ 2) * n ^ 3`. -/
theorem time_bound_linear_gap {E g C c n : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hE : E ≤ C * n) (hg : c / n ≤ g)
    (hE0 : 0 ≤ E) : E / g ^ 2 ≤ (C / c ^ 2) * n ^ 3 := by
  have hgpos : 0 < g := lt_of_lt_of_le (div_pos hc hn) hg
  have hg2 : c ^ 2 / n ^ 2 ≤ g ^ 2 := by
    have h := mul_self_le_mul_self (le_of_lt (div_pos hc hn)) hg
    have hc2 : (c / n) * (c / n) = c ^ 2 / n ^ 2 := by field_simp
    have hg2' : g * g = g ^ 2 := by ring
    rwa [hc2, hg2'] at h
  rw [div_le_iff₀ (pow_pos hgpos 2)]
  have hC : 0 ≤ C := by
    have hCn : 0 ≤ C * n := le_trans hE0 hE
    exact nonneg_of_mul_nonneg_left hCn hn
  calc E ≤ C * n := hE
    _ = (C / c ^ 2) * n ^ 3 * (c ^ 2 / n ^ 2) := by
        field_simp; try ring
    _ ≤ (C / c ^ 2) * n ^ 3 * g ^ 2 := by
        exact mul_le_mul_of_nonneg_left hg2 (by positivity)

/-- For positive `n`, the bounds `0 ≤ E ≤ n` and `1 / n ≤ g` imply `E / g ^ 2 ≤ n ^ 3`. -/
theorem ring_time_is_cubic {E g n : ℝ}
    (hn : 0 < n) (hE : E ≤ n) (hg : 1 / n ≤ g) (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ n ^ 3 := by
  have := time_bound_linear_gap (E := E) (g := g) (C := 1) (c := 1) (n := n) hn
    (by norm_num) (by simpa using hE) (by simpa using hg) hE0
  simpa using this

/-- For positive `n` and `c`, the bounds `0 ≤ E ≤ C * n ^ a` and `c * n ^ q ≤ g` imply `E / g ^
2 ≤ (C / c ^ 2) * n ^ (a - 2 * q)` [FarhiEtAl2000]. -/
theorem time_bound_power {E g C c a q : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ)) (hc : 0 < c)
    (hE : E ≤ C * (n : ℝ) ^ a) (hgap : c * (n : ℝ) ^ q ≤ g) (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ (C / c ^ 2) * (n : ℝ) ^ (a - 2 * q) := by
  have hxpos : 0 < (n : ℝ) := hn
  have hqpos : 0 < (n : ℝ) ^ q := Real.rpow_pos_of_pos hxpos q
  have hgpos : 0 < g := lt_of_lt_of_le (mul_pos hc hqpos) hgap
  have hbase : 0 ≤ c * (n : ℝ) ^ q := le_of_lt (mul_pos hc hqpos)
  have hgsq : (c * (n : ℝ) ^ q) ^ 2 ≤ g ^ 2 := by
    have := mul_self_le_mul_self hbase hgap
    simpa [pow_two] using this
  have hsq_eq : (c * (n : ℝ) ^ q) ^ 2 = c ^ 2 * (n : ℝ) ^ (2 * q) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((n : ℝ) ^ q) 2]
    rw [← Real.rpow_mul (le_of_lt hxpos)]
    congr 1
    ring
  rw [div_le_iff₀ (pow_pos hgpos 2)]
  have hC : 0 ≤ C := by
    have hCn : 0 ≤ C * (n : ℝ) ^ a := le_trans hE0 hE
    have hxapos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hxpos a
    exact nonneg_of_mul_nonneg_left hCn hxapos
  have hCc : (C / c ^ 2) * c ^ 2 = C := div_mul_cancel₀ C (pow_ne_zero 2 (ne_of_gt hc))
  have hxprod : (n : ℝ) ^ (a - 2 * q) * (n : ℝ) ^ (2 * q) = (n : ℝ) ^ a := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  calc E ≤ C * (n : ℝ) ^ a := hE
    _ = (C / c ^ 2) * (n : ℝ) ^ (a - 2 * q) * (c ^ 2 * (n : ℝ) ^ (2 * q)) := by
        rw [show C * (n : ℝ) ^ a = ((C / c ^ 2) * c ^ 2) * (n : ℝ) ^ a by rw [hCc]]
        rw [show ((C / c ^ 2) * c ^ 2) * (n : ℝ) ^ a
              = (C / c ^ 2) * (n : ℝ) ^ (a - 2 * q) * (c ^ 2 * (n : ℝ) ^ (2 * q)) by
            rw [← hxprod]; ring]
    _ ≤ (C / c ^ 2) * (n : ℝ) ^ (a - 2 * q) * g ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hsq_eq]; exact hgsq

end Qatlib.Papers.AdiabaticEvol00.MainResults
