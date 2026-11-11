/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Finite spectral flux correlation sums

This module defines the finite spectral correlation `sourceFluxCorrelation` and the flux matrix
elements `sourceFluxMatrixElement` appearing in [LidarWang1999]. For real surface weights,
conjugate symmetry of the weighted overlaps converts a product of flux entries into a squared
energy gap times a squared overlap magnitude.

The resulting weighted double sum reproduces the algebraic form of Equation 16, and its diagonal
terms vanish.

## Main statements

* `source_overlap_conj`: reversing overlap indices takes complex conjugates for real weights.
* `source_flux_correlation_eq16`: expands the correlation into thermal and dynamical weights,
  squared gaps, and squared overlap magnitudes.
* `source_flux_offdiagonal`: removing the diagonal does not change the weighted double sum.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ThermalRate98.MainResults

/-- The finite spectral flux correlation, summing thermal weights, energy-gap phases, and
products `F n m * F m n` over both energy indices. -/
def sourceFluxCorrelation {I : Type*} [Fintype I] (β t ħ : ℝ) (E : I → ℝ)
    (F : I → I → ℂ) : ℂ :=
  ∑ n, ∑ m, Complex.exp (-(β * (E n + E m)) / 2) *
    Complex.exp (Complex.I * ((E m - E n) * t / ħ)) * F n m * F m n

/-- The flux matrix element `(i/ħ) (E n - E m)` times the surface-weighted overlap of
coefficient columns `n` and `m`. -/
def sourceFluxMatrixElement {J I : Type*} [Fintype J] (ħ : ℝ) (E : I → ℝ)
    (h : J → ℂ) (A : J → I → ℂ) (n m : I) : ℂ :=
  Complex.I / (ħ : ℂ) * ((E n - E m : ℝ) : ℂ) *
    (∑ j : J, star (A j n) * A j m * h j)

/-- For surface weights with zero imaginary part, reversing the two coefficient indices in the
weighted overlap takes its complex conjugate. -/
theorem source_overlap_conj {J I : Type*} [Fintype J] (A : J → I → ℂ) (h : J → ℂ)
    (hh : ∀ j, (h j).im = 0) (n m : I) :
    (∑ j : J, star (A j m) * A j n * h j) =
      star (∑ j : J, star (A j n) * A j m * h j) := by

  have hstar : ∀ j : J, star (star (A j n) * A j m * h j)
      = star (A j m) * A j n * h j := by
    intro j
    have hhj : star (h j) = h j := Complex.conj_eq_iff_im.2 (hh j)
    rw [star_mul, star_mul]
    simp [hhj]
    ring
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (hstar j).symm

/-- For real surface weights, the product of reversed flux matrix elements equals `ħ⁻²` times
the squared energy gap and the squared magnitude of the weighted overlap, as in Equation 16
of [LidarWang1999]. -/
theorem source_flux_term_eq16 {J I : Type*} [Fintype J] (ħ : ℝ)
    (E : I → ℝ) (A : J → I → ℂ) (h : J → ℂ) (hh : ∀ j, (h j).im = 0) (n m : I) :
    sourceFluxMatrixElement ħ E h A n m * sourceFluxMatrixElement ħ E h A m n =
      ((ħ⁻¹) ^ 2 : ℂ) * (((E n - E m : ℝ) : ℂ) ^ 2) *
        (Complex.normSq (∑ j : J, star (A j n) * A j m * h j) : ℂ) := by
  unfold sourceFluxMatrixElement
  rw [source_overlap_conj A h hh n m]
  have hb : ((E m - E n : ℝ) : ℂ) = -((E n - E m : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hb]

  have hYX :
      Complex.I / (ħ : ℂ) * -((E n - E m : ℝ) : ℂ)
          * star (∑ j : J, star (A j n) * A j m * h j)
        = star (Complex.I / (ħ : ℂ) * ((E n - E m : ℝ) : ℂ)
            * (∑ j : J, star (A j n) * A j m * h j)) := by

    set S : ℂ := ∑ j : J, star (A j n) * A j m * h j with hS
    clear hS
    simp only [Complex.star_def, map_mul, map_div₀, Complex.conj_I,
      Complex.conj_ofReal]
    ring

  have hmul : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := by
    intro z
    simpa only [Complex.star_def] using Complex.mul_conj z
  rw [hYX, hmul]

  have hns : Complex.normSq (Complex.I / (ħ : ℂ) * ((E n - E m : ℝ) : ℂ)
        * (∑ j : J, star (A j n) * A j m * h j))
      = (ħ⁻¹) ^ 2 * (E n - E m) ^ 2 *
          Complex.normSq (∑ j : J, star (A j n) * A j m * h j) := by
    rw [Complex.normSq_mul, Complex.normSq_mul]
    have h1 : Complex.normSq (Complex.I / (ħ : ℂ)) = (ħ⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, Complex.normSq_mul, Complex.normSq_I, one_mul]
      rw [show ((ħ : ℂ)⁻¹) = ((ħ⁻¹ : ℝ) : ℂ) by simp]
      rw [Complex.normSq_ofReal]
      ring
    have h2 : Complex.normSq (((E n - E m : ℝ) : ℂ)) = (E n - E m) ^ 2 := by
      rw [Complex.normSq_ofReal]
      ring
    rw [h1, h2]
  rw [hns]
  push_cast
  ring

/-- For real surface weights, the finite spectral flux correlation is `ħ⁻²` times the double sum
of thermal weights, dynamical phases, squared energy gaps, and squared overlap magnitudes.
This is the algebraic finite-sum form of Equation 16 in [LidarWang1999]. -/
theorem source_flux_correlation_eq16 {J I : Type*} [Fintype J] [Fintype I]
    (β t ħ : ℝ) (E : I → ℝ) (A : J → I → ℂ) (h : J → ℂ)
    (hh : ∀ j, (h j).im = 0) :
    sourceFluxCorrelation β t ħ E (sourceFluxMatrixElement ħ E h A) =
      ((ħ⁻¹) ^ 2 : ℂ) *
        ∑ n, ∑ m, Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((E n - E m : ℝ) : ℂ) ^ 2) *
          (Complex.normSq (∑ j : J, star (A j n) * A j m * h j) : ℂ) := by
  unfold sourceFluxCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hterm := source_flux_term_eq16 ħ E A h hh n m
  calc Complex.exp (-(β * (E n + E m)) / 2) *
        Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
        sourceFluxMatrixElement ħ E h A n m * sourceFluxMatrixElement ħ E h A m n
      = Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (sourceFluxMatrixElement ħ E h A n m * sourceFluxMatrixElement ħ E h A m n) := by
        ring
    _ = Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((ħ⁻¹) ^ 2 : ℂ) * (((E n - E m : ℝ) : ℂ) ^ 2) *
            (Complex.normSq (∑ j : J, star (A j n) * A j m * h j) : ℂ)) := by
        rw [hterm]
    _ = ((ħ⁻¹) ^ 2 : ℂ) *
          (Complex.exp (-(β * (E n + E m)) / 2) *
            Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
            (((E n - E m : ℝ) : ℂ) ^ 2) *
            (Complex.normSq (∑ j : J, star (A j n) * A j m * h j) : ℂ)) := by
        ring

/-- The weighted squared-gap double sum is unchanged when each diagonal term `m = n` is omitted,
since its energy gap vanishes. -/
theorem source_flux_offdiagonal {I : Type*} [Fintype I] [DecidableEq I]
    (β t ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) :
    (∑ n, ∑ m ∈ Finset.univ.erase n,
        Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ))
      = ∑ n, ∑ m, Complex.exp (-(β * (E n + E m)) / 2) *
          Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
          (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ n)]
  have hdiag : Complex.exp (-(β * (E n + E n)) / 2) *
        Complex.exp (Complex.I * ((E n - E n) * t / ħ)) *
        (((E n - E n : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n n) : ℂ) = 0 := by
    simp
  rw [hdiag, add_zero]

/-- The dimension identity `2 ^ (l * M) = (2 ^ l) ^ M` expresses the size of a register with `M`
coordinates of `l` qubits each. -/
theorem source_register_dimension (l M : ℕ) :
    (2 : ℕ) ^ (l * M) = ((2 : ℕ) ^ l) ^ M := by
  rw [pow_mul]

end Qatlib.Papers.ThermalRate98.MainResults
