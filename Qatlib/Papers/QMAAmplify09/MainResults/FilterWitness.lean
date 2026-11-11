/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAAmplify09.MainResults.Defs
import Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Fourier filter states and witness branch weights

This module constructs discrete Fourier filter states for the reverse phase-estimation
discussion in [NagajWocjanZhang2009]. It proves exact inverse-transform recovery and
orthonormality after normalization, using the finite complex inner product `fip`.

The two-component state `phasePlus` has unit norm and a branch weight of one half. The module
also compares the previously defined amplification cost with the real-valued
`marriottWatrousCost` expression.

## Main statements

* `filterState_reverse`: inverse Fourier transform recovers the corresponding basis state.
* `fip_normFilterState`: normalized filter states are orthonormal.
* `witness_branch_prob`: the zero component of `phasePlus` has weight one half.
* `amplificationCost_le_ratio`: comparison with the quadratic inverse-gap cost expression.

## References

* [Nagaj et al., 2009][NagajWocjanZhang2009]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

open Qatlib.Papers.QMAAmplify09.MainResults.Defs
open Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification

namespace Qatlib.Papers.QMAAmplify09.MainResults.FilterWitness

/-- The finite complex inner product, conjugate-linear in its first argument and linear in its
second. -/
def fip {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (x i) * y i

/-- The finite inner product distributes over addition in its second argument. -/
theorem fip_add {ι : Type*} [Fintype ι] (x y z : ι → ℂ) :
    fip x (y + z) = fip x y + fip x z := by
  unfold fip
  simp only [Pi.add_apply, mul_add, sum_add_distrib]

/-- Scaling the second argument of `fip` multiplies the inner product by the same complex
scalar. -/
theorem fip_smul_right {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c : ℂ) :
    fip x (c • y) = c * fip x y := by
  unfold fip
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scaling the first argument of `fip` multiplies the inner product by the conjugate scalar. -/
theorem fip_smul_left {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c : ℂ) :
    fip (c • x) y = (starRingEnd ℂ) c * fip x y := by
  unfold fip
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scaling both arguments of `fip` contributes the conjugate of the first scalar times the
second scalar. -/
theorem fip_smul_smul {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c d : ℂ) :
    fip (c • x) (d • y) = (starRingEnd ℂ) c * d * fip x y := by
  rw [fip_smul_left, fip_smul_right]
  ring

variable {N : ℕ} [NeZero N]

/-- The computational basis vector supported at `m` in `ZMod N`. -/
def basisState (m : ZMod N) : ZMod N → ℂ := fun j => if j = m then 1 else 0

/-- The discrete Fourier transform of the basis vector at `m`. -/
def filterState (m : ZMod N) : ZMod N → ℂ := ZMod.dft (basisState m)

/-- The filter-state component at `k` is the standard additive character evaluated at `-(m *
k)`. -/
theorem filterState_apply (m k : ZMod N) :
    filterState m k = ZMod.stdAddChar (-(m * k)) := by
  simp [filterState, basisState, ZMod.dft_apply]

/-- The inverse discrete Fourier transform of `filterState m` is `basisState m`. See
[NagajWocjanZhang2009]. -/
theorem filterState_reverse (m : ZMod N) :
    ZMod.dft.symm (filterState m) = basisState m := by
  simp [filterState]

/-- Filter states have inner product `N` when their labels agree and zero otherwise. See
[NagajWocjanZhang2009]. -/
theorem fip_filterState (m m' : ZMod N) :
    fip (filterState m) (filterState m') = if m = m' then (N : ℂ) else 0 := by
  have hterm : ∀ k : ZMod N,
      (starRingEnd ℂ) (filterState m k) * filterState m' k =
        ZMod.stdAddChar ((m - m') * k) := by
    intro k
    rw [filterState_apply, filterState_apply]
    rw [← AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) (-(m * k))]
    rw [neg_neg, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold fip
  simp only [hterm]
  by_cases h : m = m'
  · subst h
    simp [ZMod.card]
  · rw [if_neg h]
    have ht : m - m' ≠ 0 := sub_ne_zero.mpr h
    have hne : AddChar.mulShift (ZMod.stdAddChar (N := N)) (m - m') ≠ 1 :=
      ZMod.isPrimitive_stdAddChar N ht
    have hsum := AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply] using hsum

/-- The filter state scaled by the reciprocal of `√N`. -/
def normFilterState (m : ZMod N) : ZMod N → ℂ :=
  ((Real.sqrt (N : ℝ) : ℂ))⁻¹ • filterState m

/-- Normalized filter states have inner product one for equal labels and zero for distinct
labels. -/
theorem fip_normFilterState (m m' : ZMod N) :
    fip (normFilterState m) (normFilterState m') = if m = m' then 1 else 0 := by
  unfold normFilterState
  rw [fip_smul_smul, fip_filterState]
  have hs : (starRingEnd ℂ) (((Real.sqrt (N : ℝ) : ℂ))⁻¹) *
      ((Real.sqrt (N : ℝ) : ℂ))⁻¹ = ((N : ℝ) : ℂ)⁻¹ := by
    rw [starRingEnd_apply, Complex.star_def, ← Complex.ofReal_inv,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [show (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ = ((N : ℝ))⁻¹ by
      rw [← mul_inv, ← sq, Real.sq_sqrt (Nat.cast_nonneg N)]]
    exact Complex.ofReal_inv (N : ℝ)
  by_cases h : m = m'
  · rw [if_pos h, if_pos h, hs]
    have hN : ((N : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (NeZero.ne N)
    rw [show ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring]
    exact inv_mul_cancel₀ hN
  · rw [if_neg h, if_neg h, mul_zero]

/-- If `x = c • F + w`, with `F` normalized and orthogonal to `w`, then `fip F x = c`. -/
theorem expansion_coeff {ι : Type*} [Fintype ι] {F x w : ι → ℂ} (c : ℂ)
    (hF : fip F F = 1) (horth : fip F w = 0) (hx : x = c • F + w) :
    fip F x = c := by
  subst hx
  rw [fip_add, fip_smul_right, hF, horth, mul_one, add_zero]

/-- The two-component state with both amplitudes equal to `1 / √2`. -/
def phasePlus : Fin 2 → ℂ := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The state `phasePlus` has squared norm one under `fip`. -/
theorem phasePlus_norm : fip phasePlus phasePlus = 1 := by
  unfold fip phasePlus
  rw [Fin.sum_univ_two]
  have hs : (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, ← Complex.ofReal_inv,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) by
      rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
    norm_num
  rw [hs]
  norm_num

/-- The zero component of `phasePlus` has squared amplitude one half. See
[NagajWocjanZhang2009]. -/
theorem witness_branch_prob :
    (starRingEnd ℂ) (phasePlus 0) * phasePlus 0 = 1 / 2 := by
  have hs : (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (1 / 2 : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, ← Complex.ofReal_inv,
      Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [show (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) by
      rw [← mul_inv, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
    norm_num
  simpa [phasePlus] using hs

/-- The real-valued comparison cost `2 * r / (a - b) ^ 2`. -/
noncomputable def marriottWatrousCost (P : PromiseBounds) (r : ℕ) : ℝ :=
  2 * (r : ℝ) / (P.a - P.b) ^ 2

/-- The amplification cost is bounded by `marriottWatrousCost` times `5 * π * (√a + √b) * (a -
b)`. See [NagajWocjanZhang2009]. -/
theorem amplificationCost_le_ratio (P : PromiseBounds) (r : ℕ) :
    amplificationCost P r ≤
      (5 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (P.a - P.b)) *
        marriottWatrousCost P r := by
  have h := amplificationCost_le P r
  have hgap : P.a - P.b ≠ 0 := ne_of_gt P.gap_pos
  unfold marriottWatrousCost
  have heq : (5 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (P.a - P.b)) *
        (2 * (r : ℝ) / (P.a - P.b) ^ 2) =
      10 * Real.pi * (Real.sqrt P.a + Real.sqrt P.b) * (r : ℝ) / (P.a - P.b) := by
    field_simp
    ring
  linarith [h, heq.le, heq.ge]

end Qatlib.Papers.QMAAmplify09.MainResults.FilterWitness
