/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAAmplify09.MainResults.Defs
import Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

open Qatlib.Papers.QMAAmplify09.MainResults.Defs
open Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification

namespace Qatlib.Papers.QMAAmplify09.MainResults.FilterWitness

def fip {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (x i) * y i

theorem fip_add {ι : Type*} [Fintype ι] (x y z : ι → ℂ) :
    fip x (y + z) = fip x y + fip x z := by
  unfold fip
  simp only [Pi.add_apply, mul_add, sum_add_distrib]

theorem fip_smul_right {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c : ℂ) :
    fip x (c • y) = c * fip x y := by
  unfold fip
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fip_smul_left {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c : ℂ) :
    fip (c • x) y = (starRingEnd ℂ) c * fip x y := by
  unfold fip
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fip_smul_smul {ι : Type*} [Fintype ι] (x y : ι → ℂ) (c d : ℂ) :
    fip (c • x) (d • y) = (starRingEnd ℂ) c * d * fip x y := by
  rw [fip_smul_left, fip_smul_right]
  ring

variable {N : ℕ} [NeZero N]

def basisState (m : ZMod N) : ZMod N → ℂ := fun j => if j = m then 1 else 0

def filterState (m : ZMod N) : ZMod N → ℂ := ZMod.dft (basisState m)

theorem filterState_apply (m k : ZMod N) :
    filterState m k = ZMod.stdAddChar (-(m * k)) := by
  simp [filterState, basisState, ZMod.dft_apply]

theorem filterState_reverse (m : ZMod N) :
    ZMod.dft.symm (filterState m) = basisState m := by
  simp [filterState]

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

def normFilterState (m : ZMod N) : ZMod N → ℂ :=
  ((Real.sqrt (N : ℝ) : ℂ))⁻¹ • filterState m

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

theorem expansion_coeff {ι : Type*} [Fintype ι] {F x w : ι → ℂ} (c : ℂ)
    (hF : fip F F = 1) (horth : fip F w = 0) (hx : x = c • F + w) :
    fip F x = c := by
  subst hx
  rw [fip_add, fip_smul_right, hF, horth, mul_one, add_zero]

def phasePlus : Fin 2 → ℂ := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

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

noncomputable def marriottWatrousCost (P : PromiseBounds) (r : ℕ) : ℝ :=
  2 * (r : ℝ) / (P.a - P.b) ^ 2

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
