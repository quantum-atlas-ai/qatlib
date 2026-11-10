/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
import Qatlib.Papers.EntangleTrans99.MainResults.Majorization.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.EntangleTrans99.MainResults.TTransform

open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Papers.EntangleTrans99.MainResults.Majorization
open scoped BigOperators

theorem tTransformSpectrum_zero (spec : Fin 2 → ℝ) (θ : ℝ) :
    tTransformSpectrum spec θ 0 1 0 = θ * spec 0 + (1 - θ) * spec 1 := by
  simp [tTransformSpectrum]
  ring

theorem tTransformSpectrum_one (spec : Fin 2 → ℝ) (θ : ℝ) :
    tTransformSpectrum spec θ 0 1 1 = (1 - θ) * spec 0 + θ * spec 1 := by
  simp [tTransformSpectrum]
  ring

theorem outcomeCostBits_two : outcomeCostBits 2 = 1 := by
  unfold outcomeCostBits
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h2, div_self hlog]
  norm_num

theorem majorizes_tTransformSpectrum {a : Fin 2 → ℝ}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Majorizes a (tTransformSpectrum a θ 0 1) := by
  rw [majorizes_two_iff]
  constructor
  · rw [tTransformSpectrum_zero, tTransformSpectrum_one]
    refine max_le ?_ ?_
    · nlinarith [le_max_left (a 0) (a 1), le_max_right (a 0) (a 1)]
    · nlinarith [le_max_left (a 0) (a 1), le_max_right (a 0) (a 1)]
  · rw [tTransformSpectrum_zero, tTransformSpectrum_one]
    ring_nf
    linarith

theorem exists_tTransform_of_majorizes {a b : Fin 2 → ℝ}
    (ha : a 0 + a 1 = 1) (hb : b 0 + b 1 = 1)
    (hasort : a 1 ≤ a 0) (hbsort : b 1 ≤ b 0) (hmaj : Majorizes a b) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, b = tTransformSpectrum a θ 0 1 := by
  have hmax : max (b 0) (b 1) ≤ max (a 0) (a 1) :=
    (majorizes_two_iff_max_of_sum_one ha hb).1 hmaj
  have hmaxa : max (a 0) (a 1) = a 0 := max_eq_left hasort
  have hmaxb : max (b 0) (b 1) = b 0 := max_eq_left hbsort
  have hb0a0 : b 0 ≤ a 0 := by simpa [hmaxa, hmaxb] using hmax
  have ha1half : a 1 ≤ 2⁻¹ := by linarith
  have hb0half : 2⁻¹ ≤ b 0 := by linarith
  have hb0a1 : a 1 ≤ b 0 := le_trans ha1half hb0half
  rcases eq_or_lt_of_le hasort with heq | hlt
  · have ha0' : a 0 = 2⁻¹ := by linarith
    have ha1' : a 1 = 2⁻¹ := by linarith
    have hb0' : b 0 = 2⁻¹ := by
      have hle : b 0 ≤ 2⁻¹ := by simpa [← ha0'] using hb0a0
      have hle1 : b 1 ≤ 2⁻¹ := le_trans hbsort hle
      linarith
    have hb1' : b 1 = 2⁻¹ := by linarith
    refine ⟨0, by norm_num, ?_⟩
    funext j
    fin_cases j <;> simp [tTransformSpectrum, ha0', ha1', hb0', hb1']
  · have hden : a 0 - a 1 ≠ 0 := by linarith
    set θ : ℝ := (b 0 - a 1) / (a 0 - a 1) with hθdef
    have hθ0 : 0 ≤ θ := by
      rw [hθdef]
      exact div_nonneg (by linarith) (by linarith)
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one (by linarith)]
      linarith
    refine ⟨θ, ⟨hθ0, hθ1⟩, ?_⟩
    have hb0eq : b 0 = tTransformSpectrum a θ 0 1 0 := by
      rw [tTransformSpectrum_zero, hθdef]
      field_simp
      ring
    have hb1eq : b 1 = tTransformSpectrum a θ 0 1 1 := by
      have hsum_t : tTransformSpectrum a θ 0 1 0 + tTransformSpectrum a θ 0 1 1 = a 0 + a 1 := by
        rw [tTransformSpectrum_zero, tTransformSpectrum_one]
        ring
      rw [← hb0eq] at hsum_t
      linarith
    funext j
    fin_cases j
    · simpa using hb0eq
    · simpa using hb1eq

section GeneralDim

variable {D : ℕ}

theorem tTransformSpectrum_apply_k (spec : Fin D → ℝ) (θ : ℝ) {k l : Fin D}
    (hkl : k ≠ l) :
    tTransformSpectrum spec θ k l k = θ * spec k + (1 - θ) * spec l := by
  simp [tTransformSpectrum, hkl]
  ring

theorem tTransformSpectrum_apply_l (spec : Fin D → ℝ) (θ : ℝ) {k l : Fin D}
    (hkl : k ≠ l) :
    tTransformSpectrum spec θ k l l = (1 - θ) * spec k + θ * spec l := by
  simp [tTransformSpectrum, Ne.symm hkl]
  ring

theorem tTransformSpectrum_other (spec : Fin D → ℝ) (θ : ℝ) {k l j : Fin D}
    (hjk : j ≠ k) (hjl : j ≠ l) :
    tTransformSpectrum spec θ k l j = spec j := by
  simp [tTransformSpectrum, hjk, hjl]

theorem tTransformSpectrum_sum (spec : Fin D → ℝ) (θ : ℝ) (k l : Fin D) :
    (∑ j, tTransformSpectrum spec θ k l j) = ∑ j, spec j := by
  simp only [tTransformSpectrum]
  rw [Finset.sum_add_distrib]
  have hpair : (∑ j : Fin D, ((if j = k then spec l - spec k else 0)
        + (if j = l then spec k - spec l else 0))) = 0 := by
    rw [Finset.sum_add_distrib]
    simp
  rw [← Finset.mul_sum, hpair]
  ring

theorem tTransformSpectrum_nonneg (spec : Fin D → ℝ) {θ : ℝ} {k l : Fin D}
    (hkl : k ≠ l) (hspec : ∀ j, 0 ≤ spec j) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ j, 0 ≤ tTransformSpectrum spec θ k l j := by
  intro j
  by_cases hjk : j = k
  · rw [hjk, tTransformSpectrum_apply_k spec θ hkl]
    nlinarith [hspec k, hspec l]
  · by_cases hjl : j = l
    · rw [hjl, tTransformSpectrum_apply_l spec θ hkl]
      nlinarith [hspec k, hspec l]
    · rw [tTransformSpectrum_other spec θ hjk hjl]
      exact hspec j

theorem branchSpectrum_tTransformInstrument_zero (spec : Fin D → ℝ)
    (p θ : ℝ) {k l : Fin D}
    (hfilter : ∀ j, tTransformFilter spec p θ k l j ≤ 1)
    (hfilter0 : ∀ j, 0 ≤ tTransformFilter spec p θ k l j)
    (hmass : branchMass (tTransformInstrument D spec p θ k l hfilter hfilter0) spec 0 = p)
    (hp : p ≠ 0) (j : Fin D) (hspecj : spec j ≠ 0) :
    branchSpectrum (tTransformInstrument D spec p θ k l hfilter hfilter0) spec 0 j
      = tTransformSpectrum spec θ k l j := by
  have hentry : (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j
      = Real.sqrt (tTransformFilter spec p θ k l j) := by
    simp [tTransformInstrument]
  have hsq : (tTransformInstrument D spec p θ k l hfilter hfilter0).entry 0 j ^ 2
      = tTransformFilter spec p θ k l j := by
    rw [hentry, Real.sq_sqrt (hfilter0 j)]
  unfold branchSpectrum
  rw [hmass, hsq]
  unfold tTransformFilter
  field_simp [hp, hspecj]

end GeneralDim

end Qatlib.Papers.EntangleTrans99.MainResults.TTransform
