/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm.SamplingParameters

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm

variable {H : Type*} [Fintype H] [DecidableEq H]

def measuredSubsetMass (M : H → H → ℝ) (L : Finset H) : ℝ :=
  (Fintype.card H : ℝ)⁻¹ * ∑ h, ∑ h' ∈ L, M h' h

theorem near_uniform_subset_lower (M : H → H → ℝ) (η : ℝ) (L : Finset H)
    (hMsum : ∀ h, ∑ h', M h' h = 1)
    (hMnonneg : ∀ h h', 0 ≤ M h h')
    (hMcorrect : ∀ h, 1 - η ≤ M h h) :
    (Fintype.card H : ℝ)⁻¹ * (L.card : ℝ) * (1 - η) ≤ measuredSubsetMass M L := by
  have hpoint : ∀ h, (if h ∈ L then (1 : ℝ) else 0) * (1 - η) ≤ ∑ h' ∈ L, M h' h := by
    intro h
    by_cases hh : h ∈ L
    · rw [if_pos hh, one_mul]
      exact (hMcorrect h).trans
        (Finset.single_le_sum (f := fun h' => M h' h) (fun h' _ => hMnonneg h' h) hh)
    · rw [if_neg hh, zero_mul]
      exact Finset.sum_nonneg fun h' _ => hMnonneg h' h
  have hsum : (∑ h : H, (if h ∈ L then (1 : ℝ) else 0) * (1 - η))
      ≤ ∑ h : H, ∑ h' ∈ L, M h' h :=
    Finset.sum_le_sum (fun h _ => hpoint h)
  have hcard : (∑ h : H, (if h ∈ L then (1 : ℝ) else 0)) = (L.card : ℝ) := by
    have hnat : L.card = ∑ h : H, if h ∈ L then (1 : ℕ) else 0 := by
      rw [Finset.card_eq_sum_ite (Finset.subset_univ L)]
    rw [hnat, Nat.cast_sum]
    simp
  rw [← Finset.sum_mul, hcard] at hsum
  unfold measuredSubsetMass
  rw [show (Fintype.card H : ℝ)⁻¹ * (L.card : ℝ) * (1 - η)
      = (Fintype.card H : ℝ)⁻¹ * ((L.card : ℝ) * (1 - η)) by ring]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem near_uniform_subset_upper (M : H → H → ℝ) (η : ℝ) (L : Finset H)
    (hq : 0 < Fintype.card H) (hη : 0 ≤ η)
    (hMsum : ∀ h, ∑ h', M h' h = 1)
    (hMnonneg : ∀ h h', 0 ≤ M h h')
    (hMcorrect : ∀ h, 1 - η ≤ M h h) :
    measuredSubsetMass M L ≤ (Fintype.card H : ℝ)⁻¹ * (L.card : ℝ) + η := by
  have hpoint : ∀ h, (∑ h' ∈ L, M h' h) ≤ (if h ∈ L then (1 : ℝ) else 0) + η := by
    intro h
    by_cases hh : h ∈ L
    · rw [if_pos hh]
      have hle : ∑ h' ∈ L, M h' h ≤ ∑ h', M h' h :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
          (fun x _ _ => hMnonneg x h)
      rw [hMsum h] at hle
      linarith
    · rw [if_neg hh, zero_add]
      have hsub : ∑ h' ∈ L, M h' h ≤ ∑ h' ∈ Finset.univ.erase h, M h' h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          intro hxh
          exact hh (hxh ▸ hx)
        · intro x _ _; exact hMnonneg x h
      have hsplit : ∑ h' ∈ Finset.univ.erase h, M h' h = 1 - M h h := by
        have h1 := Finset.add_sum_erase (Finset.univ : Finset H)
          (fun h' => M h' h) (Finset.mem_univ h)
        rw [hMsum h] at h1
        linarith
      have hgap : 1 - M h h ≤ η := by linarith [hMcorrect h]
      rw [hsplit] at hsub
      linarith
  have hsum : (∑ h : H, ∑ h' ∈ L, M h' h)
      ≤ ∑ h : H, ((if h ∈ L then (1 : ℝ) else 0) + η) :=
    Finset.sum_le_sum (fun h _ => hpoint h)
  have hcard : (∑ h : H, (if h ∈ L then (1 : ℝ) else 0)) = (L.card : ℝ) := by
    have hnat : L.card = ∑ h : H, if h ∈ L then (1 : ℕ) else 0 := by
      rw [Finset.card_eq_sum_ite (Finset.subset_univ L)]
    rw [hnat, Nat.cast_sum]
    simp
  have hsum2 : (∑ h : H, ((if h ∈ L then (1 : ℝ) else 0) + η))
      = (L.card : ℝ) + (Fintype.card H : ℝ) * η := by
    rw [Finset.sum_add_distrib, hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum2] at hsum
  unfold measuredSubsetMass
  have hqR : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast hq
  have hstep : (Fintype.card H : ℝ)⁻¹ * (∑ h, ∑ h' ∈ L, M h' h)
      ≤ (Fintype.card H : ℝ)⁻¹ * ((L.card : ℝ) + (Fintype.card H : ℝ) * η) :=
    mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hqR.le)
  have hsimpl : (Fintype.card H : ℝ)⁻¹ * ((L.card : ℝ) + (Fintype.card H : ℝ) * η)
      = (Fintype.card H : ℝ)⁻¹ * (L.card : ℝ) + η := by
    field_simp
  linarith [hstep]

theorem near_uniform_maximal_proper (M : H → H → ℝ) (η : ℝ) (L : Finset H)
    (hq : 0 < Fintype.card H) (hη : 0 ≤ η)
    (hMsum : ∀ h, ∑ h', M h' h = 1)
    (hMnonneg : ∀ h h', 0 ≤ M h h')
    (hMcorrect : ∀ h, 1 - η ≤ M h h)
    (hLhalf : 2 * (L.card : ℝ) ≤ (Fintype.card H : ℝ)) :
    measuredSubsetMass M L ≤ 1 / 2 + η := by
  have hupper := near_uniform_subset_upper M η L hq hη hMsum hMnonneg hMcorrect
  have hqR : (0 : ℝ) < (Fintype.card H : ℝ) := by exact_mod_cast hq
  have hratio : (Fintype.card H : ℝ)⁻¹ * (L.card : ℝ) ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hqR]
    linarith
  linarith

end Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm
