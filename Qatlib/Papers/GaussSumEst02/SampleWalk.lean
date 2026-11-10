/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset

namespace Qatlib.Papers.GaussSumEst02.SampleWalk

open Qatlib.Papers.GaussSumEst02.MainResults.Source

variable {K : Type*} [Field K]

def walkStep (χ : MultChar K) (e : AddChar K) (x : K) : ℂ :=
  χ.toFun x * e.toFun x

theorem walkStep_zero (χ : MultChar K) (e : AddChar K) : walkStep χ e 0 = 0 := by
  simp [walkStep, χ.map_zero']

theorem norm_walkStep [Fintype K] (χ : MultChar K) (e : AddChar K) {x : K} (hx : x ≠ 0) :
    ‖walkStep χ e x‖ = 1 := by
  rw [walkStep, norm_mul, χ.norm_eq_one x hx, e.norm_eq_one x, one_mul]

theorem sum_walkStep_eq_gaussSum [Fintype K] (χ : MultChar K) (e : AddChar K) :
    (∑ x : K, walkStep χ e x) = gaussSum χ.toFun e 1 := by
  rw [gaussSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [walkStep]

theorem norm_sum_walkStep [Fintype K] (χ : MultChar K) (e : AddChar K)
    (hnt : χ.IsNontrivial) :
    ‖∑ x : K, walkStep χ e x‖ = Real.sqrt (Fintype.card K : ℝ) := by
  rw [sum_walkStep_eq_gaussSum, gaussSum_norm χ e hnt one_ne_zero]

def meanStep [Fintype K] (χ : MultChar K) (e : AddChar K) : ℂ :=
  gaussSum χ.toFun e 1 / (((Fintype.card K - 1 : ℕ) : ℝ) : ℂ)

theorem norm_meanStep [Fintype K] (χ : MultChar K) (e : AddChar K) (hnt : χ.IsNontrivial) :
    ‖meanStep χ e‖
      = Real.sqrt (Fintype.card K : ℝ) / (((Fintype.card K - 1 : ℕ) : ℝ)) := by
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hpos : (0 : ℝ) < (((Fintype.card K - 1 : ℕ) : ℝ)) := by
    have : 0 < Fintype.card K - 1 := by omega
    exact_mod_cast this
  rw [meanStep, norm_div, gaussSum_norm χ e hnt one_ne_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos]

theorem sum_normSq_walkStep [Fintype K] (χ : MultChar K) (e : AddChar K) :
    (∑ x : K, ‖walkStep χ e x‖ ^ 2) = (((Fintype.card K - 1 : ℕ) : ℝ)) := by
  classical
  have hstep : ∀ x : K, x ≠ 0 → ‖walkStep χ e x‖ ^ 2 = 1 := by
    intro x hx
    rw [norm_walkStep χ e hx, one_pow]
  have hzero : ‖walkStep χ e 0‖ ^ 2 = 0 := by
    rw [walkStep_zero, norm_zero]
    norm_num
  have herase : (∑ x ∈ Finset.univ.erase (0 : K), ‖walkStep χ e x‖ ^ 2)
      = ∑ x : K, ‖walkStep χ e x‖ ^ 2 := by
    refine Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro x _ hx
    have hx0 : x = 0 := by
      by_contra h
      exact hx (Finset.mem_erase.mpr ⟨h, Finset.mem_univ x⟩)
    rw [hx0, hzero]
  rw [← herase, Finset.sum_congr rfl (fun x hx => hstep x (Finset.mem_erase.mp hx).1),
    Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ (0 : K)),
    Finset.card_univ, mul_one]

theorem biasSq_mul [Fintype K] (χ : MultChar K) (e : AddChar K) (hnt : χ.IsNontrivial) (M : ℝ) :
    M * ‖meanStep χ e‖ ^ 2
      = M * ((Fintype.card K : ℝ) / (((Fintype.card K - 1 : ℕ) : ℝ)) ^ 2) := by
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hpos : (0 : ℝ) < (((Fintype.card K - 1 : ℕ) : ℝ)) := by
    have : 0 < Fintype.card K - 1 := by omega
    exact_mod_cast this
  rw [norm_meanStep χ e hnt, div_pow, Real.sq_sqrt (by positivity)]

theorem biasSq_mul_lt_one [Fintype K] (χ : MultChar K) (e : AddChar K) (hnt : χ.IsNontrivial)
    {M : ℝ} (hM : M < ((Fintype.card K - 1 : ℕ) : ℝ) ^ 2 / (Fintype.card K : ℝ)) :
    M * ‖meanStep χ e‖ ^ 2 < 1 := by
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hp : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℝ) < (((Fintype.card K - 1 : ℕ) : ℝ)) := by
    have : 0 < Fintype.card K - 1 := by omega
    exact_mod_cast this
  rw [biasSq_mul χ e hnt]
  have hM' : M * (Fintype.card K : ℝ) < (((Fintype.card K - 1 : ℕ) : ℝ)) ^ 2 := by
    rw [lt_div_iff₀ hp] at hM
    linarith
  have hpos2 : (0 : ℝ) < (((Fintype.card K - 1 : ℕ) : ℝ)) ^ 2 := by positivity
  rw [mul_div_assoc', div_lt_one hpos2]
  exact hM'

theorem sum_char_mul_conj_shift [Fintype K] (χ : MultChar K) (hnt : χ.IsNontrivial) {s : K}
    (hs : s ≠ 0) :
    (∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x + s ≠ 0),
        χ.toFun (x / (x + s))) = -1 := by
  classical
  have hbij : (∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x + s ≠ 0),
        χ.toFun (x / (x + s)))
      = ∑ t ∈ Finset.univ.filter (fun t : K => t ≠ 0 ∧ t ≠ 1), χ.toFun t := by
    refine Finset.sum_nbij' (fun x : K => x / (x + s)) (fun t : K => t * s / (1 - t))
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨ha0, has⟩ := ha
      refine ⟨div_ne_zero ha0 has, ?_⟩
      intro h
      rw [div_eq_one_iff_eq has] at h
      exact hs (add_left_cancel (h.symm.trans (add_zero a).symm))
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨ha0, ha1⟩ := ha
      have h1 : (1 : K) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      refine ⟨div_ne_zero (mul_ne_zero ha0 hs) h1, ?_⟩
      have hcalc : a * s / (1 - a) + s = s / (1 - a) := by
        field_simp
        ring
      rw [hcalc]
      exact div_ne_zero hs h1
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨ha0, has⟩ := ha
      have h1 : (1 : K) - a / (a + s) ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        have h' : a / (a + s) = 1 := h.symm
        rw [div_eq_one_iff_eq has] at h'
        exact hs (add_left_cancel (h'.symm.trans (add_zero a).symm))
      field_simp [hs]
      ring
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨ha0, ha1⟩ := ha
      have h1 : (1 : K) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      have hden : a * s / (1 - a) + s ≠ 0 := by
        have hcalc : a * s / (1 - a) + s = s / (1 - a) := by
          field_simp
          ring
        rw [hcalc]
        exact div_ne_zero hs h1
      field_simp
      ring
    · intro a _
      rfl
  rw [hbij]

  have hfull : (∑ t : K, χ.toFun t) = 0 := multChar_sum_eq_zero χ hnt
  have hne0 : (∑ t ∈ Finset.univ.filter (fun t : K => t ≠ 0), χ.toFun t) = 0 := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset K))
      (f := fun t : K => χ.toFun t) (Finset.mem_univ (0 : K))
    rw [hfull] at h
    simp only [χ.map_zero', add_zero] at h
    have heq : Finset.univ.erase (0 : K) = Finset.univ.filter (fun t : K => t ≠ 0) := by
      ext t
      simp [Finset.mem_erase]
    rw [heq] at h
    exact h

  have hfin : (∑ t ∈ Finset.univ.filter (fun t : K => t ≠ 0 ∧ t ≠ 1), χ.toFun t) = -1 := by
    have hmem : (1 : K) ∈ Finset.univ.filter (fun t : K => t ≠ 0) := by simp
    have h := Finset.sum_erase_add (s := Finset.univ.filter (fun t : K => t ≠ 0))
      (f := fun t : K => χ.toFun t) hmem
    rw [hne0] at h
    simp only [χ.map_one'] at h
    have heq : (Finset.univ.filter (fun t : K => t ≠ 0)).erase 1
        = Finset.univ.filter (fun t : K => t ≠ 0 ∧ t ≠ 1) := by
      ext t
      simp [Finset.mem_erase, and_comm]
    rw [heq] at h
    linear_combination h
  exact hfin

theorem sum_walkStep_conj_shift [Fintype K] (χ : MultChar K) (e : AddChar K) (hnt : χ.IsNontrivial)
    {s : K} (hs : s ≠ 0) :
    (∑ x : K, walkStep χ e x * conj (walkStep χ e (x + s))) = - e.toFun (-s) := by
  classical
  have hterm : ∀ x : K, walkStep χ e x * conj (walkStep χ e (x + s))
      = if x = 0 ∨ x + s = 0 then 0
        else χ.toFun (x / (x + s)) * e.toFun (-s) := by
    intro x
    by_cases hx : x = 0
    · rw [if_pos (Or.inl hx), hx, walkStep_zero, zero_mul]
    · by_cases hxs : x + s = 0
      · rw [if_pos (Or.inr hxs), hxs, walkStep_zero, map_zero, mul_zero]
      · rw [if_neg (by tauto)]
        have hχinv : conj (χ.toFun (x + s)) = χ.toFun ((x + s)⁻¹) := by
          rw [χ.conj_apply hxs, χ.inv_apply hxs]
        have he : e.toFun x * conj (e.toFun (x + s)) = e.toFun (-s) := by
          rw [e.conj_apply, ← e.map_add']
          congr 1
          ring
        have hmul : χ.toFun x * χ.toFun ((x + s)⁻¹) = χ.toFun (x / (x + s)) := by
          rw [div_eq_mul_inv, ← χ.map_mul']
        simp only [walkStep, map_mul, hχinv]
        rw [← hmul, ← he]
        ring
  have hfilter : (∑ x : K, walkStep χ e x * conj (walkStep χ e (x + s)))
      = ∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x + s ≠ 0),
          χ.toFun (x / (x + s)) * e.toFun (-s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hterm]
    by_cases h : x = 0 ∨ x + s = 0
    · rw [if_pos h, if_neg (by tauto)]
    · rw [if_neg h, if_pos (by tauto)]
  rw [hfilter, ← Finset.sum_mul, sum_char_mul_conj_shift χ hnt hs]
  ring

end Qatlib.Papers.GaussSumEst02.SampleWalk
