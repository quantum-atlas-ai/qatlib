/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset

def clamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

lemma clamp_mem {lo hi x : ℝ} (hlo : lo ≤ hi) : clamp lo hi x ∈ Set.Icc lo hi := by
  constructor
  · exact le_max_left _ _
  · unfold clamp
    exact max_le hlo (min_le_left _ _)

lemma abs_clamp_sub_le {lo hi lam x : ℝ} (hlo : lo ≤ hi) (hlam : lam ∈ Set.Icc lo hi) :
    |clamp lo hi x - lam| ≤ |x - lam| := by
  obtain ⟨hlam_lo, hlam_hi⟩ := hlam
  by_cases h1 : x ≤ lo
  · have hc : clamp lo hi x = lo := by
      unfold clamp
      rw [min_eq_right (le_trans h1 hlo), max_eq_left h1]
    rw [hc]
    rw [abs_of_nonpos (by linarith : lo - lam ≤ 0),
      abs_of_nonpos (by linarith : x - lam ≤ 0)]
    linarith
  · rw [not_le] at h1
    by_cases h2 : hi ≤ x
    · have hc : clamp lo hi x = hi := by
        unfold clamp
        rw [min_eq_left h2, max_eq_right hlo]
      rw [hc]
      rw [abs_of_nonneg (by linarith : 0 ≤ hi - lam),
        abs_of_nonneg (by linarith : 0 ≤ x - lam)]
      linarith
    · rw [not_le] at h2
      have hc : clamp lo hi x = x := by
        unfold clamp
        rw [min_eq_right (le_of_lt h2), max_eq_right (le_of_lt h1)]
      rw [hc]

theorem lemma1_ideal_error {Ω : Type*} [Fintype Ω]
    (q : Ω → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1)
    (post : Ω → ℝ) (target M K θ η : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (good : Finset Ω)
    (hmass : 1 - θ ≤ ∑ a ∈ good, q a)
    (hgood : ∀ a ∈ good, |post a - target| ≤ 2 * Real.pi * η * K)
    (hbad : ∀ a, a ∉ good → |post a - target| ≤ 2 * M) :
    |∑ a, q a * post a - target| ≤ 2 * θ * M + 2 * Real.pi * K * η := by
  classical

  have hgood_le_one : ∑ a ∈ good, q a ≤ 1 := by
    rw [← hq1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      (fun a _ _ => hq0 a)

  have hbad_mass : ∑ a ∈ Finset.univ \ good, q a ≤ θ := by
    have hsd := Finset.sum_sdiff (s₁ := good) (s₂ := Finset.univ) (f := q)
      (Finset.subset_univ good)
    rw [hq1] at hsd
    linarith

  have hshift : ∑ a, q a * post a - target = ∑ a, q a * (post a - target) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul]
  rw [hshift]

  have hsplit : ∑ a, q a * (post a - target) =
      ∑ a ∈ good, q a * (post a - target) +
        ∑ a ∈ Finset.univ \ good, q a * (post a - target) := by
    have hsd := Finset.sum_sdiff (s₁ := good) (s₂ := Finset.univ)
      (f := fun a => q a * (post a - target)) (Finset.subset_univ good)
    rw [← hsd, add_comm]
  rw [hsplit]
  have hgood_le : |∑ a ∈ good, q a * (post a - target)| ≤
      (∑ a ∈ good, q a) * (2 * Real.pi * η * K) := by
    calc |∑ a ∈ good, q a * (post a - target)|
        ≤ ∑ a ∈ good, |q a * (post a - target)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ good, q a * (2 * Real.pi * η * K) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [abs_mul, abs_of_nonneg (hq0 a)]
          exact mul_le_mul_of_nonneg_left (hgood a ha) (hq0 a)
      _ = (∑ a ∈ good, q a) * (2 * Real.pi * η * K) := by
          rw [Finset.sum_mul]
  have hbad_le : |∑ a ∈ Finset.univ \ good,
        q a * (post a - target)| ≤ (∑ a ∈ Finset.univ \ good, q a) * (2 * M) := by
    calc |∑ a ∈ Finset.univ \ good, q a * (post a - target)|
        ≤ ∑ a ∈ Finset.univ \ good, |q a * (post a - target)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.univ \ good, q a * (2 * M) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [abs_mul, abs_of_nonneg (hq0 a)]
          exact mul_le_mul_of_nonneg_left
            (hbad a (Finset.mem_sdiff.mp ha).2) (hq0 a)
      _ = (∑ a ∈ Finset.univ \ good, q a) * (2 * M) := by
          rw [Finset.sum_mul]
  have htri := abs_add_le (∑ a ∈ good, q a * (post a - target))
    (∑ a ∈ Finset.univ \ good, q a * (post a - target))
  have hA : |∑ a ∈ good, q a * (post a - target)| ≤ 2 * Real.pi * η * K := by
    have := mul_le_mul_of_nonneg_right hgood_le_one
      (by positivity : (0:ℝ) ≤ 2 * Real.pi * η * K)
    linarith
  have hB : |∑ a ∈ Finset.univ \ good, q a * (post a - target)| ≤ 2 * θ * M := by
    have := mul_le_mul_of_nonneg_right hbad_mass (by positivity : (0:ℝ) ≤ 2 * M)
    linarith
  linarith [htri, hA, hB]

theorem lemma1_mixture_error {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (e : ι → ℝ) (E : ℝ) (hE : 0 ≤ E) (h : ∀ j, |e j| ≤ E) :
    |∑ j, w j * e j| ≤ E := by
  calc |∑ j, w j * e j| ≤ ∑ j, |w j * e j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, w j * |e j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hw0 j)]
    _ ≤ ∑ j, w j * E :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hw0 j)
    _ = (∑ j, w j) * E := by rw [Finset.sum_mul]
    _ = E := by rw [hw1, one_mul]

theorem lemma1_distribution_error {Ω : Type*} [Fintype Ω]
    (q qt post : Ω → ℝ) (D M : ℝ) (hM : 0 ≤ M)
    (hD : ∑ a, |q a - qt a| ≤ D) (hpost : ∀ a, |post a| ≤ M) :
    |∑ a, q a * post a - ∑ a, qt a * post a| ≤ D * M := by
  have hdiff : ∑ a, q a * post a - ∑ a, qt a * post a =
      ∑ a, (q a - qt a) * post a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hdiff]
  calc |∑ a, (q a - qt a) * post a| ≤ ∑ a, |(q a - qt a) * post a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |q a - qt a| * |post a| := by
        simp only [abs_mul]
    _ ≤ ∑ a, |q a - qt a| * M :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hpost a) (abs_nonneg _)
    _ = (∑ a, |q a - qt a|) * M := by rw [Finset.sum_mul]
    _ ≤ D * M := mul_le_mul_of_nonneg_right hD hM

theorem lemma1_error_bound {Ω : Type*} [Fintype Ω]
    (q qt post : Ω → ℝ) (target M K θ η D : ℝ) (hM : 0 ≤ M)
    (hideal : |∑ a, qt a * post a - target| ≤ 2 * θ * M + 2 * Real.pi * K * η)
    (hD : ∑ a, |q a - qt a| ≤ D) (hpost : ∀ a, |post a| ≤ M) :
    |∑ a, q a * post a - target| ≤ (2 * θ + D) * M + 2 * Real.pi * K * η := by
  have hpert := lemma1_distribution_error q qt post D M hM hD hpost
  have htri : |∑ a, q a * post a - target| ≤
      |∑ a, q a * post a - ∑ a, qt a * post a| +
        |∑ a, qt a * post a - target| := by
    rw [show ∑ a, q a * post a - target =
        (∑ a, q a * post a - ∑ a, qt a * post a) +
          (∑ a, qt a * post a - target) by ring]
    exact abs_add_le _ _
  have hsum : D * M + (2 * θ * M + 2 * Real.pi * K * η) =
      (2 * θ + D) * M + 2 * Real.pi * K * η := by ring
  linarith [htri, hpert, hideal, hsum]

theorem lemma1_continuous_functional_calculus {Ω : Type*} [Fintype Ω]
    (q qt : Ω → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hqt0 : ∀ a, 0 ≤ qt a)
    (hq1 : ∑ a, q a = 1) (hqt1 : ∑ a, qt a = 1)
    (outcome : Ω → ℝ) (lo hi : ℝ) (hlo : lo ≤ hi) (lam : ℝ)
    (hlam : lam ∈ Set.Icc lo hi) (f : ℝ → ℝ) (K M θ η D : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hlip : ∀ x ∈ Set.Icc lo hi, |f x - f lam| ≤ K * |x - lam|)
    (hbound : ∀ x ∈ Set.Icc lo hi, |f x| ≤ M)
    (good : Finset Ω)
    (hmass : 1 - θ ≤ ∑ a ∈ good, qt a)
    (hdev : ∀ a ∈ good, |outcome a - lam| < 2 * Real.pi * η)
    (hD : ∑ a, |q a - qt a| ≤ D) :
    |∑ a, q a * f (clamp lo hi (outcome a)) - f lam| ≤
      (2 * θ + D) * M + 2 * Real.pi * K * η := by
  classical
  have hpost : ∀ a, |f (clamp lo hi (outcome a))| ≤ M := fun a =>
    hbound _ (clamp_mem hlo)
  refine lemma1_error_bound q qt (fun a => f (clamp lo hi (outcome a))) (f lam)
    M K θ η D hM ?_ hD hpost
  refine lemma1_ideal_error qt hqt0 hqt1
    (fun a => f (clamp lo hi (outcome a))) (f lam) M K θ η hM hK hθ hη good hmass ?_ ?_
  · intro a ha
    have hcx : clamp lo hi (outcome a) ∈ Set.Icc lo hi := clamp_mem hlo
    have h1 : |f (clamp lo hi (outcome a)) - f lam| ≤ K * |clamp lo hi (outcome a) - lam| :=
      hlip _ hcx
    have h2 : |clamp lo hi (outcome a) - lam| ≤ |outcome a - lam| :=
      abs_clamp_sub_le hlo hlam
    have h3 : |outcome a - lam| < 2 * Real.pi * η := hdev a ha
    have h4 : K * |clamp lo hi (outcome a) - lam| ≤ K * (2 * Real.pi * η) :=
      mul_le_mul_of_nonneg_left (le_trans h2 (le_of_lt h3)) hK
    have h5 : K * (2 * Real.pi * η) = 2 * Real.pi * η * K := by ring
    linarith
  · intro a _
    have hcx : clamp lo hi (outcome a) ∈ Set.Icc lo hi := clamp_mem hlo
    have h1 : |f (clamp lo hi (outcome a))| ≤ M := hbound _ hcx
    have h2 : |f lam| ≤ M := hbound _ hlam
    have h3 : |f (clamp lo hi (outcome a)) - f lam| ≤
        |f (clamp lo hi (outcome a))| + |f lam| := by
      have h := abs_add_le (f (clamp lo hi (outcome a))) (-(f lam))
      simpa using! h
    linarith

theorem lemma1_delta_bound {Ω : Type*} [Fintype Ω]
    (q qt : Ω → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hqt0 : ∀ a, 0 ≤ qt a)
    (hq1 : ∑ a, q a = 1) (hqt1 : ∑ a, qt a = 1)
    (outcome : Ω → ℝ) (lo hi : ℝ) (hlo : lo ≤ hi) (lam : ℝ)
    (hlam : lam ∈ Set.Icc lo hi) (f : ℝ → ℝ) (K M θ η : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hlip : ∀ x ∈ Set.Icc lo hi, |f x - f lam| ≤ K * |x - lam|)
    (hbound : ∀ x ∈ Set.Icc lo hi, |f x| ≤ M)
    (good : Finset Ω)
    (hmass : 1 - θ ≤ ∑ a ∈ good, qt a)
    (hdev : ∀ a ∈ good, |outcome a - lam| < 2 * Real.pi * η)
    (p : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∑ a, |q a - qt a| ≤ (2 : ℝ) ^ (p + 2) * δ) :
    |∑ a, q a * f (clamp lo hi (outcome a)) - f lam| ≤
      (2 * θ + (2 : ℝ) ^ (p + 2) * δ) * M + 2 * Real.pi * K * η :=
  lemma1_continuous_functional_calculus q qt hq0 hqt0 hq1 hqt1 outcome lo hi hlo lam hlam f
    K M θ η ((2 : ℝ) ^ (p + 2) * δ) hK hM hθ hη hlip hbound good hmass hdev hD

end Qatlib.Papers.BQPMixSparse06.MainResults
