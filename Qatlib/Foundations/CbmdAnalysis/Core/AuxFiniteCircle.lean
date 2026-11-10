/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AuxRegulator
import Qatlib.Foundations.CbmdAnalysis.Core.KernelPoleSet
import Qatlib.Foundations.CbmdAnalysis.Core.AnalyticRegulator
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open Metric Complex
open scoped BigOperators Topology

noncomputable def auxPoleSet (s : Finset ℂ) (a : ℝ) (n : ℕ) : Finset ℂ := by
  classical
  exact insert (-Complex.I) (s ∪ integerRealPoleSet a n)

theorem mem_auxPoleSet_iff (s : Finset ℂ) (a : ℝ) (n : ℕ) (z : ℂ) :
    z ∈ auxPoleSet s a n ↔ z = -Complex.I ∨ z ∈ s ∨
      ∃ k ∈ Finset.Icc (-(n : ℤ)) n, z = (((k : ℝ) / a : ℝ) : ℂ) := by
  classical
  simp only [auxPoleSet, integerRealPoleSet, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  aesop

theorem auxPoleSet_inside (s : Finset ℂ) {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : 1 < ((n : ℝ) + 1 / 2) / a)
    (hsInside : ∀ p ∈ s, ‖p‖ < ((n : ℝ) + 1 / 2) / a) :
    ∀ z ∈ auxPoleSet s a n, z ∈ ball (0 : ℂ) (((n : ℝ) + 1 / 2) / a) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  rcases (mem_auxPoleSet_iff s a n z).mp hz with htarget | hp | ⟨k, hk, hlat⟩
  · subst z
    simpa only [norm_neg, Complex.norm_I] using! hR
  · exact hsInside z hp
  · subst z
    exact lattice_norm_lt_halfgrid ha n k hk

theorem auxContourDenominator_disk_zeros (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (((n : ℝ) + 1 / 2) / a)) :
    auxContourDenominator s a z = 0 ↔ z ∈ auxPoleSet s a n := by
  rw [auxContourDenominator_eq_zero_iff s hs ha z, mem_auxPoleSet_iff]
  constructor
  · rintro (htarget | hp | ⟨k, hlat⟩)
    · exact Or.inl htarget
    · exact Or.inr (Or.inl hp)
    · refine Or.inr (Or.inr ⟨k, ?_, hlat⟩)
      apply (lattice_norm_le_halfgrid_iff ha n k).mp
      rw [← hlat]
      simpa only [Metric.mem_closedBall, dist_zero_right] using! hz
  · rintro (htarget | hp | ⟨k, _, hlat⟩)
    · exact Or.inl htarget
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨k, hlat⟩)

theorem auxContourDenominator_sphere_ne_zero (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hR : 1 < ((n : ℝ) + 1 / 2) / a)
    (hsInside : ∀ p ∈ s, ‖p‖ < ((n : ℝ) + 1 / 2) / a)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (((n : ℝ) + 1 / 2) / a)) :
    auxContourDenominator s a z ≠ 0 := by
  intro hzero
  have hmem := (auxContourDenominator_disk_zeros s hs ha n z (sphere_subset_closedBall hz)).mp hzero
  have hinside := auxPoleSet_inside s ha n hR hsInside z hmem
  have he : ‖z‖ = ((n : ℝ) + 1 / 2) / a := by
    simpa only [Metric.mem_sphere, dist_zero_right] using! hz
  have hlt : ‖z‖ < ((n : ℝ) + 1 / 2) / a := by
    simpa only [Metric.mem_ball, dist_zero_right] using! hinside
  linarith

theorem auxPoleSet_aux_real_disjoint (s : Finset ℂ) (a : ℝ)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ)) (n : ℕ) :
    Disjoint s (integerRealPoleSet a n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hs hz
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hz
  exact hsLattice z hs k hk.symm

theorem auxPoleSet_target_not_mem (s : Finset ℂ) (hs : -Complex.I ∉ s) (a : ℝ) (n : ℕ) :
    -Complex.I ∉ s ∪ integerRealPoleSet a n := by
  classical
  intro h
  rcases Finset.mem_union.mp h with hp | hlat
  · exact hs hp
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hlat
    have hi := congrArg Complex.im hk
    norm_num at hi

theorem auxPoleSet_sum {M : Type*} [AddCommMonoid M] (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ))
    (n : ℕ) (f : ℂ → M) :
    (∑ z ∈ auxPoleSet s a n, f z) =
      f (-Complex.I) + (∑ p ∈ s, f p) +
        ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f (((k : ℝ) / a : ℝ) : ℂ) := by
  classical
  rw [auxPoleSet, Finset.sum_insert (auxPoleSet_target_not_mem s hs a n),
    Finset.sum_union (auxPoleSet_aux_real_disjoint s a hsLattice n)]
  simp only [integerRealPoleSet]
  rw [Finset.sum_image (fun k _ l _ h => integerRealPole_injective ha h)]
  ac_rfl

section Numerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def auxSample (s : Finset ℂ) (a : ℝ) (U : ℂ → E) (k : ℤ) : E :=
  auxWeight s a k • U (((k : ℝ) / a : ℝ) : ℂ)

noncomputable def auxLCUSum (s : Finset ℂ) (a : ℝ) (n : ℕ) (U : ℂ → E) : E :=
  ∑ k ∈ Finset.Icc (-(n : ℤ)) n, auxSample s a U k

noncomputable def auxiliaryCorrection (s : Finset ℂ) (a : ℝ) (U : ℂ → E) : E :=
  ∑ p ∈ s, auxResidueCoefficient s a p • U p

variable [CompleteSpace E]

theorem auxContour_circle_identity (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ)) (n : ℕ)
    (hR : 1 < ((n : ℝ) + 1 / 2) / a)
    (hsInside : ∀ p ∈ s, ‖p‖ < ((n : ℝ) + 1 / 2) / a)
    (U : ℂ → E) (hU : Differentiable ℂ U) :
    (∮ z in C(0, ((n : ℝ) + 1 / 2) / a), auxContourIntegrand s a U z) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        (U (-Complex.I) - auxLCUSum s a n U + auxiliaryCorrection s a U) := by
  classical
  let c : ℂ := ((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)
  have hR0 : 0 ≤ ((n : ℝ) + 1 / 2) / a := by positivity
  have hinside := auxPoleSet_inside s ha n hR hsInside
  have hzeros := auxContourDenominator_disk_zeros s hs ha n
  have hsimple : ∀ p ∈ auxPoleSet s a n, deriv (auxContourDenominator s a) p ≠ 0 := by
    intro p hp
    have hz : auxContourDenominator s a p = 0 :=
      (hzeros p (ball_subset_closedBall (hinside p hp))).mpr hp
    exact auxContourDenominator_deriv_ne_zero_of_eq_zero s hs ha hsLattice p hz
  have hF : Differentiable ℂ (fun z => c • U z) := (differentiable_const c).smul hU
  have hC := circleIntegral_analytic_regulator (auxPoleSet s a n) hR0
    (fun z => c • U z) (auxContourDenominator s a) hF.diffContOnCl
    (auxContourDenominator_differentiable s a).diffContOnCl hinside hzeros hsimple
  have heq : (fun z => auxContourIntegrand s a U z) =
      (fun z => (auxContourDenominator s a z)⁻¹ • (c • U z)) := by
    funext z
    exact auxContourIntegrand_eq_denominator s a U z
  rw [heq, hC]
  congr 1
  have hcoef (p : ℂ) : (deriv (auxContourDenominator s a) p)⁻¹ • (c • U p) =
      (c / deriv (auxContourDenominator s a) p) • U p := by
    rw [smul_smul]
    congr 1
    ring
  simp_rw [hcoef]
  rw [auxPoleSet_sum s hs ha hsLattice n]
  have haux : (∑ p ∈ s, (c / deriv (auxContourDenominator s a) p) • U p) =
      ∑ p ∈ s, auxResidueCoefficient s a p • U p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [show c / deriv (auxContourDenominator s a) p = auxResidueCoefficient s a p from
      auxContour_coefficient_pole s hs a p hp]
  rw [haux]
  dsimp [c]
  rw [auxContour_coefficient_neg_I s hs ha, one_smul]
  simp_rw [auxContour_coefficient_lattice s ha, neg_smul]
  rw [Finset.sum_neg_distrib]
  unfold auxLCUSum auxSample auxiliaryCorrection
  abel

theorem auxContour_circle_identity_normalized (s : Finset ℂ) (hs : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ)) (n : ℕ)
    (hR : 1 < ((n : ℝ) + 1 / 2) / a)
    (hsInside : ∀ p ∈ s, ‖p‖ < ((n : ℝ) + 1 / 2) / a)
    (U : ℂ → E) (hU : Differentiable ℂ U) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      (∮ z in C(0, ((n : ℝ) + 1 / 2) / a), auxContourIntegrand s a U z) =
        U (-Complex.I) - auxLCUSum s a n U + auxiliaryCorrection s a U := by
  rw [auxContour_circle_identity s hs ha hsLattice n hR hsInside U hU,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

end Numerator
end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
