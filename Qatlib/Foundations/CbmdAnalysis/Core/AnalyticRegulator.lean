/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.FiniteResidue
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section

namespace CBMD

open Complex Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem diffContOnCl_dslope {F : ℂ → E} {c a : ℂ} {R : ℝ}
    (hF : DiffContOnCl ℂ F (ball c R)) (ha : a ∈ ball c R) :
    DiffContOnCl ℂ (dslope F a) (ball c R) := by
  apply DiffContOnCl.mk_ball
  · exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr
      hF.differentiableOn
  · exact (continuousOn_dslope (closedBall_mem_nhds_of_mem ha)).mpr
      ⟨hF.continuousOn_ball, hF.differentiableAt isOpen_ball ha⟩

theorem extract_finite_simple_zeros (s : Finset ℂ) {c : ℂ} {R : ℝ}
    (h : ℂ → ℂ) (hh : DiffContOnCl ℂ h (ball c R))
    (hinside : ∀ p ∈ s, p ∈ ball c R)
    (hzeros : ∀ z ∈ closedBall c R, h z = 0 ↔ z ∈ s)
    (hsimple : ∀ p ∈ s, deriv h p ≠ 0) :
    ∃ g : ℂ → ℂ, DiffContOnCl ℂ g (ball c R) ∧
      (∀ z, h z = (∏ p ∈ s, (z - p)) * g z) ∧
      (∀ z ∈ closedBall c R, g z ≠ 0) := by
  classical
  induction s using Finset.induction_on generalizing h with
  | empty =>
    refine ⟨h, hh, ?_, ?_⟩
    · intro z
      simp
    · intro z hz
      simpa only [Finset.notMem_empty, iff_false] using hzeros z hz
  | @insert a s ha ih =>
    have haB : a ∈ ball c R := hinside a (Finset.mem_insert_self a s)
    have hha : h a = 0 := (hzeros a (ball_subset_closedBall haB)).mpr
      (Finset.mem_insert_self a s)
    let k := dslope h a
    have hk : DiffContOnCl ℂ k (ball c R) := diffContOnCl_dslope hh haB
    have hfactor (z : ℂ) : h z = (z - a) * k z := by
      simpa only [k, smul_eq_mul, hha, sub_zero] using (sub_smul_dslope h a z).symm
    have hkzeros (z : ℂ) (hz : z ∈ closedBall c R) : k z = 0 ↔ z ∈ s := by
      by_cases hza : z = a
      · subst z
        simp only [k, dslope_same]
        simp [hsimple a (Finset.mem_insert_self a s), ha]
      · have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
        have hf := hzeros z hz
        rw [hfactor z, mul_eq_zero, or_iff_right hza'] at hf
        simpa only [Finset.mem_insert, hza, false_or] using hf
    have hksimple (p : ℂ) (hp : p ∈ s) : deriv k p ≠ 0 := by
      have hpB := hinside p (Finset.mem_insert_of_mem hp)
      have hkp : k p = 0 := (hkzeros p (ball_subset_closedBall hpB)).mpr hp
      have hd := (((hasDerivAt_id p).sub_const a).mul
        (hk.differentiableAt isOpen_ball hpB).hasDerivAt).deriv
      change deriv (fun z => (z - a) * k z) p = 1 * k p + (p - a) * deriv k p at hd
      have heq : h = fun z => (z - a) * k z := funext hfactor
      rw [← heq] at hd
      simp only [one_mul, hkp, zero_add] at hd
      intro he
      apply hsimple p (Finset.mem_insert_of_mem hp)
      rw [hd, he, mul_zero]
    obtain ⟨g, hg, hkg, hgzero⟩ := ih k hk
      (fun p hp => hinside p (Finset.mem_insert_of_mem hp)) hkzeros hksimple
    refine ⟨g, hg, ?_, hgzero⟩
    intro z
    rw [hfactor, hkg, Finset.prod_insert ha, mul_assoc]

theorem circleIntegral_analytic_regulator (s : Finset ℂ) {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (F : ℂ → E) (h : ℂ → ℂ)
    (hF : DiffContOnCl ℂ F (ball c R))
    (hh : DiffContOnCl ℂ h (ball c R))
    (hinside : ∀ p ∈ s, p ∈ ball c R)
    (hzeros : ∀ z ∈ closedBall c R, h z = 0 ↔ z ∈ s)
    (hsimple : ∀ p ∈ s, deriv h p ≠ 0) :
    (∮ z in C(c, R), (h z)⁻¹ • F z) =
      (2 * Real.pi * I : ℂ) • ∑ p ∈ s, (deriv h p)⁻¹ • F p := by
  classical
  obtain ⟨g, hg, hfactor, hgzero⟩ :=
    extract_finite_simple_zeros s h hh hinside hzeros hsimple
  have hGF : DiffContOnCl ℂ (fun z => (g z)⁻¹ • F z) (ball c R) :=
    (hg.inv (fun z hz => hgzero z (closure_ball_subset_closedBall hz))).smul hF
  have hintegrand : (fun z => (h z)⁻¹ • F z) =
      (fun z => (∏ p ∈ s, (z - p))⁻¹ • ((g z)⁻¹ • F z)) := by
    funext z
    rw [hfactor z, mul_inv, smul_smul]
  rw [hintegrand]
  by_cases hs : s.Nonempty
  · have hcauchy := circleIntegral_finite_simple_poles s id hs
      Function.injective_id.injOn hGF hinside
    simp only [id_eq] at hcauchy
    rw [hcauchy]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have heq : h = fun z => (Lagrange.nodal s id).eval z * g z := by
      funext z
      simpa only [Lagrange.eval_nodal, id_eq] using hfactor z
    have hd := (((Lagrange.nodal s id).hasDerivAt p).mul
      (hg.differentiableAt isOpen_ball (hinside p hp)).hasDerivAt).deriv
    change deriv (fun z => (Lagrange.nodal s id).eval z * g z) p =
      (Lagrange.nodal s id).derivative.eval p * g p +
        (Lagrange.nodal s id).eval p * deriv g p at hd
    rw [← heq] at hd
    have heval := Lagrange.eval_nodal_at_node (v := id) hp
    have hderiv := Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hp
    simp only [id_eq] at heval hderiv
    rw [heval, zero_mul, add_zero, hderiv, Lagrange.eval_nodal] at hd
    simp only [id_eq] at hd
    rw [hd, mul_inv, smul_smul]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simpa only [Finset.prod_empty, inv_one, one_smul, Finset.sum_empty, smul_zero]
      using hGF.circleIntegral_eq_zero hR

theorem cbmd_analytic_regulator_circle (s : Finset ℂ) (p₀ : ℂ) (hp₀ : p₀ ∈ s)
    {c : ℂ} {R : ℝ} (F : ℂ → E) (h : ℂ → ℂ)
    (hF : DiffContOnCl ℂ F (ball c R))
    (hh : DiffContOnCl ℂ h (ball c R))
    (hinside : ∀ p ∈ s, p ∈ ball c R)
    (hzeros : ∀ z ∈ closedBall c R, h z = 0 ↔ z ∈ s)
    (hsimple : ∀ p ∈ s, deriv h p ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ •
        (∮ z in C(c, R), deriv h p₀ • ((h z)⁻¹ • F z)) =
      F p₀ + ∑ p ∈ s.erase p₀, (deriv h p₀ * (deriv h p)⁻¹) • F p := by
  classical
  have hR : 0 ≤ R := (lt_of_le_of_lt dist_nonneg (hinside p₀ hp₀)).le
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [circleIntegral.integral_smul,
    circleIntegral_analytic_regulator s hR F h hF hh hinside hzeros hsimple]
  rw [smul_comm (deriv h p₀), inv_smul_smul₀ hC]
  rw [← Finset.add_sum_erase _ _ hp₀, smul_add, smul_smul,
    mul_inv_cancel₀ (hsimple p₀ hp₀), one_smul, Finset.smul_sum]
  simp only [smul_smul]

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
