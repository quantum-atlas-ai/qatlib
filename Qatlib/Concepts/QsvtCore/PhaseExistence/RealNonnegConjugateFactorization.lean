/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacsNonnegative
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Mathlib.Data.Real.Sqrt
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

private theorem real_square_root_factor {f : Polynomial ℝ}
    (hf : ∀ x : ℝ, 0 ≤ f.eval x) {r : ℝ} (hr : f.IsRoot r) :
    ∃ g : Polynomial ℝ, f = (X - C r) ^ 2 * g ∧ ∀ x : ℝ, 0 ≤ g.eval x := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hr
  have hl : ∀ t ∈ Set.Ioo (r - 1) r, q.eval t ≤ 0 := by
    intro t ht
    have h := hf t
    rw [hq, eval_mul, eval_sub, eval_X, eval_C] at h
    by_contra! hqt
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos (sub_neg.mpr ht.2) hqt)
  have hu : ∀ t ∈ Set.Ioo r (r + 1), 0 ≤ q.eval t := by
    intro t ht
    apply quotient_nonneg_at hq t (hf t)
    simpa using sub_pos.mpr ht.1
  have hqr : q.IsRoot r := le_antisymm
    (nonpos_on_Icc_of_nonpos_on_Ioo (by linarith) hl r ⟨by linarith, le_rfl⟩)
    (nonneg_on_Icc_of_nonneg_on_Ioo (by linarith) hu r ⟨le_rfl, by linarith⟩)
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hqr
  have hfg : f = (X - C r) ^ 2 * g := by rw [hq, hg]; ring
  have haway : ∀ x : ℝ, x ≠ r → 0 ≤ g.eval x := by
    intro x hx
    apply quotient_nonneg_at hfg x (hf x)
    simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
  refine ⟨g, hfg, fun x => ?_⟩
  by_cases hx : x = r
  · subst x
    exact nonneg_on_Icc_of_nonneg_on_Ioo (by linarith : r < r + 1)
      (fun t ht => haway t ht.1.ne') r ⟨le_rfl, by linarith⟩
  · exact haway x hx

private theorem conjugate_factor_mul {f g : Polynomial ℝ}
    (hf : ∃ W : Polynomial ℂ, W * conjugatePolynomial W = f.map Complex.ofRealHom)
    (hg : ∃ W : Polynomial ℂ, W * conjugatePolynomial W = g.map Complex.ofRealHom) :
    ∃ W : Polynomial ℂ, W * conjugatePolynomial W = (f * g).map Complex.ofRealHom := by
  obtain ⟨U, hU⟩ := hf
  obtain ⟨V, hV⟩ := hg
  refine ⟨U * V, ?_⟩
  rw [conjugatePolynomial_mul, Polynomial.map_mul, ← hU, ← hV]
  ring

private theorem real_quadratic_conjugate_factor (z : ℂ) :
    (X - C z) * conjugatePolynomial (X - C z) =
      (rootQuadratic z).map Complex.ofRealHom := by
  simp only [conjugatePolynomial_sub, conjugatePolynomial_X, conjugatePolynomial_C,
    rootQuadratic, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_mul, map_X, map_C]
  have ha : C z + C (star z) = C (Complex.ofReal (2 * z.re)) := by
    rw [← C_add]
    congr 1
    exact Complex.add_conj z
  have hm : C z * C (star z) = C (Complex.ofReal (‖z‖ ^ 2)) := by
    rw [← C_mul, Complex.sq_norm]
    congr 1
    exact Complex.mul_conj z
  calc
    (X - C z) * (X - C (star z)) = X ^ 2 - (C z + C (star z)) * X +
        C z * C (star z) := by ring
    _ = _ := by rw [ha, hm]; rfl

theorem exists_conjugate_factor_of_nonneg (f : Polynomial ℝ)
    (hf : ∀ x : ℝ, 0 ≤ f.eval x) :
    ∃ W : Polynomial ℂ,
      W * Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial W = f.map Complex.ofRealHom := by
  have main : ∀ n : ℕ, ∀ f : Polynomial ℝ, f.natDegree = n →
      (∀ x : ℝ, 0 ≤ f.eval x) →
      ∃ W : Polynomial ℂ, W * conjugatePolynomial W = f.map Complex.ofRealHom := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp
      by_cases hp0 : p = 0
      · exact ⟨0, by simp [hp0]⟩
      by_cases hn0 : n = 0
      · have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (hn.trans hn0)
        have hc : 0 ≤ p.coeff 0 := by simpa [← coeff_zero_eq_eval_zero] using hp 0
        refine ⟨C (Complex.ofReal (Real.sqrt (p.coeff 0))), ?_⟩
        rw [hpC]
        simp only [coeff_C_zero]
        simp only [conjugatePolynomial_C, Complex.star_def, Complex.conj_ofReal,
          ← C_mul, ← Complex.ofReal_mul, map_C]
        rw [← pow_two, Real.sq_sqrt hc]
        rfl
      have hpd : 0 < p.natDegree := by omega
      have finish (a g : Polynomial ℝ) (hpg : p = a * g)
          (hg : ∀ x : ℝ, 0 ≤ g.eval x) (ha : 0 < a.natDegree)
          (hw : ∃ W : Polynomial ℂ, W * conjugatePolynomial W = a.map Complex.ofRealHom) :
          ∃ W : Polynomial ℂ, W * conjugatePolynomial W = p.map Complex.ofRealHom := by
        have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
        have hg0 : g ≠ 0 := by intro hz; apply hp0; simp [hpg, hz]
        have hdeg : p.natDegree = a.natDegree + g.natDegree := by
          rw [hpg, natDegree_mul ha0 hg0]
        obtain ⟨V, hV⟩ := ih g.natDegree (by omega) g rfl hg
        rw [hpg]
        exact conjugate_factor_mul hw ⟨V, hV⟩
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p
        (ne_of_gt (natDegree_pos_iff_degree_pos.mp hpd))
      by_cases him : z.im = 0
      · obtain ⟨g, hpg, hg⟩ := real_square_root_factor hp
          (real_isRoot_of_aeval_of_im_eq_zero hz him)
        apply finish ((X - C z.re) ^ 2) g hpg hg
        · simp
        · refine ⟨X - C (Complex.ofReal z.re), ?_⟩
          simp [pow_two]
      · obtain ⟨g, hpg⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
        apply finish (rootQuadratic z) g hpg
        · intro x
          exact quotient_nonneg_at hpg x (hp x) (rootQuadratic_pos z him x)
        · rw [rootQuadratic, root_quadratic_natDegree]
          norm_num
        · exact ⟨X - C z, real_quadratic_conjugate_factor z⟩
  exact main f.natDegree f rfl hf

end Qatlib.Concepts.QsvtCore.PhaseExistence
