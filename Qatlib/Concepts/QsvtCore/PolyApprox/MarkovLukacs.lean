/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacsAtoms
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Markov–Lukács representations for positive polynomials

`strict_positive_induction` reduces properties of real polynomials strictly positive on `[0, 1]`
to positive constants, linear factors with roots outside the interval, nonreal-root quadratics,
and multiplication. This factorization argument constructs degree-indexed Markov–Lukács
representations.

These interval positivity certificates provide algebraic ingredients for the polynomial
completion results used in quantum signal processing. See [GilyenSuLowWiebe2019].

## Main statements

* `exists_positive_root_factor`: remove a positive linear or quadratic factor and lower degree.
* `strict_positive_induction`: induct over strictly positive polynomials using those factors.
* `exists_rep_of_pos`: obtain a representation at any valid degree bound.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

/-- A real polynomial strictly positive on `[0, 1]` is nonzero. -/
theorem ne_zero_of_pos_on_unit_interval {f : Polynomial ℝ}
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t) : f ≠ 0 := by
  intro hf
  have h := hpos 0 (by constructor <;> norm_num)
  simp [hf] at h

/-- If a product and its first factor are strictly positive on `[0, 1]`, then its second factor
is strictly positive there. -/
theorem quotient_pos_on_unit_interval {f a g : Polynomial ℝ}
    (hfg : f = a * g)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a.eval t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < g.eval t := by
  intro t ht
  have hf' := hf t ht
  have ha' := ha t ht
  rw [hfg, Polynomial.eval_mul] at hf'
  by_contra! hg
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos ha'.le hg
  exact (not_lt_of_ge hnonpos) hf'

/-- Every real root of a polynomial strictly positive on `[0, 1]` lies below zero or above one. -/
theorem real_root_outside_unit_interval {f : Polynomial ℝ}
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t)
    {r : ℝ} (hr : f.IsRoot r) : r < 0 ∨ 1 < r := by
  by_contra! hout
  have h := hpos r ⟨hout.1, hout.2⟩
  rw [hr] at h
  exact (lt_irrefl 0) h

/-- A complex root of a real polynomial with zero imaginary part gives a real root at its real
part. -/
theorem real_isRoot_of_aeval_of_im_eq_zero {f : Polynomial ℝ} {z : ℂ}
    (hz : aeval z f = 0) (him : z.im = 0) : f.IsRoot z.re := by
  have heq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  apply Polynomial.isRoot_of_aeval_algebraMap_eq_zero (S := ℂ)
  change aeval (z.re : ℂ) f = 0
  rwa [heq]

/-- If `r` is a root of a real polynomial, then `C r - X` divides that polynomial. -/
theorem C_sub_X_dvd_of_isRoot {f : Polynomial ℝ} {r : ℝ}
    (hr : f.IsRoot r) : C r - X ∣ f := by
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  refine ⟨-g, ?_⟩
  rw [hg]
  ring

/-- A monic real polynomial of the form `X^2 - C u * X + C v` has natural degree two. -/
theorem root_quadratic_natDegree (u v : ℝ) :
    (X ^ 2 - C u * X + C v : Polynomial ℝ).natDegree = 2 := by
  have h : (X ^ 2 - C u * X + C v : Polynomial ℝ) =
      C (1 : ℝ) * X ^ 2 + C (-u) * X + C v := by
    simp only [map_one, one_mul, map_neg]
    ring
  rw [h]
  exact Polynomial.natDegree_quadratic one_ne_zero

/-- The real polynomial `C r - X` has natural degree one. -/
theorem C_sub_X_natDegree (r : ℝ) : (C r - X : Polynomial ℝ).natDegree = 1 := by
  have h : (C r - X : Polynomial ℝ) = -(X - C r) := by ring
  rw [h, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

/-- A nonconstant polynomial strictly positive on `[0, 1]` factors into a linear factor with a
root outside the interval or a nonreal-root quadratic, and a strictly positive quotient of
smaller natural degree. -/
theorem exists_positive_root_factor (f : Polynomial ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t)
    (hdegree : 0 < f.natDegree) :
    ∃ a g : Polynomial ℝ,
      f = a * g ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < g.eval t) ∧
      0 < a.natDegree ∧ g.natDegree < f.natDegree ∧
      ((∃ r : ℝ, r < 0 ∧ a = X - C r) ∨
       (∃ r : ℝ, 1 < r ∧ a = C r - X) ∨
       (∃ z : ℂ, z.im ≠ 0 ∧
         a = X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2))) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ f
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree))
  by_cases him : z.im = 0
  · have hr := real_isRoot_of_aeval_of_im_eq_zero hz him
    rcases real_root_outside_unit_interval hpos hr with hleft | hright
    · obtain ⟨g, hfg⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      have ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (X - C z.re).eval t := by
        intro t ht
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        linarith [ht.1]
      have hg := quotient_pos_on_unit_interval hfg hpos ha
      have hg0 := ne_zero_of_pos_on_unit_interval hg
      have ha0 := ne_zero_of_pos_on_unit_interval ha
      have hdeg : f.natDegree = 1 + g.natDegree := by
        rw [hfg, Polynomial.natDegree_mul ha0 hg0, Polynomial.natDegree_X_sub_C]
      refine ⟨X - C z.re, g, hfg, hg, ?_, ?_, Or.inl ⟨z.re, hleft, rfl⟩⟩
      · rw [Polynomial.natDegree_X_sub_C]
        norm_num
      · omega
    · obtain ⟨g, hfg⟩ := C_sub_X_dvd_of_isRoot hr
      have ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (C z.re - X).eval t := by
        intro t ht
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        linarith [ht.2]
      have hg := quotient_pos_on_unit_interval hfg hpos ha
      have hg0 := ne_zero_of_pos_on_unit_interval hg
      have ha0 := ne_zero_of_pos_on_unit_interval ha
      have hdeg : f.natDegree = 1 + g.natDegree := by
        rw [hfg, Polynomial.natDegree_mul ha0 hg0, C_sub_X_natDegree]
      refine ⟨C z.re - X, g, hfg, hg, ?_, ?_, Or.inr (Or.inl ⟨z.re, hright, rfl⟩)⟩
      · rw [C_sub_X_natDegree]
        norm_num
      · omega
  · obtain ⟨g, hfg⟩ := f.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
    let a : Polynomial ℝ := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)
    have ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < a.eval t := by
      intro t _
      dsimp only [a]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg (t - z.re), sq_pos_of_ne_zero him]
    have hg := quotient_pos_on_unit_interval hfg hpos ha
    have hg0 := ne_zero_of_pos_on_unit_interval hg
    have ha0 := ne_zero_of_pos_on_unit_interval ha
    have had : a.natDegree = 2 := root_quadratic_natDegree _ _
    have hdeg : f.natDegree = 2 + g.natDegree := by
      change f = a * g at hfg
      rw [hfg, Polynomial.natDegree_mul ha0 hg0, had]
    refine ⟨a, g, hfg, hg, ?_, ?_, Or.inr (Or.inr ⟨z, him, rfl⟩)⟩
    · omega
    · omega

/-- A property holding for positive constants, positive linear factors with roots outside `[0,
1]`, and nonreal-root quadratics, and preserved by nonzero multiplication, holds for every
polynomial strictly positive on `[0, 1]`. -/
theorem strict_positive_induction (M : Polynomial ℝ → Prop)
    (hC : ∀ c : ℝ, 0 < c → M (C c))
    (hleft : ∀ r : ℝ, r < 0 → M (X - C r))
    (hright : ∀ r : ℝ, 1 < r → M (C r - X))
    (hquad : ∀ z : ℂ, z.im ≠ 0 →
      M (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)))
    (hmul : ∀ a g : Polynomial ℝ, a ≠ 0 → g ≠ 0 → M a → M g → M (a * g))
    (f : Polynomial ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t) : M f := by
  have main : ∀ (n : ℕ) (p : Polynomial ℝ), p.natDegree = n →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < p.eval t) → M p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp
      by_cases hn0 : n = 0
      · have hpC : p = C (p.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero (hn.trans hn0)
        have hc : 0 < p.coeff 0 := by
          have h := hp 0 (by constructor <;> norm_num)
          rwa [← Polynomial.coeff_zero_eq_eval_zero] at h
        rw [hpC]
        exact hC _ hc
      · have hdegree : 0 < p.natDegree := by omega
        obtain ⟨a, g, hpg, hgpos, had, hgd, hatom⟩ :=
          exists_positive_root_factor p hp hdegree
        have ha0 : a ≠ 0 := by
          intro ha
          simp [ha] at had
        have hg0 := ne_zero_of_pos_on_unit_interval hgpos
        have hg : M g := ih g.natDegree (by omega) g rfl hgpos
        have ha : M a := by
          rcases hatom with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨z, hz, rfl⟩
          · exact hleft r hr
          · exact hright r hr
          · exact hquad z hz
        rw [hpg]
        exact hmul a g ha0 hg0 ha hg
  exact main f.natDegree f rfl hpos

/-- Every real polynomial strictly positive on `[0, 1]` possesses a Markov–Lukács representation
indexed by its natural degree. -/
theorem exists_rep_of_pos_natDegree (f : Polynomial ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t) :
    Nonempty (Representation f.natDegree f) := by
  refine strict_positive_induction
    (fun p => Nonempty (Representation p.natDegree p)) ?_ ?_ ?_ ?_ ?_ f hpos
  · intro c hc
    rw [Polynomial.natDegree_C]
    exact ⟨repConst c hc.le⟩
  · intro r hr
    rw [Polynomial.natDegree_X_sub_C]
    exact ⟨repLinearLeft r hr.le⟩
  · intro r hr
    rw [C_sub_X_natDegree]
    exact ⟨repLinearRight r hr.le⟩
  · intro z _
    rw [root_quadratic_natDegree]
    exact ⟨repQuadratic z⟩
  · intro a g ha0 hg0 ha hg
    obtain ⟨ra⟩ := ha
    obtain ⟨rg⟩ := hg
    rw [Polynomial.natDegree_mul ha0 hg0]
    exact ⟨repMul ra rg⟩

/-- Every real polynomial strictly positive on `[0, 1]` possesses a Markov–Lukács representation
indexed by any natural upper bound on its degree. -/
theorem exists_rep_of_pos (f : Polynomial ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f.eval t)
    {d : ℕ} (hd : f.degree ≤ (d : WithBot ℕ)) :
    Nonempty (Representation d f) := by
  obtain ⟨r⟩ := exists_rep_of_pos_natDegree f hpos
  exact ⟨repMono (Polynomial.natDegree_le_of_degree_le hd) r⟩

end Qatlib.Concepts.QsvtCore.PolyApprox
