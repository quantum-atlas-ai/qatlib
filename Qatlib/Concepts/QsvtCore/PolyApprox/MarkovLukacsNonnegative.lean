/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PolyApprox.MarkovLukacs
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed

/-!
# Nonnegative polynomial representations

This module proves that every real polynomial nonnegative on `[0, 1]` possesses a degree-bounded
Markov–Lukács representation. The proof removes represented factors while preserving
nonnegativity, using square divisibility at interior roots and continuity at endpoints. Such
interval-positivity certificates support polynomial constructions in quantum singular value
transformation [GilyenSuLowWiebe2019].

## Main statements

* `sq_X_sub_C_dvd_of_nonneg_on_unit_interval`: The square of an interior root factor divides a
  nonnegative polynomial.
* `exists_rep_of_nonneg_natDegree`: Construct a representation at the polynomial's natural
  degree.
* `exists_rep_of_nonneg`: Construct a representation at any prescribed degree bound.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.QsvtCore.PolyApprox

open Polynomial

/-- Nonnegativity of a real polynomial on a nonempty open interval extends to its closed
interval. -/
theorem nonneg_on_Icc_of_nonneg_on_Ioo {p : Polynomial ℝ} {a b : ℝ}
    (hab : a < b) (hp : ∀ t ∈ Set.Ioo a b, 0 ≤ p.eval t) :
    ∀ t ∈ Set.Icc a b, 0 ≤ p.eval t := by
  intro t ht
  exact le_on_closure hp continuous_const.continuousOn p.continuousOn
    (by rwa [closure_Ioo hab.ne])

/-- Nonpositivity of a real polynomial on a nonempty open interval extends to its closed
interval. -/
theorem nonpos_on_Icc_of_nonpos_on_Ioo {p : Polynomial ℝ} {a b : ℝ}
    (hab : a < b) (hp : ∀ t ∈ Set.Ioo a b, p.eval t ≤ 0) :
    ∀ t ∈ Set.Icc a b, p.eval t ≤ 0 := by
  intro t ht
  exact le_on_closure hp p.continuousOn continuous_const.continuousOn
    (by rwa [closure_Ioo hab.ne])

/-- A polynomial nonnegative on `[0, 1]` except possibly at one interior point is nonnegative
throughout the interval. -/
theorem nonneg_on_Icc_of_nonneg_except {p : Polynomial ℝ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ r → 0 ≤ p.eval t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.eval t := by
  intro t ht
  by_cases htr : t = r
  · subst t
    apply nonneg_on_Icc_of_nonneg_on_Ioo hr0 _ r ⟨hr0.le, le_rfl⟩
    intro x hx
    exact hp x ⟨hx.1.le, hx.2.le.trans hr1.le⟩ hx.2.ne
  · exact hp t ht htr

/-- If `f = a * g`, nonnegativity of `f` and strict positivity of `a` at `t` imply nonnegativity
of `g` there. -/
theorem quotient_nonneg_at {f a g : Polynomial ℝ} (hfg : f = a * g)
    (t : ℝ) (hf : 0 ≤ f.eval t) (ha : 0 < a.eval t) : 0 ≤ g.eval t := by
  rw [hfg, Polynomial.eval_mul] at hf
  by_contra! hg
  exact (not_lt_of_ge hf) (mul_neg_of_pos_of_neg ha hg)

/-- Factoring out a polynomial strictly positive on `(0, 1)` preserves nonnegativity on `[0,
1]`. -/
theorem quotient_nonneg_on_unit_interval {f a g : Polynomial ℝ}
    (hfg : f = a * g)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t)
    (ha : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < a.eval t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval t := by
  apply nonneg_on_Icc_of_nonneg_on_Ioo (by norm_num : (0 : ℝ) < 1)
  intro t ht
  exact quotient_nonneg_at hfg t (hf t ⟨ht.1.le, ht.2.le⟩) (ha t ht)

/-- The square of the linear factor at an interior root divides a polynomial nonnegative on `[0,
1]`. -/
theorem sq_X_sub_C_dvd_of_nonneg_on_unit_interval {f : Polynomial ℝ}
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hr : f.IsRoot r) :
    (X - C r) ^ 2 ∣ f := by
  obtain ⟨g, hfg⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hleft : ∀ t ∈ Set.Ioo (0 : ℝ) r, g.eval t ≤ 0 := by
    intro t ht
    have hp := hf t ⟨ht.1.le, ht.2.le.trans hr1.le⟩
    rw [hfg, eval_mul, eval_sub, eval_X, eval_C] at hp
    by_contra! hg
    exact (not_lt_of_ge hp) (mul_neg_of_neg_of_pos (sub_neg.mpr ht.2) hg)
  have hright : ∀ t ∈ Set.Ioo r (1 : ℝ), 0 ≤ g.eval t := by
    intro t ht
    apply quotient_nonneg_at hfg t (hf t ⟨hr0.le.trans ht.1.le, ht.2.le⟩)
    simp only [eval_sub, eval_X, eval_C]
    exact sub_pos.mpr ht.1
  have hle := nonpos_on_Icc_of_nonpos_on_Ioo hr0 hleft r ⟨hr0.le, le_rfl⟩
  have hge := nonneg_on_Icc_of_nonneg_on_Ioo hr1 hright r ⟨le_rfl, hr1.le⟩
  have hgroot : g.IsRoot r := le_antisymm hle hge
  obtain ⟨q, hgq⟩ := Polynomial.dvd_iff_isRoot.mpr hgroot
  refine ⟨q, ?_⟩
  rw [hfg, hgq]
  ring

/-- Removing the square of an interior linear root factor preserves nonnegativity on `[0, 1]`. -/
theorem quotient_nonneg_of_interior_square {f g : Polynomial ℝ} {r : ℝ}
    (hfg : f = (X - C r) ^ 2 * g)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval t := by
  apply nonneg_on_Icc_of_nonneg_except hr0 hr1
  intro t ht htr
  apply quotient_nonneg_at hfg t (hf t ht)
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact sq_pos_of_ne_zero (sub_ne_zero.mpr htr)

/-- The even Markov–Lukács representation of `(X - C r) ^ 2` with components `X - C r` and zero. -/
noncomputable def squareLinear (r : ℝ) : EvenRep 1 ((X - C r) ^ 2) where
  a := X - C r
  b := 0
  identity := by simp
  degreeA := (degree_X_sub_C r).le
  degreeB := by simp

/-- The degree-two Markov–Lukács representation of the square of a linear factor. -/
noncomputable def repSquareLinear (r : ℝ) : Representation 2 ((X - C r) ^ 2) :=
  squareLinear r

/-- A polynomial of positive natural degree that is nonnegative on `[0, 1]` factors into a
represented factor and a nonnegative quotient of smaller natural degree. -/
theorem exists_nonnegative_root_factor (f : Polynomial ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t)
    (hdegree : 0 < f.natDegree) :
    ∃ a g : Polynomial ℝ, f = a * g ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval t) ∧
      g.natDegree < f.natDegree ∧ Nonempty (Representation a.natDegree a) := by
  have hf0 : f ≠ 0 := by
    intro hz
    simp [hz] at hdegree
  have finish (a g : Polynomial ℝ) (hfg : f = a * g)
      (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval t)
      (had : 0 < a.natDegree) (ra : Nonempty (Representation a.natDegree a)) :
      ∃ a g : Polynomial ℝ, f = a * g ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval t) ∧
        g.natDegree < f.natDegree ∧ Nonempty (Representation a.natDegree a) := by
    have ha0 : a ≠ 0 := by
      intro hz
      simp [hz] at had
    have hg0 : g ≠ 0 := by
      intro hz
      apply hf0
      rw [hfg, hz, mul_zero]
    have hdeg : f.natDegree = a.natDegree + g.natDegree := by
      rw [hfg, natDegree_mul ha0 hg0]
    exact ⟨a, g, hfg, hg, by omega, ra⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ f
    (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree))
  by_cases him : z.im = 0
  · have hr := real_isRoot_of_aeval_of_im_eq_zero hz him
    by_cases hleft : z.re ≤ 0
    · obtain ⟨g, hfg⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      have ha : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (X - C z.re).eval t := by
        intro t ht
        simp only [eval_sub, eval_X, eval_C]
        linarith [ht.1]
      apply finish (X - C z.re) g hfg (quotient_nonneg_on_unit_interval hfg hf ha)
      · rw [natDegree_X_sub_C]
        norm_num
      · rw [natDegree_X_sub_C]
        exact ⟨repLinearLeft z.re hleft⟩
    · by_cases hright : 1 ≤ z.re
      · obtain ⟨g, hfg⟩ := C_sub_X_dvd_of_isRoot hr
        have ha : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < (C z.re - X).eval t := by
          intro t ht
          simp only [eval_sub, eval_X, eval_C]
          linarith [ht.2]
        apply finish (C z.re - X) g hfg (quotient_nonneg_on_unit_interval hfg hf ha)
        · rw [C_sub_X_natDegree]
          norm_num
        · rw [C_sub_X_natDegree]
          exact ⟨repLinearRight z.re hright⟩
      · have hr0 : 0 < z.re := lt_of_not_ge hleft
        have hr1 : z.re < 1 := lt_of_not_ge hright
        obtain ⟨g, hfg⟩ := sq_X_sub_C_dvd_of_nonneg_on_unit_interval hf hr0 hr1 hr
        apply finish ((X - C z.re) ^ 2) g hfg
          (quotient_nonneg_of_interior_square hfg hf hr0 hr1)
        · simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
          norm_num
        · simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
          exact ⟨repSquareLinear z.re⟩
  · obtain ⟨g, hfg⟩ := f.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
    let a : Polynomial ℝ := rootQuadratic z
    have ha : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < a.eval t := by
      intro t _
      exact rootQuadratic_pos z him t
    have had : a.natDegree = 2 := root_quadratic_natDegree _ _
    apply finish a g hfg (quotient_nonneg_on_unit_interval hfg hf ha)
    · omega
    · rw [had]
      exact ⟨repQuadratic z⟩

/-- Every polynomial nonnegative on `[0, 1]` possesses a Markov–Lukács representation at its
natural degree. -/
theorem exists_rep_of_nonneg_natDegree (f : Polynomial ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t) :
    Nonempty (Representation f.natDegree f) := by
  have main : ∀ (n : ℕ) (p : Polynomial ℝ), p.natDegree = n →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ p.eval t) →
      Nonempty (Representation n p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp
      by_cases hp0 : p = 0
      · subst p
        have hn0 : n = 0 := by simpa using hn.symm
        subst n
        exact ⟨repZero 0⟩
      · by_cases hn0 : n = 0
        · have hpC : p = C (p.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero (hn.trans hn0)
          have hc : 0 ≤ p.coeff 0 := by
            have h := hp 0 (by constructor <;> norm_num)
            rwa [← Polynomial.coeff_zero_eq_eval_zero] at h
          rw [hn0, hpC]
          exact ⟨repConst _ hc⟩
        · have hdegree : 0 < p.natDegree := by omega
          obtain ⟨a, g, hpg, hgpos, hgd, ⟨ra⟩⟩ :=
            exists_nonnegative_root_factor p hp hdegree
          obtain ⟨rg⟩ := ih g.natDegree (by omega) g rfl hgpos
          have ha0 : a ≠ 0 := by
            intro hz
            apply hp0
            rw [hpg, hz, zero_mul]
          have hg0 : g ≠ 0 := by
            intro hz
            apply hp0
            rw [hpg, hz, mul_zero]
          have hsum : a.natDegree + g.natDegree = n := by
            rw [← natDegree_mul ha0 hg0, ← hpg]
            exact hn
          have hrep : Nonempty (Representation (a.natDegree + g.natDegree) (a * g)) :=
            ⟨repMul ra rg⟩
          simpa only [hsum, ← hpg] using hrep
  exact main f.natDegree f rfl hf

/-- A polynomial nonnegative on `[0, 1]` possesses a Markov–Lukács representation at any given
degree bound. -/
theorem exists_rep_of_nonneg (f : Polynomial ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f.eval t)
    {d : ℕ} (hd : f.degree ≤ (d : WithBot ℕ)) :
    Nonempty (Representation d f) := by
  obtain ⟨r⟩ := exists_rep_of_nonneg_natDegree f hf
  exact ⟨repMono (Polynomial.natDegree_le_of_degree_le hd) r⟩

end Qatlib.Concepts.QsvtCore.PolyApprox
