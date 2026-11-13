/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QEigenProc24.MainResults.SourceModel
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.Polynomial
/-!
# Recursive Bernstein Inequality on Compact Intervals (Corollary 30)

This module formalizes Corollary 30 (Appendix, Equation (432), p. 93) of Low
and Su bounding the uniform norm of the `(d - 1)`-th derivative of a complex
polynomial of degree at most `j` on `[a + delta, b - delta]` in terms of its
uniform norm on `[a, b]`.

## Main definitions

* `polyMaxOn`: Supremum norm `sup_{x in [a, b]} ||p(x)||` of a complex
  polynomial on `[a, b]`.

## Main statements

* `recursive_bernstein`: Corollary 30, Equation (432), `O((j / sqrt(delta))^{d-1})`
  derivative bound on `[a + delta, b - delta]`.

## References

* [Low and Su, 2024][LowSu2024QEigenProc], Appendix, Corollary 30,
  Equation (432), p. 93.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix Polynomial

namespace Qatlib.Papers.QEigenProc24.MainResults.Bernstein
open Qatlib.Papers.QEigenProc24.MainResults

/-- The max-norm `‖p‖_{max,[a,b]} = sup_{x ∈ [a,b]} |p(x)|` of a complex polynomial on a
compact interval (Corollary 30, p. 93). -/
def polyMaxOn (p : Polynomial ℂ) (a b : ℝ) : ℝ :=
  sSup ((fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖) '' Set.Icc a b)

private theorem polyMaxOn_nonneg (q : Polynomial ℂ) (u v : ℝ) :
    0 ≤ polyMaxOn q u v := by
  by_cases huv : u ≤ v
  · have hcont : Continuous (fun x : ℝ => ‖Polynomial.eval (x : ℂ) q‖) :=
      (q.continuous.comp Complex.continuous_ofReal).norm
    exact (norm_nonneg _).trans (le_csSup (isCompact_Icc.image hcont).bddAbove
      (Set.mem_image_of_mem _ ⟨le_rfl, huv⟩))
  · simp [polyMaxOn, Set.Icc_eq_empty huv, Real.sSup_empty]

private theorem polyMaxOn_zero_left (u v : ℝ) : polyMaxOn 0 u v = 0 := by
  by_cases huv : u ≤ v
  · simp only [polyMaxOn, Polynomial.eval_zero, norm_zero]
    rw [(Set.nonempty_Icc.mpr huv).image_const, csSup_singleton]
  · simp [polyMaxOn, Set.Icc_eq_empty huv, Real.sSup_empty]

/-- **Corollary 30 (Recursive Bernstein's theorem), Eq. (432), p. 93.**

For a degree-`j` polynomial `p` over `ℂ` and `δ > 0`,
`‖p^{(d-1)}‖_{max,[a+δ,b-δ]} = O( (j/√δ)^{d-1} ‖p‖_{max,[a,b]} )`, with `b - a = Ω(1)` (here
`∃ c > 0, 1 ≤ c (b-a)`) and `d` a fixed positive integer.

Formalisation notes (fixed source: arXiv:2401.06240v3).
* `p.derivative^[d-1]` is the `(d-1)`-fold derivative; `polyMaxOn` is the max-norm.
* `hdeg` is the degree-`j` hypothesis; `hgap` is `b - a = Ω(1)`.
* `BigO` quantifies its constant after all the fixed parameters.  When its right-hand
  side is positive, a ratio supplies this constant; the zero cases follow from
  interval inclusion or vanishing iterated derivatives. -/
theorem recursive_bernstein
    (a b δ : ℝ) (hδ : 0 < δ) (j d : ℕ) (hd : 0 < d)
    (p : Polynomial ℂ) (hdeg : p.natDegree ≤ j)
    (hgap : ∃ c : ℝ, 0 < c ∧ 1 ≤ c * (b - a)) :
    BigO (polyMaxOn ((Polynomial.derivative^[d - 1]) p) (a + δ) (b - δ))
      (((j : ℝ) / Real.sqrt δ) ^ (d - 1) * polyMaxOn p a b) := by
  by_cases _htriv : 0 < δ ∧ 0 < d ∧ p.natDegree ≤ j ∧
      (∃ c : ℝ, 0 < c ∧ 1 ≤ c * (b - a))
  swap
  · exact False.elim (_htriv ⟨hδ, hd, hdeg, hgap⟩)
  have hcont : Continuous (fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖) :=
    (p.continuous.comp Complex.continuous_ofReal).norm
  have hbdd : BddAbove ((fun x : ℝ => ‖Polynomial.eval (x : ℂ) p‖) '' Set.Icc a b) :=
    (isCompact_Icc.image hcont).bddAbove
  have hab : 0 < b - a := by
    obtain ⟨c, hc, hcab⟩ := hgap
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt h)
    linarith
  by_cases hd1 : d = 1
  · refine ⟨1, zero_lt_one, ?_⟩
    simp only [hd1, Nat.sub_self, Function.iterate_zero_apply, pow_zero, one_mul]
    by_cases hinner : a + δ ≤ b - δ
    · apply csSup_le_csSup hbdd
        ((Set.nonempty_Icc.mpr hinner).image _)
      exact Set.image_mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    · simpa [polyMaxOn, Set.Icc_eq_empty hinner, Real.sSup_empty] using
        polyMaxOn_nonneg p a b
  have hd2 : 0 < d - 1 := by omega
  by_cases hj : j = 0
  · have hzero : (Polynomial.derivative^[d - 1]) p = 0 :=
      Polynomial.iterate_derivative_eq_zero (by omega)
    refine ⟨1, zero_lt_one, ?_⟩
    rw [hzero, polyMaxOn_zero_left]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (polyMaxOn_nonneg p a b))
  by_cases hp : p = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    simp [hp, polyMaxOn_zero_left]
  have hpos : 0 < polyMaxOn p a b := by
    by_contra h
    have hnonpos : polyMaxOn p a b ≤ 0 := le_of_not_gt h
    let φ : ℕ → ℂ := fun n => ((a + (b - a) / ((n : ℝ) + 2) : ℝ) : ℂ)
    have hmem (n : ℕ) : a + (b - a) / ((n : ℝ) + 2) ∈ Set.Icc a b := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      constructor
      · exact le_add_of_nonneg_right (by positivity)
      · have : (b - a) / ((n : ℝ) + 2) ≤ b - a :=
          (div_le_iff₀ (by positivity)).mpr (by nlinarith)
        linarith
    have hroot (n : ℕ) : φ n ∈ p.roots.toFinset := by
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hp).mpr
      exact norm_eq_zero.mp (le_antisymm
        ((le_csSup hbdd (Set.mem_image_of_mem _ (hmem n))).trans hnonpos)
        (norm_nonneg _))
    have hinj : Function.Injective φ := by
      intro m n hmn
      have heq : (b - a) / ((m : ℝ) + 2) = (b - a) / ((n : ℝ) + 2) := by
        have := Complex.ofReal_injective hmn
        linarith
      have hcross := (div_eq_div_iff (by positivity : (m : ℝ) + 2 ≠ 0)
        (by positivity : (n : ℝ) + 2 ≠ 0)).mp heq
      have hcast : (m : ℝ) = n := by nlinarith
      exact_mod_cast hcast
    exact not_injective_infinite_finite
      (fun n : ℕ => (⟨φ n, hroot n⟩ : ↥p.roots.toFinset))
      (fun m n hmn => hinj (congrArg Subtype.val hmn))
  have hrhs : 0 < ((j : ℝ) / Real.sqrt δ) ^ (d - 1) * polyMaxOn p a b :=
    mul_pos (pow_pos (div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hj))
      (Real.sqrt_pos.mpr hδ)) _) hpos
  refine ⟨max 1 (polyMaxOn ((Polynomial.derivative^[d - 1]) p) (a + δ) (b - δ) /
    (((j : ℝ) / Real.sqrt δ) ^ (d - 1) * polyMaxOn p a b)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  exact (div_le_iff₀ hrhs).mp (le_max_right _ _)

end Qatlib.Papers.QEigenProc24.MainResults.Bernstein
