/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Splitting complex polynomials into real parity branches

The polynomials `reP` and `imP` split complex coefficients into real and imaginary parts, while
`evenPart` and `oddPart` split each real polynomial by parity. The four `branches` reconstruct
the original polynomial and retain interval bounds suitable for polynomial transformation. These
results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `branches_identity`: reconstructs a complex polynomial from four real branches.
* `branches_parity`, `branches_degree`, and `branches_bounded`: establish parity, degree, and
  interval bounds.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD.ComplexPolynomialSplit
open Polynomial

/-- The real part of a finite complex sum is the sum of the real parts. -/
theorem re_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    Complex.re (∑ i ∈ s, f i) = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s _ ih => simp

/-- The imaginary part of a finite complex sum is the sum of the imaginary parts. -/
theorem im_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    Complex.im (∑ i ∈ s, f i) = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s _ ih => simp

/-- Polynomial evaluation commutes with finite sums over a semiring. -/
theorem eval_finset_sum_poly {R : Type} [Semiring R] {ι : Type}
    (s : Finset ι) (f : ι → Polynomial R) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Polynomial.eval_add, ih]

/-- A complex polynomial is the sum of its coefficient monomials over its support. -/
theorem coeff_sum_eq (P : Polynomial ℂ) :
    (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)) = P := by
  have h := Polynomial.sum_C_mul_X_pow_eq P
  rw [Polynomial.sum_def] at h
  simpa using h

/-- Evaluation at a real argument equals the sum of the complex coefficient monomials at that
argument. -/
theorem polynomial_eval_eq_coeff_sum (P : Polynomial ℂ) (x : ℝ) :
    P.eval (x : ℂ) = ∑ i ∈ P.support,
      (P.coeff i : ℂ) * ((x : ℂ) ^ (i : ℕ)) := by
  have heq : (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)).eval (x : ℂ)
      = P.eval (x : ℂ) :=
    congrArg (fun q : Polynomial ℂ => q.eval (x : ℂ)) (coeff_sum_eq P)
  have h2 : (∑ i ∈ P.support,
      (Polynomial.C (P.coeff i) * Polynomial.X ^ (i : ℕ) : Polynomial ℂ)).eval (x : ℂ)
      = ∑ i ∈ P.support, (P.coeff i : ℂ) * ((x : ℂ) ^ (i : ℕ)) := by
    rw [eval_finset_sum_poly]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact heq.symm.trans h2

/-- Evaluating the real-coefficient part at a real argument gives the real part of the original
evaluation. -/
theorem polynomial_eval_re_eq (P : Polynomial ℂ) (x : ℝ) :
    (∑ i ∈ P.support, Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x
      = (P.eval (x : ℂ)).re := by
  have hxr (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).re = x ^ (i : ℕ) := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hxi (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hre : (P.eval (x : ℂ)).re = ∑ i ∈ P.support, ((P.coeff i).re * x ^ (i : ℕ)) := by
    rw [polynomial_eval_eq_coeff_sum, re_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.mul_re, hxr, hxi]
    ring
  rw [hre, eval_finset_sum_poly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluating the imaginary-coefficient part at a real argument gives the imaginary part of the
original evaluation. -/
theorem polynomial_eval_im_eq (P : Polynomial ℂ) (x : ℝ) :
    (∑ i ∈ P.support, Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x
      = (P.eval (x : ℂ)).im := by
  have hxr (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).re = x ^ (i : ℕ) := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  have hxi (i : ℕ) : ((x : ℂ) ^ (i : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have him : (P.eval (x : ℂ)).im = ∑ i ∈ P.support, ((P.coeff i).im * x ^ (i : ℕ)) := by
    rw [polynomial_eval_eq_coeff_sum, im_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.mul_im, hxr, hxi]
    ring
  rw [him, eval_finset_sum_poly]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- At real arguments, a complex polynomial evaluates as its real-coefficient part plus `i`
times its imaginary-coefficient part. -/
theorem polynomial_eval_eq_re_add_im (P : Polynomial ℂ) (x : ℝ) :
    P.eval (x : ℂ) =
      Complex.ofReal ((∑ i ∈ P.support,
        Polynomial.C (P.coeff i).re * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x) +
        Complex.I * Complex.ofReal ((∑ i ∈ P.support,
          Polynomial.C (P.coeff i).im * Polynomial.X ^ (i : ℕ) : Polynomial ℝ).eval x) := by
  rw [polynomial_eval_re_eq, polynomial_eval_im_eq, mul_comm]
  exact (Complex.re_add_im (P.eval (x : ℂ))).symm

/-- Forms the real polynomial whose coefficients are the real parts of the complex coefficients. -/
def reP (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ i ∈ P.support, C (P.coeff i).re * X ^ i

/-- Forms the real polynomial whose coefficients are the imaginary parts of the complex
coefficients. -/
def imP (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ i ∈ P.support, C (P.coeff i).im * X ^ i

/-- Defines the even part of a real polynomial as `(p(X) + p(-X)) / 2`. -/
def evenPart (p : Polynomial ℝ) : Polynomial ℝ :=
  (p + p.comp (-X)) * C (1 / 2)

/-- Defines the odd part of a real polynomial as `(p(X) - p(-X)) / 2`. -/
def oddPart (p : Polynomial ℝ) : Polynomial ℝ :=
  (p - p.comp (-X)) * C (1 / 2)

/-- The even and odd parts sum to the original real polynomial. -/
theorem parity_parts_sum (p : Polynomial ℝ) : evenPart p + oddPart p = p := by
  ext n
  simp only [evenPart, oddPart, coeff_add, coeff_sub, coeff_mul_C]
  ring

/-- The even part has real parity indexed by any even natural number. -/
theorem evenPart_parity (p : Polynomial ℝ) (n : ℕ) :
    HasRealParity (2 * n) (evenPart p) := by
  unfold HasRealParity evenPart
  rw [mul_comp, add_comp, comp_assoc, neg_comp, X_comp, neg_neg, comp_X, C_comp]
  simp only [pow_mul, neg_one_sq, one_pow, C_1, one_mul]
  rw [add_comm]

/-- The odd part has real parity indexed by any odd natural number. -/
theorem oddPart_parity (p : Polynomial ℝ) (n : ℕ) :
    HasRealParity (2 * n + 1) (oddPart p) := by
  unfold HasRealParity oddPart
  rw [mul_comp, sub_comp, comp_assoc, neg_comp, X_comp, neg_neg, comp_X, C_comp]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, C_neg,
    C_1, neg_one_mul]
  ring

/-- Taking the even part does not increase natural degree. -/
theorem evenPart_natDegree_le (p : Polynomial ℝ) :
    (evenPart p).natDegree ≤ p.natDegree := by
  apply (natDegree_mul_C_le _ _).trans
  apply (natDegree_add_le _ _).trans
  apply max_le le_rfl
  simpa using (natDegree_comp_le (p := p) (q := (-X : Polynomial ℝ)))

/-- Taking the odd part does not increase natural degree. -/
theorem oddPart_natDegree_le (p : Polynomial ℝ) :
    (oddPart p).natDegree ≤ p.natDegree := by
  apply (natDegree_mul_C_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  apply max_le le_rfl
  simpa using (natDegree_comp_le (p := p) (q := (-X : Polynomial ℝ)))

/-- Applying a function to coefficients and rebuilding on the original support does not increase
natural degree. -/
theorem coeffSum_natDegree_le (P : Polynomial ℂ) (f : ℂ → ℝ) :
    (∑ i ∈ P.support, C (f (P.coeff i)) * X ^ i : Polynomial ℝ).natDegree ≤
      P.natDegree := by
  have hsum (s : Finset ℕ) (hs : ∀ i ∈ s, i ≤ P.natDegree) :
      (∑ i ∈ s, C (f (P.coeff i)) * X ^ i : Polynomial ℝ).natDegree ≤
        P.natDegree := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply natDegree_add_le_of_degree_le
      · exact (natDegree_C_mul_X_pow_le _ _).trans (hs i (Finset.mem_insert_self ..))
      · exact ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
  exact hsum P.support (fun i hi => le_natDegree_of_mem_supp i hi)

/-- The real-coefficient part has natural degree at most that of the original complex
polynomial. -/
theorem reP_natDegree_le (P : Polynomial ℂ) : (reP P).natDegree ≤ P.natDegree :=
  coeffSum_natDegree_le P Complex.re

/-- The imaginary-coefficient part has natural degree at most that of the original complex
polynomial. -/
theorem imP_natDegree_le (P : Polynomial ℂ) : (imP P).natDegree ≤ P.natDegree :=
  coeffSum_natDegree_le P Complex.im

/-- If a real polynomial is bounded in absolute value by one on `[-1, 1]`, so are its even and
odd parts. -/
theorem parts_bounded (p : Polynomial ℝ)
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(evenPart p).eval x| ≤ 1 ∧ |(oddPart p).eval x| ≤ 1 := by
  intro x hx
  have hx' : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hpos := abs_le.mp (hp x hx)
  have hneg := abs_le.mp (hp (-x) hx')
  simp only [evenPart, oddPart, eval_mul, eval_add, eval_sub, eval_comp,
    eval_neg, eval_X, eval_C]
  constructor <;> rw [abs_le] <;> constructor <;> linarith [hpos.1, hpos.2, hneg.1, hneg.2]

/-- A complex polynomial bounded in norm by one on `[-1, 1]` has real and imaginary coefficient
parts bounded in absolute value by one there. -/
theorem re_im_bounded (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(reP P).eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(imP P).eval x| ≤ 1) := by
  constructor
  · intro x hx
    rw [reP, polynomial_eval_re_eq]
    exact (Complex.abs_re_le_norm _).trans (hP x hx)
  · intro x hx
    rw [imP, polynomial_eval_im_eq]
    exact (Complex.abs_im_le_norm _).trans (hP x hx)

/-- Mapping the real and imaginary coefficient parts to complex polynomials reconstructs the
original polynomial as their sum with factor `i`. -/
theorem re_im_polynomial_identity (P : Polynomial ℂ) :
    (reP P).map Complex.ofRealHom + Complex.I • (imP P).map Complex.ofRealHom = P := by
  apply Eq.trans ?_ (coeff_sum_eq P)
  rw [reP, imP, Polynomial.map_sum, Polynomial.map_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Complex.ofRealHom_eq_coe, smul_eq_C_mul]
  rw [← mul_assoc, ← C_mul, ← add_mul, ← C_add]
  congr 2
  simpa only [mul_comm] using Complex.re_add_im (P.coeff i)

/-- Lists the even and odd parts of the real and imaginary coefficient polynomials. -/
def branches (P : Polynomial ℂ) : Fin 4 → Polynomial ℝ :=
  ![evenPart (reP P), oddPart (reP P), evenPart (imP P), oddPart (imP P)]

/-- Assigns even degree bound `2 * P.natDegree` and odd degree bound `2 * P.natDegree + 1` to
the four branches. -/
def branchDegrees (P : Polynomial ℂ) : Fin 4 → ℕ :=
  ![2 * P.natDegree, 2 * P.natDegree + 1, 2 * P.natDegree, 2 * P.natDegree + 1]

/-- Defines the reconstruction coefficients `1`, `1`, `i`, and `i` for the four real branches. -/
def coefficients : Fin 4 → ℂ := ![1, 1, Complex.I, Complex.I]

/-- The four real branches, mapped to complex coefficients and weighted by `coefficients`, sum
to the original polynomial. -/
theorem branches_identity (P : Polynomial ℂ) :
    (∑ j : Fin 4, coefficients j • (branches P j).map Complex.ofRealHom) = P := by
  rw [Fin.sum_univ_four]
  simp only [show coefficients 0 = 1 from rfl, show coefficients 1 = 1 from rfl,
    one_smul]
  change (((evenPart (reP P)).map Complex.ofRealHom +
      (oddPart (reP P)).map Complex.ofRealHom) +
      Complex.I • (evenPart (imP P)).map Complex.ofRealHom) +
      Complex.I • (oddPart (imP P)).map Complex.ofRealHom = P
  rw [add_assoc _ (Complex.I • _) (Complex.I • _), ← smul_add,
    ← Polynomial.map_add, ← Polynomial.map_add, parity_parts_sum, parity_parts_sum]
  exact re_im_polynomial_identity P

/-- Each real branch has the parity specified by its assigned branch degree. -/
theorem branches_parity (P : Polynomial ℂ) :
    ∀ j, HasRealParity (branchDegrees P j) (branches P j) := by
  intro j
  fin_cases j
  · exact evenPart_parity (reP P) P.natDegree
  · exact oddPart_parity (reP P) P.natDegree
  · exact evenPart_parity (imP P) P.natDegree
  · exact oddPart_parity (imP P) P.natDegree

/-- Each real branch has degree at most its assigned branch degree. -/
theorem branches_degree (P : Polynomial ℂ) :
    ∀ j, (branches P j).degree ≤ (branchDegrees P j : WithBot ℕ) := by
  intro j
  have heR := (evenPart_natDegree_le (reP P)).trans (reP_natDegree_le P)
  have hoR := (oddPart_natDegree_le (reP P)).trans (reP_natDegree_le P)
  have heI := (evenPart_natDegree_le (imP P)).trans (imP_natDegree_le P)
  have hoI := (oddPart_natDegree_le (imP P)).trans (imP_natDegree_le P)
  apply degree_le_natDegree.trans
  apply WithBot.coe_le_coe.mpr
  fin_cases j <;> simp [branches, branchDegrees] <;> omega

/-- Every assigned branch degree is at most `2 * P.natDegree + 1`. -/
theorem branchDegrees_le (P : Polynomial ℂ) :
    ∀ j, branchDegrees P j ≤ 2 * P.natDegree + 1 := by
  intro j
  fin_cases j <;> simp [branchDegrees]

/-- If the original complex polynomial is bounded in norm by one on `[-1, 1]`, each real branch
is bounded in absolute value by one there. -/
theorem branches_bounded (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) :
    ∀ j x, x ∈ Set.Icc (-1 : ℝ) 1 → |(branches P j).eval x| ≤ 1 := by
  obtain ⟨hr, hi⟩ := re_im_bounded P hP
  intro j x hx
  fin_cases j
  · exact (parts_bounded (reP P) hr x hx).1
  · exact (parts_bounded (reP P) hr x hx).2
  · exact (parts_bounded (imP P) hi x hx).1
  · exact (parts_bounded (imP P) hi x hx).2

end CBMD.ComplexPolynomialSplit

end
end Qatlib.Papers.Cbmd26.Algorithms
