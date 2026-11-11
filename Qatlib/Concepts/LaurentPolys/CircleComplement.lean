/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Polynomial complements on the unit circle

`circle_complement_zero_margin_exists` constructs a polynomial `Q` of controlled degree with
`‖P(z)‖² + ‖Q(z)‖² = 1` on the unit circle whenever `P` is bounded by one there. The proof
factors a nonnegative real polynomial after a rational change of variables. Such polynomial
complements occur in quantum signal processing [LowChuang2017].

`circle_complement_coefficient_residual_certificate` turns coefficient error bounds into an
explicit uniform bound for `circleResidual`.

## Main statements

* `circle_nonnegative_real_polynomial_factorization`: factorization as a polynomial times its
  coefficientwise conjugate.
* `circle_complement_zero_margin_exists`: complementation without a strict boundary margin.
* `circle_complement_coefficient_residual_certificate`: residual control from coefficient
  errors.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option warningAsError false
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Qatlib.Concepts.QsvtCore.PolyApprox

namespace Qatlib.Concepts.LaurentPolys.CircleComplement
open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open scoped ComplexOrder BigOperators

/-- The absolute defect `|‖P.eval z‖^2 + ‖Q.eval z‖^2 - 1|` of a polynomial pair at `z`. -/
noncomputable def circleResidual (P Q : Polynomial ℂ) (z : ℂ) : ℝ :=
  |‖P.eval z‖^2 + ‖Q.eval z‖^2 - 1|

/-- The two-by-two matrix with rows `(P(z), -star Q(z))` and `(Q(z), star P(z))`, indexed by
`Bool`. -/
noncomputable def circleCompletion (P Q : Polynomial ℂ) (z : ℂ) : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then star (P.eval z) else Q.eval z)
    else (if j then -star (Q.eval z) else P.eval z)

/-- Every real root of a polynomial nonnegative on the whole real line has its squared linear
factor dividing the polynomial. -/
private theorem circle_global_double_root {f : Polynomial ℝ}
    (hf : ∀ t : ℝ, 0 ≤ f.eval t) {r : ℝ} (hr : f.IsRoot r) :
    (X-C r)^2 ∣ f := by
  obtain ⟨g,hfg⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hleft : ∀ t ∈ Set.Ioo (r-1) r, g.eval t ≤ 0 := by
    intro t ht
    have hh := hf t
    rw [hfg, eval_mul, eval_sub, eval_X, eval_C] at hh
    by_contra! hg
    exact (not_lt_of_ge hh) (mul_neg_of_neg_of_pos (sub_neg.mpr ht.2) hg)
  have hright : ∀ t ∈ Set.Ioo r (r+1), 0 ≤ g.eval t := by
    intro t ht
    apply quotient_nonneg_at hfg t (hf t)
    simpa using sub_pos.mpr ht.1
  have hle := nonpos_on_Icc_of_nonpos_on_Ioo (by linarith : r-1 < r) hleft r ⟨by linarith, le_rfl⟩
  have hge := nonneg_on_Icc_of_nonneg_on_Ioo (by linarith : r < r+1) hright r ⟨le_rfl, by linarith⟩
  obtain ⟨q,hgq⟩ := Polynomial.dvd_iff_isRoot.mpr (show g.IsRoot r from le_antisymm hle hge)
  refine ⟨q, ?_⟩
  rw [hfg,hgq]
  ring

/-- If a globally nonnegative real polynomial factors as `(X - C r)^2 * g`, then `g` is globally
nonnegative. -/
private theorem circle_global_square_quotient {f g : Polynomial ℝ} (r : ℝ)
    (hfg : f = (X-C r)^2*g) (hf : ∀ t, 0 ≤ f.eval t) : ∀ t, 0 ≤ g.eval t := by
  have hn : ∀ t ∈ ({r}ᶜ : Set ℝ), 0 ≤ g.eval t := by
    intro t ht
    apply quotient_nonneg_at hfg t (hf t)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr ht)
  intro t
  exact le_on_closure hn continuous_const.continuousOn g.continuousOn
    (by rw [closure_compl_singleton]; trivial)

/-- The real quadratic associated with a complex number factors over the complex numbers as its
linear factor times the coefficientwise conjugate factor. -/
private theorem circle_quadratic_factor (z : ℂ) :
    (X^2-C (2*z.re)*X+C (‖z‖^2) : Polynomial ℝ).map Complex.ofRealHom =
      (X-C z)*conjugatePolynomial (X-C z) := by
  have hs : z+star z = ((2*z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp; ring
  have hp : z*star z = ((‖z‖^2 : ℝ) : ℂ) := by
    simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj z
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Complex.ofRealHom_eq_coe,
    conjugatePolynomial_sub, conjugatePolynomial_X, conjugatePolynomial_C]
  rw [← hs, ← hp]
  rw [map_add, map_mul]
  ring

/-- A real polynomial nonnegative everywhere factors over the complex numbers as `q *
conjugatePolynomial q`, with twice the degree of `q` at most the original degree. -/
theorem circle_nonnegative_real_polynomial_factorization (f : Polynomial ℝ) (hf : ∀ t, 0 ≤ f.eval t) :
    ∃ q : Polynomial ℂ, f.map Complex.ofRealHom = q*conjugatePolynomial q ∧
      2*q.natDegree ≤ f.natDegree := by
  generalize hd : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hz : f = 0
    · refine ⟨0, ?_, ?_⟩ <;> simp [hz]
    by_cases hn : f.natDegree = 0
    · obtain ⟨a,rfl⟩ := Polynomial.natDegree_eq_zero.mp hn
      have ha : 0 ≤ a := by simpa using hf 0
      refine ⟨C (Real.sqrt a : ℂ), ?_, by simp⟩
      simp only [Polynomial.map_C, Complex.ofRealHom_eq_coe, conjugatePolynomial_C,
        Complex.star_def, Complex.conj_ofReal, ← C_mul, ← Complex.ofReal_mul,
        Real.mul_self_sqrt ha]
    have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hn
    obtain ⟨z,hzroot⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ f
      (ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hpos))
    by_cases him : z.im = 0
    · have hr := real_isRoot_of_aeval_of_im_eq_zero hzroot him
      obtain ⟨g,hfg⟩ := circle_global_double_root hf hr
      have hg := circle_global_square_quotient z.re hfg hf
      have hg0 : g ≠ 0 := by intro h; simp [h] at hfg; exact hz hfg
      have ha0 : (X-C z.re)^2 ≠ (0 : Polynomial ℝ) := pow_ne_zero _ (X_sub_C_ne_zero _)
      have hdeg : f.natDegree = 2+g.natDegree := by
        rw [hfg, natDegree_mul ha0 hg0, natDegree_pow, natDegree_X_sub_C]
      obtain ⟨q,hq,hqd⟩ := ih g.natDegree (by omega) g hg rfl
      refine ⟨(X-C (z.re : ℂ))*q, ?_, ?_⟩
      · rw [hfg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
          Polynomial.map_X, Polynomial.map_C, Complex.ofRealHom_eq_coe, hq,
          conjugatePolynomial_mul, conjugatePolynomial_sub, conjugatePolynomial_X,
          conjugatePolynomial_C, Complex.star_def, Complex.conj_ofReal]
        ring
      · have hle := natDegree_mul_le (p := X-C (z.re : ℂ)) (q := q)
        rw [natDegree_X_sub_C] at hle
        omega
    · obtain ⟨g,hfg⟩ := f.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hzroot him
      let a : Polynomial ℝ := X^2-C (2*z.re)*X+C (‖z‖^2)
      change f = a*g at hfg
      have ha (t : ℝ) : 0 < a.eval t := by
        dsimp only [a]
        simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [sq_nonneg (t-z.re), sq_pos_of_ne_zero him]
      have hg (t : ℝ) : 0 ≤ g.eval t := quotient_nonneg_at hfg t (hf t) (ha t)
      have hg0 : g ≠ 0 := by intro h; simp [h] at hfg; exact hz hfg
      have ha0 : a ≠ 0 := by intro h; have hh := ha 0; simp [h] at hh
      have hdeg : f.natDegree = 2+g.natDegree := by
        rw [hfg, natDegree_mul ha0 hg0, root_quadratic_natDegree]
      obtain ⟨q,hq,hqd⟩ := ih g.natDegree (by omega) g hg rfl
      refine ⟨(X-C z)*q, ?_, ?_⟩
      · rw [hfg, Polynomial.map_mul, circle_quadratic_factor, hq, conjugatePolynomial_mul]
        ring
      · have hle := natDegree_mul_le (p := X-C z) (q := q)
        rw [natDegree_X_sub_C] at hle
        omega

/-- The degree-`d` polynomial transform `∑ j < d+1, C (P.coeff j) * a^j * b^(d-j)`. -/
private def circleTransform (P : Polynomial ℂ) (d : ℕ) (a b : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d+1), C (P.coeff j)*a^j*b^(d-j)

/-- If `a` and `b` have degree at most one, the transform `circleTransform P d a b` has degree
at most `d`. -/
private theorem circleTransform_degree (P : Polynomial ℂ) (d : ℕ) (a b : Polynomial ℂ)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    (circleTransform P d a b).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  dsimp only [circleTransform]
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j hj
  apply degree_le_of_natDegree_le
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hmul := natDegree_mul_le (p := C (P.coeff j)*a^j) (q := b^(d-j))
  have hc := natDegree_C_mul_le (P.coeff j) (a^j)
  have hpa : (a^j).natDegree ≤ j*a.natDegree := natDegree_pow_le
  have hpb : (b^(d-j)).natDegree ≤ (d-j)*b.natDegree := natDegree_pow_le
  have h1 := Nat.mul_le_mul_left j ha
  have h2 := Nat.mul_le_mul_left (d-j) hb
  simp only [Nat.mul_one] at h1 h2
  omega

/-- For `P` of degree at most `d` and nonzero `b.eval z`, evaluates the transform as `(b.eval
z)^d * P.eval (a.eval z / b.eval z)`. -/
private theorem circleTransform_eval (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d)
    (a b : Polynomial ℂ) (z : ℂ) (hb : b.eval z ≠ 0) :
    (circleTransform P d a b).eval z = (b.eval z)^d*P.eval (a.eval z/b.eval z) := by
  dsimp only [circleTransform]
  rw [Polynomial.eval_finsetSum]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hp), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_pow, eval_C]
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [div_pow, ← mul_div_assoc]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hjd]

/-- The real polynomial obtained by taking the real part of every coefficient of a complex
polynomial. -/
private def circleRealCoeffs (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re Complex.zero_re⟩⟩

/-- The coefficient of `circleRealCoeffs P` is the real part of the corresponding coefficient of
`P`. -/
private theorem circleRealCoeffs_coeff (P : Polynomial ℂ) (j : ℕ) :
    (circleRealCoeffs P).coeff j = (P.coeff j).re := rfl

/-- Taking real parts of coefficients cannot increase a polynomial's natural degree. -/
private theorem circleRealCoeffs_degree (P : Polynomial ℂ) :
    (circleRealCoeffs P).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [circleRealCoeffs_coeff, coeff_eq_zero_of_natDegree_lt hj]
  rfl

/-- A complex polynomial with real coefficients is recovered by mapping `circleRealCoeffs P`
back to the complex numbers. -/
private theorem circleRealCoeffs_map (P : Polynomial ℂ)
    (hP : ∀ j, (P.coeff j).im = 0) :
    (circleRealCoeffs P).map Complex.ofRealHom = P := by
  ext j
  simp only [coeff_map, circleRealCoeffs_coeff, Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · simp
  · simpa using (hP j).symm

/-- The rational circle parametrization `(x - i) / (x + i)` for real `x`. -/
private def circleSignal (x : ℝ) : ℂ := ((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I)

/-- For real `x`, the denominator `x + i` of the circle parametrization is nonzero. -/
private theorem circle_den_ne_zero (x : ℝ) : (x : ℂ)+Complex.I ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp at hh

/-- The rational circle parametrization has norm one for every real input. -/
private theorem circleSignal_norm (x : ℝ) : ‖circleSignal x‖ = 1 := by
  have he : ‖(x : ℂ)-Complex.I‖ = ‖(x : ℂ)+Complex.I‖ := by
    apply Real.sqrt_inj (by positivity) (by positivity) |>.mp
    simp [Complex.norm_def, Complex.normSq_apply]
  rw [circleSignal, norm_div, he, div_self (norm_ne_zero_iff.mpr (circle_den_ne_zero x))]

/-- The polynomial transform of `P` using `X - i` and `X + i` to clear the denominator of the
circle parametrization. -/
private def circleForward (P : Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  circleTransform P d (X-C Complex.I) (X+C Complex.I)

/-- The forward circle transform has degree at most `d`. -/
private theorem circleForward_degree (P : Polynomial ℂ) (d : ℕ) :
    (circleForward P d).natDegree ≤ d := by
  apply circleTransform_degree
  · simp
  · simp

/-- For `P` of degree at most `d`, the forward transform at real `x` equals `(x + i)^d * P.eval
(circleSignal x)`. -/
private theorem circleForward_eval (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d) (x : ℝ) :
    (circleForward P d).eval (x : ℂ) = ((x : ℂ)+Complex.I)^d*P.eval (circleSignal x) := by
  have he := circleTransform_eval P d hp (X-C Complex.I) (X+C Complex.I) (x : ℂ)
      (by simpa using circle_den_ne_zero x)
  simp only [eval_add, eval_sub, eval_X, eval_C] at he
  exact he

/-- The polynomial `(X^2 + 1)^d` minus the forward transform times its coefficientwise
conjugate. -/
private def circleClearedResidual (P : Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  (X^2+1)^d-circleForward P d*conjugatePolynomial (circleForward P d)

/-- All coefficients of the cleared residual polynomial have zero imaginary part. -/
private theorem circleClearedResidual_real (P : Polynomial ℂ) (d : ℕ) :
    ∀ j, ((circleClearedResidual P d).coeff j).im = 0 := by
  have he : conjugatePolynomial (circleClearedResidual P d) = circleClearedResidual P d := by
    simp [circleClearedResidual, mul_comm]
  intro j
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff j) he
  simp only [conjugatePolynomial_coeff] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The cleared residual polynomial has natural degree at most `2*d`. -/
private theorem circleClearedResidual_degree (P : Polynomial ℂ) (d : ℕ) :
    (circleClearedResidual P d).natDegree ≤ 2*d := by
  have hf := circleForward_degree P d
  have hm0 : (conjugatePolynomial (circleForward P d)).natDegree ≤ (circleForward P d).natDegree :=
    Polynomial.natDegree_map_le
  have hcg : (conjugatePolynomial (circleForward P d)).natDegree ≤ d :=
    hm0.trans hf
  have hm :=
      natDegree_mul_le (p := circleForward P d) (q := conjugatePolynomial (circleForward P d))
  have hx : ((X^2+1 : Polynomial ℂ)^d).natDegree ≤ 2*d := by
    have hh : ((X^2+1 : Polynomial ℂ)^d).natDegree ≤ d*(X^2+1 : Polynomial ℂ).natDegree :=
        natDegree_pow_le
    have hb : (X^2+1 : Polynomial ℂ).natDegree ≤ 2 := by
      exact (natDegree_add_le _ _).trans (by simp)
    exact hh.trans ((Nat.mul_le_mul_left d hb).trans_eq (Nat.mul_comm d 2))
  exact natDegree_sub_le _ _ |>.trans (max_le hx (by omega))

/-- At real `x`, the real-coefficient cleared residual evaluates to `(x^2 + 1)^d` minus the
squared norm of the forward transform. -/
private theorem circleClearedResidual_eval (P : Polynomial ℂ) (d : ℕ) (x : ℝ) :
    (((circleRealCoeffs (circleClearedResidual P d)).eval x : ℝ) : ℂ) =
      ((x^2+1)^d-‖(circleForward P d).eval (x : ℂ)‖^2 : ℝ) := by
  have hm := circleRealCoeffs_map (circleClearedResidual P d) (circleClearedResidual_real P d)
  have hi := congrArg (fun p : Polynomial ℂ => p.eval (x : ℂ)) hm
  (try dsimp only at hi)
  simp only [← Complex.ofRealHom_eq_coe, Polynomial.eval_map_apply] at hi
  have hprod := Complex.mul_conj ((circleForward P d).eval (x : ℂ))
  rw [Complex.normSq_eq_norm_sq] at hprod
  simpa [circleClearedResidual, conjugatePolynomial_eval_real, hprod] using hi

/-- If `P` has degree at most `d` and norm at most one on the unit circle, its cleared real
residual is nonnegative everywhere on the real line. -/
private theorem circleClearedResidual_nonneg (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∀ x : ℝ, 0 ≤ (circleRealCoeffs (circleClearedResidual P d)).eval x := by
  intro x
  have hb := hP (circleSignal x) (circleSignal_norm x)
  have he := circleClearedResidual_eval P d x
  have hr := congrArg Complex.re he
  simp only [Complex.ofReal_re] at hr
  rw [hr, circleForward_eval P d hp x, norm_mul, norm_pow, mul_pow]
  have hn : ‖(x : ℂ)+Complex.I‖^2 = x^2+1 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [← pow_mul, Nat.mul_comm d 2, pow_mul, hn]
  have hb2 : ‖P.eval (circleSignal x)‖^2 ≤ 1 := by nlinarith [norm_nonneg (P.eval (circleSignal x))]
  have hm := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ (x^2+1)^d by positivity)
  linarith

/-- For a degree-at-most-`d` polynomial bounded by one on the circle, constructs a
degree-at-most-`d` polynomial whose squared norm completes the forward transform to `(x^2 +
1)^d` on the real line. -/
private theorem circleClearedResidual_factor (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ d ∧
      ∀ x : ℝ, ‖(circleForward P d).eval (x : ℂ)‖^2+‖q.eval (x : ℂ)‖^2 = (x^2+1)^d := by
  obtain ⟨q,hq,hdeg⟩ := circle_nonnegative_real_polynomial_factorization
    (circleRealCoeffs (circleClearedResidual P d)) (circleClearedResidual_nonneg P d hp hP)
  have hnd :=
      (circleRealCoeffs_degree (circleClearedResidual P d)).trans (circleClearedResidual_degree P d)
  refine ⟨q, by omega, ?_⟩
  intro x
  have he := congrArg (fun p : Polynomial ℂ => p.eval (x : ℂ)) hq
  have hm := circleRealCoeffs_map (circleClearedResidual P d) (circleClearedResidual_real P d)
  rw [hm] at he
  (try dsimp only at he)
  rw [eval_mul, conjugatePolynomial_eval_real, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq] at he
  have hc := circleClearedResidual_eval P d x
  rw [← hm] at he
  simp only [← Complex.ofRealHom_eq_coe, Polynomial.eval_map_apply] at he
  have hi : (circleRealCoeffs (circleClearedResidual P d)).eval x = ‖q.eval (x : ℂ)‖^2 := by
    have hr := congrArg Complex.re he
    simpa only [Complex.ofRealHom_eq_coe, Complex.ofReal_re,
      ← Complex.ofReal_pow] using hr
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re] at hr
  linarith

/-- The inverse rational expression `i * (1 + z) / (1 - z)` for the circle parametrization. -/
private def circleInverse (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)

/-- The inverse circle expression has zero imaginary part at every point of norm one. -/
private theorem circleInverse_real (z : ℂ) (hz : ‖z‖ = 1) : (circleInverse z).im = 0 := by
  have hn : z.re^2+z.im^2 = 1 := by
    have hh := Complex.sq_norm z
    rw [hz] at hh
    simp only [Complex.normSq_apply, one_pow] at hh
    nlinarith
  dsimp only [circleInverse]
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub]
  rw [← sub_div]
  rw [show (1+z.re)*(1-z.re)-(-z.im)*(-z.im) = 0 by nlinarith]
  simp

/-- At a point of norm one, the real part of `circleInverse z`, embedded in the complex numbers,
equals `circleInverse z`. -/
private theorem circleInverse_cast (z : ℂ) (hz : ‖z‖ = 1) :
    ((circleInverse z).re : ℂ) = circleInverse z := by
  apply Complex.ext
  · simp
  · simp [circleInverse_real z hz]

/-- For `z ≠ 1`, the inverse expression satisfies `(circleInverse z + i) * (1 - z) = 2*i`. -/
private theorem circleInverse_shift (z : ℂ) (hz : z ≠ 1) :
    (circleInverse z+Complex.I)*(1-z) = 2*Complex.I := by
  dsimp [circleInverse]
  field_simp [sub_ne_zero.mpr hz.symm]
  ring

/-- At every unit-circle point other than one, applying `circleSignal` to the real part of the
inverse expression recovers the point. -/
private theorem circleSignal_inverse (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    circleSignal (circleInverse z).re = z := by
  rw [circleSignal, div_eq_iff (circle_den_ne_zero _), circleInverse_cast z hz]
  have he := circleInverse_shift z hz1
  linear_combination he

/-- The rational circle parametrization never takes the value one at a real input. -/
private theorem circleSignal_ne_one (x : ℝ) : circleSignal x ≠ 1 := by
  intro he
  rw [circleSignal, div_eq_one_iff_eq (circle_den_ne_zero x)] at he
  have hh := congrArg Complex.im he
  norm_num at hh

/-- Applying the inverse expression to `circleSignal x` recovers the real input `x` as a complex
number. -/
private theorem circleInverse_signal (x : ℝ) : circleInverse (circleSignal x) = x := by
  dsimp [circleInverse, circleSignal]
  field_simp [circle_den_ne_zero x]
  ring

/-- The inverse polynomial transform using `i * (1 + X)` and `1 - X`, scaled by `(2*i)^(-d)`. -/
private def circleReverse (q : Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  C (((2*Complex.I)^d)⁻¹)*circleTransform q d (C Complex.I*(1+X)) (1-X)

/-- The reverse circle transform has natural degree at most `d`. -/
private theorem circleReverse_degree (q : Polynomial ℂ) (d : ℕ) :
    (circleReverse q d).natDegree ≤ d := by
  apply (natDegree_C_mul_le _ _).trans
  apply circleTransform_degree
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  · exact (natDegree_sub_le _ _).trans (by simp)

/-- For `q` of degree at most `d`, evaluates the reverse transform at `circleSignal x` as
`q.eval x / (x + i)^d`. -/
private theorem circleReverse_eval (q : Polynomial ℂ) (d : ℕ) (hq : q.natDegree ≤ d) (x : ℝ) :
    (circleReverse q d).eval (circleSignal x) = q.eval (x : ℂ)/((x : ℂ)+Complex.I)^d := by
  have hb : (1-X : Polynomial ℂ).eval (circleSignal x) ≠ 0 := by
    simp only [eval_sub, eval_one, eval_X]
    exact sub_ne_zero.mpr (circleSignal_ne_one x).symm
  have ht := circleTransform_eval q d hq (C Complex.I*(1+X)) (1-X) (circleSignal x) hb
  have hi := circleInverse_signal x
  have hs := circleInverse_shift (circleSignal x) (circleSignal_ne_one x)
  rw [hi] at hs
  have hsPow := congrArg (fun z : ℂ => z^d) hs
  (try dsimp only at hsPow)
  rw [mul_pow] at hsPow
  dsimp only [circleReverse]
  rw [eval_mul, eval_C, ht]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_one, eval_X]
  change ((2*Complex.I)^d)⁻¹*((1-circleSignal x)^d*q.eval (circleInverse (circleSignal x))) = _
  rw [hi]
  have hc : (2*Complex.I)^d ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hd := pow_ne_zero d (circle_den_ne_zero x)
  apply (eq_div_iff hd).mpr
  calc
    _ = ((2*Complex.I)^d)⁻¹*(((x : ℂ)+Complex.I)^d*(1-circleSignal x)^d)*q.eval (x : ℂ) := by ring
    _ = _ := by rw [hsPow, inv_mul_cancel₀ hc, one_mul]

/-- A squared-norm completion of the forward transform on the real line becomes a unit-circle
completion after applying the reverse transform. -/
private theorem circleSignal_completion (P q : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hcomp : ∀ x : ℝ, ‖(circleForward P d).eval (x : ℂ)‖^2+‖q.eval (x : ℂ)‖^2 = (x^2+1)^d)
    (x : ℝ) : ‖P.eval (circleSignal x)‖^2+‖(circleReverse q d).eval (circleSignal x)‖^2 = 1 := by
  have he := hcomp x
  have hden : ‖(x : ℂ)+Complex.I‖^2 = x^2+1 := by simp [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [circleForward_eval P d hp x, norm_mul, norm_pow, mul_pow,
    ← pow_mul, Nat.mul_comm d 2, pow_mul, hden] at he
  rw [circleReverse_eval q d hq x, norm_div, div_pow, norm_pow,
    ← pow_mul, Nat.mul_comm d 2, pow_mul, hden]
  have hd : (x^2+1)^d ≠ 0 := by positivity
  field_simp
  nlinarith

/-- A polynomial squared-norm completion holding at all unit-circle points except one also holds
at one. -/
private theorem circle_extend_one (P Q : Polynomial ℂ)
    (hf : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1) :
    ‖P.eval 1‖^2+‖Q.eval 1‖^2 = 1 := by
  let phase := fun θ : ℝ => Complex.exp ((θ : ℂ)*Complex.I)
  let F := fun θ : ℝ => ‖P.eval (phase θ)‖^2+‖Q.eval (phase θ)‖^2
  have hFc : Continuous F := by fun_prop
  have he (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) : F θ = 1 := by
    apply hf
    · exact Complex.norm_exp_ofReal_mul_I θ
    · intro hh
      have hi := congrArg Complex.im hh
      have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      simp only [phase, Complex.exp_ofReal_mul_I, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        add_zero, zero_add, Complex.one_im] at hi
      linarith
  have hz : (0 : ℝ) ∈ _root_.closure (Set.Ioo 0 Real.pi) := by
    rw [closure_Ioo Real.pi_pos.ne]; simp [Real.pi_pos.le]
  have hle : F 0 ≤ 1 := le_on_closure (fun θ hθ => (he θ hθ).le)
    hFc.continuousOn continuous_const.continuousOn hz
  have hge : 1 ≤ F 0 := le_on_closure (fun θ hθ => (he θ hθ).ge)
    continuous_const.continuousOn hFc.continuousOn hz
  simpa [F, phase] using le_antisymm hle hge

/-- Every polynomial of degree at most `d` and norm at most one on the unit circle has a
degree-at-most-`d` polynomial complement whose squared norm completes it to one on that
circle. -/
theorem circle_complement_zero_margin_exists (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d)
    (hP : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ d ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1 := by
  obtain ⟨q,hq,hcomp⟩ := circleClearedResidual_factor P d hp hP
  refine ⟨circleReverse q d, circleReverse_degree q d, ?_⟩
  have hall (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
      ‖P.eval z‖^2+‖(circleReverse q d).eval z‖^2 = 1 := by
    have he := circleSignal_completion P q d hp hq hcomp (circleInverse z).re
    rw [circleSignal_inverse z hz hz1] at he
    exact he
  intro z hz
  by_cases hz1 : z = 1
  · subst z
    exact circle_extend_one P (circleReverse q d) hall
  · exact hall z hz hz1

/-- On the unit circle, a polynomial's evaluation norm is bounded by the sum of the norms of its
coefficients. -/
private theorem circle_eval_norm_le (P : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖P.eval z‖ ≤ ∑ j ∈ P.support, ‖P.coeff j‖ := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  simpa only [norm_mul, norm_pow, hz, one_pow, mul_one] using
    norm_sum_le P.support (fun j => P.coeff j*z^j)

/-- On the unit circle, the evaluation difference of two polynomials is bounded by the sum of
their coefficient differences over the union of their supports. -/
private theorem circle_eval_sub_error (P Q : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖P.eval z-Q.eval z‖ ≤ ∑ j ∈ P.support ∪ Q.support, ‖P.coeff j-Q.coeff j‖ := by
  have hh := circle_eval_norm_le (P-Q) z hz
  rw [Polynomial.eval_sub] at hh
  have hs : (P-Q).support ⊆ P.support ∪ Q.support := by
    simpa only [← sub_eq_add_neg, support_neg] using (Polynomial.support_add (p := P) (q := -Q))
  apply hh.trans
  simp only [Polynomial.coeff_sub]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => norm_nonneg _)

/-- If `‖a‖ ≤ 1` and `‖a - b‖ ≤ δ` with `δ ≥ 0`, the squared norms differ by at most `2*δ +
δ^2`. -/
private theorem circle_square_error (a b : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ‖a‖ ≤ 1) (he : ‖a-b‖ ≤ δ) : |‖b‖^2-‖a‖^2| ≤ 2*δ+δ^2 := by
  have hdiff : |‖b‖-‖a‖| ≤ δ := by
    rw [norm_sub_rev] at he
    exact (abs_norm_sub_norm_le b a).trans he
  have hb : ‖b‖ ≤ 1+δ := by
    have hh := norm_le_norm_sub_add b a
    rw [norm_sub_rev] at hh
    linarith
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg b) (norm_nonneg a))]
  rw [mul_comm (‖b‖+‖a‖)]
  calc
    _ ≤ δ*(‖b‖+‖a‖) := mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg b) (norm_nonneg a))
    _ ≤ δ*(2+δ) := mul_le_mul_of_nonneg_left (by linarith) hδ
    _ = _ := by ring

/-- If `P` and `Q` form an exact unit-circle complement and each coefficient error sum is at
most `δ ≥ 0`, the perturbed pair has circle residual at most `4*δ + 2*δ^2`. -/
theorem circle_complement_coefficient_residual_certificate (P Q P' Q' : Polynomial ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : (∑ j ∈ P.support ∪ P'.support, ‖P.coeff j-P'.coeff j‖) ≤ δ)
    (hQ : (∑ j ∈ Q.support ∪ Q'.support, ‖Q.coeff j-Q'.coeff j‖) ≤ δ)
    (hc : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖^2+‖Q.eval z‖^2 = 1)
    (z : ℂ) (hz : ‖z‖ = 1) : circleResidual P' Q' z ≤ 4*δ+2*δ^2 := by
  have hs := hc z hz
  have hp : ‖P.eval z‖ ≤ 1 := by nlinarith [norm_nonneg (P.eval z), sq_nonneg ‖Q.eval z‖]
  have hq : ‖Q.eval z‖ ≤ 1 := by nlinarith [norm_nonneg (Q.eval z), sq_nonneg ‖P.eval z‖]
  have hep := circle_square_error (P.eval z) (P'.eval z) δ hδ hp
    ((circle_eval_sub_error P P' z hz).trans hP)
  have heq := circle_square_error (Q.eval z) (Q'.eval z) δ hδ hq
    ((circle_eval_sub_error Q Q' z hz).trans hQ)
  dsimp only [circleResidual]
  have hi : ‖P'.eval z‖^2+‖Q'.eval z‖^2-1 =
      (‖P'.eval z‖^2-‖P.eval z‖^2)+(‖Q'.eval z‖^2-‖Q.eval z‖^2) := by linarith
  rw [hi]
  apply (abs_add_le _ _).trans
  linarith

end Qatlib.Concepts.LaurentPolys.CircleComplement
