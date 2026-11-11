/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization

/-!
# Cayley transport for Laurent circle factors

This module constructs a polynomial square-norm factor of a nonnegative complex Laurent
polynomial on the unit circle. The private `laurentCayleySignal`, `laurentClearedPolynomial`,
and reverse transport move between the circle and the real line; the final factor can be chosen
with all roots in the closed unit disk. `complex_laurent_circle_factor_polynomial` supplies the
circle factorization used in the ordered-search approach of [ChildsLandahlParrilo2007].

## Main statements

* `complex_laurent_circle_factor_polynomial`: existence of a factor of degree at most `n - 1`
  with roots in the closed unit disk when nonzero.
* `complexLaurentEval_ofReal`: agreement of complex and real-coefficient Laurent evaluation.
* `polynomial_eq_of_unit_circle_eval_eq`: polynomial equality from equality on the unit circle.
* `exists_unit_circle_eval_ne_zero`: every nonzero polynomial is nonzero at some unit-circle
  point.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.LaurentPolys.CircleComplement

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open scoped Classical BigOperators ComplexOrder

/-- The degree-`d` homogenized substitution sum with terms `C (P.coeff j) * a^j * b^(d-j)` for
indices from zero through `d`. -/
private def laurentCayleyTransform (P : Polynomial ℂ) (d : ℕ) (a b : Polynomial ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d+1), C (P.coeff j)*a^j*b^(d-j)

/-- The homogenized substitution has natural degree at most `d` when both substitution
polynomials have natural degree at most one. -/
private theorem laurentCayleyTransform_degree (P : Polynomial ℂ) (d : ℕ) (a b : Polynomial ℂ)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
    (laurentCayleyTransform P d a b).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  dsimp only [laurentCayleyTransform]
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

/-- For a polynomial of degree at most `d` and a nonvanishing denominator evaluation, the
transform evaluates to `b(z)^d * P(a(z)/b(z))`. -/
private theorem laurentCayleyTransform_eval (P : Polynomial ℂ) (d : ℕ) (hp : P.natDegree ≤ d)
    (a b : Polynomial ℂ) (z : ℂ) (hb : b.eval z ≠ 0) :
    (laurentCayleyTransform P d a b).eval z = (b.eval z)^d*P.eval (a.eval z/b.eval z) := by
  dsimp only [laurentCayleyTransform]
  rw [Polynomial.eval_finsetSum]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hp), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul, eval_pow, eval_C]
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [div_pow, ← mul_div_assoc]
  field_simp
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hjd]

/-- The real polynomial obtained by taking the real part of each coefficient of a complex
polynomial. -/
private def laurentCayleyRealCoeffs (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re Complex.zero_re⟩⟩

/-- The coefficient of the real-part polynomial is the real part of the corresponding original
coefficient. -/
private theorem laurentCayleyRealCoeffs_coeff (P : Polynomial ℂ) (j : ℕ) :
    (laurentCayleyRealCoeffs P).coeff j = (P.coeff j).re := rfl

/-- Taking coefficientwise real parts does not increase natural degree. -/
private theorem laurentCayleyRealCoeffs_degree (P : Polynomial ℂ) :
    (laurentCayleyRealCoeffs P).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [laurentCayleyRealCoeffs_coeff, coeff_eq_zero_of_natDegree_lt hj]
  rfl

/-- If every coefficient has zero imaginary part, coercing the real-part polynomial back to
complex coefficients recovers the original polynomial. -/
private theorem laurentCayleyRealCoeffs_map (P : Polynomial ℂ)
    (hP : ∀ j, (P.coeff j).im = 0) :
    (laurentCayleyRealCoeffs P).map Complex.ofRealHom = P := by
  ext j
  simp only [coeff_map, laurentCayleyRealCoeffs_coeff, Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · simp
  · simpa using! (hP j).symm

/-- The Cayley map from a real parameter `x` to the complex value `(x - I)/(x + I)`. -/
private def laurentCayleySignal (x : ℝ) : ℂ := ((x : ℂ)-Complex.I)/((x : ℂ)+Complex.I)

/-- For real `x`, the complex denominator `x + I` is nonzero. -/
private theorem laurentCayley_den_ne_zero (x : ℝ) : (x : ℂ)+Complex.I ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp at hh

/-- The Cayley signal of every real parameter lies on the unit circle. -/
private theorem laurentCayleySignal_norm (x : ℝ) : ‖laurentCayleySignal x‖ = 1 := by
  have he : ‖(x : ℂ)-Complex.I‖ = ‖(x : ℂ)+Complex.I‖ := by
    apply Real.sqrt_inj (by positivity) (by positivity) |>.mp
    simp [Complex.norm_def, Complex.normSq_apply]
  rw [laurentCayleySignal, norm_div, he,
      div_self (norm_ne_zero_iff.mpr (laurentCayley_den_ne_zero x))]

/-- The inverse Cayley expression `I * (1 + z)/(1 - z)`, defined on all complex inputs using
total division. -/
private def laurentCayleyInverse (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)

/-- The inverse Cayley expression has zero imaginary part at every unit-circle input. -/
private theorem laurentCayleyInverse_real (z : ℂ) (hz : ‖z‖ = 1) : (laurentCayleyInverse z).im = 0 := by
  have hn : z.re^2+z.im^2 = 1 := by
    have hh := Complex.sq_norm z
    rw [hz] at hh
    simp only [Complex.normSq_apply, one_pow] at hh
    nlinarith
  dsimp only [laurentCayleyInverse]
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_mul, one_mul, zero_add, zero_sub]
  rw [← sub_div]
  rw [show (1+z.re)*(1-z.re)-(-z.im)*(-z.im) = 0 by nlinarith]
  simp

/-- On the unit circle, the inverse Cayley expression equals the complex coercion of its real
part. -/
private theorem laurentCayleyInverse_cast (z : ℂ) (hz : ‖z‖ = 1) :
    ((laurentCayleyInverse z).re : ℂ) = laurentCayleyInverse z := by
  apply Complex.ext
  · simp
  · simp [laurentCayleyInverse_real z hz]

/-- For `z` different from one, adding `I` to the inverse Cayley expression and multiplying by
`1 - z` gives `2*I`. -/
private theorem laurentCayleyInverse_shift (z : ℂ) (hz : z ≠ 1) :
    (laurentCayleyInverse z+Complex.I)*(1-z) = 2*Complex.I := by
  dsimp [laurentCayleyInverse]
  field_simp [sub_ne_zero.mpr hz.symm]
  ring

/-- Applying the Cayley signal to the real part of the inverse expression recovers every
unit-circle point other than one. -/
private theorem laurentCayleySignal_inverse (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    laurentCayleySignal (laurentCayleyInverse z).re = z := by
  rw [laurentCayleySignal, div_eq_iff (laurentCayley_den_ne_zero _), laurentCayleyInverse_cast z hz]
  have he := laurentCayleyInverse_shift z hz1
  linear_combination he

/-- The Cayley signal of a real parameter is never one. -/
private theorem laurentCayleySignal_ne_one (x : ℝ) : laurentCayleySignal x ≠ 1 := by
  intro he
  rw [laurentCayleySignal, div_eq_one_iff_eq (laurentCayley_den_ne_zero x)] at he
  have hh := congrArg Complex.im he
  norm_num at hh

/-- The inverse Cayley expression applied to a real parameter's signal returns that parameter as
a complex number. -/
private theorem laurentCayleyInverse_signal (x : ℝ) : laurentCayleyInverse (laurentCayleySignal x) = x := by
  dsimp [laurentCayleyInverse, laurentCayleySignal]
  field_simp [laurentCayley_den_ne_zero x]
  ring

/-- The normalized homogenized inverse Cayley substitution of `q`, using numerator `I*(1 + X)`,
denominator `1 - X`, and normalization `((2*I)^d)^{-1}`. -/
private def laurentCayleyReverse (q : Polynomial ℂ) (d : ℕ) : Polynomial ℂ :=
  C (((2*Complex.I)^d)⁻¹)*laurentCayleyTransform q d (C Complex.I*(1+X)) (1-X)

/-- The reverse Cayley polynomial has natural degree at most the chosen homogenization degree
`d`. -/
private theorem laurentCayleyReverse_degree (q : Polynomial ℂ) (d : ℕ) :
    (laurentCayleyReverse q d).natDegree ≤ d := by
  apply (natDegree_C_mul_le _ _).trans
  apply laurentCayleyTransform_degree
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  · exact (natDegree_sub_le _ _).trans (by simp)

/-- For `q` of degree at most `d`, evaluating its reverse Cayley polynomial at the signal of `x`
gives `q(x)/(x + I)^d`. -/
private theorem laurentCayleyReverse_eval (q : Polynomial ℂ) (d : ℕ) (hq : q.natDegree ≤ d) (x : ℝ) :
    (laurentCayleyReverse q d).eval (laurentCayleySignal x) = q.eval (x : ℂ)/((x : ℂ)+Complex.I)^d := by
  have hb : (1-X : Polynomial ℂ).eval (laurentCayleySignal x) ≠ 0 := by
    simp only [eval_sub, eval_one, eval_X]
    exact sub_ne_zero.mpr (laurentCayleySignal_ne_one x).symm
  have ht := laurentCayleyTransform_eval q d hq (C Complex.I*(1+X)) (1-X) (laurentCayleySignal x) hb
  have hi := laurentCayleyInverse_signal x
  have hs := laurentCayleyInverse_shift (laurentCayleySignal x) (laurentCayleySignal_ne_one x)
  rw [hi] at hs
  have hsPow := congrArg (fun z : ℂ => z^d) hs

  rw [mul_pow] at hsPow
  dsimp only [laurentCayleyReverse]
  rw [eval_mul, eval_C, ht]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_one, eval_X]
  change ((2*Complex.I)^d)⁻¹*((1-laurentCayleySignal x)^d*q.eval (laurentCayleyInverse (laurentCayleySignal x))) = _
  rw [hi]
  have hc : (2*Complex.I)^d ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hd := pow_ne_zero d (laurentCayley_den_ne_zero x)
  apply (eq_div_iff hd).mpr
  calc
    _ = ((2*Complex.I)^d)⁻¹*(((x : ℂ)+Complex.I)^d*(1-laurentCayleySignal x)^d)*q.eval (x : ℂ) := by ring
    _ = _ := by rw [hsPow, inv_mul_cancel₀ hc, one_mul]

/-- If the zeroth Laurent coefficient is real, negating an integer index conjugates its Laurent
coefficient. -/
private theorem complexLaurentCoefficient_neg {n : ℕ} (a : Fin n → ℂ)
    (h0 : (complexLaurentCoefficient a 0).im=0) (j : ℤ) :
    complexLaurentCoefficient a (-j) = star (complexLaurentCoefficient a j) := by
  by_cases hj : j.natAbs<n
  · by_cases hj0 : j=0
    · subst j
      apply Complex.ext
      · simp
      · simp [h0]
    · by_cases hneg : j<0
      · have hn : ¬ -j<0 := by omega
        simp only [complexLaurentCoefficient,Int.natAbs_neg,dif_pos hj,
          if_pos hneg,if_neg hn,star_star]
      · have hn : -j<0 := by omega
        simp only [complexLaurentCoefficient,Int.natAbs_neg,dif_pos hj,
          if_neg hneg,if_pos hn]
  · simp [complexLaurentCoefficient,Int.natAbs_neg,hj]

/-- The polynomial obtained by clearing Cayley denominators in the Laurent coefficient window,
with powers of `X - I` and `X + I` indexed around `n - 1`. -/
private def laurentClearedPolynomial {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc (-(n : ℤ)+1) ((n : ℤ)-1),
    C (complexLaurentCoefficient a j)*(X-C Complex.I)^(((n-1 : ℕ) : ℤ)+j).toNat*
      (X+C Complex.I)^(((n-1 : ℕ) : ℤ)-j).toNat

/-- A real zeroth Laurent coefficient ensures that every coefficient of the denominator-cleared
polynomial has zero imaginary part. -/
private theorem laurentClearedPolynomial_real {n : ℕ} (a : Fin n → ℂ)
    (h0 : (complexLaurentCoefficient a 0).im=0) :
    ∀ k, ((laurentClearedPolynomial a).coeff k).im=0 := by
  have he : conjugatePolynomial (laurentClearedPolynomial a)=laurentClearedPolynomial a := by
    unfold laurentClearedPolynomial
    simp only [conjugatePolynomial, Polynomial.map_sum]
    change (∑ j ∈ Finset.Icc (-(n : ℤ)+1) ((n : ℤ)-1),
      conjugatePolynomial (C (complexLaurentCoefficient a j)*(X-C Complex.I)^(((n-1 : ℕ) : ℤ)+j).toNat*
        (X+C Complex.I)^(((n-1 : ℕ) : ℤ)-j).toNat)) = _
    apply Finset.sum_bij (fun j _ => -j)
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj k hk h
      omega
    · intro j hj
      refine ⟨-j,?_,by simp⟩
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj
      rw [complexLaurentCoefficient_neg a h0]
      simp only [conjugatePolynomial_mul,conjugatePolynomial_C,conjugatePolynomial_pow,
        conjugatePolynomial_sub,conjugatePolynomial_add,conjugatePolynomial_X,
        Complex.star_def,Complex.conj_I]
      simp only [C_neg,sub_neg_eq_add,← sub_eq_add_neg]
      ring
  intro k
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff k) he
  simp only [conjugatePolynomial_coeff] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith

/-- For positive size `n`, the denominator-cleared polynomial has natural degree at most `2*(n -
1)`. -/
private theorem laurentClearedPolynomial_degree {n : ℕ} (a : Fin n → ℂ) (hn : 0<n) :
    (laurentClearedPolynomial a).natDegree≤2*(n-1) := by
  apply natDegree_le_of_degree_le
  unfold laurentClearedPolynomial
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j hj
  apply degree_le_of_natDegree_le
  have hb := Finset.mem_Icc.mp hj
  have hj1 : (((n-1 : ℕ) : ℤ)+j).toNat+(((n-1 : ℕ) : ℤ)-j).toNat=2*(n-1) := by omega
  have hm := natDegree_mul_le
    (p := C (complexLaurentCoefficient a j)*(X-C Complex.I)^(((n-1 : ℕ) : ℤ)+j).toNat)
    (q := (X+C Complex.I)^(((n-1 : ℕ) : ℤ)-j).toNat)
  have hc := natDegree_C_mul_le (complexLaurentCoefficient a j)
    ((X-C Complex.I)^(((n-1 : ℕ) : ℤ)+j).toNat)
  have hp := natDegree_pow_le (p := X-C Complex.I) (n := (((n-1 : ℕ) : ℤ)+j).toNat)
  have hq := natDegree_pow_le (p := X+C Complex.I) (n := (((n-1 : ℕ) : ℤ)-j).toNat)
  have hd : (X+C Complex.I : Polynomial ℂ).natDegree≤1 := by
    exact (natDegree_add_le _ _).trans (by simp)
  rw [natDegree_X_sub_C,Nat.mul_one] at hp
  have hqd := Nat.mul_le_mul_left (((n-1 : ℕ) : ℤ)-j).toNat hd
  simp only [Nat.mul_one] at hqd
  omega

/-- For real `x`, the complex numerator `x - I` is nonzero. -/
private theorem laurentCayley_num_ne_zero (x : ℝ) : (x : ℂ)-Complex.I≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi

/-- For an integer offset between `-d` and `d`, the corresponding product of powers of `x - I`
and `x + I` equals `(x^2 + 1)^d` times the offset power of the Cayley signal. -/
private theorem laurentCayley_term (x : ℝ) (d : ℕ) (j : ℤ)
    (hj : -(d : ℤ)≤j ∧ j≤d) :
    ((x : ℂ)-Complex.I)^((d : ℤ)+j).toNat*((x : ℂ)+Complex.I)^((d : ℤ)-j).toNat =
      ((x^2+1)^d : ℝ) * (laurentCayleySignal x)^j := by
  have hdj : (((d : ℤ)+j).toNat : ℤ)=(d : ℤ)+j := Int.toNat_of_nonneg (by omega)
  have hdj' : (((d : ℤ)-j).toNat : ℤ)=(d : ℤ)-j := Int.toNat_of_nonneg (by omega)
  rw [← zpow_natCast,← zpow_natCast,hdj,hdj']
  rw [zpow_add₀ (laurentCayley_num_ne_zero x),zpow_sub₀ (laurentCayley_den_ne_zero x),zpow_natCast,zpow_natCast]
  unfold laurentCayleySignal
  rw [div_zpow]
  have hprod : ((x : ℂ)-Complex.I)*((x : ℂ)+Complex.I)=(x^2+1 : ℝ) := by
    push_cast
    linear_combination -Complex.I_mul_I
  rw [Complex.ofReal_pow,← hprod,mul_pow]
  field_simp [laurentCayley_num_ne_zero x,laurentCayley_den_ne_zero x]

/-- For positive size, the cleared polynomial at real `x` equals `(x^2 + 1)^(n - 1)` times the
Laurent evaluation at the Cayley signal of `x`. -/
private theorem laurentClearedPolynomial_eval {n : ℕ} (a : Fin n → ℂ) (hn : 0<n)
    (x : ℝ) :
    (laurentClearedPolynomial a).eval (x : ℂ) =
      ((x^2+1)^(n-1) : ℝ)*complexLaurentEval a (laurentCayleySignal x) := by
  unfold laurentClearedPolynomial complexLaurentEval
  rw [Polynomial.eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval_mul,eval_C,eval_pow,eval_sub,eval_add,eval_X]
  have hb := Finset.mem_Icc.mp hj
  have hbound : -((n-1 : ℕ) : ℤ)≤j ∧ j≤(n-1 : ℕ) := by omega
  rw [mul_assoc,laurentCayley_term x (n-1) j hbound]
  ring

/-- A Laurent coefficient family of positive size whose evaluation is nonnegative on the unit
circle has a complex polynomial factor of degree at most `n - 1` whose squared norm on the
real line equals the cleared Laurent evaluation. -/
private theorem laurentClearedPolynomial_factor {n : ℕ} (a : Fin n → ℂ)
    (hn : 0<n) (ha : complexLaurentNonnegative a) :
    ∃ q : Polynomial ℂ, q.natDegree≤n-1 ∧ ∀ x : ℝ,
      ((‖q.eval (x : ℂ)‖^2 : ℝ) : ℂ) =
        ((x^2+1)^(n-1) : ℝ)*complexLaurentEval a (laurentCayleySignal x) := by
  let f := laurentCayleyRealCoeffs (laurentClearedPolynomial a)
  have hm : f.map Complex.ofRealHom=laurentClearedPolynomial a :=
    laurentCayleyRealCoeffs_map _ (laurentClearedPolynomial_real a ha.1)
  have hf (x : ℝ) : 0≤f.eval x := by
    have he := congrArg (fun P : Polynomial ℂ => P.eval (x : ℂ)) hm

    simp only [← Complex.ofRealHom_eq_coe,Polynomial.eval_map_apply] at he
    simp only [Complex.ofRealHom_eq_coe] at he
    rw [laurentClearedPolynomial_eval a hn x] at he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,zero_mul,sub_zero] at hr
    rw [hr]
    exact mul_nonneg (by positivity) (ha.2 _ (laurentCayleySignal_norm x))
  obtain ⟨q,hq,hdeg⟩ := circle_nonnegative_real_polynomial_factorization f hf
  have hd := (laurentCayleyRealCoeffs_degree (laurentClearedPolynomial a)).trans
    (laurentClearedPolynomial_degree a hn)
  refine ⟨q,by dsimp only [f] at hdeg; omega,?_⟩
  intro x
  have he := congrArg (fun P : Polynomial ℂ => P.eval (x : ℂ)) (hm.symm.trans hq)

  rw [eval_mul,conjugatePolynomial_eval_real,Complex.star_def,
    Complex.mul_conj,Complex.normSq_eq_norm_sq] at he
  rw [laurentClearedPolynomial_eval a hn x] at he
  exact he.symm

/-- A polynomial factor of the cleared real-line evaluation gives a square-norm factor on Cayley
signals after reverse Cayley transport. -/
private theorem laurentCayley_signal_factor {n : ℕ} (a : Fin n → ℂ)
    (q : Polynomial ℂ) (hq : q.natDegree≤n-1)
    (he : ∀ x : ℝ, ((‖q.eval (x : ℂ)‖^2 : ℝ) : ℂ) =
      ((x^2+1)^(n-1) : ℝ)*complexLaurentEval a (laurentCayleySignal x)) (x : ℝ) :
    complexLaurentEval a (laurentCayleySignal x) =
      ((‖(laurentCayleyReverse q (n-1)).eval (laurentCayleySignal x)‖^2 : ℝ) : ℂ) := by
  have hden : ‖(x : ℂ)+Complex.I‖^2=x^2+1 := by
    simp [Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [laurentCayleyReverse_eval q (n-1) hq x,norm_div,div_pow,norm_pow,
    ← pow_mul,Nat.mul_comm (n-1) 2,pow_mul,hden,Complex.ofReal_div]
  have hd : (((x^2+1)^(n-1) : ℝ) : ℂ)≠0 := by
    exact_mod_cast (by positivity : (x^2+1)^(n-1)≠0)
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using! (he x).symm

/-- A polynomial square-norm identity valid on every unit-circle point other than one also holds
at one. -/
private theorem laurent_circle_factor_extend_one {n : ℕ} (a : Fin n → ℂ)
    (P : Polynomial ℂ)
    (h : ∀ z : ℂ, ‖z‖=1 → z≠1 →
      complexLaurentEval a z=((‖P.eval z‖^2 : ℝ) : ℂ)) :
    complexLaurentEval a 1=((‖P.eval 1‖^2 : ℝ) : ℂ) := by
  let phase := fun θ : ℝ => Complex.exp ((θ : ℂ)*Complex.I)
  let F := fun θ : ℝ => complexLaurentEval a (phase θ)-((‖P.eval (phase θ)‖^2 : ℝ) : ℂ)
  have hc : Continuous phase := by fun_prop
  have hl : Continuous (fun θ : ℝ => complexLaurentEval a (phase θ)) := by
    unfold complexLaurentEval
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (hc.zpow₀ j (fun θ => Or.inl (Complex.exp_ne_zero _)))
  have hF : Continuous F := by
    have hp : Continuous (fun θ : ℝ => ((‖P.eval (phase θ)‖^2 : ℝ) : ℂ)) := by fun_prop
    exact hl.sub hp
  have he (θ : ℝ) (hθ : θ∈Set.Ioo 0 Real.pi) : F θ=0 := by
    apply sub_eq_zero.mpr
    apply h
    · exact Complex.norm_exp_ofReal_mul_I θ
    · intro hh
      have hi := congrArg Complex.im hh
      have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      simp only [phase,Complex.exp_ofReal_mul_I,Complex.add_im,Complex.ofReal_im,
        Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
        add_zero,zero_add,Complex.one_im] at hi
      linarith
  have hz : (0 : ℝ)∈_root_.closure (Set.Ioo 0 Real.pi) := by
    rw [closure_Ioo Real.pi_pos.ne]
    simp [Real.pi_pos.le]
  have hle : ‖F 0‖≤0 := le_on_closure (fun θ hθ => by rw [he θ hθ]; simp)
    hF.norm.continuousOn continuous_const.continuousOn hz
  have hf0 : F 0=0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  apply sub_eq_zero.mp
  simpa [F,phase] using! hf0

/-- Every finite complex Laurent polynomial that is nonnegative on the unit circle has a
polynomial square-norm factor there of degree at most `n - 1`. When the factor is nonzero,
all its roots lie in the closed unit disk. -/
theorem complex_laurent_circle_factor_polynomial {n : ℕ} (a : Fin n → ℂ)
    (ha : complexLaurentNonnegative a) :
    ∃ P : Polynomial ℂ, P.natDegree≤n-1 ∧
      (∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z=((‖P.eval z‖^2 : ℝ) : ℂ)) ∧
      (P≠0 → ∀ z : ℂ, P.eval z=0 → ‖z‖≤1) := by
  by_cases hn : 0<n
  · obtain ⟨q,hq,he⟩ := laurentClearedPolynomial_factor a hn ha
    let A := laurentCayleyReverse q (n-1)
    have hA : A.natDegree≤n-1 := laurentCayleyReverse_degree q (n-1)
    have hall (z : ℂ) (hz : ‖z‖=1) (hz1 : z≠1) :
        complexLaurentEval a z=((‖A.eval z‖^2 : ℝ) : ℂ) := by
      have he' := laurentCayley_signal_factor a q hq he (laurentCayleyInverse z).re
      rw [laurentCayleySignal_inverse z hz hz1] at he'
      exact he'
    have hcircle (z : ℂ) (hz : ‖z‖=1) :
        complexLaurentEval a z=((‖A.eval z‖^2 : ℝ) : ℂ) := by
      by_cases hz1 : z=1
      · subst z
        exact laurent_circle_factor_extend_one a A hall
      · exact hall z hz hz1
    obtain ⟨B,hBd,_,hBc,hBr⟩ := polynomial_closed_disk_circle_factor A
    refine ⟨B,hBd.trans hA,?_,hBr⟩
    intro z hz
    rw [hBc z hz]
    exact hcircle z hz
  · have hn0 : n=0 := by omega
    subst n
    refine ⟨0,by simp,?_,fun h => (h rfl).elim⟩
    intro z _
    norm_num [complexLaurentEval]

/-- Complex Laurent evaluation of a coerced real coefficient vector agrees with `laurentEval` at
every complex input. -/
theorem complexLaurentEval_ofReal {n : ℕ} (c : Fin n → ℝ) (z : ℂ) :
    complexLaurentEval (fun i => (c i : ℂ)) z=laurentEval c z := by
  have h0 : (complexLaurentCoefficient (fun i => (c i : ℂ)) 0).im=0 := by
    unfold complexLaurentCoefficient
    split_ifs <;> simp_all
  unfold complexLaurentEval laurentEval
  rw [sum_laurent_window]
  apply Finset.sum_congr rfl
  intro i _
  have hc := complexLaurentCoefficient_nat (fun i => (c i : ℂ)) i
  by_cases hi : i.val=0
  · rw [if_pos hi,if_pos hi]
    have hz : (i.val : ℤ)=0 := by exact_mod_cast hi
    rw [hz] at hc
    simp only [hc,zpow_zero,mul_one]
  · rw [if_neg hi,if_neg hi]
    have hn := complexLaurentCoefficient_neg (fun i => (c i : ℂ)) h0 (i.val : ℤ)
    rw [hc] at hn
    rw [hc,hn]
    simp only [Complex.star_def,Complex.conj_ofReal]
    ring

/-- Two complex polynomials are equal if their evaluations agree at every point of the unit
circle. -/
theorem polynomial_eq_of_unit_circle_eval_eq (P Q : Polynomial ℂ)
    (h : ∀ z : ℂ, ‖z‖=1 → P.eval z=Q.eval z) : P=Q := by
  have hi : Function.Injective laurentCayleySignal := by
    intro x y hxy
    have he := congrArg laurentCayleyInverse hxy
    rw [laurentCayleyInverse_signal,laurentCayleyInverse_signal] at he
    exact Complex.ofReal_injective he
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hi).mono
  rintro z ⟨x,rfl⟩
  exact h _ (laurentCayleySignal_norm x)

/-- Every nonzero complex polynomial has a nonzero evaluation at some point of the unit circle. -/
theorem exists_unit_circle_eval_ne_zero (P : Polynomial ℂ) (hP : P≠0) :
    ∃ z : ℂ, ‖z‖=1 ∧ P.eval z≠0 := by
  by_contra! h
  apply hP
  apply polynomial_eq_of_unit_circle_eval_eq
  intro z hz
  simpa using! h z hz

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
