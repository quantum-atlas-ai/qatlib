/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.ComplexPolynomial
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib

theorem conjugatePolynomial_eval_imag {W : Polynomial ℂ} {m : ℕ}
    (hW : HasResponseParity m W) (y : ℝ) :
    (conjugatePolynomial W).eval ((y : ℂ) * Complex.I) =
      (-1 : ℂ) ^ m * star (W.eval ((y : ℂ) * Complex.I)) := by
  have hc := eval_map_apply (p := W) (starRingEnd ℂ) (-((y : ℂ) * Complex.I))
  have hpar := congrArg (fun p : Polynomial ℂ => p.eval ((y : ℂ) * Complex.I)) hW
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hpar
  simp only [map_neg, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_neg, neg_neg] at hc
  change (W.map (starRingEnd ℂ)).eval ((y : ℂ) * Complex.I) = _
  rw [hc, hpar]
  simp

private theorem eval_one_sub_X_sq (x : ℝ) :
    (1 - X ^ 2 : Polynomial ℂ).eval (x : ℂ) = Complex.ofReal (1 - x ^ 2) := by
  simp only [eval_sub, eval_one, eval_pow, eval_X]
  apply Complex.ext
  · simp
  · simp

private theorem eval_one_sub_imag_sq (y : ℝ) :
    (1 - X ^ 2 : Polynomial ℂ).eval ((y : ℂ) * Complex.I) = Complex.ofReal (1 + y ^ 2) := by
  simp only [eval_sub, eval_one, eval_pow, eval_X]
  have hsq : ((y : ℂ) * Complex.I) ^ 2 = Complex.ofReal (-(y ^ 2)) := by
    rw [mul_pow, Complex.I_sq]
    apply Complex.ext
    · simp
    · simp
  rw [hsq]
  apply Complex.ext
  · simp
  · simp

private theorem imag_mul_conj (z : ℂ) : z * star z = Complex.ofReal (Complex.normSq z) := by
  rw [Complex.star_def, Complex.mul_conj]

private theorem mul_ofReal_mul_conj (z : ℂ) (c : ℝ) :
    z * (Complex.ofReal c * star z) = Complex.ofReal (c * Complex.normSq z) := by
  have h1 : z * (Complex.ofReal c * star z) = Complex.ofReal c * (z * star z) := by ring
  rw [h1, imag_mul_conj, Complex.ofReal_mul]

private theorem ofReal_mul_ofReal_mul_conj (a c : ℝ) (z : ℂ) :
    Complex.ofReal a * (z * (Complex.ofReal c * star z)) =
      Complex.ofReal (a * (c * Complex.normSq z)) := by
  have h1 : z * (Complex.ofReal c * star z) = Complex.ofReal c * (z * star z) := by ring
  rw [h1, imag_mul_conj, Complex.ofReal_mul, Complex.ofReal_mul]

private theorem eval_one_C (x : ℂ) : Polynomial.eval x (1 : Polynomial ℂ) = Complex.ofReal 1 := by
  simp

private theorem one_sub_sq_complex (x : ℝ) :
    (1 : ℂ) - (x : ℂ) ^ 2 = Complex.ofReal (1 - x ^ 2) := by
  apply Complex.ext <;> simp

private theorem one_sub_imag_sq_complex (y : ℝ) :
    (1 : ℂ) - ((y : ℂ) * Complex.I) ^ 2 = Complex.ofReal (1 + y ^ 2) := by
  have h := eval_one_sub_imag_sq y
  rw [eval_sub, eval_one, eval_pow, eval_X] at h
  exact h

private theorem ofReal_mul_star_re (a c : ℝ) (z : ℂ) :
    (Complex.ofReal a * (z * (Complex.ofReal c * star z))).re
      = (a * c) * Complex.normSq z := by
  have hc : Complex.ofReal a * Complex.ofReal c = Complex.ofReal (a * c) :=
    (Complex.ofReal_mul a c).symm
  have h : Complex.ofReal a * (z * (Complex.ofReal c * star z))
      = Complex.ofReal ((a * c) * Complex.normSq z) := by
    calc
      Complex.ofReal a * (z * (Complex.ofReal c * star z))
          = z * ((Complex.ofReal a * Complex.ofReal c) * star z) := by ring
      _ = z * (Complex.ofReal (a * c) * star z) := by rw [hc]
      _ = Complex.ofReal ((a * c) * Complex.normSq z) := mul_ofReal_mul_conj z (a * c)
  rw [h, Complex.ofReal_re]

private theorem ofReal_mul_star_re_l (a c : ℝ) (z : ℂ) :
    (Complex.ofReal a * z * (Complex.ofReal c * star z)).re
      = (a * c) * Complex.normSq z := by
  have h : Complex.ofReal a * z * (Complex.ofReal c * star z)
      = Complex.ofReal a * (z * (Complex.ofReal c * star z)) := by ring
  rw [h, ofReal_mul_star_re]

private theorem ofReal_mul_star_re' (a : ℝ) (z : ℂ) :
    (Complex.ofReal a * (z * star z)).re = a * Complex.normSq z := by
  have h : Complex.ofReal a * (z * star z) = Complex.ofReal (a * Complex.normSq z) := by
    calc
      Complex.ofReal a * (z * star z) = z * (Complex.ofReal a * star z) := by ring
      _ = Complex.ofReal (a * Complex.normSq z) := mul_ofReal_mul_conj z a
  rw [h, Complex.ofReal_re]

theorem responsePairNorm_eval_real (P Q : Polynomial ℂ) (x : ℝ) :
    (responsePairNorm P Q).eval (x : ℂ) =
      Complex.ofReal (Complex.normSq (P.eval (x : ℂ))
        + (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ))) := by
  have hrewrite : responsePairNorm P Q =
      P * conjugatePolynomial P + (1 - X ^ 2) * (Q * conjugatePolynomial Q) := by
    unfold responsePairNorm
    ring
  rw [hrewrite]
  simp only [eval_add, eval_mul, eval_one_sub_X_sq, conjugatePolynomial_eval_real]
  rw [imag_mul_conj (P.eval (x : ℂ)), imag_mul_conj (Q.eval (x : ℂ))]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_add]

theorem responsePairNorm_eval_imag {n : ℕ} {P Q : Polynomial ℂ}
    (hP : HasResponseParity n P) (hQ : HasResponseParity (n + 1) Q) (y : ℝ) :
    (responsePairNorm P Q).eval ((y : ℂ) * Complex.I) =
      Complex.ofReal ((-1 : ℝ) ^ n *
        (Complex.normSq (P.eval ((y : ℂ) * Complex.I))
          - (1 + y ^ 2) * Complex.normSq (Q.eval ((y : ℂ) * Complex.I)))) := by
  have hrewrite : responsePairNorm P Q =
      P * conjugatePolynomial P + (1 - X ^ 2) * (Q * conjugatePolynomial Q) := by
    unfold responsePairNorm
    ring
  rw [hrewrite]
  simp only [eval_add, eval_mul, eval_one_sub_imag_sq]
  rw [conjugatePolynomial_eval_imag hP y, conjugatePolynomial_eval_imag hQ y]
  have hpow (m : ℕ) : (-1 : ℂ) ^ m = Complex.ofReal ((-1 : ℝ) ^ m) := by simp
  rw [hpow n, hpow (n + 1)]
  rw [mul_ofReal_mul_conj (P.eval ((y : ℂ) * Complex.I)),
    ofReal_mul_ofReal_mul_conj (1 + y ^ 2) ((-1 : ℝ) ^ (n + 1))
      (Q.eval ((y : ℂ) * Complex.I))]
  rw [← Complex.ofReal_add]
  apply congrArg Complex.ofReal
  ring

namespace PhaseSynthesis

theorem CompletedPair.normSq_eval_le_one {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Complex.normSq (P.eval (x : ℂ)) ≤ 1 := by
  have hn := congrArg (Polynomial.eval (x : ℂ)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_real P Q x] at hn
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.eval_one_C] at hn
  have hn := Complex.ofReal_injective hn
  have hq := Complex.normSq_nonneg (Q.eval (x : ℂ))
  have hxx : 0 ≤ 1 - x ^ 2 := by
    have h1 : (-1 : ℝ) ≤ x := hx.1
    have h2 : x ≤ 1 := hx.2
    nlinarith
  nlinarith

theorem CompletedPair.one_le_normSq_eval {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) {x : ℝ} (hx : x ∉ Set.Ioo (-1 : ℝ) 1) :
    1 ≤ Complex.normSq (P.eval (x : ℂ)) := by
  have hn := congrArg (Polynomial.eval (x : ℂ)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_real P Q x] at hn
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.eval_one_C] at hn
  have hn := Complex.ofReal_injective hn
  have hq := Complex.normSq_nonneg (Q.eval (x : ℂ))
  have hxx : x ^ 2 - 1 ≥ 0 := by
    by_contra! hc
    have hsq : x ^ 2 < 1 := by linarith
    exact hx ⟨(by nlinarith [hsq]), (by nlinarith [hsq])⟩
  nlinarith

theorem CompletedPair.one_le_normSq_eval_imag {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) (heven : n % 2 = 0) (y : ℝ) :
    1 ≤ Complex.normSq (P.eval ((y : ℂ) * Complex.I)) := by
  have hpow : (-1 : ℝ) ^ n = 1 := (Nat.even_iff.mpr heven).neg_one_pow
  have hn := congrArg (Polynomial.eval ((y : ℂ) * Complex.I)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_imag h.parityP h.parityQ y] at hn
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.eval_one_C] at hn
  have hn := Complex.ofReal_injective hn
  have hq := Complex.normSq_nonneg (Q.eval ((y : ℂ) * Complex.I))
  have hpos : 0 ≤ (1 + y ^ 2) * Complex.normSq (Q.eval ((y : ℂ) * Complex.I)) :=
    mul_nonneg (by positivity) hq
  nlinarith [hpow, hpos]

theorem CompletedPair.scaled_normSq_eval_le_one {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) ≤ 1 := by
  have hn := congrArg (Polynomial.eval (x : ℂ)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_real P Q x] at hn
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.eval_one_C] at hn
  have hn := Complex.ofReal_injective hn
  have hp := Complex.normSq_nonneg (P.eval (x : ℂ))
  have hxx : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  linarith

theorem CompletedPair.one_le_scaled_normSq_eval_imag {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) (hodd : n % 2 = 1) (y : ℝ) :
    1 ≤ (1 + y ^ 2) * Complex.normSq (Q.eval ((y : ℂ) * Complex.I)) := by
  have hpow : (-1 : ℝ) ^ n = -1 := (Nat.odd_iff.mpr hodd).neg_one_pow
  have hn := congrArg (Polynomial.eval ((y : ℂ) * Complex.I)) h.normalization
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.responsePairNorm_eval_imag h.parityP h.parityQ y] at hn
  rw [Qatlib.Concepts.QsvtCore.PhaseExistence.eval_one_C] at hn
  have hn := Complex.ofReal_injective hn
  have hp := Complex.normSq_nonneg (P.eval ((y : ℂ) * Complex.I))
  have hpos : 0 ≤ Complex.normSq (P.eval ((y : ℂ) * Complex.I)) := hp
  nlinarith [hpow, hpos]

end PhaseSynthesis

private noncomputable def dualResidualRealCoeffs (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re Complex.zero_re⟩⟩

private theorem dualResidual_real_coeff (P : Polynomial ℂ) (j : ℕ) :
    (dualResidualRealCoeffs P).coeff j = (P.coeff j).re := rfl

private theorem dualResidual_real_map {P : Polynomial ℂ}
    (hs : conjugatePolynomial P = P) :
    (dualResidualRealCoeffs P).map Complex.ofRealHom = P := by
  ext j
  have hj := congrArg (fun p : Polynomial ℂ => (p.coeff j).im) hs
  simp only [conjugatePolynomial_coeff, Complex.star_def, Complex.conj_im] at hj
  simp only [coeff_map, dualResidual_real_coeff, Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

private theorem dualResidual_self_conj (Q : Polynomial ℂ) :
    conjugatePolynomial (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q) =
      1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := by
  simp only [conjugatePolynomial_sub, conjugatePolynomial_one, conjugatePolynomial_mul,
    conjugatePolynomial_pow, conjugatePolynomial_X, conjugatePolynomial_conjugate]
  ring

private theorem dualResidual_real_even (Q : Polynomial ℂ) (n : ℕ)
    (hp : HasResponseParity (n + 1) Q) :
    (dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q)).comp (-X) =
      dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q) := by
  change Q.comp (-X) = C ((-1 : ℂ) ^ (n + 1)) * Q at hp
  have hc : (conjugatePolynomial Q).comp (-X) =
      C ((-1 : ℂ) ^ (n + 1)) * conjugatePolynomial Q := by
    have h := congrArg conjugatePolynomial hp
    simpa [conjugatePolynomial, Polynomial.map_comp] using! h
  have h1X2 : (-X : Polynomial ℂ) ^ 2 = X ^ 2 := by
    rw [pow_two]; ring_nf
  have he : (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q).comp (-X) =
      1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := by
    simp only [sub_comp, one_comp, mul_comp, pow_comp, X_comp, hp, hc, h1X2]
    have hpow : ((-1 : ℂ) ^ (n + 1)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul]; norm_num
    calc
      1 - (1 - X ^ 2) * (C ((-1 : ℂ) ^ (n + 1)) * Q) *
          (C ((-1 : ℂ) ^ (n + 1)) * conjugatePolynomial Q) =
        1 - (1 - X ^ 2) * C (((-1 : ℂ) ^ (n + 1)) ^ 2) *
            (Q * conjugatePolynomial Q) := by
            simp only [map_pow]; ring
      _ = _ := by rw [hpow]; norm_num; ring
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa only [Polynomial.map_comp, Polynomial.map_neg, map_X, dualResidual_real_map
    (dualResidual_self_conj Q)] using! he

private theorem dualResidual_comp_square_raw (Q : Polynomial ℂ) (n : ℕ)
    (hp : HasResponseParity (n + 1) Q) :
    (contract 2 (dualResidualRealCoeffs
      (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q))).comp (X ^ 2) =
      dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q) :=
  comp_square_contract_of_even (dualResidual_real_even Q n hp)

private theorem dualResidual_comp_square (Q : Polynomial ℂ) (n : ℕ)
    (hp : HasResponseParity (n + 1) Q) :
    ((contract 2 (dualResidualRealCoeffs
      (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q))).comp (X ^ 2)).map
        Complex.ofRealHom =
      1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := by
  rw [dualResidual_comp_square_raw Q n hp,
    dualResidual_real_map (dualResidual_self_conj Q)]

private theorem dualResidual_square_eval (Q : Polynomial ℂ) (n : ℕ)
    (hp : HasResponseParity (n + 1) Q) (x : ℝ) :
    (contract 2 (dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q))).eval
        (x ^ 2) =
      1 - (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (dualResidual_comp_square_raw Q n hp)
  simp only [eval_comp, eval_pow, eval_X] at h
  rw [h]
  have hm := congrArg (fun p : Polynomial ℂ => (p.eval (x : ℂ)).re)
    (dualResidual_real_map (dualResidual_self_conj Q))

  have hev : ∀ f : Polynomial ℝ, (f.map Complex.ofRealHom).eval (x : ℂ) =
      Complex.ofReal (f.eval x) := fun f => eval_map_apply Complex.ofRealHom x
  rw [hev] at hm
  have hre : ((1 - (1 - X ^ 2) * Q * conjugatePolynomial Q).eval (x : ℂ)).re =
      1 - (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) := by
    simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X, mul_assoc,
      conjugatePolynomial_eval_real]
    simp only [Complex.sub_re, Complex.one_re, one_sub_sq_complex,
      ofReal_mul_star_re' (1 - x ^ 2)]
  rw [hre] at hm
  exact hm

private theorem dualResidual_imag_eval (Q : Polynomial ℂ) (n : ℕ)
    (hp : HasResponseParity (n + 1) Q) (y : ℝ) :
    (contract 2 (dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q))).eval
        (-(y ^ 2)) =
      1 - (-1 : ℝ) ^ (n + 1) * (1 + y ^ 2) *
        Complex.normSq (Q.eval ((y : ℂ) * Complex.I)) := by
  have hid := dualResidual_comp_square Q n hp
  have he := congrArg (Polynomial.eval ((y : ℂ) * Complex.I)) hid
  have hsquare : ((y : ℂ) * Complex.I) ^ 2 = Complex.ofReal (-(y ^ 2)) := by
    rw [mul_pow, Complex.I_sq]
    simp
  have hev : ∀ f : Polynomial ℝ, (f.map Complex.ofRealHom).eval (Complex.ofReal (-(y ^ 2))) =
      Complex.ofReal (f.eval (-(y ^ 2))) := fun f => eval_map_apply Complex.ofRealHom _
  simp only [Polynomial.map_comp, Polynomial.map_pow, map_X, eval_comp,
    eval_pow, eval_X, hsquare, hev] at he
  have hr := congrArg Complex.re he
  simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X,
    conjugatePolynomial_eval_imag hp y] at hr
  have hpow : (-1 : ℂ) ^ (n + 1) = Complex.ofReal ((-1 : ℝ) ^ (n + 1)) := by simp
  rw [hpow] at hr
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, one_sub_imag_sq_complex,
    ofReal_mul_star_re_l (1 + y ^ 2) ((-1 : ℝ) ^ (n + 1))] at hr
  rw [hr]
  ring

private theorem divide_X_nonneg (a : Polynomial ℝ)
    (hzero : a.eval 0 = 0)
    (hright : ∀ x : ℝ, 0 ≤ x → 0 ≤ a.eval x)
    (hleft : ∀ x : ℝ, x ≤ 0 → a.eval x ≤ 0) :
    ∃ g : Polynomial ℝ, a = X * g ∧ ∀ x : ℝ, 0 ≤ g.eval x := by
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr (show a.IsRoot 0 from hzero)
  have hfg : a = X * g := by
    have hx0 : X - C (0 : ℝ) = X := by simp
    rw [hg, hx0]
  have ha : ∀ x : ℝ, x ≠ 0 → 0 ≤ g.eval x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hl | hr
    · have h := hleft x hl.le
      rw [hfg] at h
      simp only [eval_mul, eval_X] at h
      by_contra! hneg
      exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg (by linarith) hneg)
    · apply quotient_nonneg_at hfg x (hright x hr.le) (by simpa using! hr)
  refine ⟨g, hfg, fun x => ?_⟩
  by_cases hx : x = 0
  · subst x
    exact nonneg_on_Icc_of_nonneg_on_Ioo (by norm_num : (0 : ℝ) < 1)
      (fun t ht => ha t ht.1.ne') 0 ⟨le_rfl, by norm_num⟩
  · exact ha x hx

private theorem dual_degree_le (Q : Polynomial ℂ) (n : ℕ)
    (hdeg : Q.degree < (n : WithBot ℕ))
    (P : Polynomial ℂ) (hP : P * conjugatePolynomial P =
      1 - (1 - X ^ 2) * Q * conjugatePolynomial Q) :
    P.degree ≤ (n : WithBot ℕ) := by
  have hdegc (W : Polynomial ℂ) : (conjugatePolynomial W).natDegree = W.natDegree :=
    natDegree_map_eq_of_injective (star_injective) W
  have hfdeg : (1 - X ^ 2 : Polynomial ℂ).natDegree = 2 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    simp
  by_cases hp0 : P = 0
  · rw [hp0, degree_zero]
    exact bot_le
  have hcP : conjugatePolynomial P ≠ 0 := by
    intro hz
    have h := congrArg conjugatePolynomial hz
    exact hp0 (by simpa using! h)
  have hmul' : (P * conjugatePolynomial P).natDegree = 2 * P.natDegree := by
    rw [natDegree_mul hp0 hcP, hdegc]
    ring
  have hbound : (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q).natDegree ≤ 2 * n := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · by_cases hq0 : Q = 0
      · have h1 : (1 - X ^ 2) * Q * conjugatePolynomial Q = 0 := by
          rw [hq0, conjugatePolynomial_zero]
          ring
        rw [h1, natDegree_zero]
        exact Nat.zero_le _
      · have hqn : Q.natDegree < n := by
          rw [degree_eq_natDegree hq0] at hdeg
          exact_mod_cast hdeg
        have h1 := natDegree_mul_le (p := (1 - X ^ 2 : Polynomial ℂ)) (q := Q)
        have h1' : ((1 - X ^ 2) * Q).natDegree ≤ 2 + Q.natDegree := by
          rw [hfdeg] at h1
          exact h1
        have h2 := natDegree_mul_le (p := ((1 - X ^ 2) * Q : Polynomial ℂ))
          (q := conjugatePolynomial Q)
        exact le_trans h2 (by rw [hdegc Q]; omega)
  rw [← hP, hmul'] at hbound
  apply degree_le_of_natDegree_le
  omega

private theorem map_comp_pow_two (g : Polynomial ℝ) :
    (g.map Complex.ofRealHom).comp (X ^ 2) = (g.comp (X ^ 2)).map Complex.ofRealHom := by
  have h := @Polynomial.map_comp ℝ ℂ _ _ Complex.ofRealHom g (X ^ 2)
  rw [Polynomial.map_pow, Polynomial.map_X] at h
  exact h.symm

private theorem conjugate_comp_square (W : Polynomial ℂ) :
    conjugatePolynomial (W.comp (X ^ 2)) = (conjugatePolynomial W).comp (X ^ 2) := by
  simp [conjugatePolynomial, Polynomial.map_comp]

theorem exists_completedPair_of_q_conditions (Q : Polynomial ℂ) (n : ℕ)
    (hdeg : Q.degree < (n : WithBot ℕ))
    (hpar : HasResponseParity (n + 1) Q)
    (hin : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      (1 - x ^ 2) * Complex.normSq (Q.eval (Complex.ofReal x)) ≤ 1)
    (himag : n % 2 = 1 → ∀ y : ℝ,
      1 ≤ (1 + y ^ 2) * Complex.normSq (Q.eval (Complex.ofReal y * Complex.I))) :
    ∃ P : Polynomial ℂ, CompletedPair n P Q := by
  let a : Polynomial ℝ :=
    contract 2 (dualResidualRealCoeffs (1 - (1 - X ^ 2) * Q * conjugatePolynomial Q))
  have hsquare (x : ℝ) : a.eval (x ^ 2) =
      1 - (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) :=
    dualResidual_square_eval Q n hpar x
  have himage (y : ℝ) : a.eval (-(y ^ 2)) =
      1 - (-1 : ℝ) ^ (n + 1) * (1 + y ^ 2) *
        Complex.normSq (Q.eval ((y : ℂ) * Complex.I)) :=
    dualResidual_imag_eval Q n hpar y
  have hid : (a.comp (X ^ 2)).map Complex.ofRealHom =
      1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := by
    exact dualResidual_comp_square Q n hpar

  have hapos : ∀ t : ℝ, 0 ≤ t → 0 ≤ a.eval t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hx0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
      have h := hin (Real.sqrt t) ⟨by linarith [hx0], Real.sqrt_le_one.mpr ht1⟩
      have he := hsquare (Real.sqrt t)
      rw [Real.sq_sqrt ht] at he h
      linarith
    · have he := hsquare (Real.sqrt t)
      rw [Real.sq_sqrt ht] at he
      have hq := Complex.normSq_nonneg (Q.eval ((Real.sqrt t : ℝ) : ℂ))
      have hpos : 0 ≤ (t - 1) * Complex.normSq (Q.eval ((Real.sqrt t : ℝ) : ℂ)) :=
        mul_nonneg (by linarith [le_of_not_ge ht1]) hq
      linarith
  have hfinish (P : Polynomial ℂ) (hparP : HasResponseParity n P)
      (hPP : P * conjugatePolynomial P = 1 - (1 - X ^ 2) * Q * conjugatePolynomial Q) :
      ∃ P : Polynomial ℂ, CompletedPair n P Q :=
    ⟨P, dual_degree_le Q n hdeg P hPP, hdeg, hparP, hpar, by
      unfold responsePairNorm
      rw [hPP]
      ring⟩
  by_cases he : n % 2 = 0
  · have hodd1 : Odd (n + 1) := Nat.odd_iff.mpr (by omega)
    have hpos : ∀ t : ℝ, 0 ≤ a.eval t := by
      intro t
      by_cases ht0 : 0 ≤ t
      · exact hapos t ht0
      · have hv := himage (Real.sqrt (-t))
        rw [Real.sq_sqrt (neg_nonneg.mpr (le_of_not_ge ht0)), neg_neg,
          hodd1.neg_one_pow] at hv
        have hq := Complex.normSq_nonneg
          (Q.eval ((Real.sqrt (-t) : ℂ) * Complex.I))
        have hmul : 0 ≤ (1 - t) * Complex.normSq
            (Q.eval ((Real.sqrt (-t) : ℂ) * Complex.I)) :=
          mul_nonneg (by linarith [le_of_not_ge ht0]) hq
        linarith
    obtain ⟨W, hW⟩ := exists_conjugate_factor_of_nonneg a hpos
    refine hfinish (W.comp (X ^ 2)) ?_ ?_
    · have heven : Even n := Nat.even_iff.mpr he
      simp [HasResponseParity, comp_assoc, pow_comp, heven.neg_one_pow]
    calc
      (W.comp (X ^ 2)) * conjugatePolynomial (W.comp (X ^ 2))
          = (W * conjugatePolynomial W).comp (X ^ 2) := by
            rw [conjugate_comp_square, mul_comp]
      _ = (a.map Complex.ofRealHom).comp (X ^ 2) := by rw [hW]
      _ = (a.comp (X ^ 2)).map Complex.ofRealHom := map_comp_pow_two a
      _ = 1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := hid
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    have heven1 : Even (n + 1) := Nat.even_iff.mpr (by omega)
    have hodd2 : n % 2 = 1 := Nat.odd_iff.mp hodd
    have hneganeg : ∀ t : ℝ, t ≤ 0 → a.eval t ≤ 0 := by
      intro t ht
      have h := himag hodd2 (Real.sqrt (-t))
      have hv := himage (Real.sqrt (-t))
      rw [Real.sq_sqrt (neg_nonneg.mpr ht), neg_neg, heven1.neg_one_pow] at hv
      rw [Real.sq_sqrt (neg_nonneg.mpr ht)] at h
      linarith
    have hazero : a.eval 0 = 0 := le_antisymm (hneganeg 0 le_rfl) (hapos 0 le_rfl)
    obtain ⟨g, hg, hgn⟩ := divide_X_nonneg a hazero hapos hneganeg
    obtain ⟨W, hW⟩ := exists_conjugate_factor_of_nonneg g hgn
    refine hfinish (X * W.comp (X ^ 2)) ?_ ?_
    · simp [HasResponseParity, mul_comp, comp_assoc, pow_comp, hodd.neg_one_pow]
    calc
      (X * W.comp (X ^ 2)) * conjugatePolynomial (X * W.comp (X ^ 2))
          = X * (X * ((W * conjugatePolynomial W).comp (X ^ 2))) := by
            rw [conjugatePolynomial_mul, conjugatePolynomial_X, conjugate_comp_square,
              mul_comp]
            ring
      _ = X * (X * ((g.map Complex.ofRealHom).comp (X ^ 2))) := by rw [hW]
      _ = X * (X * ((g.comp (X ^ 2)).map Complex.ofRealHom)) :=
            congrArg (fun t => X * (X * t)) (map_comp_pow_two g)
      _ = ((X * g).comp (X ^ 2)).map Complex.ofRealHom := by
            rw [← map_comp_pow_two g]
            simp only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_X,
              Polynomial.map_pow]
            rw [Polynomial.mul_comp, Polynomial.X_comp]
            ring
      _ = (a.comp (X ^ 2)).map Complex.ofRealHom := by rw [hg]
      _ = 1 - (1 - X ^ 2) * Q * conjugatePolynomial Q := hid

end Qatlib.Concepts.QsvtCore.PhaseExistence
