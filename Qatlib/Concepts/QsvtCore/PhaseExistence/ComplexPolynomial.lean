/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.RealNonnegConjugateFactorization
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial

/-!
# Complex polynomial completion for QSP

This module constructs `CompletedPair` data from the degree, parity, and real- and
imaginary-axis inequalities used in complex QSP phase existence [GilyenSuLowWiebe2019]. The
construction analyzes the real coefficients of `1 - P * conjugatePolynomial P` after contraction
by the square variable.

The auxiliary lemmas factor residual polynomials with prescribed sign changes and control the
degree of the complementary polynomial.

## Main statements

* `residual_square_eval`: relates the contracted residual to the squared norm on the real axis.
* `divide_X_one_sub_X_nonneg`: extracts a globally nonnegative factor from a residual with
  endpoint zeros.
* `exists_completedPair_of_cor8_conditions`: produces a complementary polynomial satisfying
  `CompletedPair`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib

/-- The real polynomial obtained by taking the real part of every coefficient of a complex
polynomial. -/
private noncomputable def complexResidualRealCoeffs (P : Polynomial ℂ) : Polynomial ℝ :=
  ⟨⟨P.toFinsupp.coeff.mapRange Complex.re Complex.zero_re⟩⟩

/-- The jth coefficient of `complexResidualRealCoeffs P` is the real part of the jth coefficient
of P. -/
private theorem residual_real_coeff (P : Polynomial ℂ) (j : ℕ) :
    (complexResidualRealCoeffs P).coeff j = (P.coeff j).re := rfl

/-- Mapping the real coefficients of the residual `1 - P * conjugatePolynomial P` back to ℂ
recovers that residual. -/
private theorem residual_real_map (P : Polynomial ℂ) :
    (complexResidualRealCoeffs (1 - P * conjugatePolynomial P)).map Complex.ofRealHom =
      1 - P * conjugatePolynomial P := by
  have hs : conjugatePolynomial (1 - P * conjugatePolynomial P) =
      1 - P * conjugatePolynomial P := by simp [mul_comm]
  ext j
  have hj := congrArg (fun p : Polynomial ℂ => (p.coeff j).im) hs
  simp only [conjugatePolynomial_coeff, Complex.star_def, Complex.conj_im] at hj
  simp only [coeff_map, residual_real_coeff, Complex.ofRealHom_eq_coe]
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

/-- For a response polynomial with parity d, the real residual `1 - P * conjugatePolynomial P`
is invariant under composition with `-X`. -/
private theorem residual_real_even (P : Polynomial ℂ) (d : ℕ)
    (hp : HasResponseParity d P) :
    (complexResidualRealCoeffs (1 - P * conjugatePolynomial P)).comp (-X) =
      complexResidualRealCoeffs (1 - P * conjugatePolynomial P) := by
  change P.comp (-X) = C ((-1 : ℂ) ^ d) * P at hp
  have hc : (conjugatePolynomial P).comp (-X) =
      C ((-1 : ℂ) ^ d) * conjugatePolynomial P := by
    have h := congrArg conjugatePolynomial hp
    simpa [conjugatePolynomial, Polynomial.map_comp] using h
  have he : (1 - P * conjugatePolynomial P).comp (-X) =
      1 - P * conjugatePolynomial P := by
    simp only [sub_comp, one_comp, mul_comp, hp, hc]
    have hpow : ((-1 : ℂ) ^ d) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
    calc
      1 - (C ((-1 : ℂ) ^ d) * P) *
          (C ((-1 : ℂ) ^ d) * conjugatePolynomial P) =
        1 - C (((-1 : ℂ) ^ d) ^ 2) * (P * conjugatePolynomial P) := by
          simp only [map_pow]; ring
      _ = _ := by rw [hpow]; simp
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa only [Polynomial.map_comp, Polynomial.map_neg, map_X, residual_real_map] using he

/-- For a response polynomial with parity d, evaluates the contracted real residual at x² as one
minus the squared norm of P at the real input x. -/
private theorem residual_square_eval (P : Polynomial ℂ) (d : ℕ)
    (hp : HasResponseParity d P) (x : ℝ) :
    (contract 2 (complexResidualRealCoeffs (1 - P * conjugatePolynomial P))).eval (x ^ 2) =
      1 - Complex.normSq (P.eval (x : ℂ)) := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x)
    (comp_square_contract_of_even (residual_real_even P d hp))
  simp only [eval_comp, eval_pow, eval_X] at h
  rw [h]
  have hm := congrArg (fun p : Polynomial ℂ => (p.eval (x : ℂ)).re) (residual_real_map P)
  (try dsimp only at hm)
  have hev : ∀ f : Polynomial ℝ, (f.map Complex.ofRealHom).eval (x : ℂ) =
      Complex.ofReal (f.eval x) := fun f => eval_map_apply Complex.ofRealHom x
  rw [hev] at hm
  simpa only [Complex.ofReal_re, eval_sub, eval_one, eval_mul,
    conjugatePolynomial_eval_real, Complex.star_def, Complex.mul_conj,
    Complex.sub_re, Complex.one_re] using hm

/-- For a response polynomial with parity d, evaluates the contracted real residual at -y² as
one minus (-1)^d times the squared norm of P at the imaginary input yi. -/
private theorem residual_imag_eval (P : Polynomial ℂ) (d : ℕ)
    (hp : HasResponseParity d P) (y : ℝ) :
    (contract 2 (complexResidualRealCoeffs (1 - P * conjugatePolynomial P))).eval (-(y ^ 2)) =
      1 - (-1 : ℝ) ^ d * Complex.normSq (P.eval ((y : ℂ) * Complex.I)) := by
  let a := contract 2 (complexResidualRealCoeffs (1 - P * conjugatePolynomial P))
  have hid : (a.comp (X ^ 2)).map Complex.ofRealHom =
      1 - P * conjugatePolynomial P := by
    rw [comp_square_contract_of_even (residual_real_even P d hp), residual_real_map]
  have he := congrArg (fun p : Polynomial ℂ => p.eval ((y : ℂ) * Complex.I)) hid
  have hsquare : ((y : ℂ) * Complex.I) ^ 2 = Complex.ofReal (-(y ^ 2)) := by
    rw [mul_pow, Complex.I_sq]; simp
  have hev : (a.map Complex.ofRealHom).eval (Complex.ofReal (-(y ^ 2))) =
      Complex.ofReal (a.eval (-(y ^ 2))) := eval_map_apply Complex.ofRealHom _
  simp only [Polynomial.map_comp, Polynomial.map_pow, map_X, eval_comp,
    eval_pow, eval_X, hsquare, hev, eval_sub, eval_one, eval_mul] at he
  have hconj : (conjugatePolynomial P).eval ((y : ℂ) * Complex.I) =
      (-1 : ℂ) ^ d * star (P.eval ((y : ℂ) * Complex.I)) := by
    have hc := eval_map_apply (p := P) (starRingEnd ℂ) (-((y : ℂ) * Complex.I))
    have hpar := congrArg (fun p : Polynomial ℂ => p.eval ((y : ℂ) * Complex.I)) hp
    simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] at hpar
    simp only [map_neg, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, neg_neg] at hc
    change (P.map (starRingEnd ℂ)).eval ((y : ℂ) * Complex.I) = _
    rw [hc, hpar]
    simp
  rw [hconj] at he
  have hpow : (-1 : ℂ) ^ d = Complex.ofReal ((-1 : ℝ) ^ d) := by simp
  simp only [Complex.star_def] at he
  rw [mul_left_comm, Complex.mul_conj, hpow, ← Complex.ofReal_mul,
    ← Complex.ofReal_one, ← Complex.ofReal_sub] at he
  exact Complex.ofReal_injective he

/-- A real polynomial vanishing at one, nonnegative to the left of one and nonpositive to the
right, factors as `(1 - X) * g` with g nonnegative on all real inputs. -/
private theorem divide_one_sub_X_nonneg (a : Polynomial ℝ)
    (hroot : a.eval 1 = 0)
    (hleft : ∀ x : ℝ, x ≤ 1 → 0 ≤ a.eval x)
    (hright : ∀ x : ℝ, 1 ≤ x → a.eval x ≤ 0) :
    ∃ g : Polynomial ℝ, a = (1 - X) * g ∧ ∀ x : ℝ, 0 ≤ g.eval x := by
  obtain ⟨g, hg⟩ := C_sub_X_dvd_of_isRoot (show a.IsRoot 1 from hroot)
  have hfg : a = (1 - X) * g := by simpa using hg
  have ha : ∀ x : ℝ, x ≠ 1 → 0 ≤ g.eval x := by
    intro x hx
    rcases lt_or_gt_of_ne hx with hl | hr
    · apply quotient_nonneg_at hfg x (hleft x hl.le)
      simpa using sub_pos.mpr hl
    · have h := hright x hr.le
      rw [hfg, eval_mul] at h
      simp only [eval_sub, eval_one, eval_X] at h
      by_contra! hneg
      exact (not_lt_of_ge (neg_nonneg.mpr h))
        (neg_neg_of_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hr) hneg))
  refine ⟨g, hfg, fun x => ?_⟩
  by_cases hx : x = 1
  · subst x
    exact nonneg_on_Icc_of_nonneg_on_Ioo (by norm_num : (1 : ℝ) < 2)
      (fun t ht => ha t ht.1.ne') 1 ⟨le_rfl, by norm_num⟩
  · exact ha x hx

/-- A real polynomial vanishing at zero and one, nonnegative on [0, 1] and nonpositive outside,
factors as `X * (1 - X) * g` with g nonnegative on all real inputs. -/
private theorem divide_X_one_sub_X_nonneg (a : Polynomial ℝ)
    (hzero : a.eval 0 = 0) (hone : a.eval 1 = 0)
    (hinside : ∀ x : ℝ, x ∈ Set.Icc 0 1 → 0 ≤ a.eval x)
    (houtside : ∀ x : ℝ, x ≤ 0 ∨ 1 ≤ x → a.eval x ≤ 0) :
    ∃ g : Polynomial ℝ, a = X * (1 - X) * g ∧ ∀ x : ℝ, 0 ≤ g.eval x := by
  obtain ⟨b, hb⟩ := dvd_iff_isRoot.mpr (show a.IsRoot 0 from hzero)
  have hb' : a = X * b := by simpa using hb
  have hb1 : b.IsRoot 1 := by simpa [hb'] using hone
  obtain ⟨g, hg⟩ := C_sub_X_dvd_of_isRoot hb1
  have hfg : a = X * (1 - X) * g := by simpa [hg, mul_assoc] using hb'
  have ha : ∀ x : ℝ, x ≠ 0 → x ≠ 1 → 0 ≤ g.eval x := by
    intro x hx0 hx1
    by_cases hin : x ∈ Set.Icc (0 : ℝ) 1
    · apply quotient_nonneg_at hfg x (hinside x hin)
      simp only [eval_mul, eval_X, eval_sub, eval_one]
      exact mul_pos (lt_of_le_of_ne hin.1 hx0.symm) (sub_pos.mpr (lt_of_le_of_ne hin.2 hx1))
    · have ho : x ≤ 0 ∨ 1 ≤ x := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hin
        exact hin.imp le_of_lt le_of_lt
      have hfac : x * (1 - x) < 0 := by
        rcases ho with ho | ho
        · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne ho hx0) (by linarith)
        · exact mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr (lt_of_le_of_ne ho hx1.symm))
      have h := houtside x ho
      rw [hfg] at h
      simp only [eval_mul, eval_X, eval_sub, eval_one] at h
      by_contra! hneg
      exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg hfac hneg)
  have hclosed : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g.eval x :=
    nonneg_on_Icc_of_nonneg_on_Ioo (by norm_num)
      (fun t ht => ha t ht.1.ne' ht.2.ne)
  refine ⟨g, hfg, fun x => ?_⟩
  by_cases hx0 : x = 0
  · subst x; exact hclosed 0 ⟨le_rfl, by norm_num⟩
  by_cases hx1 : x = 1
  · subst x; exact hclosed 1 ⟨by norm_num, le_rfl⟩
  exact ha x hx0 hx1

/-- If P has degree at most d and `(1 - X ^ 2) * Q * conjugatePolynomial Q` is its normalization
residual, then Q has degree strictly less than d. -/
private theorem complement_degree_lt (P Q : Polynomial ℂ) (d : ℕ)
    (hp : P.degree ≤ (d : WithBot ℕ))
    (hn : (1 - X ^ 2) * Q * conjugatePolynomial Q = 1 - P * conjugatePolynomial P) :
    Q.degree < (d : WithBot ℕ) := by
  by_cases hq : Q = 0
  · simp [hq]
  have hcq : conjugatePolynomial Q ≠ 0 := by
    intro hz
    have h := congrArg conjugatePolynomial hz
    exact hq (by simpa using h)
  have hdegc (W : Polynomial ℂ) : (conjugatePolynomial W).natDegree = W.natDegree :=
    natDegree_map_eq_of_injective (star_injective) W
  have hfdeg : (1 - X ^ 2 : Polynomial ℂ).natDegree = 2 := by
    rw [natDegree_sub_eq_right_of_natDegree_lt (by simp)]
    simp
  have hf0 : (1 - X ^ 2 : Polynomial ℂ) ≠ 0 := by
    intro hz; simp [hz] at hfdeg
  have hleft : ((1 - X ^ 2) * Q * conjugatePolynomial Q).natDegree = 2 + 2 * Q.natDegree := by
    rw [natDegree_mul (mul_ne_zero hf0 hq) hcq, natDegree_mul hf0 hq, hfdeg, hdegc]
    omega
  have hpd := natDegree_le_of_degree_le hp
  have hbound : (1 - P * conjugatePolynomial P).natDegree ≤ 2 * d := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · have hmul := natDegree_mul_le (p := P) (q := conjugatePolynomial P)
      rw [hdegc] at hmul
      omega
  rw [← hn, hleft] at hbound
  rw [degree_eq_natDegree hq]
  exact_mod_cast (show Q.natDegree < d by omega)

/-- Coefficientwise conjugation commutes with composition by `X ^ 2`. -/
private theorem conjugate_comp_square (W : Polynomial ℂ) :
    conjugatePolynomial (W.comp (X ^ 2)) = (conjugatePolynomial W).comp (X ^ 2) := by
  simp [conjugatePolynomial, Polynomial.map_comp]

/-- A complex polynomial satisfying the degree, parity, interval, exterior, and even-degree
imaginary-axis conditions of Corollary 8 possesses a complementary polynomial forming
`CompletedPair d P Q` [GilyenSuLowWiebe2019]. -/
theorem exists_completedPair_of_cor8_conditions (P : Polynomial ℂ) (d : ℕ)
    (hdeg : P.degree ≤ (d : WithBot ℕ))
    (hpar : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity d P)
    (hin : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1)
    (hout : ∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
      1 ≤ Complex.normSq (P.eval (Complex.ofReal x)))
    (himag : d % 2 = 0 → ∀ y : ℝ,
      1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))) :
    ∃ Q : Polynomial ℂ, Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair d P Q := by
  let a : Polynomial ℝ := contract 2 (complexResidualRealCoeffs (1 - P * conjugatePolynomial P))
  have hsquare (x : ℝ) : a.eval (x ^ 2) = 1 - Complex.normSq (P.eval (x : ℂ)) :=
    residual_square_eval P d hpar x
  have himage (y : ℝ) : a.eval (-(y ^ 2)) =
      1 - (-1 : ℝ) ^ d * Complex.normSq (P.eval ((y : ℂ) * Complex.I)) :=
    residual_imag_eval P d hpar y
  have hain : ∀ t : ℝ, t ∈ Set.Icc 0 1 → 0 ≤ a.eval t := by
    intro t ht
    have h := hin (Real.sqrt t) ⟨by linarith [Real.sqrt_nonneg t], Real.sqrt_le_one.mpr ht.2⟩
    have he := hsquare (Real.sqrt t)
    rw [Real.sq_sqrt ht.1] at he
    linarith
  have haout : ∀ t : ℝ, 1 ≤ t → a.eval t ≤ 0 := by
    intro t ht
    have hs : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
    have h := hout (Real.sqrt t) (fun hx => (not_lt_of_ge hs) hx.2)
    have he := hsquare (Real.sqrt t)
    rw [Real.sq_sqrt (by linarith)] at he
    linarith
  have haone : a.eval 1 = 0 := le_antisymm (haout 1 le_rfl) (hain 1 ⟨by norm_num, le_rfl⟩)
  have hid : (a.comp (X ^ 2)).map Complex.ofRealHom = 1 - P * conjugatePolynomial P := by
    rw [comp_square_contract_of_even (residual_real_even P d hpar), residual_real_map]
  have finish (Q : Polynomial ℂ)
      (hQ : HasResponseParity (d + 1) Q)
      (heq : (1 - X ^ 2) * Q * conjugatePolynomial Q = 1 - P * conjugatePolynomial P) :
      ∃ Q : Polynomial ℂ, CompletedPair d P Q := by
    refine ⟨Q, hdeg, complement_degree_lt P Q d hdeg heq, hpar, hQ, ?_⟩
    unfold responsePairNorm
    rw [heq]
    ring
  by_cases he : d % 2 = 0
  · have hpow : (-1 : ℝ) ^ d = 1 := (Nat.even_iff.mpr he).neg_one_pow
    have haneg : ∀ t : ℝ, t ≤ 0 → a.eval t ≤ 0 := by
      intro t ht
      have h := himag he (Real.sqrt (-t))
      have hv := himage (Real.sqrt (-t))
      rw [Real.sq_sqrt (neg_nonneg.mpr ht), neg_neg, hpow] at hv
      linarith
    have hazero : a.eval 0 = 0 := le_antisymm (haneg 0 le_rfl) (hain 0 ⟨le_rfl, by norm_num⟩)
    obtain ⟨g, hg, hgn⟩ := divide_X_one_sub_X_nonneg a hazero haone hain
      (fun t ht => ht.elim (haneg t) (haout t))
    obtain ⟨W, hW⟩ := exists_conjugate_factor_of_nonneg g hgn
    refine finish (X * W.comp (X ^ 2)) ?_ ?_
    · have hodd : Odd (d + 1) := Nat.odd_iff.mpr (by omega)
      simp [HasResponseParity, mul_comp, comp_assoc, pow_comp, hodd.neg_one_pow]
    · rw [← hid, hg]
      simp only [mul_comp, X_comp, sub_comp, one_comp, Polynomial.map_mul,
        Polynomial.map_pow, map_X, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_comp,
        ← hW, conjugatePolynomial_mul, conjugatePolynomial_X, conjugate_comp_square]
      ring
  · have hodd : Odd d := Nat.odd_iff.mpr (by omega)
    have haneg : ∀ t : ℝ, t ≤ 0 → 0 ≤ a.eval t := by
      intro t ht
      have hv := himage (Real.sqrt (-t))
      rw [Real.sq_sqrt (neg_nonneg.mpr ht), neg_neg, hodd.neg_one_pow] at hv
      have hn := Complex.normSq_nonneg (P.eval ((Real.sqrt (-t) : ℂ) * Complex.I))
      linarith
    have haleft : ∀ t : ℝ, t ≤ 1 → 0 ≤ a.eval t := by
      intro t ht
      by_cases ht0 : 0 ≤ t
      · exact hain t ⟨ht0, ht⟩
      · exact haneg t (le_of_lt (lt_of_not_ge ht0))
    obtain ⟨g, hg, hgn⟩ := divide_one_sub_X_nonneg a haone haleft haout
    obtain ⟨W, hW⟩ := exists_conjugate_factor_of_nonneg g hgn
    refine finish (W.comp (X ^ 2)) ?_ ?_
    · have heven : Even (d + 1) := Nat.even_iff.mpr (by omega)
      simp [HasResponseParity, comp_assoc, pow_comp, heven.neg_one_pow]
    · rw [← hid, hg]
      simp only [mul_comp, sub_comp, one_comp, X_comp, Polynomial.map_mul,
        Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, map_X, Polynomial.map_comp,
        ← hW, mul_comp, conjugate_comp_square]
      ring

end Qatlib.Concepts.QsvtCore.PhaseExistence
