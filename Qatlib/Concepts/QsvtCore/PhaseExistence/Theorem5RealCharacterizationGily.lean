/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationStat
import Qatlib.Concepts.QsvtCore.PolyApprox.EvenIntervalSOS
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality

/-!
# Real parts of completed signal-processing pairs

`theorem5RealCharacterization` proves that two real polynomials satisfying the degree, parity,
and weighted interval inequality are the real parts of a complex completed pair, and conversely.
Auxiliary results transfer degree and parity through complex completion and extraction of real
parts. See [GilyenSuLowWiebe2019].

## Main statements

* `theorem5RealCharacterization`: characterize the real parts of a completed pair.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- Complex completion of two real polynomials with parity `k` has response parity `k`. -/
private theorem completion_parity {k : ℕ} {p b : Polynomial ℝ}
    (hp : HasRealParity k p) (hb : HasRealParity k b) :
    HasResponseParity k (completionP p b) := by
  have hp' := hp.map
  have hb' := hb.map
  simp only [HasResponseParity] at hp' hb' ⊢
  simp only [completionP, add_comp, mul_comp, C_comp, hp', hb']
  ring

/-- The degree of a complex completion is at most the maximum of the degrees of its two real
components. -/
private theorem completion_degree (p b : Polynomial ℝ) :
    (completionP p b).degree ≤ max p.degree b.degree := by
  unfold completionP
  refine (degree_add_le _ _).trans (max_le ?_ ?_)
  · exact degree_map_le.trans (le_max_left _ _)
  · rw [degree_C_mul (by norm_num : (Complex.I : ℂ) ≠ 0)]
    exact degree_map_le.trans (le_max_right _ _)

/-- If `p` has degree at most `k` and `q` has degree less than `k`, the residual `1 - p^2 - (1 -
X^2) * q^2` has degree at most `2 * k`. -/
private theorem residual_degree {k : ℕ} {p q : Polynomial ℝ}
    (hp : p.degree ≤ (k : WithBot ℕ)) (hq : q.degree < (k : WithBot ℕ)) :
    (1 - p ^ 2 - (1 - X ^ 2) * q ^ 2).degree ≤ ((2 * k : ℕ) : WithBot ℕ) := by
  by_cases hk : k = 0
  · subst k
    have hq0 : q = 0 := by
      by_contra hz
      rw [degree_eq_natDegree hz] at hq
      have : q.natDegree < 0 := by exact_mod_cast hq
      omega
    simp only [hq0, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
    apply degree_le_of_natDegree_le
    have hn := natDegree_le_of_degree_le hp
    have hs := natDegree_sub_le (1 : Polynomial ℝ) (p ^ 2)
    rw [natDegree_one, natDegree_pow] at hs
    omega
  apply degree_le_of_natDegree_le
  have hn := natDegree_le_of_degree_le hp
  have hqn : q.natDegree ≤ k - 1 := by
    by_cases hz : q = 0
    · simp [hz]
    · rw [degree_eq_natDegree hz] at hq
      have : q.natDegree < k := by exact_mod_cast hq
      omega
  have h1 := natDegree_sub_le (1 : Polynomial ℝ) (p ^ 2)
  rw [natDegree_one, natDegree_pow] at h1
  have hX := natDegree_sub_le (1 : Polynomial ℝ) (X ^ 2)
  rw [natDegree_one, natDegree_X_pow] at hX
  have h2 := natDegree_mul_le (p := (1 - X ^ 2 : Polynomial ℝ)) (q := q ^ 2)
  rw [natDegree_pow] at h2
  have h3 := natDegree_sub_le (1 - p ^ 2) ((1 - X ^ 2) * q ^ 2)
  omega

/-- The polynomial identity expressing `p` as the real part of `P` implies equality of their
real evaluations at every real argument. -/
private theorem real_part_eval {P : Polynomial ℂ} {p : Polynomial ℝ}
    (h : P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom)
    (x : ℝ) : (P.eval (x : ℂ)).re = p.eval x := by
  have he := congrArg (fun f : Polynomial ℂ => (f.eval (x : ℂ)).re) h
  have hm : (p.map Complex.ofRealHom).eval (x : ℂ) = Complex.ofReal (p.eval x) :=
    eval_map_apply Complex.ofRealHom x
  simp [conjugatePolynomial_eval_real, hm, Complex.mul_re] at he
  linarith

/-- A real polynomial extracted from the real part of a complex polynomial inherits its
prescribed parity. -/
private theorem real_part_parity {P : Polynomial ℂ} {p : Polynomial ℝ} {k : ℕ}
    (hp : HasResponseParity k P)
    (hr : P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom) :
    HasRealParity k p := by
  apply Polynomial.funext
  intro x
  have he := congrArg (fun f : Polynomial ℂ => (f.eval (x : ℂ)).re) hp
  have hpow : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by simp
  simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, hpow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by simp,
    real_part_eval hr (-x), real_part_eval hr x] at he
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using he

/-- The degree of a real polynomial extracted from the real part of `P` is at most the degree of
`P`. -/
private theorem real_part_degree {P : Polynomial ℂ} {p : Polynomial ℝ}
    (hr : P + conjugatePolynomial P = C (2 : ℂ) * p.map Complex.ofRealHom) :
    p.degree ≤ P.degree := by
  have hd := degree_add_le P (conjugatePolynomial P)
  rw [hr, degree_C_mul (by norm_num : (2 : ℂ) ≠ 0),
    degree_map_eq_of_injective Complex.ofRealHom.injective] at hd
  exact hd.trans (max_le le_rfl degree_map_le)

/-- Real polynomial pairs satisfying the prescribed degree and parity constraints and weighted
squared bound on `[-1, 1]` are exactly the real parts of complex completed pairs, as in
[Gilyén et al., Theorem 5][GilyenSuLowWiebe2019]. -/
theorem theorem5RealCharacterization : Theorem5RealCharacterization := by
  intro k Pt Qt
  constructor
  · rintro ⟨hP, hQ, hPp, hQp, hbound⟩
    let a : Polynomial ℝ := 1 - Pt ^ 2 - (1 - X ^ 2) * Qt ^ 2
    have heven : HasRealParity 0 a := by
      have hp2 := residual_even hPp
      have hq2 := residual_even hQp
      have hq : (Qt ^ 2).comp (-X) = Qt ^ 2 := by
        apply sub_right_inj.mp
        simpa only [sub_comp, one_comp] using hq2
      simp only [a, HasRealParity, pow_zero, C_1, one_mul, sub_comp, one_comp,
        mul_comp, pow_comp, X_comp, neg_sq, hp2, hq]
    have hnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ a.eval x := by
      intro x hx
      have h := hbound x hx
      simp only [a, eval_sub, eval_one, eval_pow, eval_mul, eval_X]
      linarith
    obtain ⟨b, c, hi, hb, hc, hbp, hcp⟩ :=
      even_interval_sos_with_source_parities a k heven (residual_degree hP hQ) hnonneg
    have hc' : c.degree < (k : WithBot ℕ) := by
      rcases hc with hz | hc
      · simp only [hz, degree_zero]
        exact WithBot.bot_lt_coe _
      · by_cases hz : c = 0
        · simp only [hz, degree_zero]
          exact WithBot.bot_lt_coe _
        · rw [degree_eq_natDegree hz] at hc ⊢
          have hn : c.natDegree + 1 ≤ k := by exact_mod_cast hc
          exact_mod_cast (show c.natDegree < k by omega)
    refine ⟨completionP Pt b, completionP Qt c, ?_,
      completionP_real_part Pt b, completionP_real_part Qt c⟩
    refine ⟨(completion_degree Pt b).trans (max_le hP hb),
      (completion_degree Qt c).trans_lt (max_lt hQ hc'),
      completion_parity hPp hbp, completion_parity hQp hcp, ?_⟩
    have hi' := congrArg (Polynomial.map Complex.ofRealHom) hi
    simp only [a, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X] at hi'
    have hi2 : (C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
      rw [← C_pow, Complex.I_sq]
      simp
    simp only [responsePairNorm, completionP, conjugatePolynomial_add,
      conjugatePolynomial_mul, conjugatePolynomial_C, conjugate_real_map,
      Complex.star_def, Complex.conj_I, map_neg]
    calc
      _ = (Pt.map Complex.ofRealHom) ^ 2 - (C Complex.I) ^ 2 * (b.map Complex.ofRealHom) ^ 2 +
          (1 - X ^ 2) * ((Qt.map Complex.ofRealHom) ^ 2 -
            (C Complex.I) ^ 2 * (c.map Complex.ofRealHom) ^ 2) := by ring
      _ = (Pt.map Complex.ofRealHom) ^ 2 + (1 - X ^ 2) * (Qt.map Complex.ofRealHom) ^ 2 +
          ((b.map Complex.ofRealHom) ^ 2 + (1 - X ^ 2) * (c.map Complex.ofRealHom) ^ 2) := by
            rw [hi2]; ring
      _ = 1 := by rw [← hi']; ring
  · rintro ⟨P, Q, hp, hPr, hQr⟩
    refine ⟨(real_part_degree hPr).trans hp.degreeP,
      (real_part_degree hQr).trans_lt hp.degreeQ,
      real_part_parity hp.parityP hPr, real_part_parity hp.parityQ hQr, ?_⟩
    intro x hx
    have hn := congrArg (Polynomial.eval (x : ℂ)) hp.normalization
    rw [responsePairNorm_eval_real, eval_one] at hn
    have hn' : Complex.normSq (P.eval (x : ℂ)) +
        (1 - x ^ 2) * Complex.normSq (Q.eval (x : ℂ)) = 1 := by exact_mod_cast hn
    have hpx : Pt.eval x ^ 2 ≤ Complex.normSq (P.eval (x : ℂ)) := by
      rw [← real_part_eval hPr x, Complex.normSq_apply]
      nlinarith [sq_nonneg (P.eval (x : ℂ)).im]
    have hqx : Qt.eval x ^ 2 ≤ Complex.normSq (Q.eval (x : ℂ)) := by
      rw [← real_part_eval hQr x, Complex.normSq_apply]
      nlinarith [sq_nonneg (Q.eval (x : ℂ)).im]
    have hs : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hm := mul_le_mul_of_nonneg_left hqx hs
    linarith

end Qatlib.Concepts.QsvtCore.PhaseExistence
