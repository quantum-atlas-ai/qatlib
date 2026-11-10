/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
set_option warningAsError false


open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

noncomputable def conjugatePolynomial (P : Polynomial ℂ) : Polynomial ℂ :=
  P.map (starRingEnd ℂ)

@[simp] theorem conjugatePolynomial_coeff (P : Polynomial ℂ) (k : ℕ) :
    (conjugatePolynomial P).coeff k = star (P.coeff k) := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_C (z : ℂ) :
    conjugatePolynomial (C z) = C (star z) := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_X :
    conjugatePolynomial (X : Polynomial ℂ) = X := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_zero :
    conjugatePolynomial (0 : Polynomial ℂ) = 0 := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_one :
    conjugatePolynomial (1 : Polynomial ℂ) = 1 := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_add (P Q : Polynomial ℂ) :
    conjugatePolynomial (P + Q) = conjugatePolynomial P + conjugatePolynomial Q := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_sub (P Q : Polynomial ℂ) :
    conjugatePolynomial (P - Q) = conjugatePolynomial P - conjugatePolynomial Q := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_mul (P Q : Polynomial ℂ) :
    conjugatePolynomial (P * Q) = conjugatePolynomial P * conjugatePolynomial Q := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_pow (P : Polynomial ℂ) (n : ℕ) :
    conjugatePolynomial (P ^ n) = conjugatePolynomial P ^ n := by
  simp [conjugatePolynomial]

@[simp] theorem conjugatePolynomial_conjugate (P : Polynomial ℂ) :
    conjugatePolynomial (conjugatePolynomial P) = P := by
  ext k
  simp

@[simp] theorem conjugatePolynomial_eval_real (P : Polynomial ℂ) (x : ℝ) :
    (conjugatePolynomial P).eval (x : ℂ) = star (P.eval (x : ℂ)) := by
  simpa [conjugatePolynomial] using
    (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (x : ℂ))

theorem response_conjugate (base : ℂ) (zs : List ℂ) :
    responseP (star base) (zs.map star) = conjugatePolynomial (responseP base zs) ∧
    responseQ (star base) (zs.map star) = conjugatePolynomial (responseQ base zs) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, responseP_cons, responseQ_cons]
    rw [ih.1, ih.2]
    constructor <;> simp

noncomputable def responsePairNorm (P Q : Polynomial ℂ) : Polynomial ℂ :=
  P * conjugatePolynomial P + (1 - X ^ 2) * Q * conjugatePolynomial Q

private theorem phase_C_mul {z : ℂ} (hz : IsPhase z) :
    C (star z) * C z = (1 : Polynomial ℂ) := by
  rw [← C_mul]
  change C (star z * z) = 1
  rw [show star z * z = 1 from hz, C_1]

theorem isPhase_conjugate {z : ℂ} (hz : IsPhase z) : IsPhase (star z) := by
  simpa only [IsPhase, star_star, mul_comm] using hz

theorem isPhase_iff_normSq {z : ℂ} : IsPhase z ↔ Complex.normSq z = 1 := by
  constructor
  · exact IsPhase.normSq
  · intro h
    change star z * z = 1
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, h]
    rfl

private theorem responsePairNorm_signal (P Q : Polynomial ℂ) :
    responsePairNorm (X * P + (1 - X ^ 2) * Q) (P - X * Q) =
      responsePairNorm P Q := by
  simp only [responsePairNorm, conjugatePolynomial_add, conjugatePolynomial_sub,
    conjugatePolynomial_mul, conjugatePolynomial_pow, conjugatePolynomial_one,
    conjugatePolynomial_X]
  ring

private theorem responsePairNorm_phase {z : ℂ} (hz : IsPhase z) (P Q : Polynomial ℂ) :
    responsePairNorm (C z * P) (C (star z) * Q) = responsePairNorm P Q := by
  simp only [responsePairNorm, conjugatePolynomial_mul, conjugatePolynomial_C, star_star]
  calc
    C z * P * (C (star z) * conjugatePolynomial P) +
        (1 - X ^ 2) * (C (star z) * Q) * (C z * conjugatePolynomial Q) =
      (C (star z) * C z) *
        (P * conjugatePolynomial P + (1 - X ^ 2) * Q * conjugatePolynomial Q) := by ring
    _ = P * conjugatePolynomial P + (1 - X ^ 2) * Q * conjugatePolynomial Q := by
      rw [phase_C_mul hz, one_mul]

theorem response_polynomial_normalization {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    responsePairNorm (responseP base zs) (responseQ base zs) = 1 := by
  induction zs with
  | nil =>
    simp only [responseP_nil, responseQ_nil, responsePairNorm, conjugatePolynomial_C,
      conjugatePolynomial_zero, mul_zero, add_zero]
    simpa only [mul_comm] using phase_C_mul hb
  | cons z zs ih =>
    rw [responseP_cons, responseQ_cons,
      responsePairNorm_phase (hzs z (by simp)), responsePairNorm_signal]
    exact ih (fun w hw => hzs w (List.mem_cons_of_mem z hw))

def HasResponseParity (n : ℕ) (P : Polynomial ℂ) : Prop :=
  P.comp (-X) = C ((-1 : ℂ) ^ n) * P

structure CompletedPair (n : ℕ) (P Q : Polynomial ℂ) : Prop where
  degreeP : P.degree ≤ (n : WithBot ℕ)
  degreeQ : Q.degree < (n : WithBot ℕ)
  parityP : HasResponseParity n P
  parityQ : HasResponseParity (n + 1) Q
  normalization : responsePairNorm P Q = 1

noncomputable def inverseResponseP (z : ℂ) (P Q : Polynomial ℂ) : Polynomial ℂ :=
  X * (C (star z) * P) + (1 - X ^ 2) * (C z * Q)

noncomputable def inverseResponseQ (z : ℂ) (P Q : Polynomial ℂ) : Polynomial ℂ :=
  C (star z) * P - X * (C z * Q)

theorem inverseResponse_signal (z : ℂ) (P Q : Polynomial ℂ) :
    X * inverseResponseP z P Q + (1 - X ^ 2) * inverseResponseQ z P Q = C (star z) * P ∧
    inverseResponseP z P Q - X * inverseResponseQ z P Q = C z * Q := by
  simp only [inverseResponseP, inverseResponseQ]
  constructor <;> ring

theorem inverseResponse_reconstruct {z : ℂ} (hz : IsPhase z) (P Q : Polynomial ℂ) :
    C z * (X * inverseResponseP z P Q + (1 - X ^ 2) * inverseResponseQ z P Q) = P ∧
    C (star z) * (inverseResponseP z P Q - X * inverseResponseQ z P Q) = Q := by
  rw [(inverseResponse_signal z P Q).1, (inverseResponse_signal z P Q).2]
  constructor
  · calc
      C z * (C (star z) * P) = (C (star z) * C z) * P := by ring
      _ = P := by rw [phase_C_mul hz, one_mul]
  · rw [← mul_assoc, phase_C_mul hz, one_mul]

theorem inverseResponse_normalization {z : ℂ} (hz : IsPhase z) (P Q : Polynomial ℂ) :
    responsePairNorm (inverseResponseP z P Q) (inverseResponseQ z P Q) =
      responsePairNorm P Q := by
  unfold inverseResponseP inverseResponseQ
  rw [responsePairNorm_signal]
  simpa only [star_star] using responsePairNorm_phase (isPhase_conjugate hz) P Q

theorem CompletedPair.normSq_eval_one {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) : Complex.normSq (P.eval 1) = 1 := by
  have he := congrArg (Polynomial.eval (1 : ℂ)) h.normalization
  have hc := conjugatePolynomial_eval_real P 1
  simp only [Complex.ofReal_one] at hc
  simp only [responsePairNorm, eval_add, eval_mul, eval_sub, eval_one, eval_pow,
    eval_X, one_pow, sub_self, zero_mul, add_zero, hc] at he
  have hr := congrArg Complex.re he
  simpa [Complex.normSq_apply, Complex.mul_re] using hr

theorem CompletedPair.upper_ne_zero {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) : P ≠ 0 := by
  intro hp
  have he := h.normSq_eval_one
  simp [hp] at he

noncomputable def halfPhase (u : ℂ) : ℂ := by
  classical
  exact if u = -1 then Complex.I else (1 + u) / (‖1 + u‖ : ℂ)

theorem halfPhase_spec {u : ℂ} (hu : IsPhase u) :
    IsPhase (halfPhase u) ∧ star (halfPhase u) * u = halfPhase u := by
  classical
  by_cases hm : u = -1
  · subst u
    simp [halfPhase, IsPhase]
  · have hc : 1 + u ≠ 0 := by
      intro he
      apply hm
      linear_combination he
    have hr : ‖1 + u‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    simp only [halfPhase, if_neg hm]
    constructor
    · apply isPhase_iff_normSq.mpr
      rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
        pow_two, div_self (mul_ne_zero hr hr)]
    · rw [star_div₀, star_add, star_one]
      have hreal : star (‖1 + u‖ : ℂ) = (‖1 + u‖ : ℂ) := by
        simp
      rw [hreal, div_mul_eq_mul_div]
      congr 1
      calc
        (1 + star u) * u = u + star u * u := by ring
        _ = 1 + u := by rw [show star u * u = 1 from hu]; ring

noncomputable def alignPhase (a b : ℂ) : ℂ := by
  classical
  exact if b = 0 then 1 else halfPhase (a / b)

theorem alignPhase_spec {a b : ℂ} (h : Complex.normSq a = Complex.normSq b) :
    IsPhase (alignPhase a b) ∧ star (alignPhase a b) * a = alignPhase a b * b := by
  classical
  by_cases hb : b = 0
  · have ha : a = 0 := Complex.normSq_eq_zero.mp (by simpa [hb] using h)
    simp [alignPhase, hb, ha, IsPhase]
  · have hu : IsPhase (a / b) := by
      apply isPhase_iff_normSq.mpr
      rw [Complex.normSq_div, h, div_self (mt Complex.normSq_eq_zero.mp hb)]
    obtain ⟨hz, he⟩ := halfPhase_spec hu
    simp only [alignPhase, if_neg hb]
    refine ⟨hz, ?_⟩
    have he' := congrArg (fun w : ℂ => w * b) he
    simpa only [mul_assoc, div_mul_cancel₀ _ hb] using he'

theorem HasResponseParity.coeff {n : ℕ} {P : Polynomial ℂ}
    (h : HasResponseParity n P) (k : ℕ) :
    P.coeff k * (-1 : ℂ) ^ k = (-1 : ℂ) ^ n * P.coeff k := by
  have he := congrArg (fun p : Polynomial ℂ => p.coeff k) h
  have hx : (-X : Polynomial ℂ) = C (-1) * X := by simp
  simpa only [hx, Polynomial.comp_C_mul_X_coeff, coeff_C_mul] using he

private theorem neg_one_pow_ne_succ (n : ℕ) :
    (-1 : ℂ) ^ n ≠ (-1 : ℂ) ^ (n + 1) := by
  intro he
  rw [pow_succ] at he
  have hm : (1 : ℂ) = -1 :=
    mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)) (by simpa using he)
  norm_num at hm

private theorem parity_coeff_zero {n k : ℕ} {P : Polynomial ℂ}
    (h : HasResponseParity n P) (hk : (-1 : ℂ) ^ k ≠ (-1 : ℂ) ^ n) :
    P.coeff k = 0 := by
  have he := h.coeff k
  have hm : P.coeff k * ((-1 : ℂ) ^ k - (-1 : ℂ) ^ n) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hk)

theorem inverseResponse_parity {n : ℕ} {P Q : Polynomial ℂ} (z : ℂ)
    (hp : HasResponseParity (n + 1) P) (hq : HasResponseParity (n + 2) Q) :
    HasResponseParity n (inverseResponseP z P Q) ∧
    HasResponseParity (n + 1) (inverseResponseQ z P Q) := by
  change P.comp (-X) = C ((-1 : ℂ) ^ (n + 1)) * P at hp
  change Q.comp (-X) = C ((-1 : ℂ) ^ (n + 2)) * Q at hq
  constructor <;>
    simp only [HasResponseParity, inverseResponseP, inverseResponseQ, add_comp,
      sub_comp, mul_comp, C_comp, X_comp, one_comp, pow_comp, hp, hq,
      pow_succ, map_mul, map_neg, map_one] <;> ring

private theorem degreeQ_natDegree {n : ℕ} {Q : Polynomial ℂ}
    (hq : Q.degree < ((n + 1 : ℕ) : WithBot ℕ)) : Q.natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  exact (degree_lt_iff_coeff_zero Q (n + 1)).mp hq k (by omega)

theorem CompletedPair.leading_normSq {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair (n + 1) P Q) :
    Complex.normSq (P.coeff (n + 1)) = Complex.normSq (Q.coeff n) := by
  have hp : P.natDegree ≤ n + 1 := natDegree_le_of_degree_le h.degreeP
  have hq : Q.natDegree ≤ n := degreeQ_natDegree h.degreeQ
  have hp' : (conjugatePolynomial P).natDegree ≤ n + 1 :=
    (Polynomial.natDegree_map_le (f := starRingEnd ℂ)).trans hp
  have hq' : (conjugatePolynomial Q).natDegree ≤ n :=
    (Polynomial.natDegree_map_le (f := starRingEnd ℂ)).trans hq
  have hpp := Polynomial.coeff_mul_add_eq_of_natDegree_le hp hp'
  have hqq := Polynomial.coeff_mul_add_eq_of_natDegree_le hq hq'
  have hqdeg : (Q * conjugatePolynomial Q).natDegree ≤ n + n :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hq hq')
  have hhigh : (Q * conjugatePolynomial Q).coeff ((n + 1) + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hqdeg (by omega))
  have hn := congrArg (fun p : Polynomial ℂ => p.coeff ((n + 1) + (n + 1)))
    h.normalization
  have hexpand : responsePairNorm P Q = P * conjugatePolynomial P +
      Q * conjugatePolynomial Q - X ^ 2 * (Q * conjugatePolynomial Q) := by
    unfold responsePairNorm
    ring
  rw [hexpand] at hn
  (try dsimp only at hn)
  rw [coeff_sub, coeff_add, hpp, hhigh] at hn
  have hshift : (X ^ 2 * (Q * conjugatePolynomial Q)).coeff ((n + 1) + (n + 1)) =
      (Q * conjugatePolynomial Q).coeff (n + n) := by
    rw [show (n + 1) + (n + 1) = (n + n) + 2 by omega, coeff_X_pow_mul]
  rw [hshift, hqq, conjugatePolynomial_coeff, conjugatePolynomial_coeff] at hn
  have hconst : (1 : Polynomial ℂ).coeff ((n + 1) + (n + 1)) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    simp only [natDegree_one]
    omega
  rw [hconst, add_zero] at hn
  have hr := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.zero_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at hr
  simp only [Complex.normSq_apply]
  nlinarith

private theorem inverseResponse_degree_bound {n : ℕ} {P Q : Polynomial ℂ} (z : ℂ)
    (hp : P.natDegree ≤ n + 1) (hq : Q.natDegree ≤ n) :
    (inverseResponseP z P Q).natDegree ≤ n + 2 ∧
    (inverseResponseQ z P Q).natDegree ≤ n + 1 := by
  have hpC : (C (star z) * P).natDegree ≤ n + 1 := (natDegree_C_mul_le _ _).trans hp
  have hqC : (C z * Q).natDegree ≤ n := (natDegree_C_mul_le _ _).trans hq
  have hxp : (X * (C (star z) * P)).natDegree ≤ n + 2 := by
    have he := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := C (star z) * P)
    simp only [natDegree_X] at he
    omega
  have hxq : (X * (C z * Q)).natDegree ≤ n + 1 := by
    have he := Polynomial.natDegree_mul_le (p := (X : Polynomial ℂ)) (q := C z * Q)
    simp only [natDegree_X] at he
    omega
  have hD : (1 - X ^ 2 : Polynomial ℂ).natDegree ≤ 2 := by
    calc
      (1 - X ^ 2 : Polynomial ℂ).natDegree ≤
          max (1 : Polynomial ℂ).natDegree ((X : Polynomial ℂ) ^ 2).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ 2 := by simp
  have hdq : ((1 - X ^ 2) * (C z * Q)).natDegree ≤ n + 2 := by
    exact Polynomial.natDegree_mul_le.trans (by omega)
  constructor
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le hxp hdq)
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le hpC hxq)

theorem inverseResponse_leading_zero {n : ℕ} {P Q : Polynomial ℂ} {z : ℂ}
    (hq : Q.natDegree ≤ n)
    (halign : star z * P.coeff (n + 1) = z * Q.coeff n) :
    (inverseResponseP z P Q).coeff (n + 2) = 0 ∧
    (inverseResponseQ z P Q).coeff (n + 1) = 0 := by
  have hqC : (C z * Q).natDegree ≤ n := (natDegree_C_mul_le _ _).trans hq
  have hzero : (C z * Q).coeff (n + 2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hqC (by omega))
  have hxp : (X * (C (star z) * P)).coeff (n + 2) = star z * P.coeff (n + 1) := by
    simpa only [Nat.add_assoc, coeff_C_mul] using
      Polynomial.coeff_X_mul (C (star z) * P) (n + 1)
  have hxq : (X ^ 2 * (C z * Q)).coeff (n + 2) = z * Q.coeff n := by
    simp only [coeff_X_pow_mul, coeff_C_mul]
  constructor
  · simp only [inverseResponseP, sub_mul, one_mul, coeff_add, coeff_sub]
    rw [hxp, hzero, hxq, halign]
    ring
  · simp only [inverseResponseQ, coeff_sub, coeff_C_mul, coeff_X_mul, halign, sub_self]

theorem CompletedPair.inverse_step {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair (n + 1) P Q) :
    let z := alignPhase (P.coeff (n + 1)) (Q.coeff n)
    IsPhase z ∧ CompletedPair n (inverseResponseP z P Q) (inverseResponseQ z P Q) := by
  let z := alignPhase (P.coeff (n + 1)) (Q.coeff n)
  have hz := alignPhase_spec h.leading_normSq
  change IsPhase z ∧ _ at hz
  have hp : P.natDegree ≤ n + 1 := natDegree_le_of_degree_le h.degreeP
  have hq : Q.natDegree ≤ n := degreeQ_natDegree h.degreeQ
  have hpar := inverseResponse_parity z h.parityP (by simpa [Nat.add_assoc] using h.parityQ)
  have htop := inverseResponse_leading_zero hq hz.2
  have hbound := inverseResponse_degree_bound z hp hq
  refine ⟨hz.1, ?_⟩
  refine ⟨?_, ?_, hpar.1, hpar.2, ?_⟩
  · apply degree_le_of_natDegree_le
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    by_cases h₁ : k = n + 1
    · subst k
      exact parity_coeff_zero hpar.1 (Ne.symm (neg_one_pow_ne_succ n))
    by_cases h₂ : k = n + 2
    · subst k
      exact htop.1
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hbound.1 (by omega))
  · apply (degree_lt_iff_coeff_zero _ n).mpr
    intro k hk
    by_cases h₁ : k = n
    · subst k
      exact parity_coeff_zero hpar.2 (neg_one_pow_ne_succ n)
    by_cases h₂ : k = n + 1
    · subst k
      exact htop.2
    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hbound.2 (by omega))
  · rw [inverseResponse_normalization hz.1, h.normalization]

noncomputable def synthesizePair : ℕ → Polynomial ℂ → Polynomial ℂ → ℂ × List ℂ
  | 0, P, _ => (P.coeff 0, [])
  | n + 1, P, Q =>
    let z := alignPhase (P.coeff (n + 1)) (Q.coeff n)
    let result := synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)
    (result.1, z :: result.2)

theorem synthesizePair_length (n : ℕ) (P Q : Polynomial ℂ) :
    (synthesizePair n P Q).2.length = n := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih => simp only [synthesizePair, List.length_cons, ih]

private theorem completedPair_zero {P Q : Polynomial ℂ} (h : CompletedPair 0 P Q) :
    P = C (P.coeff 0) ∧ Q = 0 ∧ IsPhase (P.coeff 0) := by
  have hp : P = C (P.coeff 0) :=
    eq_C_of_natDegree_le_zero (natDegree_le_of_degree_le h.degreeP)
  have hq : Q = 0 := by
    ext k
    simpa only [coeff_zero] using (degree_lt_iff_coeff_zero Q 0).mp h.degreeQ k (Nat.zero_le k)
  refine ⟨hp, hq, ?_⟩
  have hn := h.normalization
  rw [hp, hq] at hn
  have he := congrArg (fun p : Polynomial ℂ => p.coeff 0) hn
  simpa [responsePairNorm, IsPhase, mul_comm] using he

theorem synthesizePair_correct {n : ℕ} {P Q : Polynomial ℂ} (h : CompletedPair n P Q) :
    IsPhase (synthesizePair n P Q).1 ∧
    (∀ z ∈ (synthesizePair n P Q).2, IsPhase z) ∧
    responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 = P ∧
    responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 = Q := by
  induction n generalizing P Q with
  | zero =>
    obtain ⟨hp, hq, hb⟩ := completedPair_zero h
    simpa only [synthesizePair, responseP_nil, responseQ_nil] using
      And.intro hb (And.intro (by simp) (And.intro hp.symm hq.symm))
  | succ n ih =>
    let z := alignPhase (P.coeff (n + 1)) (Q.coeff n)
    have hstep := h.inverse_step
    change IsPhase z ∧ CompletedPair n (inverseResponseP z P Q) (inverseResponseQ z P Q) at hstep
    obtain ⟨hb, hzs, hp, hq⟩ := ih hstep.2
    change IsPhase (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).1 ∧
      (∀ w ∈ z :: (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).2,
        IsPhase w) ∧ _
    refine ⟨hb, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with he | he
      · subst w
        exact hstep.1
      · exact hzs w he
    · change responseP
        (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).1
        (z :: (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).2) = P
      rw [responseP_cons, hp, hq]
      exact (inverseResponse_reconstruct hstep.1 P Q).1
    · change responseQ
        (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).1
        (z :: (synthesizePair n (inverseResponseP z P Q) (inverseResponseQ z P Q)).2) = Q
      rw [responseQ_cons, hp, hq]
      exact (inverseResponse_reconstruct hstep.1 P Q).2

theorem exists_response_of_completedPair {n : ℕ} {P Q : Polynomial ℂ}
    (h : CompletedPair n P Q) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q := by
  obtain ⟨hb, hzs, hp, hq⟩ := synthesizePair_correct h
  exact ⟨(synthesizePair n P Q).1, (synthesizePair n P Q).2,
    hb, hzs, synthesizePair_length n P Q, hp, hq⟩

theorem completedPair_response {base : ℂ} (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    CompletedPair zs.length (responseP base zs) (responseQ base zs) := by
  obtain ⟨hp, hq⟩ := response_degree base zs
  refine ⟨degree_le_of_natDegree_le hp, ?_, ?_, ?_,
    response_polynomial_normalization hb zs hzs⟩
  · rcases hq with hq | hq
    · simp [hq]
    · apply lt_of_le_of_lt (degree_le_natDegree (p := responseQ base zs))
      exact_mod_cast (show (responseQ base zs).natDegree < zs.length by omega)
  · apply Polynomial.funext
    intro x
    simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using
      (response_parity base zs x).1
  · apply Polynomial.funext
    intro x
    simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C, pow_succ,
      mul_neg_one] using (response_parity base zs x).2

theorem completedPair_iff_response {n : ℕ} {P Q : Polynomial ℂ} :
    CompletedPair n P Q ↔
      ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
        zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q := by
  constructor
  · exact exists_response_of_completedPair
  · rintro ⟨base, zs, hb, hzs, hn, hp, hq⟩
    simpa only [hn, hp, hq] using completedPair_response hb zs hzs

end Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
