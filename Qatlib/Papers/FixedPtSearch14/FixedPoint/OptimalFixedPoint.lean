/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExt
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Intervals
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix Polynomial
open Qatlib

noncomputable def responseStep (alpha beta : ℝ)
    (p : Polynomial ℂ × Polynomial ℂ) : Polynomial ℂ × Polynomial ℂ :=
  let u : Polynomial ℂ := C (Complex.exp (-(Complex.I * (alpha : ℂ))))
  let v : Polynomial ℂ := C (Complex.exp (Complex.I * (beta : ℂ)))
  (-(X + (1 - X) * u) * p.1 + (1 - u) * X * v * p.2,
    (1 - u) * (1 - X) * p.1 - (1 - X + X * u) * v * p.2)

noncomputable def responsePolynomials : List (ℝ × ℝ) → Polynomial ℂ × Polynomial ℂ
  | [] => (1, 1)
  | ab :: tail => responseStep ab.1 ab.2 (responsePolynomials tail)

noncomputable def phaseWord (phases : List (ℝ × ℝ)) (lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (phases.map fun ab => groverIterate lam ab.1 ab.2).prod

noncomputable def polynomialState (lam : ℝ) (p : Polynomial ℂ × Polynomial ℂ) :
    QState (Fin 2) :=
  ![(Real.sqrt (1 - lam) : ℂ) * p.1.eval (lam : ℂ),
    (Real.sqrt lam : ℂ) * p.2.eval (lam : ℂ)]

theorem responseStep_realizes (alpha beta lam : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (p : Polynomial ℂ × Polynomial ℂ) :
    groverIterate lam alpha beta *ᵥ polynomialState lam p =
      polynomialState lam (responseStep alpha beta p) := by
  have hs : (Real.sqrt lam : ℂ) ^ 2 = (lam : ℂ) := ofReal_sqrt_sq hl
  have hf : (Real.sqrt (1 - lam) : ℂ) ^ 2 = 1 - (lam : ℂ) := by
    simpa using (ofReal_sqrt_sq (show 0 ≤ 1 - lam by linarith))
  rw [groverIterate, stateReflection_entry lam alpha hl hu,
    Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  ext i
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    simp [polynomialState, responseStep, targetReflection,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_neg] <;>
    ring_nf <;> simp_all [sq] <;> ring

theorem phaseWord_realizes (phases : List (ℝ × ℝ)) (lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    phaseWord phases lam *ᵥ ampState lam =
      polynomialState lam (responsePolynomials phases) := by
  induction phases with
  | nil =>
    ext i
    fin_cases i <;> simp [phaseWord, responsePolynomials, polynomialState, ampState]
  | cons ab tail ih =>
    change (groverIterate lam ab.1 ab.2 * phaseWord tail lam) *ᵥ ampState lam =
      polynomialState lam (responseStep ab.1 ab.2 (responsePolynomials tail))
    rw [← Matrix.mulVec_mulVec, ih]
    exact responseStep_realizes ab.1 ab.2 lam hl hu (responsePolynomials tail)

theorem responseStep_degree (alpha beta : ℝ) (p : Polynomial ℂ × Polynomial ℂ)
    (n : ℕ) (hp : p.1.natDegree ≤ n) (hq : p.2.natDegree ≤ n) :
    (responseStep alpha beta p).1.natDegree ≤ n + 1 ∧
      (responseStep alpha beta p).2.natDegree ≤ n + 1 := by
  let u : Polynomial ℂ := C (Complex.exp (-(Complex.I * (alpha : ℂ))))
  let v : Polynomial ℂ := C (Complex.exp (Complex.I * (beta : ℂ)))
  have hu : u.natDegree ≤ 0 := by simp [u]
  have hv : v.natDegree ≤ 0 := by simp [v]
  have h1 : (1 : Polynomial ℂ).natDegree ≤ 0 := by simp
  have hx := (natDegree_X_le (R := ℂ))
  have hmx : (1 - (X : Polynomial ℂ)).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le h1 hx
  have hmu : (1 - u).natDegree ≤ 0 := by
    simpa using natDegree_sub_le_of_le h1 hu
  have ha : (X + (1 - X) * u).natDegree ≤ 1 := by
    exact natDegree_add_le_of_degree_le hx
      (by simpa using natDegree_mul_le_of_le hmx hu)
  have hb : ((1 - u) * X * v).natDegree ≤ 1 := by
    simpa using natDegree_mul_le_of_le (natDegree_mul_le_of_le hmu hx) hv
  have hc : ((1 - u) * (1 - X)).natDegree ≤ 1 := by
    simpa using natDegree_mul_le_of_le hmu hmx
  have hd : ((1 - X + X * u) * v).natDegree ≤ 1 := by
    have hd' : (1 - X + X * u).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le hmx (by simpa using natDegree_mul_le_of_le hx hu)
    simpa using natDegree_mul_le_of_le hd' hv
  change ((-(X + (1 - X) * u)) * p.1 + ((1 - u) * X * v) * p.2).natDegree ≤ n + 1 ∧
    (((1 - u) * (1 - X)) * p.1 - ((1 - X + X * u) * v) * p.2).natDegree ≤ n + 1
  constructor
  · apply natDegree_add_le_of_degree_le
    · simpa [Nat.add_comm] using natDegree_mul_le_of_le (natDegree_neg_le_of_le ha) hp
    · simpa [Nat.add_comm] using natDegree_mul_le_of_le hb hq
  · exact (natDegree_sub_le _ _).trans (max_le
      (by simpa [Nat.add_comm] using natDegree_mul_le_of_le hc hp)
      (by simpa [Nat.add_comm] using natDegree_mul_le_of_le hd hq))

theorem responsePolynomials_degree (phases : List (ℝ × ℝ)) :
    (responsePolynomials phases).1.natDegree ≤ phases.length ∧
      (responsePolynomials phases).2.natDegree ≤ phases.length := by
  induction phases with
  | nil => simp [responsePolynomials]
  | cons ab tail ih =>
    exact responseStep_degree ab.1 ab.2 (responsePolynomials tail) tail.length ih.1 ih.2

noncomputable def publicPhases (l : ℕ) (delta : ℝ) : List (ℝ × ℝ) :=
  ((List.range l).map fun i =>
    (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta),
      -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))).reverse

theorem publicPhases_length (l : ℕ) (delta : ℝ) : (publicPhases l delta).length = l := by
  simp [publicPhases]

theorem phaseWord_publicPhases (l : ℕ) (delta lam : ℝ) :
    phaseWord (publicPhases l delta) lam = publicWord l delta lam := by
  simp only [phaseWord, publicPhases, publicWord, List.map_reverse, List.map_map]
  rfl

theorem frontier1 (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicWord l delta lam *ᵥ ampState lam =
      polynomialState lam (responsePolynomials (publicPhases l delta)) := by
  rw [← phaseWord_publicPhases]
  exact phaseWord_realizes _ lam hl hu

theorem publicFailureProb_polynomial (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicFailureProb l delta lam = (1 - lam) *
      ‖(responsePolynomials (publicPhases l delta)).1.eval (lam : ℂ)‖ ^ 2 := by
  have hs : ‖(Real.sqrt (1 - lam) : ℂ)‖ ^ 2 = 1 - lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith)]
  rw [publicFailureProb, publicFailureAmplitude, inner_ylcFailVec, frontier1 l delta lam hl hu]
  simp only [polynomialState, Matrix.cons_val_zero, norm_mul, mul_pow, hs]

theorem publicSuccessProb_polynomial (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicSuccessProb l delta lam = lam *
      ‖(responsePolynomials (publicPhases l delta)).2.eval (lam : ℂ)‖ ^ 2 := by
  have hs : ‖(Real.sqrt lam : ℂ)‖ ^ 2 = lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hl]
  rw [publicSuccessProb, publicSuccessAmplitude, inner_ylcTargetVec, frontier1 l delta lam hl hu]
  simp only [polynomialState, Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul, mul_pow, hs]

noncomputable def normSquarePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ) * p

theorem normSquarePolynomial_eval (p : Polynomial ℂ) (lam : ℝ) :
    (normSquarePolynomial p).eval (lam : ℂ) = (‖p.eval (lam : ℂ)‖ ^ 2 : ℝ) := by
  have he : (p.map (starRingEnd ℂ)).eval (lam : ℂ) =
      (starRingEnd ℂ) (p.eval (lam : ℂ)) := by
    simpa using (eval_map_apply (starRingEnd ℂ) (p := p) (lam : ℂ))
  rw [normSquarePolynomial, eval_mul, he, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

noncomputable def publicSuccessPolynomial (l : ℕ) (delta : ℝ) : Polynomial ℂ :=
  X * normSquarePolynomial (responsePolynomials (publicPhases l delta)).2

theorem publicSuccessPolynomial_eval (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    (publicSuccessPolynomial l delta).eval (lam : ℂ) = (publicSuccessProb l delta lam : ℂ) := by
  rw [publicSuccessPolynomial, eval_mul, eval_X, normSquarePolynomial_eval,
    publicSuccessProb_polynomial l delta lam hl hu]
  simp only [Complex.ofReal_mul]

theorem publicSuccessPolynomial_degree (l : ℕ) (delta : ℝ) :
    (publicSuccessPolynomial l delta).natDegree ≤ 2 * l + 1 := by
  have hp : (responsePolynomials (publicPhases l delta)).2.natDegree ≤ l := by
    simpa only [publicPhases_length] using (responsePolynomials_degree (publicPhases l delta)).2
  have hn : (normSquarePolynomial (responsePolynomials (publicPhases l delta)).2).natDegree ≤
      l + l := by
    exact natDegree_mul_le_of_le (natDegree_map_le.trans hp) hp
  exact (natDegree_mul_le_of_le (natDegree_X_le (R := ℂ)) hn).trans (by omega)

theorem responsePolynomials_conservation (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    (1 - lam) * ‖(responsePolynomials (publicPhases l delta)).1.eval (lam : ℂ)‖ ^ 2 +
      lam * ‖(responsePolynomials (publicPhases l delta)).2.eval (lam : ℂ)‖ ^ 2 = 1 := by
  rw [← publicFailureProb_polynomial l delta lam hl hu,
    ← publicSuccessProb_polynomial l delta lam hl hu]
  have hn : Normalized (publicWord l delta lam *ᵥ ampState lam) := by
    simpa [ApplyGate] using normalized_applyGate
      (publicWord_unitary l delta lam hl hu) (ampState_normalized hl hu)
  have ht := two_component_normSq (publicWord l delta lam *ᵥ ampState lam)
  change publicFailureProb l delta lam + publicSuccessProb l delta lam = 1
  simpa [publicFailureProb, publicSuccessProb, publicFailureAmplitude, publicSuccessAmplitude,
    add_comm] using ht.trans hn

theorem publicWord_endpoints (l : ℕ) (delta : ℝ) :
    publicSuccessProb l delta 0 = 0 ∧ publicSuccessProb l delta 1 = 1 := by
  constructor
  · simp [publicSuccessProb_polynomial l delta 0 (by norm_num) (by norm_num)]
  · have h := responsePolynomials_conservation l delta 1 (by norm_num) (by norm_num)
    simpa [publicSuccessProb_polynomial l delta 1 (by norm_num) (by norm_num)] using h

theorem continuant_elimination (x p q w a b : ℂ) (hpq : p * q = x ^ 2 - 1) :
    x * (x * a + p * b) + (w * p) * (q * a + x * b) =
      x * (1 + w) * (x * a + p * b) - w * a := by
  linear_combination w * a * hpq

theorem su2A_continuant (zeta eta x s : ℝ) (hn : x ^ 2 + s ^ 2 = 1)
    (a : QState (Fin 2)) :
    (su2A eta x s *ᵥ (su2A zeta x s *ᵥ a)) 0 =
      (x : ℂ) * (1 + Complex.exp (-(Complex.I * ((eta - zeta : ℝ) : ℂ)))) *
        (su2A zeta x s *ᵥ a) 0 -
      Complex.exp (-(Complex.I * ((eta - zeta : ℝ) : ℂ))) * a 0 := by
  let p : ℂ := -Complex.I * (s : ℂ) * Complex.exp (-(Complex.I * (zeta : ℂ)))
  let q : ℂ := -Complex.I * (s : ℂ) * Complex.exp (Complex.I * (zeta : ℂ))
  let w : ℂ := Complex.exp (-(Complex.I * ((eta - zeta : ℝ) : ℂ)))
  have he : Complex.exp (-(Complex.I * (zeta : ℂ))) *
      Complex.exp (Complex.I * (zeta : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hpq : p * q = (x : ℂ) ^ 2 - 1 := by
    have hc : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hn
    dsimp [p, q]
    calc
      _ = -(s : ℂ) ^ 2 * (Complex.exp (-(Complex.I * (zeta : ℂ))) *
          Complex.exp (Complex.I * (zeta : ℂ))) := by ring_nf; simp [Complex.I_sq]
      _ = (x : ℂ) ^ 2 - 1 := by rw [he]; linear_combination -hc
  have hp : -Complex.I * (s : ℂ) * Complex.exp (-(Complex.I * (eta : ℂ))) = w * p := by
    dsimp [w, p]
    have he' : Complex.exp (-(Complex.I * ((eta - zeta : ℝ) : ℂ))) *
        Complex.exp (-(Complex.I * (zeta : ℂ))) =
        Complex.exp (-(Complex.I * (eta : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = -Complex.I * (s : ℂ) * (Complex.exp (-(Complex.I * ((eta - zeta : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I * (zeta : ℂ)))) := by rw [he']
      _ = _ := by ring
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, su2A]
  change (x : ℂ) * ((x : ℂ) * a 0 + p * a 1) +
    (-Complex.I * (s : ℂ) * Complex.exp (-(Complex.I * (eta : ℂ)))) *
      (q * a 0 + (x : ℂ) * a 1) =
    (x : ℂ) * (1 + w) * ((x : ℂ) * a 0 + p * a 1) - w * a 0
  rw [hp]
  exact continuant_elimination (x : ℂ) p q w (a 0) (a 1) hpq

theorem root_scaling_support (L : ℕ) (hL : 0 < L) (q : ℂ)
    (hq : IsPrimitiveRoot q L) (p : Polynomial ℂ) (hp : p.natDegree ≤ L)
    (hi : p.comp (C q * X) = p) :
    p = C (p.coeff 0) + C (p.coeff L) * X ^ L := by
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [coeff_C, hL.ne]
  by_cases hn : n = L
  · subst n
    simp [coeff_C, hL.ne']
  have hz : p.coeff n = 0 := by
    by_cases hlt : n < L
    · have hqn : q ^ n ≠ 1 := hq.pow_ne_one_of_pos_of_lt h0 hlt
      have he : p.coeff n * q ^ n = p.coeff n := by
        simpa only [comp_C_mul_X_coeff] using congrArg (fun f : Polynomial ℂ => f.coeff n) hi
      have he' : p.coeff n * (q ^ n - 1) = 0 := by linear_combination he
      exact (mul_eq_zero.mp he').resolve_right (sub_ne_zero.mpr hqn)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_C, hz, h0, hn]

def affineOrbit {R : Type*} [CommRing R] (B D : Matrix (Fin 2) (Fin 2) R)
    (q u : R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | n + 1 => affineOrbit B D q u n * (B + (q ^ n * u) • D)

theorem affineOrbit_shift_head {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    (B + u • D) * affineOrbit B D q (q * u) n = affineOrbit B D q u (n + 1) := by
  induction n with
  | zero => simp [affineOrbit]
  | succ n ih =>
    rw [affineOrbit, ← mul_assoc, ih, affineOrbit]
    rw [show q ^ n * (q * u) = q ^ (n + 1) * u by rw [pow_succ, mul_assoc]]
    rfl

theorem affineOrbit_trace_scale {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (L : ℕ) (hL : 0 < L)
    (hq : q ^ L = 1) :
    Matrix.trace (affineOrbit B D q (q * u) L) =
      Matrix.trace (affineOrbit B D q u L) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
  rw [affineOrbit]
  have he : q ^ n * (q * u) = u := by
    rw [← mul_assoc, ← pow_succ, hq, one_mul]
  rw [he, Matrix.trace_mul_comm, affineOrbit_shift_head]

theorem affineOrbit_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    (affineOrbit B D q u n).map f =
      affineOrbit (B.map f) (D.map f) (f q) (f u) n := by
  induction n with
  | zero => simp [affineOrbit]
  | succ n ih =>
    simp only [affineOrbit, Matrix.map_mul, ih]
    congr 1
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

noncomputable def traceOrbitPolynomial (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : Polynomial ℂ :=
  Matrix.trace (affineOrbit (B.map Polynomial.C) (D.map Polynomial.C) (C q) X L)

theorem traceOrbitPolynomial_scale (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) (hL : 0 < L) (hq : q ^ L = 1) :
    (traceOrbitPolynomial B D q L).comp (C q * X) = traceOrbitPolynomial B D q L := by
  let f : Polynomial ℂ →+* Polynomial ℂ := Polynomial.compRingHom (C q * X)
  have hB : (B.map Polynomial.C).map f = B.map Polynomial.C := by
    ext i j
    simp [f]
  have hD : (D.map Polynomial.C).map f = D.map Polynomial.C := by
    ext i j
    simp [f]
  change f (Matrix.trace _) = _
  rw [AddMonoidHom.map_trace, affineOrbit_map, hB, hD]
  simpa [f, traceOrbitPolynomial] using
    affineOrbit_trace_scale (B.map Polynomial.C) (D.map Polynomial.C)
      (C q) (X : Polynomial ℂ) L hL (by simpa using congrArg Polynomial.C hq)

private theorem matrixPolynomial_mul_degree (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (m n : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ m) (hB : ∀ i j, (B i j).natDegree ≤ n) :
    ∀ i j, ((A * B) i j).natDegree ≤ m + n := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact natDegree_add_le_of_degree_le
    (natDegree_mul_le_of_le (hA i 0) (hB 0 j))
    (natDegree_mul_le_of_le (hA i 1) (hB 1 j))

private theorem matrixPolynomial_mul_top (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (m n : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ m) (hB : ∀ i j, (B i j).natDegree ≤ n) :
    ∀ i j, ((A * B) i j).coeff (m + n) =
      (A i 0).coeff m * (B 0 j).coeff n + (A i 1).coeff m * (B 1 j).coeff n := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, coeff_add,
    coeff_mul_add_eq_of_natDegree_le (hA i 0) (hB 0 j),
    coeff_mul_add_eq_of_natDegree_le (hA i 1) (hB 1 j)]

private theorem affineFactor_degree (B D : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    ∀ i j, ((B.map Polynomial.C + (C q * X) • D.map Polynomial.C) i j).natDegree ≤ 1 := by
  intro i j
  change (C (B i j) + (C q * X) * C (D i j)).natDegree ≤ 1
  apply natDegree_add_le_of_degree_le
  · simp
  · simpa using natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (C q).natDegree ≤ 0 by simp) (natDegree_X_le (R := ℂ)))
      (show (C (D i j)).natDegree ≤ 0 by simp)

theorem affineOrbit_polynomial_degree (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (n : ℕ) :
    ∀ i j, (affineOrbit (B.map Polynomial.C) (D.map Polynomial.C) (C q) X n i j).natDegree ≤ n := by
  induction n with
  | zero =>
    intro i j
    by_cases h : i = j <;> simp [affineOrbit, Matrix.one_apply, h]
  | succ n ih =>
    exact matrixPolynomial_mul_degree _ _ n 1 ih
      (by simpa using affineFactor_degree B D (q ^ n))

theorem traceOrbitPolynomial_degree (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : (traceOrbitPolynomial B D q L).natDegree ≤ L := by
  unfold traceOrbitPolynomial Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two]
  exact natDegree_add_le_of_degree_le
    (affineOrbit_polynomial_degree B D q L 0 0)
    (affineOrbit_polynomial_degree B D q L 1 1)

theorem affineOrbit_zero {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q : R) (n : ℕ) :
    affineOrbit B D q 0 n = B ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [affineOrbit, ih, pow_succ]

theorem traceOrbitPolynomial_constant (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : (traceOrbitPolynomial B D q L).coeff 0 = Matrix.trace (B ^ L) := by
  have hB : (B.map Polynomial.C).map Polynomial.constantCoeff = B := by
    ext i j
    simp
  have hD : (D.map Polynomial.C).map Polynomial.constantCoeff = D := by
    ext i j
    simp
  change Polynomial.constantCoeff (Matrix.trace
    (affineOrbit (B.map Polynomial.C) (D.map Polynomial.C) (C q) X L)) = Matrix.trace (B ^ L)
  rw [AddMonoidHom.map_trace, affineOrbit_map, hB, hD]
  simp [affineOrbit_zero]

theorem affineOrbit_polynomial_top (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (n : ℕ) :
    ∀ i j, (affineOrbit (B.map Polynomial.C) (D.map Polynomial.C) (C q) X n i j).coeff n =
      (∏ k ∈ Finset.range n, q ^ k) * (D ^ n) i j := by
  induction n with
  | zero =>
    intro i j
    by_cases h : i = j <;> simp [affineOrbit, Matrix.one_apply, h]
  | succ n ih =>
    intro i j
    have hf : ∀ a b,
        ((B.map Polynomial.C + ((C q) ^ n * X) • D.map Polynomial.C) a b).coeff 1 =
          q ^ n * D a b := by
      intro a b
      change (C (B a b) + ((C q) ^ n * X) * C (D a b)).coeff 1 = q ^ n * D a b
      rw [← C_pow]
      simp only [coeff_add, coeff_C, coeff_mul_C, coeff_C_mul, coeff_X]
      norm_num
    rw [affineOrbit, matrixPolynomial_mul_top _ _ n 1
      (affineOrbit_polynomial_degree B D q n)
      (by simpa using affineFactor_degree B D (q ^ n))]
    rw [ih i 0, ih i 1, hf 0 j, hf 1 j]
    simp only [Finset.prod_range_succ, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem traceOrbitPolynomial_top (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : (traceOrbitPolynomial B D q L).coeff L =
      (∏ k ∈ Finset.range L, q ^ k) * Matrix.trace (D ^ L) := by
  unfold traceOrbitPolynomial Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, coeff_add,
    affineOrbit_polynomial_top B D q L 0 0, affineOrbit_polynomial_top B D q L 1 1]
  simp only [Fin.sum_univ_two]
  ring

theorem odd_root_orbit_weight (l : ℕ) (q : ℂ) (hq : q ^ (2 * l + 1) = 1) :
    (∏ k ∈ Finset.range (2 * l + 1), q ^ k) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hs : (∑ k ∈ Finset.range (2 * l + 1), k) = (2 * l + 1) * l := by
    have h := Finset.sum_range_id_mul_two (2 * l + 1)
    simp only [Nat.add_sub_cancel] at h
    nlinarith
  rw [hs, pow_mul, hq, one_pow]

theorem traceOrbitPolynomial_closed (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (l : ℕ) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    traceOrbitPolynomial B D q (2 * l + 1) =
      C (Matrix.trace (B ^ (2 * l + 1))) +
        C (Matrix.trace (D ^ (2 * l + 1))) * X ^ (2 * l + 1) := by
  have hpow : q ^ (2 * l + 1) = 1 := hq.pow_eq_one
  rw [root_scaling_support (2 * l + 1) (by omega) q hq
    (traceOrbitPolynomial B D q (2 * l + 1)) (traceOrbitPolynomial_degree B D q _)
    (traceOrbitPolynomial_scale B D q _ (by omega) hpow)]
  rw [traceOrbitPolynomial_constant, traceOrbitPolynomial_top, odd_root_orbit_weight l q hpow,
    one_mul]

def continuantConstant (x a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -a; b, 0]

theorem continuantConstant_sq (x a b : ℂ) :
    continuantConstant x a b ^ 2 =
      (2 * x) • continuantConstant x a b - (a * b) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [continuantConstant, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem continuantConstant_power_recurrence (x a b : ℂ) (n : ℕ) :
    continuantConstant x a b ^ (n + 2) =
      (2 * x) • continuantConstant x a b ^ (n + 1) -
        (a * b) • continuantConstant x a b ^ n := by
  rw [pow_add, continuantConstant_sq, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, ← pow_succ]

theorem continuantConstant_trace_power (x a b gamma : ℂ) (hg : gamma ≠ 0)
    (hab : a * b = gamma ^ 2) (n : ℕ) :
    Matrix.trace (continuantConstant x a b ^ n) =
      2 * gamma ^ n * (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval (x / gamma) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [pow_one, Nat.cast_one, Polynomial.Chebyshev.T_one, eval_X]
    have ht : Matrix.trace (continuantConstant x a b) = 2 * x := by
      simp [continuantConstant, Matrix.trace, Fin.sum_univ_two]
    rw [ht]
    field_simp
  | more n ih0 ih1 =>
    rw [continuantConstant_power_recurrence, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ih1, ih0, hab]
    have hc := congrArg (fun p : Polynomial ℂ => p.eval (x / gamma))
      (Polynomial.Chebyshev.T_add_two ℂ (n : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hc
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, hc]
    have hn : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    rw [hn]
    simp only [pow_succ]
    field_simp

theorem traceOrbitPolynomial_eval (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q u : ℂ) (L : ℕ) :
    (traceOrbitPolynomial B D q L).eval u = Matrix.trace (affineOrbit B D q u L) := by
  have hB : (B.map Polynomial.C).map (Polynomial.evalRingHom u) = B := by
    ext i j
    simp
  have hD : (D.map Polynomial.C).map (Polynomial.evalRingHom u) = D := by
    ext i j
    simp
  change (Polynomial.evalRingHom u) (Matrix.trace _) = _
  rw [AddMonoidHom.map_trace, affineOrbit_map, hB, hD]
  simp

theorem affineOrbit_trace_closed (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q u : ℂ) (l : ℕ) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    Matrix.trace (affineOrbit B D q u (2 * l + 1)) =
      Matrix.trace (B ^ (2 * l + 1)) + u ^ (2 * l + 1) * Matrix.trace (D ^ (2 * l + 1)) := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval u) (traceOrbitPolynomial_closed B D q l hq)
  simp only [traceOrbitPolynomial_eval, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
  simpa only [mul_comm] using h

theorem quasiChebyshev_orbit_trace (x a b gamma q u : ℂ) (l : ℕ)
    (hg : gamma ≠ 0) (hab : a * b = gamma ^ 2) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    Matrix.trace (affineOrbit (continuantConstant x a b) (continuantConstant x b a)
      q u (2 * l + 1)) =
      2 * gamma ^ (2 * l + 1) *
        (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (x / gamma) *
        (1 + u ^ (2 * l + 1)) := by
  rw [affineOrbit_trace_closed _ _ q u l hq,
    continuantConstant_trace_power x a b gamma hg hab,
    continuantConstant_trace_power x b a gamma hg (by simpa [mul_comm] using hab)]
  ring

def continuantStep (x s w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![x, -s * w; s, x * w]

theorem continuantStep_invariant (x s w : ℂ) (hxs : x ^ 2 + s ^ 2 = 1)
    (v : QState (Fin 2)) :
    x * (continuantStep x s w *ᵥ v) 0 + s * (continuantStep x s w *ᵥ v) 1 = v 0 := by
  simp only [continuantStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change x * (x * v 0 + (-s * w) * v 1) + s * (s * v 0 + (x * w) * v 1) = v 0
  linear_combination v 0 * hxs

theorem continuantStep_eliminate (x s w a : ℂ) (v : QState (Fin 2))
    (hv : x * v 0 + s * v 1 = a) :
    (continuantStep x s w *ᵥ v) 0 = x * (1 + w) * v 0 - w * a := by
  simp only [continuantStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change x * v 0 + (-s * w) * v 1 = _
  linear_combination -w * hv

noncomputable def recurrenceRun (L : ℕ) (mu x s : ℝ) : ℕ → QState (Fin 2)
  | 0 => ![1, 0]
  | n + 1 => continuantStep (x : ℂ) (s : ℂ) (ylcRecW L mu (n + 1)) *ᵥ
      recurrenceRun L mu x s n

theorem recurrenceRun_first (L : ℕ) (mu x s : ℝ) (hxs : x ^ 2 + s ^ 2 = 1) (n : ℕ) :
    recurrenceRun L mu x s n 0 = ylcRecA L mu x n := by
  have hc : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hxs
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [recurrenceRun, continuantStep, ylcRecA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | more n ih0 ih1 =>
    have hv : (x : ℂ) * recurrenceRun L mu x s (n + 1) 0 +
        (s : ℂ) * recurrenceRun L mu x s (n + 1) 1 = recurrenceRun L mu x s n 0 :=
      continuantStep_invariant (x : ℂ) (s : ℂ) (ylcRecW L mu (n + 1)) hc
        (recurrenceRun L mu x s n)
    rw [recurrenceRun, continuantStep_eliminate (x : ℂ) (s : ℂ)
      (ylcRecW L mu (n + 2)) (recurrenceRun L mu x s n 0)
      (recurrenceRun L mu x s (n + 1)) hv, ih1, ih0]
    rfl

namespace OrbitReflection

def J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

noncomputable def reflect (A : Matrix (Fin 2) (Fin 2) ℂ) := J * Aᵀ * J

theorem J_sq : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflect_twice (A : Matrix (Fin 2) (Fin 2) ℂ) : reflect (reflect A) = A := by
  have hJ : Jᵀ = J := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [reflect, Matrix.transpose_mul, hJ, Matrix.transpose_transpose]
  calc
    _ = (J * J) * A * (J * J) := by noncomm_ring
    _ = A := by rw [J_sq]; simp

theorem reflect_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    reflect (A * B) = reflect B * reflect A := by
  simp only [reflect, Matrix.transpose_mul]
  have hh : (J * Bᵀ * J) * (J * Aᵀ * J) = J * Bᵀ * (J * J) * Aᵀ * J := by
    noncomm_ring
  rw [hh, J_sq]
  simp only [Matrix.mul_one]
  noncomm_ring

theorem reflect_prod (xs : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    reflect xs.prod = (xs.reverse.map reflect).prod := by
  induction xs with
  | nil => simpa [reflect] using J_sq
  | cons a xs ih => simp [List.reverse_cons, reflect_mul, ih]

noncomputable def M (B : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) := B + v • reflect B

theorem reflect_point (B : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (hab : a * b = 1) :
    reflect (M B a) = a • M B b := by
  have hd : reflect (M B a) = reflect B + a • reflect (reflect B) := by
    simp [reflect, M, Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul]
  rw [hd, reflect_twice, M, smul_add, smul_smul, hab, one_smul]
  exact add_comm _ _

theorem scalar_prod (n : ℕ) (a : ℕ → ℂ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    ((List.range n).map fun i => a i • f i).prod =
      ((List.range n).map a).prod • ((List.range n).map f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [ih, smul_mul_smul_comm]

theorem reverse_range_map (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    (List.range n).map (fun i => f (n - i)) =
      ((List.range n).map (fun i => f (i + 1))).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    congr 1
    simp only [List.length_map, List.length_range] at h₁
    omega

theorem powers_prod (q : ℂ) (n : ℕ) :
    ((List.range n).map fun i => q ^ (i + 1)).prod = q ^ (n * (n + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one, ih, ← pow_add]
    congr 1
    have hh : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    omega

theorem orbit_reflect (B : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) (l : ℕ)
    (hq : q ^ (2 * l + 1) = 1) :
    let P := (((List.range (2 * l)).map fun i => M B (q ^ (i + 1))).reverse).prod
    P = J * Pᵀ * J := by
  (try dsimp only)
  change _ = reflect _
  rw [reflect_prod, List.reverse_reverse, List.map_map]
  have hp : ((List.range (2 * l)).map fun i => reflect (M B (q ^ (i + 1)))) =
      (List.range (2 * l)).map (fun i => (q ^ (i + 1)) • M B (q ^ (2 * l - i))) := by
    apply List.map_congr_left
    intro i hi
    apply reflect_point
    rw [← pow_add]
    have hi' : i < 2 * l := List.mem_range.mp hi
    simpa only [show i + 1 + (2 * l - i) = 2 * l + 1 by omega] using hq
  change _ = ((List.range (2 * l)).map fun i => reflect (M B (q ^ (i + 1)))).prod
  rw [hp, scalar_prod, powers_prod]
  have hexp : 2 * l * (2 * l + 1) / 2 = (2 * l + 1) * l := by
    rw [show 2 * l * (2 * l + 1) = ((2 * l + 1) * l) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  rw [hexp, pow_mul, hq, one_pow, one_smul]
  exact congrArg List.prod (reverse_range_map (fun k => M B (q ^ k)) (2 * l)).symm

end OrbitReflection

def reverseAffineOrbit {R : Type*} [CommRing R] (B D : Matrix (Fin 2) (Fin 2) R)
    (q u : R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | n + 1 => (B + (q ^ n * u) • D) * reverseAffineOrbit B D q u n

theorem reverseAffineOrbit_transpose {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u n = (affineOrbit Bᵀ Dᵀ q u n)ᵀ := by
  induction n with
  | zero => simp [affineOrbit, reverseAffineOrbit]
  | succ n ih =>
    simp [affineOrbit, reverseAffineOrbit, Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.transpose_smul, ih]

theorem reverseAffineOrbit_trace_closed (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q u : ℂ) (l : ℕ) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    Matrix.trace (reverseAffineOrbit B D q u (2 * l + 1)) =
      Matrix.trace (B ^ (2 * l + 1)) + u ^ (2 * l + 1) * Matrix.trace (D ^ (2 * l + 1)) := by
  rw [reverseAffineOrbit_transpose, Matrix.trace_transpose, affineOrbit_trace_closed _ _ q u l hq,
    ← Matrix.transpose_pow, ← Matrix.transpose_pow, Matrix.trace_transpose, Matrix.trace_transpose]

theorem reverseAffineOrbit_shift_tail {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u (n + 1) =
      reverseAffineOrbit B D q (q * u) n * (B + u • D) := by
  induction n with
  | zero => simp [reverseAffineOrbit]
  | succ n ih =>
    rw [reverseAffineOrbit, ih, ← mul_assoc, reverseAffineOrbit]
    rw [show q ^ n * (q * u) = q ^ (n + 1) * u by rw [pow_succ, mul_assoc]]

theorem reverseAffineOrbit_eq_list {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u n =
      (((List.range n).map fun i => B + (q ^ i * u) • D).reverse).prod := by
  induction n with
  | zero => simp [reverseAffineOrbit]
  | succ n ih =>
    simp [reverseAffineOrbit, List.range_succ, List.reverse_append, ih]

theorem continuantConstant_reflect (x a b : ℂ) :
    OrbitReflection.reflect (continuantConstant x a b) = continuantConstant x b a := by
  ext i j
  simp only [OrbitReflection.reflect, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [OrbitReflection.J, continuantConstant]

theorem continuantOrbit_offdiag (x a b q : ℂ) (l : ℕ) (hq : q ^ (2 * l + 1) = 1) :
    let P := reverseAffineOrbit (continuantConstant x a b) (continuantConstant x b a) q q (2 * l)
    P 0 1 = -(P 1 0) := by
  have h := OrbitReflection.orbit_reflect (continuantConstant x a b) q l hq
  have he : reverseAffineOrbit (continuantConstant x a b) (continuantConstant x b a) q q (2 * l) =
      (((List.range (2 * l)).map fun i => OrbitReflection.M (continuantConstant x a b)
        (q ^ (i + 1))).reverse).prod := by
    rw [reverseAffineOrbit_eq_list]
    simp only [OrbitReflection.M, continuantConstant_reflect, pow_succ]
  rw [← he] at h
  have hc := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at hc
  simpa [OrbitReflection.J] using hc

noncomputable def algebraicRecW (q a b : ℂ) (k : ℕ) : ℂ :=
  (b * q ^ k + a) / (a * q ^ k + b)

noncomputable def algebraicRecA (q x a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => x
  | n + 2 => x * (1 + algebraicRecW q a b (n + 1)) * algebraicRecA q x a b (n + 1) -
      algebraicRecW q a b (n + 1) * algebraicRecA q x a b n

noncomputable def algebraicDenominator (q a b : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ Finset.range n, (a * q ^ (i + 1) + b)

theorem algebraicFactor_step (q x a b : ℂ) (k : ℕ) (hab : a + b = 2)
    (hd : a * q ^ k + b ≠ 0) (v0 v1 : ℂ) :
    (continuantConstant x a b + (q ^ k) • continuantConstant x b a) *ᵥ ![v0, v1] =
      (a * q ^ k + b) • ![x * (1 + algebraicRecW q a b k) * v0 -
        algebraicRecW q a b k * v1, v0] := by
  have hw : (a * q ^ k + b) * algebraicRecW q a b k = b * q ^ k + a := by
    unfold algebraicRecW
    field_simp
  have hc : (a * q ^ k + b) * (1 + algebraicRecW q a b k) = 2 * (1 + q ^ k) := by
    rw [mul_add, mul_one, hw]
    linear_combination (1 + q ^ k) * hab
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
    change (2 * x + q ^ k * (2 * x)) * v0 + (-a + q ^ k * (-b)) * v1 =
      (a * q ^ k + b) * (x * (1 + algebraicRecW q a b k) * v0 - algebraicRecW q a b k * v1)
    linear_combination -(x * v0) * hc + v1 * hw
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
    change (b + q ^ k * a) * v0 + (0 + q ^ k * 0) * v1 = (a * q ^ k + b) * v0
    ring

theorem algebraicRecA_product (q x a b : ℂ) (hab : a + b = 2)
    (hd : ∀ k : ℕ, a * q ^ k + b ≠ 0) (n : ℕ) :
    reverseAffineOrbit (continuantConstant x a b) (continuantConstant x b a) q q n *ᵥ ![x, 1] =
      algebraicDenominator q a b n • ![algebraicRecA q x a b (n + 1), algebraicRecA q x a b n] := by
  induction n with
  | zero => simp [reverseAffineOrbit, algebraicDenominator, algebraicRecA]
  | succ n ih =>
    rw [reverseAffineOrbit, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
    rw [show q ^ n * q = q ^ (n + 1) by rw [pow_succ]]
    rw [algebraicFactor_step q x a b (n + 1) hab (hd (n + 1))]
    simp only [smul_smul, algebraicDenominator, Finset.prod_range_succ, algebraicRecA]

theorem algebraicRecA_chebyshev_unnormalized (q x a b gamma : ℂ) (l : ℕ)
    (hab : a + b = 2) (hprod : a * b = gamma ^ 2) (hg : gamma ≠ 0)
    (hq : IsPrimitiveRoot q (2 * l + 1)) (hd : ∀ k : ℕ, a * q ^ k + b ≠ 0) :
    algebraicDenominator q a b (2 * l) * algebraicRecA q x a b (2 * l + 1) =
      gamma ^ (2 * l + 1) *
        (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (x / gamma) := by
  let B := continuantConstant x a b
  let D := continuantConstant x b a
  let P := reverseAffineOrbit B D q q (2 * l)
  have hP : P 0 1 = -(P 1 0) := continuantOrbit_offdiag x a b q l hq.pow_eq_one
  have hBD : B + D = !![4 * x, -2; 2, 0] := by
    have hneg : -a + -b = -2 := by linear_combination -hab
    have hba : b + a = 2 := by linear_combination hab
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, D, continuantConstant, hneg, hba]
    ring
  have htrace : Matrix.trace (P * (B + D)) = 4 * (x * P 0 0 + P 0 1) := by
    rw [hBD]
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.mul_apply]
    change P 0 0 * (4 * x) + P 0 1 * 2 + (P 1 0 * (-2) + P 1 1 * 0) = _
    rw [hP]
    ring
  have hv : x * P 0 0 + P 0 1 =
      algebraicDenominator q a b (2 * l) * algebraicRecA q x a b (2 * l + 1) := by
    have h :=
        congrArg (fun v : QState (Fin 2) => v 0) (algebraicRecA_product q x a b hab hd (2 * l))
    change (P *ᵥ ![x, 1]) 0 = _ at h
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, mul_comm] using h
  have ht : Matrix.trace (reverseAffineOrbit B D q 1 (2 * l + 1)) =
      4 * gamma ^ (2 * l + 1) *
        (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (x / gamma) := by
    rw [reverseAffineOrbit_trace_closed B D q 1 l hq]
    dsimp only [B, D]
    rw [continuantConstant_trace_power x a b gamma hg hprod,
      continuantConstant_trace_power x b a gamma hg (by simpa [mul_comm] using hprod)]
    simp only [one_pow, one_mul]
    ring
  have hs : reverseAffineOrbit B D q 1 (2 * l + 1) = P * (B + D) := by
    simpa [P] using reverseAffineOrbit_shift_tail B D q 1 (2 * l)
  rw [hs, htrace, hv] at ht
  linear_combination (1 / 4 : ℂ) * ht

theorem algebraicRecA_one (q a b : ℂ) (n : ℕ) : algebraicRecA q 1 a b n = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 => rw [algebraicRecA, ih0, ih1]; ring

theorem algebraicRecA_chebyshev (q x a b gamma : ℂ) (l : ℕ)
    (hab : a + b = 2) (hprod : a * b = gamma ^ 2) (hg : gamma ≠ 0)
    (hq : IsPrimitiveRoot q (2 * l + 1)) (hd : ∀ k : ℕ, a * q ^ k + b ≠ 0) :
    algebraicRecA q x a b (2 * l + 1) =
      (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (x / gamma) /
        (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (1 / gamma) := by
  have hx := algebraicRecA_chebyshev_unnormalized q x a b gamma l hab hprod hg hq hd
  have h1 := algebraicRecA_chebyshev_unnormalized q 1 a b gamma l hab hprod hg hq hd
  rw [algebraicRecA_one, mul_one] at h1
  have hdn : algebraicDenominator q a b (2 * l) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hd (i + 1)
  have htn : (Polynomial.Chebyshev.T ℂ ((2 * l + 1 : ℕ) : ℤ)).eval (1 / gamma) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact hdn h1
  apply (eq_div_iff htn).2
  apply mul_left_cancel₀ (pow_ne_zero (2 * l + 1) hg)
  rw [h1] at hx
  linear_combination hx

namespace PhaseCoefficients

theorem exp_neg_two_I_arctan (u : ℝ) :
    Complex.exp (-(2 * Complex.I * (Real.arctan u : ℂ))) =
      (1 - Complex.I * (u : ℂ)) / (1 + Complex.I * (u : ℂ)) := by
  have hd : (1 + Complex.I * (u : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  apply (eq_div_iff hd).2
  apply Complex.ext
  · simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im]
    rw [Real.cos_two_mul, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hs : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
    have hn : Real.sqrt (1 + u ^ 2) ≠ 0 := by positivity
    field_simp
    nlinarith [hs]
  · simp [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.mul_im]
    rw [Real.cos_two_mul, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hs : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
    have hn : Real.sqrt (1 + u ^ 2) ≠ 0 := by positivity
    field_simp
    nlinarith [hs]

theorem neg_exp_I_cot_phase (u : ℝ) :
    -Complex.exp (Complex.I * ((2 * (Real.pi / 2 - Real.arctan u) : ℝ) : ℂ)) =
      (1 - Complex.I * (u : ℂ)) / (1 + Complex.I * (u : ℂ)) := by
  have hz : Complex.I * ((2 * (Real.pi / 2 - Real.arctan u) : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I + -(2 * Complex.I * (Real.arctan u : ℂ)) := by
    push_cast
    ring
  rw [hz, Complex.exp_add, Complex.exp_pi_mul_I]
  simpa using exp_neg_two_I_arctan u

theorem cos_nat_pi_div_odd_ne_zero (l n : ℕ) :
    Real.cos ((n : ℝ) * Real.pi / (2 * l + 1)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have hden : (2 * (l : ℝ) + 1) ≠ 0 := by positivity
  have he : 2 * (n : ℝ) = (2 * (k : ℝ) + 1) * (2 * (l : ℝ) + 1) := by
    field_simp [hden] at hk
    nlinarith [hk]
  have hi : 2 * (n : ℤ) = (2 * k + 1) * (2 * (l : ℤ) + 1) := by exact_mod_cast he
  have hi' : 2 * ((n : ℤ) - (2 * k * (l : ℤ) + k + (l : ℤ))) = 1 := by
    linear_combination hi
  omega

theorem tan_ratio_eq_cos_ratio (theta mu : ℝ) (hc : Real.cos theta ≠ 0) :
    (1 - Complex.I * ((Real.tan theta * mu : ℝ) : ℂ)) /
      (1 + Complex.I * ((Real.tan theta * mu : ℝ) : ℂ)) =
    ((Real.cos theta : ℂ) - Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) /
      ((Real.cos theta : ℂ) + Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) := by
  have hc' : (Real.cos theta : ℂ) ≠ 0 := by exact_mod_cast hc
  have hd : (Real.cos theta : ℂ) + Complex.I * (mu : ℂ) * (Real.sin theta : ℂ) ≠ 0 := by
    intro h
    apply hc
    simpa using! congrArg Complex.re h
  have h1 : (1 + Complex.I * ((Real.tan theta * mu : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  apply (div_eq_div_iff h1 hd).2
  rw [Real.tan_eq_sin_div_cos]
  simp only [Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [hc']

theorem neg_exp_alpha_eq_recW (l k : ℕ) (gamma : ℝ) :
    -Complex.exp (Complex.I * (ylcAlpha (2 * l + 1) k gamma : ℂ)) =
      ylcRecW (2 * l + 1) (Real.sqrt (1 - gamma ^ 2)) (2 * k + 1) := by
  unfold ylcAlpha ylcRecW
  simp only [Nat.add_sub_cancel]
  rw [neg_exp_I_cot_phase]
  have ht : 2 * Real.pi * (k : ℝ) / ((2 * l + 1 : ℕ) : ℝ) =
      ((2 * k : ℕ) : ℝ) * Real.pi / ((2 * l + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [ht]
  exact tan_ratio_eq_cos_ratio _ _ (by
    convert! cos_nat_pi_div_odd_ne_zero l (2 * k) using 1; push_cast; ring)

theorem neg_exp_neg_cot_phase (u : ℝ) :
    -Complex.exp (Complex.I * -((2 * (Real.pi / 2 - Real.arctan (-u)) : ℝ) : ℂ)) =
      (1 - Complex.I * (u : ℂ)) / (1 + Complex.I * (u : ℂ)) := by
  rw [Real.arctan_neg]
  have hz : Complex.I * -((2 * (Real.pi / 2 - -Real.arctan u) : ℝ) : ℂ) =
      -((Real.pi : ℂ) * Complex.I) + -(2 * Complex.I * (Real.arctan u : ℂ)) := by
    push_cast
    ring
  rw [hz, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  simpa using exp_neg_two_I_arctan u

theorem neg_exp_beta_eq_recW (l i : ℕ) (hi : i < l) (gamma : ℝ) :
    -Complex.exp (Complex.I * (-(ylcAlpha (2 * l + 1) (l - i) gamma) : ℂ)) =
      ylcRecW (2 * l + 1) (Real.sqrt (1 - gamma ^ 2)) (2 * i + 2) := by
  have ht : 2 * Real.pi * (l - i : ℕ) / ((2 * l + 1 : ℕ) : ℝ) =
      Real.pi - ((2 * i + 1 : ℕ) : ℝ) * Real.pi / ((2 * l + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  unfold ylcAlpha ylcRecW
  simp only [show 2 * i + 2 - 1 = 2 * i + 1 by omega]
  rw [ht, Real.tan_pi_sub, neg_mul, neg_exp_neg_cot_phase,
    tan_ratio_eq_cos_ratio _ _ (by
      convert! cos_nat_pi_div_odd_ne_zero l (2 * i + 1) using 1; push_cast; ring)]

theorem cos_ratio_eq_exp_ratio (theta mu : ℝ) (hc : Real.cos theta ≠ 0) :
    ((Real.cos theta : ℂ) - Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) /
      ((Real.cos theta : ℂ) + Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) =
    ((1 - (mu : ℂ)) * Complex.exp (2 * Complex.I * (theta : ℂ)) + (1 + (mu : ℂ))) /
      ((1 + (mu : ℂ)) * Complex.exp (2 * Complex.I * (theta : ℂ)) + (1 - (mu : ℂ))) := by
  let E : ℂ := Complex.exp (Complex.I * (theta : ℂ))
  have he : E = (Real.cos theta : ℂ) + Complex.I * (Real.sin theta : ℂ) := by
    dsimp [E]
    rw [mul_comm, Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_comm]
  have he0 : E ≠ 0 := Complex.exp_ne_zero _
  have hq : Complex.exp (2 * Complex.I * (theta : ℂ)) = E ^ 2 := by
    calc
      _ = Complex.exp (Complex.I * (theta : ℂ) + Complex.I * (theta : ℂ)) := by congr 1; ring
      _ = E ^ 2 := by simp [Complex.exp_add, E, pow_two]
  have hn : (Real.cos theta : ℂ) ^ 2 + (Real.sin theta : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq theta
  have hI : Complex.I ^ 2 + 1 = 0 := by simp
  have hden : (1 + (mu : ℂ)) * E ^ 2 + (1 - (mu : ℂ)) =
      2 * E * ((Real.cos theta : ℂ) + Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) := by
    rw [he]
    linear_combination ((mu : ℂ) - 1) * hn +
      (1 - (mu : ℂ)) * (Real.sin theta : ℂ) ^ 2 * hI
  have hnum : (1 - (mu : ℂ)) * E ^ 2 + (1 + (mu : ℂ)) =
      2 * E * ((Real.cos theta : ℂ) - Complex.I * (mu : ℂ) * (Real.sin theta : ℂ)) := by
    rw [he]
    linear_combination -(1 + (mu : ℂ)) * hn +
      (1 + (mu : ℂ)) * (Real.sin theta : ℂ) ^ 2 * hI
  have hd : (Real.cos theta : ℂ) + Complex.I * (mu : ℂ) * (Real.sin theta : ℂ) ≠ 0 := by
    intro h
    apply hc
    simpa using! congrArg Complex.re h
  rw [hq, hnum, hden]
  field_simp

theorem recW_eq_exp_ratio (L n : ℕ) (mu : ℝ)
    (hc : Real.cos ((n : ℝ) * Real.pi / L) ≠ 0) :
    ylcRecW L mu (n + 1) =
      ((1 - (mu : ℂ)) * Complex.exp (2 * Complex.I * (((n : ℝ) * Real.pi / L : ℝ) : ℂ)) +
        (1 + (mu : ℂ))) /
      ((1 + (mu : ℂ)) * Complex.exp (2 * Complex.I * (((n : ℝ) * Real.pi / L : ℝ) : ℂ)) +
        (1 - (mu : ℂ))) := by
  unfold ylcRecW
  simp only [Nat.add_sub_cancel]
  exact cos_ratio_eq_exp_ratio _ _ hc

theorem exponential_root_power (L n : ℕ) :
    Complex.exp (2 * Complex.I * (((n : ℝ) * Real.pi / L : ℝ) : ℂ)) =
      (Complex.exp (2 * Complex.I * ((Real.pi / L : ℝ) : ℂ))) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end PhaseCoefficients

noncomputable def ylcRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * Complex.I * ((Real.pi / L : ℝ) : ℂ))

theorem ylcRoot_primitive (l : ℕ) : IsPrimitiveRoot (ylcRoot (2 * l + 1)) (2 * l + 1) := by
  have h := Complex.isPrimitiveRoot_exp (2 * l + 1) (by omega)
  convert! h using 1
  unfold ylcRoot
  congr 1
  push_cast
  ring

theorem ylcRoot_norm (L : ℕ) : ‖ylcRoot L‖ = 1 := by
  simp [ylcRoot, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem root_denominator_ne_zero (q : ℂ) (hq : ‖q‖ = 1) (mu : ℝ) (hm : 0 < mu) (k : ℕ) :
    ((1 + mu : ℝ) : ℂ) * q ^ k + ((1 - mu : ℝ) : ℂ) ≠ 0 := by
  intro h
  have he : ((1 + mu : ℝ) : ℂ) * q ^ k = -((1 - mu : ℝ) : ℂ) := by
    linear_combination h
  have hn := congrArg (fun z : ℂ => ‖z‖) he
  simp only [norm_mul, norm_pow, hq, one_pow, mul_one, norm_neg, Complex.norm_real,
    Real.norm_eq_abs] at hn
  have hs := congrArg (fun t : ℝ => t ^ 2) hn
  simp only [sq_abs] at hs
  nlinarith

theorem ylcRecW_algebraic (l : ℕ) (mu : ℝ) (n : ℕ) :
    ylcRecW (2 * l + 1) mu (n + 1) =
      algebraicRecW (ylcRoot (2 * l + 1)) (1 + (mu : ℂ)) (1 - (mu : ℂ)) n := by
  rw [PhaseCoefficients.recW_eq_exp_ratio (2 * l + 1) n mu (by
    convert! PhaseCoefficients.cos_nat_pi_div_odd_ne_zero l n using 1
    push_cast
    rfl)]
  rw [PhaseCoefficients.exponential_root_power]
  rfl

theorem ylcRecA_algebraic (l : ℕ) (mu x : ℝ) (n : ℕ) :
    ylcRecA (2 * l + 1) mu x n =
      algebraicRecA (ylcRoot (2 * l + 1)) (x : ℂ) (1 + (mu : ℂ)) (1 - (mu : ℂ)) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 =>
    rw [ylcRecA, algebraicRecA, ih0, ih1, ylcRecW_algebraic l mu (n + 1)]

theorem cheb_complex (n : ℕ) (x : ℝ) :
    (cheb n x : ℂ) = (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval (x : ℂ) := by
  unfold cheb
  rw [← Polynomial.Chebyshev.map_T Complex.ofRealHom (n : ℤ)]
  exact (Polynomial.eval_map_apply Complex.ofRealHom (p := Polynomial.Chebyshev.T ℝ (n : ℤ)) x).symm

theorem ylcRecA_chebyshev_of_width (l : ℕ) (mu gamma x : ℝ)
    (hm : 0 < mu) (hg : gamma ≠ 0) (hmg : mu ^ 2 + gamma ^ 2 = 1) :
    ylcRecA (2 * l + 1) mu x (2 * l + 1) =
      ((cheb (2 * l + 1) (x / gamma) / cheb (2 * l + 1) (1 / gamma) : ℝ) : ℂ) := by
  let q := ylcRoot (2 * l + 1)
  have hab : (1 + (mu : ℂ)) + (1 - (mu : ℂ)) = 2 := by ring
  have hprod : (1 + (mu : ℂ)) * (1 - (mu : ℂ)) = (gamma : ℂ) ^ 2 := by
    have hc : (mu : ℂ) ^ 2 + (gamma : ℂ) ^ 2 = 1 := by exact_mod_cast hmg
    linear_combination -hc
  have hd : ∀ k : ℕ, (1 + (mu : ℂ)) * q ^ k + (1 - (mu : ℂ)) ≠ 0 := by
    intro k
    simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one] using
      root_denominator_ne_zero q (ylcRoot_norm (2 * l + 1)) mu hm k
  rw [ylcRecA_algebraic]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, cheb_complex] using
    algebraicRecA_chebyshev q (x : ℂ) (1 + (mu : ℂ)) (1 - (mu : ℂ)) (gamma : ℂ) l
      hab hprod (by exact_mod_cast hg) (ylcRoot_primitive l) hd

theorem ylcRecA_miracle (l : ℕ) (delta x : ℝ) (hd : 0 < delta) (hu : delta < 1) :
    ylcRecA (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) x (2 * l + 1) =
      ((delta * cheb (2 * l + 1) (x / ylcGamma (2 * l + 1) delta) : ℝ) : ℂ) := by
  let gamma := ylcGamma (2 * l + 1) delta
  let mu := Real.sqrt (1 - gamma ^ 2)
  have hw := widthIdentity (2 * l + 1) delta (by omega) ⟨hd, hu⟩
  have hgp : 0 < gamma := hw.1
  have hgl : gamma < 1 := hw.2.1
  have hpos : 0 < 1 - gamma ^ 2 := by
    have h := mul_pos (sub_pos.mpr hgl) (show 0 < 1 + gamma by linarith)
    nlinarith
  have hmp : 0 < mu := Real.sqrt_pos.2 hpos
  have hmg : mu ^ 2 + gamma ^ 2 = 1 := by
    have h := Real.sq_sqrt hpos.le
    change mu ^ 2 = 1 - gamma ^ 2 at h
    linarith
  have h := ylcRecA_chebyshev_of_width l mu gamma x hmp hgp.ne' hmg
  have hc : cheb (2 * l + 1) (1 / gamma) = 1 / delta := hw.2.2
  rw [hc] at h
  rw [one_div, div_inv_eq_mul, mul_comm (cheb (2 * l + 1) (x / gamma)) delta] at h
  exact h

theorem ylcBridgeRec_miracle_proved : ylcBridgeRec_miracle := by
  intro L delta lam hodd _ hd hu _ _
  obtain ⟨l, hl⟩ := hodd
  have hL : L = 2 * l + 1 := by omega
  subst L
  simpa only [Complex.ofReal_mul] using ylcRecA_miracle l delta (Real.sqrt (1 - lam)) hd hu

namespace PhysicalTransport

noncomputable def mirrorMatrix (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (1 - lam) : ℂ), (Real.sqrt lam : ℂ);
    (Real.sqrt lam : ℂ), -(Real.sqrt (1 - lam) : ℂ)]

theorem stateReflection_factor (lam alpha : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    stateReflection lam alpha = Complex.exp (-(Complex.I * (alpha : ℂ))) •
      (mirrorMatrix lam * targetReflection alpha * mirrorMatrix lam) := by
  have he : Complex.exp (-(Complex.I * (alpha : ℂ))) *
      Complex.exp (Complex.I * (alpha : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hx : (Real.sqrt (1 - lam) : ℂ) ^ 2 = 1 - (lam : ℂ) := by
    simpa using ofReal_sqrt_sq (show 0 ≤ 1 - lam by linarith)
  have hs : (Real.sqrt lam : ℂ) ^ 2 = (lam : ℂ) := ofReal_sqrt_sq hl
  rw [stateReflection_entry lam alpha hl hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [mirrorMatrix, targetReflection]
  · linear_combination -Complex.exp (-(Complex.I * (alpha : ℂ))) * hx -
        Complex.exp (-(Complex.I * (alpha : ℂ))) *
          Complex.exp (Complex.I * (alpha : ℂ)) * hs - (lam : ℂ) * he
  · linear_combination (Real.sqrt (1 - lam) : ℂ) * (Real.sqrt lam : ℂ) * he
  · linear_combination (Real.sqrt (1 - lam) : ℂ) * (Real.sqrt lam : ℂ) * he
  · linear_combination -Complex.exp (-(Complex.I * (alpha : ℂ))) * hs -
        Complex.exp (-(Complex.I * (alpha : ℂ))) *
          Complex.exp (Complex.I * (alpha : ℂ)) * hx - (1 - (lam : ℂ)) * he

theorem groverIterate_factor (lam alpha beta : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    groverIterate lam alpha beta = (-Complex.exp (-(Complex.I * (alpha : ℂ)))) •
      ((mirrorMatrix lam * targetReflection alpha) * (mirrorMatrix lam * targetReflection beta)) := by
  rw [groverIterate, stateReflection_factor lam alpha hl hu, Matrix.smul_mul, ← Matrix.mul_assoc]
  simp only [neg_smul]

theorem mirror_phase_eq_step (lam theta : ℝ) (w : ℂ)
    (hw : -Complex.exp (Complex.I * (theta : ℂ)) = w) :
    mirrorMatrix lam * targetReflection theta =
      continuantStep (Real.sqrt (1 - lam) : ℂ) (Real.sqrt lam : ℂ) w := by
  rw [← hw]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [mirrorMatrix, targetReflection, continuantStep]

noncomputable def executionPhase (l : ℕ) (delta : ℝ) (i : ℕ) : ℂ :=
  -Complex.exp (-(Complex.I * (ylcAlpha (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta) : ℂ)))

noncomputable def executionScalar (l : ℕ) (delta : ℝ) (k : ℕ) : ℂ :=
  ((List.range k).map (executionPhase l delta)).prod

noncomputable def executionPrefix (l : ℕ) (delta lam : ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.range k).map (publicIterate l delta lam)).reverse.prod

theorem executionScalar_succ (l : ℕ) (delta : ℝ) (k : ℕ) :
    executionScalar l delta (k + 1) = executionScalar l delta k * executionPhase l delta k := by
  simp [executionScalar, List.range_succ]

theorem executionScalar_norm (l : ℕ) (delta : ℝ) (k : ℕ) : ‖executionScalar l delta k‖ = 1 := by
  induction k with
  | zero => simp [executionScalar]
  | succ k ih =>
    rw [executionScalar_succ, norm_mul, ih]
    simp only [executionPhase, norm_neg, norm_exp_neg_I_mul, mul_one]

theorem executionPrefix_succ (l : ℕ) (delta lam : ℝ) (k : ℕ) :
    executionPrefix l delta lam (k + 1) =
      publicIterate l delta lam k * executionPrefix l delta lam k := by
  simp [executionPrefix, List.range_succ, List.reverse_append]

theorem publicIterate_steps (l i : ℕ) (hi : i < l) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicIterate l delta lam i = executionPhase l delta i •
      (continuantStep (Real.sqrt (1 - lam) : ℂ) (Real.sqrt lam : ℂ)
        (ylcRecW (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) (2 * i + 3)) *
      continuantStep (Real.sqrt (1 - lam) : ℂ) (Real.sqrt lam : ℂ)
        (ylcRecW (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2)) (2 * i + 2))) := by
  let gamma := ylcGamma (2 * l + 1) delta
  have ha := mirror_phase_eq_step lam (ylcAlpha (2 * l + 1) (i + 1) gamma) _
    (PhaseCoefficients.neg_exp_alpha_eq_recW l (i + 1) gamma)
  have hb := mirror_phase_eq_step lam (-(ylcAlpha (2 * l + 1) (l - i) gamma)) _
    (by simpa only [Complex.ofReal_neg] using PhaseCoefficients.neg_exp_beta_eq_recW l i hi gamma)
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] at ha
  change groverIterate lam (ylcAlpha (2 * l + 1) (i + 1) gamma)
    (-(ylcAlpha (2 * l + 1) (l - i) gamma)) = _
  rw [groverIterate_factor lam _ _ hl hu, ha, hb]
  rfl

theorem executionPrefix_run (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1)
    (k : ℕ) (hk : k ≤ l) :
    executionPrefix l delta lam k *ᵥ ampState lam = executionScalar l delta k •
      recurrenceRun (2 * l + 1) (Real.sqrt (1 - ylcGamma (2 * l + 1) delta ^ 2))
        (Real.sqrt (1 - lam)) (Real.sqrt lam) (2 * k + 1) := by
  revert hk
  induction k with
  | zero =>
    intro _
    ext i
    fin_cases i <;> simp [executionPrefix, executionScalar, recurrenceRun, continuantStep,
      ampState, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | succ k ih =>
    intro hk
    rw [executionPrefix_succ, ← Matrix.mulVec_mulVec, ih (by omega), Matrix.mulVec_smul,
      publicIterate_steps l k (by omega) delta lam hl hu, Matrix.smul_mulVec,
      smul_smul, ← Matrix.mulVec_mulVec, executionScalar_succ]
    congr 1

end PhysicalTransport

theorem ylcBridgeRec_rearrangement_proved : ylcBridgeRec_rearrangement := by
  intro L delta lam hodd _ _ _ hl hu
  obtain ⟨l, hlodd⟩ := hodd
  have hL : L = 2 * l + 1 := by omega
  subst L
  have hxs : Real.sqrt (1 - lam) ^ 2 + Real.sqrt lam ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hl]
    ring
  refine ⟨PhysicalTransport.executionScalar l delta l,
    PhysicalTransport.executionScalar_norm l delta l, ?_⟩
  have hh : ((2 * l + 1 : ℕ) - 1) / 2 = l := by omega
  rw [hh]
  change Qatlib.Foundations.PureStateMath.Inner ylcFailVec
      (ylcWordMatrix l delta lam *ᵥ ampState lam) = _
  rw [inner_ylcFailVec]
  change (PhysicalTransport.executionPrefix l delta lam l *ᵥ ampState lam) 0 = _
  rw [PhysicalTransport.executionPrefix_run l delta lam hl hu l (le_refl _)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [recurrenceRun_first (2 * l + 1) _ _ _ hxs]

theorem publicWord_success_response (l : ℕ) (delta lam : ℝ)
    (hd : 0 < delta) (hdu : delta < 1) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicSuccessProb l delta lam = responseProb (2 * l + 1) delta lam := by
  have h := ylc_master_response_of_bridges ylcBridgeRec_rearrangement_proved
    ylcBridgeRec_miracle_proved l delta lam hd hdu hl hu
  simpa only [publicSuccessProb, publicSuccessAmplitude, publicWord_eq, ylcTargetVec] using! h

theorem publicWord_uniform_guarantee (lam0 delta : ℝ) (h0 : 0 < lam0) (h0u : lam0 < 1)
    (hd : 0 < delta) (hdu : delta < 1) :
    ∀ lam : ℝ, lam0 ≤ lam → lam ≤ 1 →
      1 - delta ^ 2 ≤ publicSuccessProb (publicIterateCount lam0 delta) delta lam := by
  intro lam hl hu
  rw [publicWord_success_response _ delta lam hd hdu (by linarith) hu]
  have hchoice := clause1_uniform_success lam0 delta ⟨h0, h0u⟩ ⟨hd, hdu⟩
  have hn : 2 * publicIterateCount lam0 delta + 1 = publicLength lam0 delta := by
    obtain ⟨k, hk⟩ := hchoice.1
    unfold publicIterateCount
    omega
  rw [hn]
  exact hchoice.2.2 lam ⟨hl, hu⟩

namespace MarkedSearch

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def goodMass (P : Matrix I I ℂ) (s : QState I) : ℝ := ProjectiveBranchMass P true s

theorem goodMass_bounds (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) :
    0 ≤ goodMass P s ∧ goodMass P s ≤ 1 := by
  have hc := projectiveBranchMass_add hP s
  have hn := projectiveBranchMass_nonneg P false s
  have ht : MeasureProb s Finset.univ = 1 := measureProb_univ hs
  refine ⟨projectiveBranchMass_nonneg P true s, ?_⟩
  dsimp only [goodMass]
  linarith

omit [DecidableEq I] in

theorem projector_good (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : P *ᵥ (P *ᵥ s) = P *ᵥ s := by
  rw [Matrix.mulVec_mulVec, hP.1]

omit [DecidableEq I] in

theorem projector_bad (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : P *ᵥ (s - P *ᵥ s) = 0 := by
  rw [Matrix.mulVec_sub, projector_good P s hP, sub_self]

theorem good_inner_self (P : Matrix I I ℂ) (s : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (P *ᵥ s) (P *ᵥ s) = (goodMass P s : ℂ) := by
  rw [inner_self, ← Complex.ofReal_sum]
  rfl

theorem source_inner_good (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = (goodMass P s : ℂ) := by
  have hpstar : Pᴴ = P := hP.2
  calc
    Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = Qatlib.Foundations.PureStateMath.Inner (P *ᵥ s) (P *ᵥ s) := by
      rw [inner_mulVec_left_rect, hpstar, projector_good P s hP]
    _ = _ := good_inner_self P s

theorem source_inner_bad (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) :
    Qatlib.Foundations.PureStateMath.Inner s (s - P *ᵥ s) = 1 - (goodMass P s : ℂ) := by
  change star s ⬝ᵥ (s - P *ᵥ s) = _
  rw [dotProduct_sub]
  change Qatlib.Foundations.PureStateMath.Inner s s - Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = _
  rw [(normalized_iff_inner_self s).mp hs, source_inner_good P s hP]

noncomputable def markedPhase (P : Matrix I I ℂ) (beta : ℝ) : Matrix I I ℂ :=
  1 - (1 - Complex.exp (Complex.I * (beta : ℂ))) • P

theorem markedPhase_unitary (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P) (beta : ℝ) :
    markedPhase P beta ∈ Matrix.unitaryGroup I ℂ := by
  have he : Complex.exp (Complex.I * (beta : ℂ)) *
      star (Complex.exp (Complex.I * (beta : ℂ))) = 1 := by
    change Complex.exp (Complex.I * (beta : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (beta : ℂ))) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hn : ‖Complex.exp (Complex.I * (beta : ℂ))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    simp only [hn, one_pow, Complex.ofReal_one]
  apply Matrix.mem_unitaryGroup_iff.mpr
  change markedPhase P beta * (markedPhase P beta)ᴴ = 1
  have hHerm : Pᴴ = P := hP.2
  have hIdem : P * P = P := hP.1
  simp only [markedPhase, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, hHerm, sub_mul, mul_sub, one_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, hIdem]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_one]
  linear_combination (P i j) * he

theorem prepared_reflection (A : Matrix I I ℂ) (seed : QState I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (alpha : ℝ) :
    fullStateReflection (A *ᵥ seed) alpha = A * fullStateReflection seed alpha * Aᴴ := by
  have hout : A * outerProduct seed * Aᴴ = outerProduct (A *ᵥ seed) := by
    change A * Matrix.vecMulVec seed (fun i => star (seed i)) * Aᴴ =
      Matrix.vecMulVec (A *ᵥ seed) (fun i => star ((A *ᵥ seed) i))
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    congr 1
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  have hAA : A * Aᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hA
  simp only [fullStateReflection, mul_sub, mul_one, sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, hAA, hout]

theorem markedPhase_frame (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (F G : ℂ) (beta : ℝ) :
    markedPhase P beta *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s)) =
      F • (s - P *ᵥ s) + (Complex.exp (Complex.I * (beta : ℂ)) * G) • (P *ᵥ s) := by
  have hp : P *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = G • (P *ᵥ s) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      projector_bad P s hP, projector_good P s hP, smul_zero, zero_add]
  rw [markedPhase, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hp, smul_smul]
  module

omit [DecidableEq I] in

theorem projector_frame (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (F G : ℂ) :
    P *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = G • (P *ᵥ s) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    projector_bad P s hP, projector_good P s hP, smul_zero, zero_add]

theorem projector_frame_mass (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (F G : ℂ) :
    ProjectiveBranchMass P true (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = ‖G‖ ^ 2 * goodMass P s := by
  change MeasureProb (P *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s))) Finset.univ = _
  rw [projector_frame P s hP, Qatlib.Foundations.BornMetrics.EventProbability.measureProb_smul]
  rfl

noncomputable def polynomialFrame (P : Matrix I I ℂ) (s : QState I)
    (p : Polynomial ℂ × Polynomial ℂ) : QState I :=
  p.1.eval (goodMass P s : ℂ) • (s - P *ᵥ s) + p.2.eval (goodMass P s : ℂ) • (P *ᵥ s)

noncomputable def markedIterate (P : Matrix I I ℂ) (s : QState I) (alpha beta : ℝ) :
    Matrix I I ℂ := -(fullStateReflection s alpha * markedPhase P beta)

omit [DecidableEq I] in

theorem inner_add_right (s v w : QState I) : Qatlib.Foundations.PureStateMath.Inner s (v + w) = Qatlib.Foundations.PureStateMath.Inner s v + Qatlib.Foundations.PureStateMath.Inner s w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_add]

theorem markedIterate_frame (P : Matrix I I ℂ) (s : QState I) (hP : IsOrthogonalProjector P)
    (hs : Normalized s) (alpha beta : ℝ) (p : Polynomial ℂ × Polynomial ℂ) :
    markedIterate P s alpha beta *ᵥ polynomialFrame P s p =
      polynomialFrame P s (responseStep alpha beta p) := by
  let lam := goodMass P s
  let F := p.1.eval (lam : ℂ)
  let G := p.2.eval (lam : ℂ)
  let v := Complex.exp (Complex.I * (beta : ℂ))
  have hin : Qatlib.Foundations.PureStateMath.Inner s (F • (s - P *ᵥ s) + (v * G) • (P *ᵥ s)) =
      F * (1 - (lam : ℂ)) + (v * G) * (lam : ℂ) := by
    rw [inner_add_right, Qatlib.Papers.FixedPtSearch14.FixedPoint.inner_smul_right,
      Qatlib.Papers.FixedPtSearch14.FixedPoint.inner_smul_right,
      source_inner_bad P s hP hs, source_inner_good P s hP]
  change -(fullStateReflection s alpha * markedPhase P beta) *ᵥ
    (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = _
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, markedPhase_frame P s hP F G beta]
  rw [fullStateReflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    outerProduct_mulVec, smul_smul, hin]
  simp only [polynomialFrame, responseStep, eval_add, eval_mul, eval_sub, eval_neg, eval_one,
    eval_X, eval_C]
  dsimp only [F, G, v, lam]
  module

noncomputable def markedPhaseWord (P : Matrix I I ℂ) (s : QState I)
    (phases : List (ℝ × ℝ)) : Matrix I I ℂ :=
  (phases.map fun ab => markedIterate P s ab.1 ab.2).prod

theorem markedPhaseWord_frame (P : Matrix I I ℂ) (s : QState I) (hP : IsOrthogonalProjector P)
    (hs : Normalized s) (phases : List (ℝ × ℝ)) :
    markedPhaseWord P s phases *ᵥ s = polynomialFrame P s (responsePolynomials phases) := by
  induction phases with
  | nil => simp [markedPhaseWord, responsePolynomials, polynomialFrame]
  | cons ab tail ih =>
    change (markedIterate P s ab.1 ab.2 * markedPhaseWord P s tail) *ᵥ s =
      polynomialFrame P s (responseStep ab.1 ab.2 (responsePolynomials tail))
    rw [← Matrix.mulVec_mulVec, ih]
    exact markedIterate_frame P s hP hs ab.1 ab.2 (responsePolynomials tail)

noncomputable def markedWordMatrix (P : Matrix I I ℂ) (s : QState I) (l : ℕ) (delta : ℝ) :
    Matrix I I ℂ := markedPhaseWord P s (publicPhases l delta)

theorem markedWord_unitary (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (l : ℕ) (delta : ℝ) :
    markedWordMatrix P s l delta ∈ Matrix.unitaryGroup I ℂ := by
  have hstep (alpha beta : ℝ) : markedIterate P s alpha beta ∈ Matrix.unitaryGroup I ℂ := by
    have heq : fullStateReflection s alpha = markedPhase (outerProduct s) (-alpha) := by
      simp [fullStateReflection, markedPhase]
    have hsrc : fullStateReflection s alpha ∈ Matrix.unitaryGroup I ℂ := by
      rw [heq]
      exact markedPhase_unitary _ (isOrthogonalProjector_outerProduct hs) _
    have hp := (Matrix.unitaryGroup I ℂ).mul_mem hsrc (markedPhase_unitary P hP beta)
    apply Matrix.mem_unitaryGroup_iff.mpr
    change (-(fullStateReflection s alpha * markedPhase P beta)) *
      (-(fullStateReflection s alpha * markedPhase P beta))ᴴ = 1
    simpa only [Matrix.conjTranspose_neg, neg_mul_neg] using! Matrix.mem_unitaryGroup_iff.mp hp
  unfold markedWordMatrix markedPhaseWord
  apply (Matrix.unitaryGroup I ℂ).list_prod_mem
  intro a ha
  obtain ⟨ab, _, rfl⟩ := List.mem_map.mp ha
  exact hstep ab.1 ab.2

theorem markedWord_success_eq_twoLevel (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (l : ℕ) (delta : ℝ) :
    ProjectiveBranchMass P true (markedWordMatrix P s l delta *ᵥ s) =
      publicSuccessProb l delta (goodMass P s) := by
  rw [markedWordMatrix, markedPhaseWord_frame P s hP hs]
  change ProjectiveBranchMass P true (_ • (s - P *ᵥ s) + _ • (P *ᵥ s)) = _
  rw [projector_frame_mass P s hP]
  have hb := goodMass_bounds P s hP hs
  rw [publicSuccessProb_polynomial l delta (goodMass P s) hb.1 hb.2]
  ring

theorem markedWord_success_response (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (l : ℕ) (delta : ℝ)
    (hd : 0 < delta) (hdu : delta < 1) :
    ProjectiveBranchMass P true (markedWordMatrix P s l delta *ᵥ s) =
      responseProb (2 * l + 1) delta (goodMass P s) := by
  rw [markedWord_success_eq_twoLevel P s hP hs]
  have hb := goodMass_bounds P s hP hs
  exact publicWord_success_response l delta (goodMass P s) hd hdu hb.1 hb.2

theorem markedWord_endpoints (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (l : ℕ) (delta : ℝ) :
    (goodMass P s = 0 → ProjectiveBranchMass P true (markedWordMatrix P s l delta *ᵥ s) = 0) ∧
    (goodMass P s = 1 → ProjectiveBranchMass P true (markedWordMatrix P s l delta *ᵥ s) = 1) := by
  constructor
  · intro h
    rw [markedWord_success_eq_twoLevel P s hP hs, h]
    exact (publicWord_endpoints l delta).1
  · intro h
    rw [markedWord_success_eq_twoLevel P s hP hs, h]
    exact (publicWord_endpoints l delta).2

theorem publicLength_as_iterates (lam0 delta : ℝ) :
    2 * publicIterateCount lam0 delta + 1 = publicLength lam0 delta := by
  unfold publicIterateCount publicLength ylcLength
  split_ifs <;> omega

theorem markedWord_uniform_guarantee (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (lam0 delta : ℝ)
    (h0 : 0 < lam0) (hd : 0 < delta) (hdu : delta < 1) (hm : lam0 ≤ goodMass P s) :
    1 - delta ^ 2 ≤ ProjectiveBranchMass P true
      (markedWordMatrix P s (publicIterateCount lam0 delta) delta *ᵥ s) := by
  rw [markedWord_success_eq_twoLevel P s hP hs]
  have hb := goodMass_bounds P s hP hs
  by_cases he : lam0 = 1
  · have hmass : goodMass P s = 1 := by rw [he] at hm; linarith
    subst lam0
    have hn : publicIterateCount 1 delta = 0 := by
      simp [publicIterateCount, publicLength, ylcLength]
    rw [hn, hmass, (publicWord_endpoints 0 delta).2]
    nlinarith [sq_nonneg delta]
  · have hlt : lam0 < 1 := lt_of_le_of_ne (hm.trans hb.2) he
    exact publicWord_uniform_guarantee lam0 delta h0 hlt hd hdu (goodMass P s) hm hb.2

theorem prepared_marked_search_complete (A : Matrix I I ℂ) (seed : QState I)
    (P : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hseed : Normalized seed)
    (hP : IsOrthogonalProjector P) (lam0 delta : ℝ) (h0 : 0 < lam0)
    (hd : 0 < delta) (hdu : delta < 1) (hm : lam0 ≤ goodMass P (A *ᵥ seed)) :
    let s := A *ᵥ seed
    let l := publicIterateCount lam0 delta
    let W := markedWordMatrix P s l delta
    2 * l + 1 = publicLength lam0 delta ∧
      ProjectiveBranchMass P true (W *ᵥ s) = responseProb (publicLength lam0 delta) delta (goodMass P s) ∧
      1 - delta ^ 2 ≤ ProjectiveBranchMass P true (W *ᵥ s) := by
  (try dsimp only)
  have hs : Normalized (A *ᵥ seed) := by
    simpa only [ApplyGate] using normalized_applyGate hA hseed
  have hn := publicLength_as_iterates lam0 delta
  refine ⟨hn, ?_, markedWord_uniform_guarantee P (A *ᵥ seed) hP hs lam0 delta h0 hd hdu hm⟩
  rw [markedWord_success_response P (A *ᵥ seed) hP hs _ delta hd hdu, hn]

theorem complete_clause1 (lam0 delta : ℝ) (h0 : 0 < lam0) (hd : 0 < delta) (hdu : delta < 1) :
    ∃ l : ℕ, l = publicIterateCount lam0 delta ∧
      ∀ (J : Type) [Fintype J] [DecidableEq J] (A : Matrix J J ℂ) (seed : QState J)
        (P : Matrix J J ℂ), A ∈ Matrix.unitaryGroup J ℂ → Normalized seed →
          IsOrthogonalProjector P →
          let s := A *ᵥ seed
          let out := markedWordMatrix P s l delta *ᵥ s
          ProjectiveBranchMass P true out = responseProb (publicLength lam0 delta) delta (goodMass P s) ∧
            (lam0 ≤ goodMass P s → 1 - delta ^ 2 ≤ ProjectiveBranchMass P true out) ∧
            (goodMass P s = 0 → ProjectiveBranchMass P true out = 0) ∧
            (goodMass P s = 1 → ProjectiveBranchMass P true out = 1) := by
  refine ⟨publicIterateCount lam0 delta, rfl, ?_⟩
  intro J _ _ A seed P hA hseed hP
  (try dsimp only)
  have hs : Normalized (A *ᵥ seed) := by
    simpa only [ApplyGate] using normalized_applyGate hA hseed
  have he := markedWord_endpoints P (A *ᵥ seed) hP hs (publicIterateCount lam0 delta) delta
  refine ⟨?_, ?_, he.1, he.2⟩
  · rw [markedWord_success_response P (A *ᵥ seed) hP hs _ delta hd hdu,
      publicLength_as_iterates]
  · intro hm
    exact markedWord_uniform_guarantee P (A *ᵥ seed) hP hs lam0 delta h0 hd hdu hm

end MarkedSearch

end Qatlib.Papers.FixedPtSearch14.FixedPoint
