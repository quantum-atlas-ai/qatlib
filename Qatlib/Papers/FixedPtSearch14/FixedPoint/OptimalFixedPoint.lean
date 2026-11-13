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

/-!
# Polynomial response and marked fixed-point search

This module proves the Chebyshev response of the public fixed-point word of
[YoderLowChuang2014]. Polynomial response factors describe arbitrary phase words; affine matrix
orbits and continuant recurrences establish the recurrence identity and connect it to the
executed word.

The `MarkedSearch` development transports the two-level response to an arbitrary orthogonal
marked projector and a normalized prepared source. `complete_clause1` chooses an iterate count
from the public lower bound and error parameter and supplies the exact response, uniform success
bound, and endpoint behavior.

## Main statements

* `phaseWord_realizes`: realization of the polynomial response factors.
* `ylcRecA_miracle`: the scaled Chebyshev recurrence identity.
* `publicWord_success_response`: the exact two-level success formula.
* `markedWord_success_response`: transport to a marked subspace.
* `complete_clause1`: a uniform choice for unitary-prepared inputs.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

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

/-- The polynomial update for the failure and success response factors under one generalized
Grover iterate with phases `alpha` and `beta`. -/
noncomputable def responseStep (alpha beta : ℝ)
    (p : Polynomial ℂ × Polynomial ℂ) : Polynomial ℂ × Polynomial ℂ :=
  let u : Polynomial ℂ := C (Complex.exp (-(Complex.I * (alpha : ℂ))))
  let v : Polynomial ℂ := C (Complex.exp (Complex.I * (beta : ℂ)))
  (-(X + (1 - X) * u) * p.1 + (1 - u) * X * v * p.2,
    (1 - u) * (1 - X) * p.1 - (1 - X + X * u) * v * p.2)

/-- The pair of response polynomials recursively obtained from a list of phase pairs, starting
from the constant pair `(1, 1)`. -/
noncomputable def responsePolynomials : List (ℝ × ℝ) → Polynomial ℂ × Polynomial ℂ
  | [] => (1, 1)
  | ab :: tail => responseStep ab.1 ab.2 (responsePolynomials tail)

/-- The matrix product of the generalized Grover iterates specified by a list of phase pairs. -/
noncomputable def phaseWord (phases : List (ℝ × ℝ)) (lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (phases.map fun ab => groverIterate lam ab.1 ab.2).prod

/-- The two-component vector formed by evaluating the response polynomials at `lam` and
multiplying by `√(1 - lam)` and `√lam`, respectively. -/
noncomputable def polynomialState (lam : ℝ) (p : Polynomial ℂ × Polynomial ℂ) :
    QState (Fin 2) :=
  ![(Real.sqrt (1 - lam) : ℂ) * p.1.eval (lam : ℂ),
    (Real.sqrt lam : ℂ) * p.2.eval (lam : ℂ)]

/-- For `lam ∈ [0, 1]`, applying one generalized Grover iterate to a polynomial state realizes
`responseStep`. -/
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

/-- For `lam ∈ [0, 1]`, a phase word applied to `ampState lam` equals the polynomial state of
its response polynomials. -/
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

/-- If both input response polynomials have natural degree at most `n`, both updated polynomials
have natural degree at most `n + 1`. -/
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

/-- Both response polynomials have natural degree at most the number of phase pairs. -/
theorem responsePolynomials_degree (phases : List (ℝ × ℝ)) :
    (responsePolynomials phases).1.natDegree ≤ phases.length ∧
      (responsePolynomials phases).2.natDegree ≤ phases.length := by
  induction phases with
  | nil => simp [responsePolynomials]
  | cons ab tail ih =>
    exact responseStep_degree ab.1 ab.2 (responsePolynomials tail) tail.length ih.1 ih.2

/-- The reversed list of analytic phase pairs used by the public fixed-point word. -/
noncomputable def publicPhases (l : ℕ) (delta : ℝ) : List (ℝ × ℝ) :=
  ((List.range l).map fun i =>
    (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta),
      -wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))).reverse

/-- The public phase-pair list for `l` iterates has length `l`. -/
theorem publicPhases_length (l : ℕ) (delta : ℝ) : (publicPhases l delta).length = l := by
  simp [publicPhases]

/-- The phase word determined by `publicPhases` equals the public fixed-point word. -/
theorem phaseWord_publicPhases (l : ℕ) (delta lam : ℝ) :
    phaseWord (publicPhases l delta) lam = publicWord l delta lam := by
  simp only [phaseWord, publicPhases, publicWord, List.map_reverse, List.map_map]
  rfl

/-- For `lam ∈ [0, 1]`, the public word applied to the amplitude state equals the state
represented by its public response polynomials. -/
theorem frontier1 (l : ℕ) (delta lam : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicWord l delta lam *ᵥ ampState lam =
      polynomialState lam (responsePolynomials (publicPhases l delta)) := by
  rw [← phaseWord_publicPhases]
  exact phaseWord_realizes _ lam hl hu

/-- For `lam ∈ [0, 1]`, the public failure probability is `1 - lam` times the squared modulus of
the first response polynomial evaluated at `lam`. -/
theorem publicFailureProb_polynomial (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicFailureProb l delta lam = (1 - lam) *
      ‖(responsePolynomials (publicPhases l delta)).1.eval (lam : ℂ)‖ ^ 2 := by
  have hs : ‖(Real.sqrt (1 - lam) : ℂ)‖ ^ 2 = 1 - lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith)]
  rw [publicFailureProb, publicFailureAmplitude, inner_ylcFailVec, frontier1 l delta lam hl hu]
  simp only [polynomialState, Matrix.cons_val_zero, norm_mul, mul_pow, hs]

/-- For `lam ∈ [0, 1]`, the public success probability is `lam` times the squared modulus of the
second response polynomial evaluated at `lam`. -/
theorem publicSuccessProb_polynomial (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicSuccessProb l delta lam = lam *
      ‖(responsePolynomials (publicPhases l delta)).2.eval (lam : ℂ)‖ ^ 2 := by
  have hs : ‖(Real.sqrt lam : ℂ)‖ ^ 2 = lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hl]
  rw [publicSuccessProb, publicSuccessAmplitude, inner_ylcTargetVec, frontier1 l delta lam hl hu]
  simp only [polynomialState, Matrix.cons_val_one, Matrix.cons_val_zero, norm_mul, mul_pow, hs]

/-- The product of a complex polynomial with the polynomial obtained by conjugating its
coefficients. -/
noncomputable def normSquarePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ) * p

/-- At a real argument, `normSquarePolynomial p` evaluates to the complex coercion of the
squared modulus of `p` at that argument. -/
theorem normSquarePolynomial_eval (p : Polynomial ℂ) (lam : ℝ) :
    (normSquarePolynomial p).eval (lam : ℂ) = (‖p.eval (lam : ℂ)‖ ^ 2 : ℝ) := by
  have he : (p.map (starRingEnd ℂ)).eval (lam : ℂ) =
      (starRingEnd ℂ) (p.eval (lam : ℂ)) := by
    simpa using (eval_map_apply (starRingEnd ℂ) (p := p) (lam : ℂ))
  rw [normSquarePolynomial, eval_mul, he, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]

/-- The polynomial `X` multiplied by the coefficientwise norm-square polynomial of the public
success response factor. -/
noncomputable def publicSuccessPolynomial (l : ℕ) (delta : ℝ) : Polynomial ℂ :=
  X * normSquarePolynomial (responsePolynomials (publicPhases l delta)).2

/-- On `[0, 1]`, the public success polynomial evaluates to the complex coercion of the public
success probability. -/
theorem publicSuccessPolynomial_eval (l : ℕ) (delta lam : ℝ)
    (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    (publicSuccessPolynomial l delta).eval (lam : ℂ) = (publicSuccessProb l delta lam : ℂ) := by
  rw [publicSuccessPolynomial, eval_mul, eval_X, normSquarePolynomial_eval,
    publicSuccessProb_polynomial l delta lam hl hu]
  simp only [Complex.ofReal_mul]

/-- The public success polynomial for `l` iterates has natural degree at most `2 * l + 1`. -/
theorem publicSuccessPolynomial_degree (l : ℕ) (delta : ℝ) :
    (publicSuccessPolynomial l delta).natDegree ≤ 2 * l + 1 := by
  have hp : (responsePolynomials (publicPhases l delta)).2.natDegree ≤ l := by
    simpa only [publicPhases_length] using (responsePolynomials_degree (publicPhases l delta)).2
  have hn : (normSquarePolynomial (responsePolynomials (publicPhases l delta)).2).natDegree ≤
      l + l := by
    exact natDegree_mul_le_of_le (natDegree_map_le.trans hp) hp
  exact (natDegree_mul_le_of_le (natDegree_X_le (R := ℂ)) hn).trans (by omega)

/-- For `lam ∈ [0, 1]`, the failure and success response polynomials satisfy the weighted
norm-square conservation identity. -/
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

/-- The public word has success probability zero at `lam = 0` and one at `lam = 1`. -/
theorem publicWord_endpoints (l : ℕ) (delta : ℝ) :
    publicSuccessProb l delta 0 = 0 ∧ publicSuccessProb l delta 1 = 1 := by
  constructor
  · simp [publicSuccessProb_polynomial l delta 0 (by norm_num) (by norm_num)]
  · have h := responsePolynomials_conservation l delta 1 (by norm_num) (by norm_num)
    simpa [publicSuccessProb_polynomial l delta 1 (by norm_num) (by norm_num)] using h

/-- Under `p * q = x ^ 2 - 1`, elimination of the auxiliary component gives the displayed
second-order continuant identity. -/
theorem continuant_elimination (x p q w a b : ℂ) (hpq : p * q = x ^ 2 - 1) :
    x * (x * a + p * b) + (w * p) * (q * a + x * b) =
      x * (1 + w) * (x * a + p * b) - w * a := by
  linear_combination w * a * hpq

/-- When `x ^ 2 + s ^ 2 = 1`, the first components of two successive `su2A` steps satisfy the
displayed second-order recurrence. -/
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

/-- A complex polynomial of natural degree at most positive `L` that is invariant under scaling
by a primitive `L`th root has only constant and degree-`L` terms. -/
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

/-- The ordered product of affine matrix factors `B + (q ^ k * u) • D` for successive indices
starting at zero. -/
def affineOrbit {R : Type*} [CommRing R] (B D : Matrix (Fin 2) (Fin 2) R)
    (q u : R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | n + 1 => affineOrbit B D q u n * (B + (q ^ n * u) • D)

/-- An affine orbit of length `n + 1` splits into its initial factor and a length-`n` orbit with
parameter `q * u`. -/
theorem affineOrbit_shift_head {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    (B + u • D) * affineOrbit B D q (q * u) n = affineOrbit B D q u (n + 1) := by
  induction n with
  | zero => simp [affineOrbit]
  | succ n ih =>
    rw [affineOrbit, ← mul_assoc, ih, affineOrbit]
    rw [show q ^ n * (q * u) = q ^ (n + 1) * u by rw [pow_succ, mul_assoc]]
    rfl

/-- For positive `L` and `q ^ L = 1`, multiplying the affine-orbit parameter by `q` leaves its
length-`L` trace unchanged. -/
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

/-- Applying a ring homomorphism entrywise to an affine orbit commutes with forming the orbit. -/
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

/-- The polynomial trace of the affine orbit with polynomial parameter `X` and constant matrices
`B` and `D`. -/
noncomputable def traceOrbitPolynomial (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : Polynomial ℂ :=
  Matrix.trace (affineOrbit (B.map Polynomial.C) (D.map Polynomial.C) (C q) X L)

/-- For positive `L` and `q ^ L = 1`, the trace-orbit polynomial is invariant under substituting
`q * X` for `X`. -/
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

/-- Multiplying two polynomial matrices with entry degrees bounded by `m` and `n` gives entries
of natural degree at most `m + n`. -/
private theorem matrixPolynomial_mul_degree (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (m n : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ m) (hB : ∀ i j, (B i j).natDegree ≤ n) :
    ∀ i j, ((A * B) i j).natDegree ≤ m + n := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact natDegree_add_le_of_degree_le
    (natDegree_mul_le_of_le (hA i 0) (hB 0 j))
    (natDegree_mul_le_of_le (hA i 1) (hB 1 j))

/-- For polynomial matrices with entry degrees bounded by `m` and `n`, the degree-`m + n`
coefficients multiply as the corresponding coefficient matrices. -/
private theorem matrixPolynomial_mul_top (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ))
    (m n : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ m) (hB : ∀ i j, (B i j).natDegree ≤ n) :
    ∀ i j, ((A * B) i j).coeff (m + n) =
      (A i 0).coeff m * (B 0 j).coeff n + (A i 1).coeff m * (B 1 j).coeff n := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, coeff_add,
    coeff_mul_add_eq_of_natDegree_le (hA i 0) (hB 0 j),
    coeff_mul_add_eq_of_natDegree_le (hA i 1) (hB 1 j)]

/-- Each entry of the displayed affine polynomial matrix has natural degree at most one. -/
private theorem affineFactor_degree (B D : Matrix (Fin 2) (Fin 2) ℂ) (q : ℂ) :
    ∀ i j, ((B.map Polynomial.C + (C q * X) • D.map Polynomial.C) i j).natDegree ≤ 1 := by
  intro i j
  change (C (B i j) + (C q * X) * C (D i j)).natDegree ≤ 1
  apply natDegree_add_le_of_degree_le
  · simp
  · simpa using natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (C q).natDegree ≤ 0 by simp) (natDegree_X_le (R := ℂ)))
      (show (C (D i j)).natDegree ≤ 0 by simp)

/-- Every entry of a length-`n` affine orbit in the polynomial parameter has natural degree at
most `n`. -/
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

/-- The length-`L` trace-orbit polynomial has natural degree at most `L`. -/
theorem traceOrbitPolynomial_degree (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : (traceOrbitPolynomial B D q L).natDegree ≤ L := by
  unfold traceOrbitPolynomial Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two]
  exact natDegree_add_le_of_degree_le
    (affineOrbit_polynomial_degree B D q L 0 0)
    (affineOrbit_polynomial_degree B D q L 1 1)

/-- Setting the affine-orbit parameter to zero gives the matrix power `B ^ n`. -/
theorem affineOrbit_zero {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q : R) (n : ℕ) :
    affineOrbit B D q 0 n = B ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [affineOrbit, ih, pow_succ]

/-- The constant coefficient of the trace-orbit polynomial is `Matrix.trace (B ^ L)`. -/
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

/-- The degree-`n` coefficient of each affine-orbit entry is the corresponding entry of `D ^ n`
multiplied by the product of the powers `q ^ k`. -/
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

/-- The degree-`L` coefficient of the trace-orbit polynomial is `Matrix.trace (D ^ L)`
multiplied by the product of the powers `q ^ k`. -/
theorem traceOrbitPolynomial_top (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q : ℂ) (L : ℕ) : (traceOrbitPolynomial B D q L).coeff L =
      (∏ k ∈ Finset.range L, q ^ k) * Matrix.trace (D ^ L) := by
  unfold traceOrbitPolynomial Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, coeff_add,
    affineOrbit_polynomial_top B D q L 0 0, affineOrbit_polynomial_top B D q L 1 1]
  simp only [Fin.sum_univ_two]
  ring

/-- If `q ^ (2 * l + 1) = 1`, the product of `q ^ k` over indices from zero through `2 * l` is
one. -/
theorem odd_root_orbit_weight (l : ℕ) (q : ℂ) (hq : q ^ (2 * l + 1) = 1) :
    (∏ k ∈ Finset.range (2 * l + 1), q ^ k) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hs : (∑ k ∈ Finset.range (2 * l + 1), k) = (2 * l + 1) * l := by
    have h := Finset.sum_range_id_mul_two (2 * l + 1)
    simp only [Nat.add_sub_cancel] at h
    nlinarith
  rw [hs, pow_mul, hq, one_pow]

/-- For a primitive root of odd order `2 * l + 1`, the trace-orbit polynomial consists of the
constant trace of `B` to that power and the corresponding top-degree trace of `D`. -/
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

/-- The constant continuant matrix with rows `(2 * x, -a)` and `(b, 0)`. -/
def continuantConstant (x a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -a; b, 0]

/-- The continuant matrix satisfies the quadratic identity `C ^ 2 = (2 * x) • C - (a * b) • 1`. -/
theorem continuantConstant_sq (x a b : ℂ) :
    continuantConstant x a b ^ 2 =
      (2 * x) • continuantConstant x a b - (a * b) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [continuantConstant, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul] <;> ring

/-- Powers of the continuant matrix satisfy the second-order recurrence with coefficients `2 *
x` and `a * b`. -/
theorem continuantConstant_power_recurrence (x a b : ℂ) (n : ℕ) :
    continuantConstant x a b ^ (n + 2) =
      (2 * x) • continuantConstant x a b ^ (n + 1) -
        (a * b) • continuantConstant x a b ^ n := by
  rw [pow_add, continuantConstant_sq, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, ← pow_succ]

/-- If `a * b = gamma ^ 2` and `gamma ≠ 0`, the trace of the `n`th continuant power equals `2 *
gamma ^ n` times the Chebyshev polynomial at `x / gamma`. -/
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

/-- Evaluating the trace-orbit polynomial at `u` gives the trace of the affine matrix orbit with
parameter `u`. -/
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

/-- For a primitive root of odd order, the affine-orbit trace is the trace of the corresponding
power of `B` plus `u` to that order times the trace of the power of `D`. -/
theorem affineOrbit_trace_closed (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q u : ℂ) (l : ℕ) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    Matrix.trace (affineOrbit B D q u (2 * l + 1)) =
      Matrix.trace (B ^ (2 * l + 1)) + u ^ (2 * l + 1) * Matrix.trace (D ^ (2 * l + 1)) := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval u) (traceOrbitPolynomial_closed B D q l hq)
  simp only [traceOrbitPolynomial_eval, eval_add, eval_mul, eval_C, eval_pow, eval_X] at h
  simpa only [mul_comm] using h

/-- Under the stated width and primitive-root hypotheses, the odd-length orbit of the two
continuant matrices has the displayed Chebyshev trace multiplied by `1 + u ^ (2 * l + 1)`. -/
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

/-- The two-component recurrence matrix with rows `(x, -s * w)` and `(s, x * w)`. -/
def continuantStep (x s w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![x, -s * w; s, x * w]

/-- When `x ^ 2 + s ^ 2 = 1`, the linear combination with coefficients `x` and `s` of the output
of a continuant step equals the previous first component. -/
theorem continuantStep_invariant (x s w : ℂ) (hxs : x ^ 2 + s ^ 2 = 1)
    (v : QState (Fin 2)) :
    x * (continuantStep x s w *ᵥ v) 0 + s * (continuantStep x s w *ᵥ v) 1 = v 0 := by
  simp only [continuantStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change x * (x * v 0 + (-s * w) * v 1) + s * (s * v 0 + (x * w) * v 1) = v 0
  linear_combination v 0 * hxs

/-- If `x * v 0 + s * v 1 = a`, the next first component is `x * (1 + w) * v 0 - w * a`. -/
theorem continuantStep_eliminate (x s w a : ℂ) (v : QState (Fin 2))
    (hv : x * v 0 + s * v 1 = a) :
    (continuantStep x s w *ᵥ v) 0 = x * (1 + w) * v 0 - w * a := by
  simp only [continuantStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change x * v 0 + (-s * w) * v 1 = _
  linear_combination -w * hv

/-- The vector recurrence starting from `(1, 0)` and applying continuant steps weighted by
`ylcRecW`. -/
noncomputable def recurrenceRun (L : ℕ) (mu x s : ℝ) : ℕ → QState (Fin 2)
  | 0 => ![1, 0]
  | n + 1 => continuantStep (x : ℂ) (s : ℂ) (ylcRecW L mu (n + 1)) *ᵥ
      recurrenceRun L mu x s n

/-- When `x ^ 2 + s ^ 2 = 1`, the first coordinate of `recurrenceRun` equals `ylcRecA` at every
index. -/
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

/-- The diagonal matrix with entries one and negative one used to define orbit reflection. -/
def J : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The transpose reflection `J * Aᵀ * J` of a two-by-two complex matrix. -/
noncomputable def reflect (A : Matrix (Fin 2) (Fin 2) ℂ) := J * Aᵀ * J

/-- The matrix `J` squares to the identity. -/
theorem J_sq : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_two]

/-- Applying orbit reflection twice returns the original matrix. -/
theorem reflect_twice (A : Matrix (Fin 2) (Fin 2) ℂ) : reflect (reflect A) = A := by
  have hJ : Jᵀ = J := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  simp only [reflect, Matrix.transpose_mul, hJ, Matrix.transpose_transpose]
  calc
    _ = (J * J) * A * (J * J) := by noncomm_ring
    _ = A := by rw [J_sq]; simp

/-- Orbit reflection reverses the order of matrix multiplication. -/
theorem reflect_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    reflect (A * B) = reflect B * reflect A := by
  simp only [reflect, Matrix.transpose_mul]
  have hh : (J * Bᵀ * J) * (J * Aᵀ * J) = J * Bᵀ * (J * J) * Aᵀ * J := by
    noncomm_ring
  rw [hh, J_sq]
  simp only [Matrix.mul_one]
  noncomm_ring

/-- Reflecting a list product equals the product of the reflected matrices in reverse order. -/
theorem reflect_prod (xs : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    reflect xs.prod = (xs.reverse.map reflect).prod := by
  induction xs with
  | nil => simpa [reflect] using J_sq
  | cons a xs ih => simp [List.reverse_cons, reflect_mul, ih]

/-- The affine matrix `B + v • reflect B`. -/
noncomputable def M (B : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ) := B + v • reflect B

/-- If `a * b = 1`, reflecting the affine matrix at `a` gives `a` times the affine matrix at
`b`. -/
theorem reflect_point (B : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (hab : a * b = 1) :
    reflect (M B a) = a • M B b := by
  have hd : reflect (M B a) = reflect B + a • reflect (reflect B) := by
    simp [reflect, M, Matrix.transpose_add, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul]
  rw [hd, reflect_twice, M, smul_add, smul_smul, hab, one_smul]
  exact add_comm _ _

/-- A product of scalar multiples of matrices factors into the product of the scalars acting on
the product of the matrices. -/
theorem scalar_prod (n : ℕ) (a : ℕ → ℂ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ) :
    ((List.range n).map fun i => a i • f i).prod =
      ((List.range n).map a).prod • ((List.range n).map f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [ih, smul_mul_smul_comm]

/-- The list of values `f (n - i)` for `i < n` is the reverse of the list of values `f (i + 1)`. -/
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

/-- The product of the first `n` positive powers of `q` is `q ^ (n * (n + 1) / 2)`. -/
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

/-- If `q` has odd-order power one, the displayed reverse product of affine matrices is fixed by
transpose reflection. -/
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

/-- The affine matrix orbit with each successive factor multiplied on the left. -/
def reverseAffineOrbit {R : Type*} [CommRing R] (B D : Matrix (Fin 2) (Fin 2) R)
    (q u : R) : ℕ → Matrix (Fin 2) (Fin 2) R
  | 0 => 1
  | n + 1 => (B + (q ^ n * u) • D) * reverseAffineOrbit B D q u n

/-- The reverse affine orbit is the transpose of the forward affine orbit of the transposed
matrices. -/
theorem reverseAffineOrbit_transpose {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u n = (affineOrbit Bᵀ Dᵀ q u n)ᵀ := by
  induction n with
  | zero => simp [affineOrbit, reverseAffineOrbit]
  | succ n ih =>
    simp [affineOrbit, reverseAffineOrbit, Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.transpose_smul, ih]

/-- For a primitive root of odd order, the reverse affine orbit has trace `trace (B ^ L) + u ^ L
* trace (D ^ L)` with `L = 2 * l + 1`. -/
theorem reverseAffineOrbit_trace_closed (B D : Matrix (Fin 2) (Fin 2) ℂ)
    (q u : ℂ) (l : ℕ) (hq : IsPrimitiveRoot q (2 * l + 1)) :
    Matrix.trace (reverseAffineOrbit B D q u (2 * l + 1)) =
      Matrix.trace (B ^ (2 * l + 1)) + u ^ (2 * l + 1) * Matrix.trace (D ^ (2 * l + 1)) := by
  rw [reverseAffineOrbit_transpose, Matrix.trace_transpose, affineOrbit_trace_closed _ _ q u l hq,
    ← Matrix.transpose_pow, ← Matrix.transpose_pow, Matrix.trace_transpose, Matrix.trace_transpose]

/-- A reverse affine orbit splits into a shifted orbit followed by its initial affine factor. -/
theorem reverseAffineOrbit_shift_tail {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u (n + 1) =
      reverseAffineOrbit B D q (q * u) n * (B + u • D) := by
  induction n with
  | zero => simp [reverseAffineOrbit]
  | succ n ih =>
    rw [reverseAffineOrbit, ih, ← mul_assoc, reverseAffineOrbit]
    rw [show q ^ n * (q * u) = q ^ (n + 1) * u by rw [pow_succ, mul_assoc]]

/-- The reverse affine orbit equals the product of its affine factors listed in reverse index
order. -/
theorem reverseAffineOrbit_eq_list {R : Type*} [CommRing R]
    (B D : Matrix (Fin 2) (Fin 2) R) (q u : R) (n : ℕ) :
    reverseAffineOrbit B D q u n =
      (((List.range n).map fun i => B + (q ^ i * u) • D).reverse).prod := by
  induction n with
  | zero => simp [reverseAffineOrbit]
  | succ n ih =>
    simp [reverseAffineOrbit, List.range_succ, List.reverse_append, ih]

/-- Orbit reflection swaps the parameters `a` and `b` of a constant continuant matrix. -/
theorem continuantConstant_reflect (x a b : ℂ) :
    OrbitReflection.reflect (continuantConstant x a b) = continuantConstant x b a := by
  ext i j
  simp only [OrbitReflection.reflect, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [OrbitReflection.J, continuantConstant]

/-- If `q ^ (2 * l + 1) = 1`, the off-diagonal entries of the displayed length-`2 * l` reverse
continuant orbit are negatives of each other. -/
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

/-- The rational recurrence coefficient `(b * q ^ k + a) / (a * q ^ k + b)`. -/
noncomputable def algebraicRecW (q a b : ℂ) (k : ℕ) : ℂ :=
  (b * q ^ k + a) / (a * q ^ k + b)

/-- The algebraic second-order recurrence with initial values one and `x`, using the
coefficients `algebraicRecW`. -/
noncomputable def algebraicRecA (q x a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => x
  | n + 2 => x * (1 + algebraicRecW q a b (n + 1)) * algebraicRecA q x a b (n + 1) -
      algebraicRecW q a b (n + 1) * algebraicRecA q x a b n

/-- The product of the factors `a * q ^ (i + 1) + b` over the first `n` indices. -/
noncomputable def algebraicDenominator (q a b : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ Finset.range n, (a * q ^ (i + 1) + b)

/-- If `a + b = 2` and the denominator is nonzero, an affine continuant factor acts as the
stated scalar multiple of one algebraic recurrence step. -/
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

/-- Under the stated sum and nonvanishing hypotheses, the reverse continuant orbit applied to
`(x, 1)` gives the denominator-scaled pair of consecutive algebraic recurrence values. -/
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

/-- Under the stated width, primitive-root, and nonvanishing hypotheses, the final odd
recurrence value multiplied by its denominator equals the scaled Chebyshev polynomial. -/
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

/-- The algebraic recurrence is identically one when its argument `x` is one. -/
theorem algebraicRecA_one (q a b : ℂ) (n : ℕ) : algebraicRecA q 1 a b n = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 => rw [algebraicRecA, ih0, ih1]; ring

/-- Under the stated width, primitive-root, and denominator hypotheses, the final odd algebraic
recurrence value is the ratio of the Chebyshev evaluations at `x / gamma` and `1 / gamma`. -/
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

/-- For real `u`, the exponential `exp(-2 * i * arctan u)` equals `(1 - i * u) / (1 + i * u)`. -/
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

/-- The negative exponential of the displayed cotangent phase equals the rational phase ratio
`(1 - i * u) / (1 + i * u)`. -/
theorem neg_exp_I_cot_phase (u : ℝ) :
    -Complex.exp (Complex.I * ((2 * (Real.pi / 2 - Real.arctan u) : ℝ) : ℂ)) =
      (1 - Complex.I * (u : ℂ)) / (1 + Complex.I * (u : ℂ)) := by
  have hz : Complex.I * ((2 * (Real.pi / 2 - Real.arctan u) : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I + -(2 * Complex.I * (Real.arctan u : ℂ)) := by
    push_cast
    ring
  rw [hz, Complex.exp_add, Complex.exp_pi_mul_I]
  simpa using exp_neg_two_I_arctan u

/-- The cosine of an integer multiple of `π / (2 * l + 1)` is nonzero. -/
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

/-- When `cos theta ≠ 0`, the rational phase ratio expressed using `tan theta * mu` equals the
corresponding ratio of cosine and sine expressions. -/
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

/-- The negative exponential of an analytic source phase equals the indicated odd-indexed
`ylcRecW` coefficient. -/
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

/-- The displayed negated cotangent phase has negative exponential `(1 - i * u) / (1 + i * u)`. -/
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

/-- For `i < l`, the negative exponential of the scheduled target phase equals the indicated
even-indexed `ylcRecW` coefficient. -/
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

/-- When `cos theta ≠ 0`, the cosine-sine phase ratio equals the displayed fractional expression
in `exp(2 * i * theta)`. -/
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

/-- When the specified cosine is nonzero, `ylcRecW` equals the displayed rational expression in
the corresponding complex exponential. -/
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

/-- The exponential at angle `2 * n * π / L` is the `n`th power of the exponential at angle `2 *
π / L`. -/
theorem exponential_root_power (L n : ℕ) :
    Complex.exp (2 * Complex.I * (((n : ℝ) * Real.pi / L : ℝ) : ℂ)) =
      (Complex.exp (2 * Complex.I * ((Real.pi / L : ℝ) : ℂ))) ^ n := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end PhaseCoefficients

/-- The complex exponential `exp(2 * i * π / L)` used as the recurrence's root parameter. -/
noncomputable def ylcRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * Complex.I * ((Real.pi / L : ℝ) : ℂ))

/-- For odd positive length `2 * l + 1`, `ylcRoot` is a primitive root of that order. -/
theorem ylcRoot_primitive (l : ℕ) : IsPrimitiveRoot (ylcRoot (2 * l + 1)) (2 * l + 1) := by
  have h := Complex.isPrimitiveRoot_exp (2 * l + 1) (by omega)
  convert! h using 1
  unfold ylcRoot
  congr 1
  push_cast
  ring

/-- The complex number `ylcRoot L` has norm one. -/
theorem ylcRoot_norm (L : ℕ) : ‖ylcRoot L‖ = 1 := by
  simp [ylcRoot, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- For a unit-modulus `q` and positive `mu`, the denominator `(1 + mu) * q ^ k + (1 - mu)` is
nonzero. -/
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

/-- At odd length, the trigonometric recurrence coefficient equals its algebraic form with root
`ylcRoot` and parameters `1 + mu` and `1 - mu`. -/
theorem ylcRecW_algebraic (l : ℕ) (mu : ℝ) (n : ℕ) :
    ylcRecW (2 * l + 1) mu (n + 1) =
      algebraicRecW (ylcRoot (2 * l + 1)) (1 + (mu : ℂ)) (1 - (mu : ℂ)) n := by
  rw [PhaseCoefficients.recW_eq_exp_ratio (2 * l + 1) n mu (by
    convert! PhaseCoefficients.cos_nat_pi_div_odd_ne_zero l n using 1
    push_cast
    rfl)]
  rw [PhaseCoefficients.exponential_root_power]
  rfl

/-- At odd length, the trigonometric recurrence equals the algebraic recurrence with root
`ylcRoot` and parameters `1 + mu` and `1 - mu`. -/
theorem ylcRecA_algebraic (l : ℕ) (mu x : ℝ) (n : ℕ) :
    ylcRecA (2 * l + 1) mu x n =
      algebraicRecA (ylcRoot (2 * l + 1)) (x : ℂ) (1 + (mu : ℂ)) (1 - (mu : ℂ)) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih0 ih1 =>
    rw [ylcRecA, algebraicRecA, ih0, ih1, ylcRecW_algebraic l mu (n + 1)]

/-- Coercing a real Chebyshev evaluation to the complex numbers agrees with evaluating the
complex Chebyshev polynomial. -/
theorem cheb_complex (n : ℕ) (x : ℝ) :
    (cheb n x : ℂ) = (Polynomial.Chebyshev.T ℂ (n : ℤ)).eval (x : ℂ) := by
  unfold cheb
  rw [← Polynomial.Chebyshev.map_T Complex.ofRealHom (n : ℤ)]
  exact (Polynomial.eval_map_apply Complex.ofRealHom (p := Polynomial.Chebyshev.T ℝ (n : ℤ)) x).symm

/-- For positive `mu`, nonzero `gamma`, and `mu ^ 2 + gamma ^ 2 = 1`, the final odd recurrence
value is the displayed ratio of real Chebyshev evaluations. -/
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

/-- For `0 < delta < 1`, the final odd recurrence value at the Yoder–Low–Chuang width equals
`delta` times the corresponding Chebyshev evaluation [YoderLowChuang2014]. -/
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

/-- Establishes the Chebyshev recurrence identity packaged by `ylcBridgeRec_miracle`
[YoderLowChuang2014]. -/
theorem ylcBridgeRec_miracle_proved : ylcBridgeRec_miracle := by
  intro L delta lam hodd _ hd hu _ _
  obtain ⟨l, hl⟩ := hodd
  have hL : L = 2 * l + 1 := by omega
  subst L
  simpa only [Complex.ofReal_mul] using ylcRecA_miracle l delta (Real.sqrt (1 - lam)) hd hu

namespace PhysicalTransport

/-- The real symmetric two-level matrix with rows `(√(1 - lam), √lam)` and `(√lam, -√(1 -
lam))`. -/
noncomputable def mirrorMatrix (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (1 - lam) : ℂ), (Real.sqrt lam : ℂ);
    (Real.sqrt lam : ℂ), -(Real.sqrt (1 - lam) : ℂ)]

/-- For `lam ∈ [0, 1]`, the source reflection factors as a scalar phase times a target
reflection conjugated by `mirrorMatrix lam`. -/
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

/-- For `lam ∈ [0, 1]`, a generalized Grover iterate factors into two mirror-phase factors and
the displayed scalar phase. -/
theorem groverIterate_factor (lam alpha beta : ℝ) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    groverIterate lam alpha beta = (-Complex.exp (-(Complex.I * (alpha : ℂ)))) •
      ((mirrorMatrix lam * targetReflection alpha) * (mirrorMatrix lam * targetReflection beta)) := by
  rw [groverIterate, stateReflection_factor lam alpha hl hu, Matrix.smul_mul, ← Matrix.mul_assoc]
  simp only [neg_smul]

/-- If `w = -exp(i * theta)`, the product of the mirror matrix and target reflection is the
corresponding continuant step. -/
theorem mirror_phase_eq_step (lam theta : ℝ) (w : ℂ)
    (hw : -Complex.exp (Complex.I * (theta : ℂ)) = w) :
    mirrorMatrix lam * targetReflection theta =
      continuantStep (Real.sqrt (1 - lam) : ℂ) (Real.sqrt lam : ℂ) w := by
  rw [← hw]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [mirrorMatrix, targetReflection, continuantStep]

/-- The scalar factor `-exp(-i * alpha)` for the source phase of the indexed public iterate. -/
noncomputable def executionPhase (l : ℕ) (delta : ℝ) (i : ℕ) : ℂ :=
  -Complex.exp (-(Complex.I * (ylcAlpha (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta) : ℂ)))

/-- The product of the scalar execution phases over the first `k` public iterates. -/
noncomputable def executionScalar (l : ℕ) (delta : ℝ) (k : ℕ) : ℂ :=
  ((List.range k).map (executionPhase l delta)).prod

/-- The reverse-ordered product of the first `k` public iterates. -/
noncomputable def executionPrefix (l : ℕ) (delta lam : ℝ) (k : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((List.range k).map (publicIterate l delta lam)).reverse.prod

/-- The scalar factor for a prefix of length `k + 1` is the length-`k` factor multiplied by the
next execution phase. -/
theorem executionScalar_succ (l : ℕ) (delta : ℝ) (k : ℕ) :
    executionScalar l delta (k + 1) = executionScalar l delta k * executionPhase l delta k := by
  simp [executionScalar, List.range_succ]

/-- Every scalar execution-prefix factor has norm one. -/
theorem executionScalar_norm (l : ℕ) (delta : ℝ) (k : ℕ) : ‖executionScalar l delta k‖ = 1 := by
  induction k with
  | zero => simp [executionScalar]
  | succ k ih =>
    rw [executionScalar_succ, norm_mul, ih]
    simp only [executionPhase, norm_neg, norm_exp_neg_I_mul, mul_one]

/-- Extending an execution prefix by one iterate multiplies the prefix matrix on the left by the
next public iterate. -/
theorem executionPrefix_succ (l : ℕ) (delta lam : ℝ) (k : ℕ) :
    executionPrefix l delta lam (k + 1) =
      publicIterate l delta lam k * executionPrefix l delta lam k := by
  simp [executionPrefix, List.range_succ, List.reverse_append]

/-- For `i < l` and `lam ∈ [0, 1]`, a public iterate is its execution phase times the displayed
pair of consecutive continuant steps. -/
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

/-- For a prefix length at most `l` and `lam ∈ [0, 1]`, the executed prefix state equals its
scalar phase times the corresponding odd-indexed recurrence vector. -/
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

/-- Establishes the unit-modulus rearrangement connecting the physical word's failure amplitude
to `ylcRecA` [YoderLowChuang2014]. -/
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

/-- For `0 < delta < 1` and `lam ∈ [0, 1]`, the public word's success probability equals the
Chebyshev response of degree `2 * l + 1` [YoderLowChuang2014]. -/
theorem publicWord_success_response (l : ℕ) (delta lam : ℝ)
    (hd : 0 < delta) (hdu : delta < 1) (hl : 0 ≤ lam) (hu : lam ≤ 1) :
    publicSuccessProb l delta lam = responseProb (2 * l + 1) delta lam := by
  have h := ylc_master_response_of_bridges ylcBridgeRec_rearrangement_proved
    ylcBridgeRec_miracle_proved l delta lam hd hdu hl hu
  simpa only [publicSuccessProb, publicSuccessAmplitude, publicWord_eq, ylcTargetVec] using! h

/-- For `lam0` and `delta` in `(0, 1)`, the iterate count chosen from these parameters gives
success probability at least `1 - delta ^ 2` for every `lam ∈ [lam0, 1]`
[YoderLowChuang2014]. -/
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

/-- The selected projective branch mass of a source vector for the matrix `P`. -/
noncomputable def goodMass (P : Matrix I I ℂ) (s : QState I) : ℝ := ProjectiveBranchMass P true s

/-- For an orthogonal projector and a normalized source, the selected branch mass lies in `[0,
1]`. -/
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

/-- Applying an orthogonal projector twice to a vector gives the same result as applying it
once. -/
theorem projector_good (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : P *ᵥ (P *ᵥ s) = P *ᵥ s := by
  rw [Matrix.mulVec_mulVec, hP.1]

omit [DecidableEq I] in

/-- An orthogonal projector annihilates the residual vector `s - P *ᵥ s`. -/
theorem projector_bad (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : P *ᵥ (s - P *ᵥ s) = 0 := by
  rw [Matrix.mulVec_sub, projector_good P s hP, sub_self]

/-- The self-inner-product of the projected source equals the complex coercion of its selected
branch mass. -/
theorem good_inner_self (P : Matrix I I ℂ) (s : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (P *ᵥ s) (P *ᵥ s) = (goodMass P s : ℂ) := by
  rw [inner_self, ← Complex.ofReal_sum]
  rfl

/-- For an orthogonal projector, the inner product of the source with its projected component
equals the selected branch mass. -/
theorem source_inner_good (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) : Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = (goodMass P s : ℂ) := by
  have hpstar : Pᴴ = P := hP.2
  calc
    Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = Qatlib.Foundations.PureStateMath.Inner (P *ᵥ s) (P *ᵥ s) := by
      rw [inner_mulVec_left_rect, hpstar, projector_good P s hP]
    _ = _ := good_inner_self P s

/-- For an orthogonal projector and normalized source, the source's inner product with its
residual component is one minus the selected branch mass. -/
theorem source_inner_bad (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) :
    Qatlib.Foundations.PureStateMath.Inner s (s - P *ᵥ s) = 1 - (goodMass P s : ℂ) := by
  change star s ⬝ᵥ (s - P *ᵥ s) = _
  rw [dotProduct_sub]
  change Qatlib.Foundations.PureStateMath.Inner s s - Qatlib.Foundations.PureStateMath.Inner s (P *ᵥ s) = _
  rw [(normalized_iff_inner_self s).mp hs, source_inner_good P s hP]

/-- The phase update `1 - (1 - exp(i * beta)) • P` associated with a marked subspace. -/
noncomputable def markedPhase (P : Matrix I I ℂ) (beta : ℝ) : Matrix I I ℂ :=
  1 - (1 - Complex.exp (Complex.I * (beta : ℂ))) • P

/-- The marked phase update is unitary when `P` is an orthogonal projector. -/
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

/-- A source reflection about a state prepared by a unitary `A` equals the reflection about the
seed conjugated by `A`. -/
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

/-- For an orthogonal projector, a marked phase update leaves the residual source component
unchanged and multiplies its marked component by `exp(i * beta)`. -/
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

/-- An orthogonal projector selects the marked coefficient from a linear combination of the
source's residual and marked components. -/
theorem projector_frame (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (F G : ℂ) :
    P *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = G • (P *ᵥ s) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    projector_bad P s hP, projector_good P s hP, smul_zero, zero_add]

/-- The selected branch mass of the displayed source decomposition is `‖G‖ ^ 2` times the
source's marked mass. -/
theorem projector_frame_mass (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (F G : ℂ) :
    ProjectiveBranchMass P true (F • (s - P *ᵥ s) + G • (P *ᵥ s)) = ‖G‖ ^ 2 * goodMass P s := by
  change MeasureProb (P *ᵥ (F • (s - P *ᵥ s) + G • (P *ᵥ s))) Finset.univ = _
  rw [projector_frame P s hP, Qatlib.Foundations.BornMetrics.EventProbability.measureProb_smul]
  rfl

/-- The source decomposition into residual and marked components weighted by response
polynomials evaluated at the marked mass. -/
noncomputable def polynomialFrame (P : Matrix I I ℂ) (s : QState I)
    (p : Polynomial ℂ × Polynomial ℂ) : QState I :=
  p.1.eval (goodMass P s : ℂ) • (s - P *ᵥ s) + p.2.eval (goodMass P s : ℂ) • (P *ᵥ s)

/-- The negative product of a full source reflection and a marked-subspace phase update. -/
noncomputable def markedIterate (P : Matrix I I ℂ) (s : QState I) (alpha beta : ℝ) :
    Matrix I I ℂ := -(fullStateReflection s alpha * markedPhase P beta)

omit [DecidableEq I] in

/-- The state inner product is additive in its second argument. -/
theorem inner_add_right (s v w : QState I) : Qatlib.Foundations.PureStateMath.Inner s (v + w) = Qatlib.Foundations.PureStateMath.Inner s v + Qatlib.Foundations.PureStateMath.Inner s w := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_add]

/-- For an orthogonal projector and normalized source, a marked iterate updates the polynomial
frame by `responseStep`. -/
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

/-- The matrix product of marked iterates specified by a list of phase pairs. -/
noncomputable def markedPhaseWord (P : Matrix I I ℂ) (s : QState I)
    (phases : List (ℝ × ℝ)) : Matrix I I ℂ :=
  (phases.map fun ab => markedIterate P s ab.1 ab.2).prod

/-- For an orthogonal projector and normalized source, a marked phase word produces the
polynomial frame of its response polynomials. -/
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

/-- The marked-subspace phase word using the public fixed-point phase schedule. -/
noncomputable def markedWordMatrix (P : Matrix I I ℂ) (s : QState I) (l : ℕ) (delta : ℝ) :
    Matrix I I ℂ := markedPhaseWord P s (publicPhases l delta)

/-- For an orthogonal projector and normalized source, the marked fixed-point word is unitary. -/
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

/-- For an orthogonal projector and normalized source, the marked word's selected branch mass
equals the two-level public success probability at the source's marked mass. -/
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

/-- For an orthogonal projector, normalized source, and `0 < delta < 1`, the marked word's
selected branch mass is the Chebyshev response at the initial marked mass
[YoderLowChuang2014]. -/
theorem markedWord_success_response (P : Matrix I I ℂ) (s : QState I)
    (hP : IsOrthogonalProjector P) (hs : Normalized s) (l : ℕ) (delta : ℝ)
    (hd : 0 < delta) (hdu : delta < 1) :
    ProjectiveBranchMass P true (markedWordMatrix P s l delta *ᵥ s) =
      responseProb (2 * l + 1) delta (goodMass P s) := by
  rw [markedWord_success_eq_twoLevel P s hP hs]
  have hb := goodMass_bounds P s hP hs
  exact publicWord_success_response l delta (goodMass P s) hd hdu hb.1 hb.2

/-- For an orthogonal projector and normalized source, initial marked mass zero remains zero and
initial marked mass one gives selected branch mass one. -/
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

/-- The public length is `2 * publicIterateCount lam0 delta + 1`. -/
theorem publicLength_as_iterates (lam0 delta : ℝ) :
    2 * publicIterateCount lam0 delta + 1 = publicLength lam0 delta := by
  unfold publicIterateCount publicLength ylcLength
  split_ifs <;> omega

/-- For a normalized source with marked mass at least positive `lam0`, the chosen marked word
succeeds with probability at least `1 - delta ^ 2` when `0 < delta < 1`
[YoderLowChuang2014]. -/
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

/-- For a unitary-prepared normalized seed and an orthogonal marked projector, the chosen word
has the public length and the exact Chebyshev success response. If its initial marked mass
is at least positive `lam0` and `0 < delta < 1`, success is at least `1 - delta ^ 2`
[YoderLowChuang2014]. -/
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

/-- For positive `lam0` and `0 < delta < 1`, a single iterate count works for every finite
register, unitary preparation, normalized seed, and orthogonal marked projector. The
resulting mass has the exact Chebyshev response, the uniform success bound above `lam0`, and
the zero and unit endpoint guarantees [YoderLowChuang2014]. -/
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
