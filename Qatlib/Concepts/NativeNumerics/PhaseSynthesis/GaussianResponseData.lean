/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ext
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP

/-!
# Gaussian-rational response coefficients

This module computes quantum signal processing response coefficients using lists of Gaussian
rationals. The operations `gaddList`, `gsubList`, `gshift`, and `gscale` implement polynomial
arithmetic, and `responseData` realizes the response recursion in the polynomial transformation
setting of [GilyenSuLowWiebe2019].

The semantic lemmas identify the computed lists with `responseP` and `responseQ`. The rational
score measures the sum of real coefficient errors through the chosen degree, with exact
response-round and coefficient-visit counts.

## Main statements

* `responseData_semantics`: The computed coefficient lists represent the response polynomial
  pair.
* `scoreLoop_semantics`: The rational score equals the sum of real coefficient discrepancies.
* `gaussian_response_native_coefficients`: Combined response semantics, score identity, and work
  counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.PhaseGeometry.Phase Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The Gaussian-rational representation `(0,0)` of complex zero. -/
def gzero : GaussianRat := (0,0)
/-- The Gaussian-rational representation `(1,0)` of complex one. -/
def gone : GaussianRat := (1,0)
/-- Addition of Gaussian rationals by componentwise addition of their real and imaginary
coordinates. -/
def gadd (a b : GaussianRat) : GaussianRat := (a.1+b.1,a.2+b.2)
/-- Subtraction of Gaussian rationals by componentwise subtraction of their real and imaginary
coordinates. -/
def gsub (a b : GaussianRat) : GaussianRat := (a.1-b.1,a.2-b.2)
/-- Multiplication of Gaussian rationals using the usual complex multiplication formula. -/
def gmul (a b : GaussianRat) : GaussianRat := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
/-- Complex conjugation of a Gaussian rational, negating its imaginary coordinate. -/
def gconj (a : GaussianRat) : GaussianRat := (a.1,-a.2)
/-- Adds Gaussian-rational coefficient lists entrywise, treating missing entries as zero. -/
def gaddList : List GaussianRat → List GaussianRat → List GaussianRat
  | [],ys => ys | xs,[] => xs | x::xs,y::ys => gadd x y :: gaddList xs ys
/-- Subtracts Gaussian-rational coefficient lists entrywise, treating missing entries as zero. -/
def gsubList : List GaussianRat → List GaussianRat → List GaussianRat
  | [],ys => ys.map (fun y => gsub gzero y) | xs,[] => xs
  | x::xs,y::ys => gsub x y :: gsubList xs ys
/-- Prepends a zero coefficient, representing multiplication by `X`. -/
def gshift (xs : List GaussianRat) : List GaussianRat := gzero::xs
/-- Multiplies every coefficient in a Gaussian-rational list by `z`. -/
def gscale (z : GaussianRat) (xs : List GaussianRat) := xs.map (gmul z)
/-- Computes the two Gaussian-rational response coefficient lists recursively and records one
response round per phase. -/
def responseData (base : GaussianRat) : List GaussianRat → (List GaussianRat × List GaussianRat) × ℕ
  | [] => (([base],[]),0)
  | z::tail =>
    let r := responseData base tail
    let P := r.1.1
    let Q := r.1.2
    ((gscale z (gaddList (gshift P) (gsubList Q (gshift (gshift Q)))),
      gscale (gconj z) (gsubList P (gshift Q))),r.2+1)
/-- The complex polynomial represented by a Gaussian-rational coefficient list in increasing
degree order. -/
noncomputable def dataPolynomial (xs : List GaussianRat) : Polynomial ℂ :=
  ∑ i ∈ Finset.range xs.length, C (gaussianRatComplex (xs.getD i gzero))*X^i
/-- A Gaussian-rational base phase and a list of Gaussian-rational response phases. -/
structure PhaseData where
  base : GaussianRat
  phases : List GaussianRat

/-- Sums the absolute discrepancies between the first `n` real response coefficients and
rational target coefficients, returning the score and coefficient-visit count. -/
def scoreLoop (p : List ℚ) (coeffs : List GaussianRat) : ℕ → ℚ × ℕ
  | 0 => (0,0)
  | n+1 => let r := scoreLoop p coeffs n
    (r.1+|(coeffs.getD n gzero).1-p.getD n 0|,r.2+1)
/-- Computes the response and its rational real-coefficient discrepancy through degree `d`,
together with response-round and coefficient-visit counts. -/
def scoreData (p : List ℚ) (d : ℕ) (w : PhaseData) : (ℚ × ℕ) × ℕ :=
  let r := responseData w.base w.phases
  let q := scoreLoop p r.1.1 (d+1)
  ((q.1,r.2),q.2)

/-- The complex interpretation of `gzero` is zero. -/
@[simp] theorem complex_gzero : gaussianRatComplex gzero = 0 := by simp [gzero,gaussianRatComplex]

/-- The complex interpretation of `gone` is one. -/
@[simp] theorem complex_gone : gaussianRatComplex gone = 1 := by simp [gone,gaussianRatComplex]

/-- The complex interpretation of Gaussian-rational addition is complex addition. -/
@[simp] theorem complex_gadd (a b : GaussianRat) : gaussianRatComplex (gadd a b) = gaussianRatComplex a+gaussianRatComplex b := by
  simp only [gadd,gaussianRatComplex,Rat.cast_add]; ring

/-- The complex interpretation of Gaussian-rational subtraction is complex subtraction. -/
@[simp] theorem complex_gsub (a b : GaussianRat) : gaussianRatComplex (gsub a b) = gaussianRatComplex a-gaussianRatComplex b := by
  simp only [gsub,gaussianRatComplex,Rat.cast_sub]; ring

/-- The complex interpretation of Gaussian-rational conjugation is complex conjugation. -/
@[simp] theorem complex_gconj (a : GaussianRat) : gaussianRatComplex (gconj a) = star (gaussianRatComplex a) := by
  simp [gconj,gaussianRatComplex]

/-- The complex interpretation of Gaussian-rational multiplication is complex multiplication. -/
@[simp] theorem complex_gmul (a b : GaussianRat) : gaussianRatComplex (gmul a b) = gaussianRatComplex a*gaussianRatComplex b := by
  simp only [gmul,gaussianRatComplex,Rat.cast_add,Rat.cast_sub,Rat.cast_mul]
  linear_combination -(a.2:ℂ)*(b.2:ℂ)*Complex.I_sq

/-- The coefficient at `i` of a list's polynomial is the complex interpretation of its entry at
`i`, with zero as the default. -/
theorem dataPolynomial_coeff (xs : List GaussianRat) (i : ℕ) :
    (dataPolynomial xs).coeff i = gaussianRatComplex (xs.getD i gzero) := by
  simp only [dataPolynomial]
  by_cases hi : i < xs.length
  · simp [hi]
  · have he : xs.getD i gzero = gzero := List.getD_eq_default xs gzero (by omega)
    simp [hi]

/-- The polynomial represented by the empty coefficient list is zero. -/
@[simp] theorem dataPolynomial_nil : dataPolynomial [] = 0 := by simp [dataPolynomial]

/-- Prepending a coefficient represents its constant polynomial plus `X` times the polynomial of
the remaining list. -/
theorem dataPolynomial_cons (x : GaussianRat) (xs : List GaussianRat) :
    dataPolynomial (x::xs) = C (gaussianRatComplex x)+X*dataPolynomial xs := by
  ext i
  cases i with
  | zero => simp [dataPolynomial_coeff]
  | succ i => simp [dataPolynomial_coeff,Polynomial.coeff_X_mul]

/-- Adding Gaussian-rational coefficient lists represents addition of their complex polynomials. -/
theorem dataPolynomial_add (xs ys : List GaussianRat) :
    dataPolynomial (gaddList xs ys) = dataPolynomial xs+dataPolynomial ys := by
  induction xs generalizing ys with
  | nil => simp [gaddList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [gaddList]
    | cons y ys =>
      rw [gaddList,dataPolynomial_cons,dataPolynomial_cons,dataPolynomial_cons,ih,complex_gadd,Polynomial.C_add]
      ring

/-- Scaling a Gaussian-rational coefficient list represents multiplication of its polynomial by
the corresponding complex constant polynomial. -/
theorem dataPolynomial_scale (z : GaussianRat) (xs : List GaussianRat) :
    dataPolynomial (gscale z xs) = C (gaussianRatComplex z)*dataPolynomial xs := by
  induction xs with
  | nil => simp [gscale]
  | cons x xs ih =>
    simp only [gscale,List.map_cons,dataPolynomial_cons,complex_gmul,Polynomial.C_mul]
    rw [show dataPolynomial (List.map (gmul z) xs) = C (gaussianRatComplex z)*dataPolynomial xs from ih]
    ring

/-- Subtracting Gaussian-rational coefficient lists represents subtraction of their complex
polynomials. -/
theorem dataPolynomial_sub (xs ys : List GaussianRat) :
    dataPolynomial (gsubList xs ys) = dataPolynomial xs-dataPolynomial ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [gsubList]
    | cons y ys ih =>
      simp only [gsubList,List.map_cons,dataPolynomial_cons,complex_gsub,complex_gzero,zero_sub,
        Polynomial.C_neg]
      rw [show dataPolynomial (ys.map (fun y => gsub gzero y)) = -dataPolynomial ys by simpa [gsubList] using ih]
      rw [dataPolynomial_nil]
      ring
  | cons x xs ih =>
    cases ys with
    | nil => simp [gsubList]
    | cons y ys =>
      rw [gsubList,dataPolynomial_cons,dataPolynomial_cons,dataPolynomial_cons,ih,complex_gsub,Polynomial.C_sub]
      ring

/-- Shifting a coefficient list by prepending zero represents multiplication of its polynomial
by `X`. -/
theorem dataPolynomial_shift (xs : List GaussianRat) : dataPolynomial (gshift xs) = X*dataPolynomial xs := by
  simp [gshift,dataPolynomial_cons]

/-- The two lists returned by `responseData` represent `responseP` and `responseQ`, and the
response-round count equals the number of phases. -/
theorem responseData_semantics (base : GaussianRat) (zs : List GaussianRat) :
    dataPolynomial (responseData base zs).1.1 = responseP (gaussianRatComplex base) (zs.map gaussianRatComplex) ∧
    dataPolynomial (responseData base zs).1.2 = responseQ (gaussianRatComplex base) (zs.map gaussianRatComplex) ∧
    (responseData base zs).2 = zs.length := by
  induction zs with
  | nil => simp [responseData,dataPolynomial_cons]
  | cons z zs ih =>
    simp only [responseData,List.map_cons,List.length_cons,dataPolynomial_scale,dataPolynomial_add,
      dataPolynomial_sub,dataPolynomial_shift,complex_gconj,responseP_cons,responseQ_cons,ih.1,ih.2.1,ih.2.2]
    constructor
    · congr 1; ring
    · exact ⟨True.intro,True.intro⟩

/-- The score loop visits exactly `n` coefficients, and its rational score cast to ℝ equals the
sum of the first `n` absolute real coefficient discrepancies. -/
theorem scoreLoop_semantics (p : List ℚ) (xs : List GaussianRat) (n : ℕ) :
    (scoreLoop p xs n).2 = n ∧
    ((scoreLoop p xs n).1:ℝ) = ∑ i ∈ Finset.range n,
      |(gaussianRatComplex (xs.getD i gzero)).re-((p.getD i 0:ℚ):ℝ)| := by
  induction n with
  | zero => simp [scoreLoop]
  | succ n ih =>
    simp only [scoreLoop,ih.1,Rat.cast_add,Rat.cast_abs,Rat.cast_sub,
      Finset.sum_range_succ,ih.2]
    constructor
    · exact True.intro
    · simp [gaussianRatComplex]

/-- Native Gaussian-rational response computation represents the exact response pair, uses one
round per phase, and computes the stated real-coefficient error sum with exactly `d+1`
coefficient visits. -/
theorem gaussian_response_native_coefficients : ∀ (base : GaussianRat) (zs : List GaussianRat),
  dataPolynomial (responseData base zs).1.1 = responseP (gaussianRatComplex base) (zs.map gaussianRatComplex) ∧
  dataPolynomial (responseData base zs).1.2 = responseQ (gaussianRatComplex base) (zs.map gaussianRatComplex) ∧
  (responseData base zs).2 = zs.length ∧
  (∀ (p : List ℚ) (d : ℕ), let data : PhaseData := ⟨base,zs⟩
    (scoreData p d data).1.2 = zs.length ∧ (scoreData p d data).2 = d+1 ∧
    (((scoreData p d data).1.1:ℚ):ℝ) =
      ∑ i ∈ Finset.range (d+1), |((responseP (gaussianRatComplex base)
        (zs.map gaussianRatComplex)).coeff i).re-((p.getD i 0:ℚ):ℝ)|) := by
  intro base zs
  have hr := responseData_semantics base zs
  refine ⟨hr.1,hr.2.1,hr.2.2,?_⟩
  intro p d
  dsimp only [scoreData]
  have hs := scoreLoop_semantics p (responseData base zs).1.1 (d+1)
  refine ⟨hr.2.2,hs.1,?_⟩
  rw [hs.2]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hr.1,dataPolynomial_coeff]

end Qatlib.Concepts.NativeNumerics.PhaseSynthesis
