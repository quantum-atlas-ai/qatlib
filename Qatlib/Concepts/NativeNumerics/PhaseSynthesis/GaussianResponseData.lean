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
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.PhaseGeometry.Phase Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

def gzero : GaussianRat := (0,0)
def gone : GaussianRat := (1,0)
def gadd (a b : GaussianRat) : GaussianRat := (a.1+b.1,a.2+b.2)
def gsub (a b : GaussianRat) : GaussianRat := (a.1-b.1,a.2-b.2)
def gmul (a b : GaussianRat) : GaussianRat := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def gconj (a : GaussianRat) : GaussianRat := (a.1,-a.2)
def gaddList : List GaussianRat → List GaussianRat → List GaussianRat
  | [],ys => ys | xs,[] => xs | x::xs,y::ys => gadd x y :: gaddList xs ys
def gsubList : List GaussianRat → List GaussianRat → List GaussianRat
  | [],ys => ys.map (fun y => gsub gzero y) | xs,[] => xs
  | x::xs,y::ys => gsub x y :: gsubList xs ys
def gshift (xs : List GaussianRat) : List GaussianRat := gzero::xs
def gscale (z : GaussianRat) (xs : List GaussianRat) := xs.map (gmul z)
def responseData (base : GaussianRat) : List GaussianRat → (List GaussianRat × List GaussianRat) × ℕ
  | [] => (([base],[]),0)
  | z::tail =>
    let r := responseData base tail
    let P := r.1.1
    let Q := r.1.2
    ((gscale z (gaddList (gshift P) (gsubList Q (gshift (gshift Q)))),
      gscale (gconj z) (gsubList P (gshift Q))),r.2+1)
noncomputable def dataPolynomial (xs : List GaussianRat) : Polynomial ℂ :=
  ∑ i ∈ Finset.range xs.length, C (gaussianRatComplex (xs.getD i gzero))*X^i
structure PhaseData where
  base : GaussianRat
  phases : List GaussianRat

def scoreLoop (p : List ℚ) (coeffs : List GaussianRat) : ℕ → ℚ × ℕ
  | 0 => (0,0)
  | n+1 => let r := scoreLoop p coeffs n
    (r.1+|(coeffs.getD n gzero).1-p.getD n 0|,r.2+1)
def scoreData (p : List ℚ) (d : ℕ) (w : PhaseData) : (ℚ × ℕ) × ℕ :=
  let r := responseData w.base w.phases
  let q := scoreLoop p r.1.1 (d+1)
  ((q.1,r.2),q.2)

@[simp] theorem complex_gzero : gaussianRatComplex gzero = 0 := by simp [gzero,gaussianRatComplex]

@[simp] theorem complex_gone : gaussianRatComplex gone = 1 := by simp [gone,gaussianRatComplex]

@[simp] theorem complex_gadd (a b : GaussianRat) : gaussianRatComplex (gadd a b) = gaussianRatComplex a+gaussianRatComplex b := by
  simp only [gadd,gaussianRatComplex,Rat.cast_add]; ring

@[simp] theorem complex_gsub (a b : GaussianRat) : gaussianRatComplex (gsub a b) = gaussianRatComplex a-gaussianRatComplex b := by
  simp only [gsub,gaussianRatComplex,Rat.cast_sub]; ring

@[simp] theorem complex_gconj (a : GaussianRat) : gaussianRatComplex (gconj a) = star (gaussianRatComplex a) := by
  simp [gconj,gaussianRatComplex]

@[simp] theorem complex_gmul (a b : GaussianRat) : gaussianRatComplex (gmul a b) = gaussianRatComplex a*gaussianRatComplex b := by
  simp only [gmul,gaussianRatComplex,Rat.cast_add,Rat.cast_sub,Rat.cast_mul]
  linear_combination -(a.2:ℂ)*(b.2:ℂ)*Complex.I_sq

theorem dataPolynomial_coeff (xs : List GaussianRat) (i : ℕ) :
    (dataPolynomial xs).coeff i = gaussianRatComplex (xs.getD i gzero) := by
  simp only [dataPolynomial]
  by_cases hi : i < xs.length
  · simp [hi]
  · have he : xs.getD i gzero = gzero := List.getD_eq_default xs gzero (by omega)
    simp [hi]

@[simp] theorem dataPolynomial_nil : dataPolynomial [] = 0 := by simp [dataPolynomial]

theorem dataPolynomial_cons (x : GaussianRat) (xs : List GaussianRat) :
    dataPolynomial (x::xs) = C (gaussianRatComplex x)+X*dataPolynomial xs := by
  ext i
  cases i with
  | zero => simp [dataPolynomial_coeff]
  | succ i => simp [dataPolynomial_coeff,Polynomial.coeff_X_mul]

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

theorem dataPolynomial_scale (z : GaussianRat) (xs : List GaussianRat) :
    dataPolynomial (gscale z xs) = C (gaussianRatComplex z)*dataPolynomial xs := by
  induction xs with
  | nil => simp [gscale]
  | cons x xs ih =>
    simp only [gscale,List.map_cons,dataPolynomial_cons,complex_gmul,Polynomial.C_mul]
    rw [show dataPolynomial (List.map (gmul z) xs) = C (gaussianRatComplex z)*dataPolynomial xs from ih]
    ring

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

theorem dataPolynomial_shift (xs : List GaussianRat) : dataPolynomial (gshift xs) = X*dataPolynomial xs := by
  simp [gshift,dataPolynomial_cons]

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
