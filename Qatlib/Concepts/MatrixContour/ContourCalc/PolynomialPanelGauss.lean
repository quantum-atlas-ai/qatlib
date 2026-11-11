/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.LocalResolventApproximation
import Qatlib.Foundations.OpCalculus.ContourCalc.BanachPolynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Algebra.Polynomial

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc


/-!
# Polynomial-times-resolvent quadrature on a straight panel

The finite local approximation is expanded into an actual vector coefficient
array.  One positive Gauss rule integrates that array exactly and controls the
actual resolvent integrand by the separation-derived geometric remainder.
The panel uses real parameter measure `dt`; a contour `dz` factor is separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc

open Qatlib Polynomial MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

/-- Complex polynomial coefficients multiplied by a fixed matrix are literal
real-vector polynomial coefficients on a real parameter. -/
theorem finiteVectorPolynomial_complex_coefficients
    {I : Type} [Fintype I] [DecidableEq I]
    (P : Polynomial ℂ) (K : ℕ) (hP : P.natDegree ≤ K)
    (B : Matrix I I ℂ) (t : ℝ) :
    finiteVectorPolynomial K (fun i => P.coeff (i : ℕ) • B) t =
      P.eval (t : ℂ) • B := by
  unfold finiteVectorPolynomial
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_smul,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, RCLike.ofReal_pow, mul_comm]
  rfl

/-- A straight panel is continuous, including zero direction. -/
theorem contourPanel_continuous (z₀ u : ℂ) (a h : ℝ) :
    Continuous (contourPanel z₀ u a h) := by
  unfold contourPanel
  exact continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).mul continuous_const)

/-- The local expansion is centered at the actual midpoint of the panel. -/
@[simp] theorem contourPanel_midpoint (z₀ u : ℂ) (a h : ℝ) :
    contourPanel z₀ u a h (a + h / 2) = z₀ := by
  simp [contourPanel]

/-- The real parameter width and direction bound place the whole panel in the
local resolvent approximation ball. -/
theorem contourPanel_norm_sub_le
    (z₀ u : ℂ) (a h r : ℝ) (hh : 0 < h) (hsmall : h ≤ r / 4)
    (hu : ‖u‖ ≤ 1) (t : ℝ) (ht : t ∈ Icc a (a + h)) :
    ‖contourPanel z₀ u a h t - z₀‖ ≤ r / 8 := by
  have hcenter : |t - (a + h / 2)| ≤ h / 2 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  simp only [contourPanel, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |t - (a + h / 2)| * ‖u‖ ≤ (h / 2) * 1 :=
      mul_le_mul hcenter hu (norm_nonneg _) (by positivity)
    _ ≤ r / 8 := by linarith

/-- Literal scalar-times-resolvent coefficients, exposed so a finite scalar
precision envelope can be proved independently of the unknown matrix. -/
def polynomialLocalCoefficients
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ u : ℂ) (a h : ℝ) (d m : ℕ) :
    Fin (d + m + 1) → Matrix I I ℂ :=
  let tc := a + h / 2
  let affine : Polynomial ℂ := C (z₀ - (tc : ℂ) * u) + C u * X
  let q : Polynomial ℂ := p.comp affine
  let v : Polynomial ℂ := C (-u) * (X - C (tc : ℂ))
  fun j => ∑ n ∈ Finset.range (m + 1), (q * v ^ n).coeff (j : ℕ) •
    (matrixResolvent A z₀) ^ (n + 1)

/-- The literal local resolvent integrand admits the actual coefficient array
of a vector polynomial of degree at most `d + m`. -/
theorem polynomial_local_resolvent_coefficients_explicit
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ u : ℂ) (a h : ℝ)
    (d m : ℕ) (hp : p.natDegree ≤ d) :
    ∀ t : ℝ,
      finiteVectorPolynomial (d + m)
        (polynomialLocalCoefficients A p z₀ u a h d m) t =
        p.eval (contourPanel z₀ u a h t) •
          localResolventPolynomial A z₀ m (contourPanel z₀ u a h t) := by
  let tc := a + h / 2
  let affine : Polynomial ℂ := C (z₀ - (tc : ℂ) * u) + C u * X
  let q : Polynomial ℂ := p.comp affine
  let v : Polynomial ℂ := C (-u) * (X - C (tc : ℂ))
  let c : Fin (d + m + 1) → Matrix I I ℂ := fun j =>
    ∑ n ∈ Finset.range (m + 1), (q * v ^ n).coeff (j : ℕ) •
      (matrixResolvent A z₀) ^ (n + 1)
  have haffine : affine.natDegree ≤ 1 := by
    change (C (z₀ - (tc : ℂ) * u) + C u * X).natDegree ≤ 1
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp only [Polynomial.natDegree_C]; omega)
        ((Polynomial.natDegree_C_mul_le _ _).trans
          (by simpa only [Polynomial.natDegree_X] using (le_refl (1 : ℕ)))))
  have hq : q.natDegree ≤ d := by
    calc
      q.natDegree ≤ p.natDegree * affine.natDegree := Polynomial.natDegree_comp_le
      _ ≤ d * 1 := Nat.mul_le_mul hp haffine
      _ = d := Nat.mul_one d
  have hv : v.natDegree ≤ 1 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans (by simp))
  have hdegree (n : ℕ) (hn : n ∈ Finset.range (m + 1)) :
      (q * v ^ n).natDegree ≤ d + m := by
    have hvn : (v ^ n).natDegree ≤ n := by
      calc
        (v ^ n).natDegree ≤ n * v.natDegree := Polynomial.natDegree_pow_le
        _ ≤ n * 1 := Nat.mul_le_mul_left n hv
        _ = n := Nat.mul_one n
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add hq (hvn.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn))))
  have haffine_eval (t : ℝ) : affine.eval (t : ℂ) = contourPanel z₀ u a h t := by
    simp only [affine, tc, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, contourPanel, Complex.ofReal_sub]
    ring
  have hq_eval (t : ℝ) : q.eval (t : ℂ) = p.eval (contourPanel z₀ u a h t) := by
    dsimp only [q]
    rw [Polynomial.eval_comp, haffine_eval]
  have hv_eval (t : ℝ) : v.eval (t : ℂ) = -(contourPanel z₀ u a h t - z₀) := by
    simp only [v, tc, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, contourPanel, Complex.ofReal_sub]
    ring
  change ∀ t : ℝ, finiteVectorPolynomial (d + m) c t =
    p.eval (contourPanel z₀ u a h t) •
      localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)
  intro t
  calc
    finiteVectorPolynomial (d + m) c t =
        ∑ n ∈ Finset.range (m + 1),
          finiteVectorPolynomial (d + m)
            (fun j => (q * v ^ n).coeff (j : ℕ) •
              (matrixResolvent A z₀) ^ (n + 1)) t := by
      simp only [finiteVectorPolynomial, c, Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range (m + 1),
        (q * v ^ n).eval (t : ℂ) • (matrixResolvent A z₀) ^ (n + 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact finiteVectorPolynomial_complex_coefficients (q * v ^ n) (d + m)
        (hdegree n hn) _ t
    _ = p.eval (contourPanel z₀ u a h t) •
        localResolventPolynomial A z₀ m (contourPanel z₀ u a h t) := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, hq_eval, hv_eval,
        localResolventPolynomial, Finset.smul_sum, smul_smul]

/-- The original existential coefficient interface, retained verbatim. -/
theorem polynomial_local_resolvent_coefficients
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℂ) (z₀ u : ℂ) (a h : ℝ)
    (d m : ℕ) (hp : p.natDegree ≤ d) :
    ∃ c : Fin (d + m + 1) → Matrix I I ℂ, ∀ t : ℝ,
      finiteVectorPolynomial (d + m) c t =
        p.eval (contourPanel z₀ u a h t) •
          localResolventPolynomial A z₀ m (contourPanel z₀ u a h t) := by
  exact ⟨polynomialLocalCoefficients A p z₀ u a h d m,
    polynomial_local_resolvent_coefficients_explicit A p z₀ u a h d m hp⟩

/-- Typeclass instance for polynomial Panel ENormed Add Monoid in the polynomial panel gauss model. -/
noncomputable local instance polynomialPanelENormedAddMonoid {I : Type} [Fintype I] [DecidableEq I] :
    ENormedAddMonoid (Matrix I I ℂ) := NormedAddGroup.toENormedAddMonoid

/-- The identity or estimate `polynomial_panel_approximation_data` holds with the displayed separation, geometry and norm hypotheses. -/
theorem polynomial_panel_approximation_data
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (p : Polynomial ℂ) (z₀ u : ℂ) (a h r M : ℝ) (d m : ℕ)
    (hr : 0 < r) (hh : 0 < h) (hsmall : h ≤ r/4) (hu : ‖u‖ ≤ 1)
    (hp : p.natDegree ≤ d) (hM : 0 ≤ M)
    (hsep : ∀ t ∈ Icc a (a+h), ∀ w ∈ matrixNumericalRange A,
      r ≤ ‖contourPanel z₀ u a h t-w‖)
    (hpbound : ∀ t ∈ Icc a (a+h), ‖p.eval (contourPanel z₀ u a h t)‖ ≤ M) :
    ∃ c : Fin (d+m+1) → Matrix I I ℂ,
      (∀ t : ℝ, finiteVectorPolynomial (d+m) c t =
        p.eval (contourPanel z₀ u a h t) • localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)) ∧
      IntervalIntegrable (fun t => p.eval (contourPanel z₀ u a h t) •
        matrixResolvent A (contourPanel z₀ u a h t)) volume a (a+h) ∧
      0 ≤ M*r⁻¹*(1/8 : ℝ)^(m+1) ∧
      (∀ t ∈ Icc a (a+h), ‖p.eval (contourPanel z₀ u a h t) •
        matrixResolvent A (contourPanel z₀ u a h t)-finiteVectorPolynomial (d+m) c t‖ ≤
          M*r⁻¹*(1/8 : ℝ)^(m+1)) := by
  have htc : a + h / 2 ∈ Icc a (a + h) := by
    constructor <;> linarith
  have hsep₀ : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z₀ - w‖ := by
    intro w hw
    simpa only [contourPanel_midpoint] using hsep (a + h / 2) htc w hw
  obtain ⟨c, hcoeff⟩ := polynomial_local_resolvent_coefficients A p z₀ u a h d m hp
  let f : ℝ → Matrix I I ℂ := fun t =>
    p.eval (contourPanel z₀ u a h t) • matrixResolvent A (contourPanel z₀ u a h t)
  let E : ℝ := M * r⁻¹ * (1 / 8 : ℝ) ^ (m + 1)
  have hpanel := contourPanel_continuous z₀ u a h
  have hRcont : ContinuousOn (fun t => matrixResolvent A (contourPanel z₀ u a h t))
      (Icc a (a + h)) :=
    (matrixResolvent_continuousOn_of_separation A r hr).comp' hpanel.continuousOn
      (fun t ht => hsep t ht)
  have hpcont : Continuous (fun t => p.eval (contourPanel z₀ u a h t)) :=
    p.continuous.comp hpanel
  have hfcont : ContinuousOn f (Icc a (a + h)) := hpcont.continuousOn.smul hRcont
  have hf := _root_.ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by linarith : a ≤ a + h) hfcont
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbound (t : ℝ) (ht : t ∈ Icc a (a + h)) :
      ‖f t - finiteVectorPolynomial (d + m) c t‖ ≤ E := by
    have hlocal := (local_resolvent_approximation A z₀ (contourPanel z₀ u a h t) r m
      hr hsep₀ (hsep t ht) (contourPanel_norm_sub_le z₀ u a h r hh hsmall hu t ht)).2
    rw [hcoeff]
    change ‖p.eval (contourPanel z₀ u a h t) • matrixResolvent A (contourPanel z₀ u a h t) -
      p.eval (contourPanel z₀ u a h t) •
        localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)‖ ≤ E
    rw [← smul_sub, norm_smul]
    calc
      ‖p.eval (contourPanel z₀ u a h t)‖ *
          ‖matrixResolvent A (contourPanel z₀ u a h t) -
            localResolventPolynomial A z₀ m (contourPanel z₀ u a h t)‖ ≤
          M * (r⁻¹ * (1 / 8 : ℝ) ^ (m + 1)) :=
        mul_le_mul (hpbound t ht) hlocal (norm_nonneg _) hM
      _ = E := by dsimp [E]; ring
  exact ⟨c, hcoeff, hf, hE, hbound⟩

end Qatlib.Concepts.MatrixContour.ContourCalc
