/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignKernel
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreRefined
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Effective sign and rectangle approximation interfaces

This module develops sign and rectangle approximation contracts, error-function smoothing, and
finite Chebyshev truncation estimates. `nearOptimalSign_of_weightedDecay` and its
projection-based variant produce sign approximations from explicitly assumed finite
representations and coefficient-decay bounds; two translated sign responses produce rectangle
bands. Background and related constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `NearOptimalSignApproximation`: bounded odd sign approximation with a degree budget.
* `twoTranslateRectangleBands_allThresholds`: converts sign error bounds to rectangle bands.
* `nearOptimalSign_of_weightedDecay_projections`: a conditional construction from Chebyshev
  projections.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section


namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

/-- Requires a bounded odd sign approximation on [−2, 2] with error at most `ε` outside |x| <
`δ` and degree at most C(1 + δ⁻¹ log(ε⁻¹)). It also requires `C`, `δ`, and `ε` to be
positive. -/
def NearOptimalSignApproximation (C δ ε : ℝ) (S : Polynomial ℝ) : Prop :=
  0 < C ∧ 0 < δ ∧ 0 < ε ∧
  (∀ x : ℝ, |x| ≤ 2 → |S.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 2 → δ ≤ |x| → |S.eval x - Real.sign x| ≤ ε) ∧
  (∀ x : ℝ, S.eval (-x) = -S.eval x) ∧
  (S.natDegree : ℝ) ≤ C * (1 + (1 / δ) * Real.log (1 / ε))

/-- A near-optimal sign approximation takes values in [1 − ε, 1] at positive points of [−2, 2]
outside the gap. -/
theorem nearOptimalSign_pos {C δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ ε S) {y : ℝ} (hy2 : |y| ≤ 2)
    (hyδ : δ ≤ |y|) (hypos : 0 < y) :
    1 - ε ≤ S.eval y ∧ S.eval y ≤ 1 := by
  have hb : |S.eval y| ≤ 1 := hS.2.2.2.1 y hy2
  have he : |S.eval y - Real.sign y| ≤ ε := hS.2.2.2.2.1 y hy2 hyδ
  rw [Real.sign_of_pos hypos] at he
  rcases abs_le.mp he with ⟨hlo, hhi⟩
  rcases abs_le.mp hb with ⟨hbl, hbh⟩
  constructor <;> linarith

/-- A near-optimal sign approximation takes values in [−1, −1 + ε] at negative points of [−2, 2]
outside the gap. -/
theorem nearOptimalSign_neg {C δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ ε S) {y : ℝ} (hy2 : |y| ≤ 2)
    (hyδ : δ ≤ |y|) (hyneg : y < 0) :
    -1 ≤ S.eval y ∧ S.eval y ≤ -1 + ε := by
  have hb : |S.eval y| ≤ 1 := hS.2.2.2.1 y hy2
  have he : |S.eval y - Real.sign y| ≤ ε := hS.2.2.2.2.1 y hy2 hyδ
  rw [Real.sign_of_neg hyneg] at he
  rcases abs_le.mp he with ⟨hlo, hhi⟩
  rcases abs_le.mp hb with ⟨hbl, hbh⟩
  constructor <;> linarith

/-- Requires a polynomial bounded by one on [−1, 1], with values in [0, ε'] outside the
threshold plus gap and in [1 − ε', 1] inside the threshold minus gap. -/
def PrintedRectangleBand (P : Polynomial ℝ) (ε' δ' t : ℝ) : Prop :=
  (∀ x : ℝ, |x| ≤ 1 → |P.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(t + δ') ∨ t + δ' ≤ x) →
    0 ≤ P.eval x ∧ P.eval x ≤ ε') ∧
  (∀ x : ℝ, |x| ≤ 1 → -(t - δ') ≤ x ∧ x ≤ t - δ' →
    1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1)

/-- Uses the zero polynomial for a negative threshold and `rectanglePolynomial S ε₀ t`
otherwise. -/
def sourceRectanglePolynomial (S : Polynomial ℝ) (ε₀ t : ℝ) : Polynomial ℝ :=
  if t < 0 then 0 else rectanglePolynomial S ε₀ t

/-- At a nonnegative threshold, the source rectangle evaluates to ((1 − ε₀)/2)(S(x + t) + S(t −
x)) + ε₀. -/
theorem sourceRectanglePolynomial_eval {S : Polynomial ℝ} {ε₀ t x : ℝ} (ht : 0 ≤ t) :
    (sourceRectanglePolynomial S ε₀ t).eval x =
      ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) + ε₀ := by
  rw [sourceRectanglePolynomial, if_neg (by linarith)]
  exact rectanglePolynomial_eval S ε₀ t x

/-- For a nonnegative threshold, the source rectangle response is even. -/
theorem sourceRectanglePolynomial_even {S : Polynomial ℝ} {ε₀ t x : ℝ} (ht : 0 ≤ t) :
    (sourceRectanglePolynomial S ε₀ t).eval (-x) = (sourceRectanglePolynomial S ε₀ t).eval x := by
  rw [sourceRectanglePolynomial, if_neg (by linarith)]
  exact rectanglePolynomial_even S ε₀ t x

/-- Two translated sign approximations satisfy `PrintedRectangleBand` for every threshold in [0,
1] when the scale and offset meet the stated lower and upper error budgets. -/
theorem twoTranslateRectangleBands_allThresholds {S : Polynomial ℝ} {δ' ε' σ t c e₀ : ℝ}
    (hδ : 0 < δ') (hc : 0 ≤ c) (he0 : 0 ≤ e₀) (hcoef : (1 - e₀) / 2 = c)
    (hlow : 2 * c * σ ≤ e₀) (hupp : e₀ + 2 * c * σ ≤ ε')
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hS : SignApproximation S δ' σ) :
    PrintedRectangleBand (rectanglePolynomial S e₀ t) ε' δ' t := by
  have hsign : ∀ y : ℝ, |y| ≤ 2 → δ' ≤ |y| → 0 < y →
      1 - σ ≤ S.eval y ∧ S.eval y ≤ 1 := by
    intro y hy2 hyδ hypos
    have hb : |S.eval y| ≤ 1 := hS.1 y hy2
    have he : |S.eval y - Real.sign y| ≤ σ := hS.2.1 y hy2 hyδ
    rw [Real.sign_of_pos hypos] at he
    rcases abs_le.mp he with ⟨hlo, hhi⟩
    rcases abs_le.mp hb with ⟨hbl, hbh⟩
    constructor <;> linarith
  have hsignneg : ∀ y : ℝ, |y| ≤ 2 → δ' ≤ |y| → y < 0 →
      -1 ≤ S.eval y ∧ S.eval y ≤ -1 + σ := by
    intro y hy2 hyδ hyneg
    have hb : |S.eval y| ≤ 1 := hS.1 y hy2
    have he : |S.eval y - Real.sign y| ≤ σ := hS.2.1 y hy2 hyδ
    rw [Real.sign_of_neg hyneg] at he
    rcases abs_le.mp he with ⟨hlo, hhi⟩
    rcases abs_le.mp hb with ⟨hbl, hbh⟩
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' := abs_le.mp hx
    rw [rectanglePolynomial_eval, hcoef]
    have h1 : |S.eval (x + t)| ≤ 1 := hS.1 (x + t) (by
      rw [abs_le]; constructor <;> linarith)
    have h2 : |S.eval (t - x)| ≤ 1 := hS.1 (t - x) (by
      rw [abs_le]; constructor <;> linarith)
    have hsum : |S.eval (x + t) + S.eval (t - x)| ≤ 2 := by
      calc |S.eval (x + t) + S.eval (t - x)| ≤ |S.eval (x + t)| + |S.eval (t - x)| := abs_add_le _ _
        _ ≤ 2 := by linarith [add_le_add h1 h2]
    calc |c * (S.eval (x + t) + S.eval (t - x)) + e₀|
        ≤ |c * (S.eval (x + t) + S.eval (t - x))| + |e₀| := abs_add_le _ _
      _ = |c| * |S.eval (x + t) + S.eval (t - x)| + |e₀| := by rw [abs_mul]
      _ = c * |S.eval (x + t) + S.eval (t - x)| + e₀ := by
          rw [abs_of_nonneg hc, abs_of_nonneg he0]
      _ ≤ c * 2 + e₀ := by
        have h := mul_le_mul_of_nonneg_left hsum hc
        linarith
      _ = 1 := by linarith
  · intro x hx hband
    have hx' := abs_le.mp hx
    rw [rectanglePolynomial_eval, hcoef]
    have hxt : |x + t| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have htx : |t - x| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    rcases hband with hleft | hright
    · have hxtneg : x + t < 0 := by linarith
      have hxtδ : δ' ≤ |x + t| := by
        rw [abs_of_nonpos (le_of_lt hxtneg)]
        linarith
      have htxpos : 0 < t - x := by linarith
      have htxδ : δ' ≤ |t - x| := by
        rw [abs_of_nonneg (le_of_lt htxpos)]
        linarith
      have h1 := hsignneg (x + t) hxt hxtδ hxtneg
      have h2 := hsign (t - x) htx htxδ htxpos
      have hsumlo : -2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 * σ := by linarith
      have hlo : -(2 * c * σ) ≤ c * (S.eval (x + t) + S.eval (t - x)) := by
        have h := mul_le_mul_of_nonneg_left hsumlo hc
        convert! h using 1
        ring
      have hhi : c * (S.eval (x + t) + S.eval (t - x)) ≤ 2 * c * σ := by
        have h := mul_le_mul_of_nonneg_left hsumhi hc
        convert! h using 1
        ring
      constructor <;> linarith
    · have hxtpos : 0 < x + t := by linarith
      have hxtδ : δ' ≤ |x + t| := by
        rw [abs_of_nonneg (le_of_lt hxtpos)]
        linarith
      have htxneg : t - x < 0 := by linarith
      have htxδ : δ' ≤ |t - x| := by
        rw [abs_of_nonpos (le_of_lt htxneg)]
        linarith
      have h1 := hsign (x + t) hxt hxtδ hxtpos
      have h2 := hsignneg (t - x) htx htxδ htxneg
      have hsumlo : -2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 * σ := by linarith
      have hlo : -(2 * c * σ) ≤ c * (S.eval (x + t) + S.eval (t - x)) := by
        have h := mul_le_mul_of_nonneg_left hsumlo hc
        convert! h using 1
        ring
      have hhi : c * (S.eval (x + t) + S.eval (t - x)) ≤ 2 * c * σ := by
        have h := mul_le_mul_of_nonneg_left hsumhi hc
        convert! h using 1
        ring
      constructor <;> linarith
  · intro x hx hband
    have hx' := abs_le.mp hx
    rw [rectanglePolynomial_eval, hcoef]
    have hxt : |x + t| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have htx : |t - x| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hxtpos : 0 < x + t := by linarith
    have hxtδ : δ' ≤ |x + t| := by
      rw [abs_of_nonneg (le_of_lt hxtpos)]
      linarith
    have htxpos : 0 < t - x := by linarith
    have htxδ : δ' ≤ |t - x| := by
      rw [abs_of_nonneg (le_of_lt htxpos)]
      linarith
    have h1 := hsign (x + t) hxt hxtδ hxtpos
    have h2 := hsign (t - x) htx htxδ htxpos
    have hsumlo : 2 - 2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 := by linarith
    have hlo : 2 * c - 2 * c * σ ≤ c * (S.eval (x + t) + S.eval (t - x)) := by
      have h := mul_le_mul_of_nonneg_left hsumlo hc
      convert! h using 1
      ring
    have hhi : c * (S.eval (x + t) + S.eval (t - x)) ≤ 2 * c := by
      have h := mul_le_mul_of_nonneg_left hsumhi hc
      convert! h using 1
      ring
    constructor <;> linarith

/-- Two translated sign approximations satisfy `PrintedRectangleBand` when the threshold lies
between the gap width and one minus the gap width and the stated coefficient budgets hold. -/
theorem twoTranslateRectangleBands {S : Polynomial ℝ} {δ' ε' σ t c e₀ : ℝ}
    (hδ : 0 < δ') (hc : 0 ≤ c) (he0 : 0 ≤ e₀) (hcoef : (1 - e₀) / 2 = c)
    (hlow : 2*c*σ ≤ e₀) (hupp : e₀+2*c*σ ≤ ε')
    (ht0 : δ' ≤ t) (ht1 : t ≤ 1-δ') (hS : SignApproximation S δ' σ) :
    PrintedRectangleBand (rectanglePolynomial S e₀ t) ε' δ' t :=
  twoTranslateRectangleBands_allThresholds hδ hc he0 hcoef hlow hupp
    (by linarith) (by linarith) hS

/-- With offset `ε' / 2`, a sign approximation yields the printed rectangle bands when its error
satisfies `(1 - ε' / 2) * σ ≤ ε' / 2` and the threshold lies in the prescribed interior
interval. -/
theorem twoTranslateRectanglePrintedBands {S : Polynomial ℝ} {δ' ε' σ t : ℝ}
    (hδ : 0 < δ') (hε : 0 < ε') (hε2 : ε' ≤ 1 / 2)
    (ht0 : δ' ≤ t) (ht1 : t ≤ 1 - δ')
    (hσ : (1 - ε' / 2) * σ ≤ ε' / 2)
    (hS : SignApproximation S δ' σ) :
    PrintedRectangleBand (rectanglePolynomial S (ε' / 2) t) ε' δ' t := by
  have hc : 0 ≤ (1 - ε' / 2) / 2 := by
    have h : (1 : ℝ) - ε' / 2 ≥ 3 / 4 := by linarith
    linarith
  have hlow : 2 * ((1 - ε' / 2) / 2) * σ ≤ ε' / 2 := by
    have h := hσ
    convert! h using 1
    ring
  have hupp : ε' / 2 + 2 * ((1 - ε' / 2) / 2) * σ ≤ ε' := by
    have h := mul_le_mul_of_nonneg_right hσ (by linarith : (0 : ℝ) ≤ ε' / 2)
    linarith
  exact twoTranslateRectangleBands (S := S) (δ' := δ') (ε' := ε') (σ := σ) (t := t)
    (c := (1 - ε' / 2) / 2) (e₀ := ε' / 2) hδ hc (by linarith) rfl
    hlow hupp ht0 ht1 hS

/-- For a negative threshold, nonnegative error, and positive gap, the zero branch of the source
rectangle satisfies `PrintedRectangleBand`. -/
theorem sourceRectangle_neg_t {S : Polynomial ℝ} {ε' δ' t : ℝ} (hε : 0 ≤ ε')
    (hδ : 0 < δ') (ht : t < 0) :
    PrintedRectangleBand (sourceRectanglePolynomial S (ε' / 2) t) ε' δ' t := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sourceRectanglePolynomial, if_pos ht]
    simp
  · intro x hx hband
    rw [sourceRectanglePolynomial, if_pos ht]
    simp only [Polynomial.eval_zero]
    constructor <;> linarith
  · intro x hx hband
    exfalso
    rcases hband with ⟨hlo, hhi⟩
    linarith

/-- Composing a polynomial with `X + C t` does not increase its natural degree. -/
theorem comp_linear_natDegree_le {S : Polynomial ℝ} (t : ℝ) :
    (S.comp (Polynomial.X + Polynomial.C t)).natDegree ≤ S.natDegree := by
  have hq : (Polynomial.X + Polynomial.C t : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Nat.le_of_eq Polynomial.natDegree_X
    · exact Nat.le_trans (Nat.le_of_eq (Polynomial.natDegree_C t)) (Nat.zero_le 1)
  refine (Polynomial.natDegree_comp_le).trans ?_
  calc S.natDegree * (Polynomial.X + Polynomial.C t).natDegree
      ≤ S.natDegree * 1 := mul_le_mul_of_nonneg_left hq (Nat.zero_le _)
    _ = S.natDegree := by simp

/-- Composing a polynomial with `C t - X` does not increase its natural degree. -/
theorem comp_linear_neg_natDegree_le {S : Polynomial ℝ} (t : ℝ) :
    (S.comp (Polynomial.C t - Polynomial.X)).natDegree ≤ S.natDegree := by
  have hq : (Polynomial.C t - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Nat.le_trans (Nat.le_of_eq (Polynomial.natDegree_C t)) (Nat.zero_le 1)
    · exact Nat.le_trans (Nat.le_of_eq (Polynomial.natDegree_neg Polynomial.X))
        (Nat.le_of_eq Polynomial.natDegree_X)
  refine (Polynomial.natDegree_comp_le).trans ?_
  calc S.natDegree * (Polynomial.C t - Polynomial.X).natDegree
      ≤ S.natDegree * 1 := mul_le_mul_of_nonneg_left hq (Nat.zero_le _)
    _ = S.natDegree := by simp

/-- The rectangle polynomial has natural degree at most that of its input polynomial. -/
theorem twoTranslate_natDegree_le {S : Polynomial ℝ} {ε₀ t : ℝ} :
    (rectanglePolynomial S ε₀ t).natDegree ≤ S.natDegree := by
  unfold rectanglePolynomial
  have hsum : (S.comp (Polynomial.X + Polynomial.C t) +
      S.comp (Polynomial.C t - Polynomial.X)).natDegree ≤ S.natDegree := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact comp_linear_natDegree_le (S := S) t
    · exact comp_linear_neg_natDegree_le (S := S) t
  have hmul : (Polynomial.C ((1 - ε₀) / 2) *
      (S.comp (Polynomial.X + Polynomial.C t) +
        S.comp (Polynomial.C t - Polynomial.X))).natDegree ≤ S.natDegree := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C]
    omega
  refine (Polynomial.natDegree_add_le _ _).trans (max_le hmul ?_)
  rw [Polynomial.natDegree_C]
  omega

/-- The source rectangle polynomial has natural degree at most that of its input polynomial for
every threshold. -/
theorem sourceRectangle_natDegree_le {S : Polynomial ℝ} {ε₀ t : ℝ} :
    (sourceRectanglePolynomial S ε₀ t).natDegree ≤ S.natDegree := by
  by_cases h : t < 0
  · rw [sourceRectanglePolynomial, if_pos h]
    rw [Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · rw [sourceRectanglePolynomial, if_neg h]
    exact twoTranslate_natDegree_le (S := S) (ε₀ := ε₀) (t := t)

/-- The source rectangle built from a near-optimal sign approximation inherits its degree bound
C(1 + δ⁻¹ log(ε⁻¹)). -/
theorem sourceRectangle_nearOptimal_degree {C δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ ε S) {t : ℝ} :
    ((sourceRectanglePolynomial S (ε / 2) t).natDegree : ℝ) ≤
      C * (1 + (1 / δ) * Real.log (1 / ε)) := by
  have hdeg := sourceRectangle_natDegree_le (S := S) (ε₀ := ε / 2) (t := t)
  have hcast : ((sourceRectanglePolynomial S (ε / 2) t).natDegree : ℝ) ≤ (S.natDegree : ℝ) := by
    exact_mod_cast hdeg
  calc ((sourceRectanglePolynomial S (ε / 2) t).natDegree : ℝ)
      ≤ (S.natDegree : ℝ) := hcast
    _ ≤ C * (1 + (1 / δ) * Real.log (1 / ε)) := hS.2.2.2.2.2.2

open Filter Real Set Topology
set_option warningAsError false

/-- The error function defined by the integral of exp(−t²) from zero to `x`, multiplied by 2/√π. -/
def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0)..x, Real.exp (-t ^ 2)

/-- The error function vanishes at zero. -/
@[simp] theorem erf_zero : erf 0 = 0 := by
  simp [erf]

/-- Reflecting an interval and reversing its endpoints preserves the interval integral of an
even function. -/
theorem integral_even_symm {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (a b : ℝ) :
    ∫ t in (-b)..(-a), f t = ∫ t in a..b, f t := by
  have h := intervalIntegral.integral_comp_neg (a := a) (b := b) (f := f)
  rw [h.symm]
  apply intervalIntegral.integral_congr
  intro t ht
  exact hf t

/-- The error function is odd. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  have h : (∫ t in (-x)..0, Real.exp (-t ^ 2)) = ∫ t in (0)..x, Real.exp (-t ^ 2) := by
    have h := integral_even_symm (f := fun t : ℝ => Real.exp (-t ^ 2)) (by intro t; simp) 0 x
    simpa using! h
  rw [erf, erf, intervalIntegral.integral_symm, h]
  ring

/-- The integral of exp(−t²) over the positive half-line equals √π/2. -/
theorem integral_exp_neg_sq_Ioi_zero :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) = Real.sqrt Real.pi / 2 := by
  have h := integral_gaussian_Ioi 1
  convert! h using 1 <;> ring_nf

/-- For a positive lower endpoint, the function t exp(−t²) is integrable on the corresponding
open positive tail. -/
theorem integrableOn_x_mul_exp_neg_sq (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-t ^ 2)) (Ioi s)
      MeasureTheory.volume := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (1 : ℝ)) (by norm_num)
  simpa using! h0.mono_set (Ioi_subset_Ioi (le_of_lt hs))

/-- For positive `s`, the Gaussian tail integral beyond `s` is at most exp(−s²)/(2s). -/
theorem integral_exp_neg_sq_Ioi_le (s : ℝ) (hs : 0 < s) :
    ∫ t in Ioi s, Real.exp (-t ^ 2) ≤ Real.exp (-s ^ 2) / (2 * s) := by
  have hmono : (∫ t in Ioi s, Real.exp (-t ^ 2))
      ≤ ∫ t in Ioi s, (t * Real.exp (-t ^ 2)) * (1 / s) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi s)
        MeasureTheory.volume := by
      have h := (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (1 : ℝ))).mpr (by norm_num)
      simpa using! h.mono_set (Ioi_subset_Ioi (le_of_lt hs))
    have h2 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (t * Real.exp (-t ^ 2)) * (1 / s)) (Ioi s) MeasureTheory.volume := by
      rw [MeasureTheory.IntegrableOn]
      exact MeasureTheory.Integrable.mul_const (integrableOn_x_mul_exp_neg_sq s hs) (1 / s)
    have h3 : ∀ t ∈ Ioi s, Real.exp (-t ^ 2) ≤ (t * Real.exp (-t ^ 2)) * (1 / s) := by
      intro t ht
      have ht' : s < t := mem_Ioi.mp ht
      have hq : (1 : ℝ) ≤ t / s := (le_div_iff₀ hs).2 (by simpa using! ht'.le)
      have he : (0 : ℝ) ≤ Real.exp (-t ^ 2) := (Real.exp_pos (-t ^ 2)).le
      calc Real.exp (-t ^ 2)
          ≤ Real.exp (-t ^ 2) * (t * (1 / s)) := by
            have hmul := mul_le_mul_of_nonneg_left hq he
            convert! hmul using 1 <;> ring
        _ = (t * Real.exp (-t ^ 2)) * (1 / s) := by ring
    exact MeasureTheory.setIntegral_mono_on (μ := MeasureTheory.volume) h1 h2
      measurableSet_Ioi h3
  have hI : (∫ t in Ioi s, (t * Real.exp (-t ^ 2)) * (1 / s))
      = Real.exp (-s ^ 2) / (2 * s) := by
    have A : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(1 / (2 * s)) * Real.exp (-y ^ 2)
        ) ((x * Real.exp (-(x ^ 2))) * (1 / s)) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
          (Real.exp (-(x ^ 2)) * (-2 * x)) x := by
        have h := (Real.hasDerivAt_exp (-(x ^ 2))).comp x
          ((hasDerivAt_id x).pow 2 |>.neg)
        convert! h using 1
        simp only [id_eq]
        norm_num
      have h2 : HasDerivAt (fun y : ℝ => (-(1 / (2 * s))) * Real.exp (-(y ^ 2))
          ) ((-(1 / (2 * s))) * (Real.exp (-(x ^ 2)) * (-2 * x))) x := h1.const_mul _
      convert! h2 using 1
      field_simp [hs.ne', hs]
    have B : Tendsto (fun y : ℝ => -(1 / (2 * s)) * Real.exp (-y ^ 2)) atTop (𝓝 0) := by
      have hneg : Tendsto (fun y : ℝ => -(y ^ 2)) Filter.atTop Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp
          (Filter.tendsto_pow_atTop (n := 2) (by norm_num))
      have h1 : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2))) Filter.atTop (𝓝 0) :=
        tendsto_exp_atBot.comp hneg
      have h2 : Tendsto (fun y : ℝ => (-(1 / (2 * s))) * Real.exp (-(y ^ 2)))
          Filter.atTop (𝓝 ((-(1 / (2 * s))) * 0)) := tendsto_const_nhds.mul h1
      simpa using! h2
    have hint : MeasureTheory.IntegrableOn
        (fun y : ℝ => (y * Real.exp (-(y ^ 2))) * (1 / s)) (Ioi s) MeasureTheory.volume := by
      rw [MeasureTheory.IntegrableOn]
      exact MeasureTheory.Integrable.mul_const (integrableOn_x_mul_exp_neg_sq s hs) (1 / s)
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := s)
      (f := fun y : ℝ => -(1 / (2 * s)) * Real.exp (-y ^ 2))
      (f' := fun y : ℝ => (y * Real.exp (-(y ^ 2))) * (1 / s))
      (fun x _ => A x) hint B
    have h' : (∫ t in Ioi s, (t * Real.exp (-t ^ 2)) * (1 / s))
        = 0 - (-(1 / (2 * s)) * Real.exp (-(s ^ 2))) := by
      simpa using! h
    rw [h']
    field_simp [hs.ne']
    ring
  rw [hI] at hmono
  linarith

/-- For positive `u`, the Gaussian integral from zero to `u` plus the tail beyond `u` equals the
integral over the positive half-line. -/
theorem integral_exp_neg_sq_split (u : ℝ) (hu : 0 < u) :
    (∫ t in (0)..u, Real.exp (-t ^ 2)) + (∫ t in Ioi u, Real.exp (-t ^ 2))
      = ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 2) := by
  have hI0 : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi (0 : ℝ))
      MeasureTheory.volume := by
    have h := (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (1 : ℝ))).mpr (by norm_num)
    simpa using! h
  have hIu : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Ioi u)
      MeasureTheory.volume := by
    have h := (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (1 : ℝ))).mpr (by norm_num)
    simpa using! h.mono_set (Ioi_subset_Ioi (le_of_lt hu))
  exact intervalIntegral.integral_interval_add_Ioi hI0 hIu

/-- The error function is nonnegative at nonnegative arguments. -/
theorem erf_ge_zero (x : ℝ) (hx : 0 ≤ x) : 0 ≤ erf x := by
  have h : 0 ≤ ∫ t in (0)..x, Real.exp (-t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith [hx])
      (by intro t ht; exact (Real.exp_pos (-t ^ 2)).le)
  have hc : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi := by positivity
  rw [erf]
  nlinarith [mul_nonneg hc h]

/-- The error function is at most one at every real argument. -/
theorem erf_le_one (x : ℝ) : erf x ≤ 1 := by
  rcases lt_or_ge 0 x with hx | hx
  · have hsplit := integral_exp_neg_sq_split x hx
    have htail : 0 ≤ ∫ t in Ioi x, Real.exp (-t ^ 2) := by
      refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi ?_
      intro t ht
      exact (Real.exp_pos (-t ^ 2)).le
    have hmain : (∫ t in (0)..x, Real.exp (-t ^ 2))
        ≤ Real.sqrt Real.pi / 2 := by
      have h := hsplit
      rw [integral_exp_neg_sq_Ioi_zero] at h
      linarith
    have hhalf : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
    have hc : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi := by positivity
    rw [erf]
    calc (2 / Real.sqrt Real.pi) * (∫ t in (0)..x, Real.exp (-t ^ 2))
        ≤ (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hmain hc
      _ = 1 := hhalf
  · have hneg := erf_ge_zero (-x) (by linarith [hx])
    rw [erf_neg] at hneg
    linarith

/-- The error function is at least negative one at every real argument. -/
theorem erf_ge_neg_one (x : ℝ) : -1 ≤ erf x := by
  rcases lt_or_ge 0 x with hx | hx
  · have h := erf_ge_zero x (le_of_lt hx)
    linarith
  · have h := erf_le_one (-x)
    rw [erf_neg] at h
    linarith

/-- The error function has absolute value at most one. -/
theorem abs_erf_le_one (x : ℝ) : |erf x| ≤ 1 := by
  rw [abs_le]
  exact ⟨erf_ge_neg_one x, erf_le_one x⟩

/-- For positive `u`, the difference 1 − erf(u) equals 2/√π times the Gaussian tail integral
beyond `u`. -/
theorem one_sub_erf_eq (u : ℝ) (hu : 0 < u) :
    1 - erf u = (2 / Real.sqrt Real.pi) * (∫ t in Ioi u, Real.exp (-t ^ 2)) := by
  have hsplit := integral_exp_neg_sq_split u hu
  have hone : (∫ t in (0)..u, Real.exp (-t ^ 2))
      = Real.sqrt Real.pi / 2 - (∫ t in Ioi u, Real.exp (-t ^ 2)) := by
    have h := hsplit
    rw [integral_exp_neg_sq_Ioi_zero] at h
    linarith
  have hhalf : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)]
  rw [erf, hone]
  have hspread : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2
      - (∫ t in Ioi u, Real.exp (-t ^ 2)))
      = (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2)
        - (2 / Real.sqrt Real.pi) * (∫ t in Ioi u, Real.exp (-t ^ 2)) := by ring
  rw [hspread, hhalf]
  ring

/-- For positive `u`, the error-function tail is at most exp(−u²)/(u√π). -/
theorem one_sub_erf_le (u : ℝ) (hu : 0 < u) :
    1 - erf u ≤ Real.exp (-u ^ 2) / (u * Real.sqrt Real.pi) := by
  have htail := integral_exp_neg_sq_Ioi_le u hu
  have hmul : (2 / Real.sqrt Real.pi) * (∫ t in Ioi u, Real.exp (-t ^ 2))
      ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-u ^ 2) / (2 * u)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hkey : (2 / Real.sqrt Real.pi) * (Real.exp (-u ^ 2) / (2 * u))
      = Real.exp (-u ^ 2) / (u * Real.sqrt Real.pi) := by
    field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos), hu.ne', hu]
  calc 1 - erf u = (2 / Real.sqrt Real.pi) * (∫ t in Ioi u, Real.exp (-t ^ 2)) :=
      one_sub_erf_eq u hu
    _ ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-u ^ 2) / (2 * u)) := hmul
    _ = Real.exp (-u ^ 2) / (u * Real.sqrt Real.pi) := hkey

/-- The natural logarithm of two is at least one half. -/
theorem log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

/-- For 0 < ε ≤ 1/2, the natural logarithm log(2/ε) is at least one. -/
theorem log_two_div_eps_ge_one (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (1 : ℝ) ≤ Real.log (2 / ε) := by
  have h4 : (4 : ℝ) ≤ 2 / ε := (le_div_iff₀ hε).2 (by linarith [hε2])
  have hlog4 : Real.log 4 ≤ Real.log (2 / ε) := Real.log_le_log (by norm_num) h4
  have hlog4' : (1 : ℝ) ≤ Real.log 4 := by
    have h : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [log_two_ge_half]
  linarith

/-- For 0 < ε ≤ 1/2 and u ≥ √(2 log(2/ε)), the error-function tail 1 − erf(u) is at most `ε`. -/
theorem one_sub_erf_le_eps (u ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : Real.sqrt (2 * Real.log (2 / ε)) ≤ u) : 1 - erf u ≤ ε := by
  have hL : (1 : ℝ) ≤ Real.log (2 / ε) := log_two_div_eps_ge_one ε hε hε2
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * Real.log (2 / ε)) := Real.sqrt_pos.2 (by linarith [hL])
  have hu0 : 0 < u := by linarith [hsqrt, hu]
  have hmain := one_sub_erf_le u hu0
  have hu2 : 2 * Real.log (2 / ε) ≤ u ^ 2 := by
    have h := (sq_le_sq₀ (by linarith [hsqrt]) (by linarith [hu])).2 hu
    rw [Real.sq_sqrt (by linarith [hL])] at h
    linarith
  have hexp : Real.exp (-u ^ 2) ≤ Real.exp (-2 * Real.log (2 / ε)) :=
    Real.exp_le_exp.mpr (by linarith [hu2])
  have hexp2 : Real.exp (-2 * Real.log (2 / ε)) = (ε / 2) ^ 2 := by
    have hpos : (0 : ℝ) < 2 / ε := by positivity
    have h1 : Real.exp (-Real.log (2 / ε)) = (2 / ε)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hpos]
    have h2 : Real.exp (-2 * Real.log (2 / ε))
        = Real.exp (-Real.log (2 / ε)) * Real.exp (-Real.log (2 / ε)) := by
      have he : (-2 : ℝ) * Real.log (2 / ε) = -Real.log (2 / ε) + -Real.log (2 / ε) := by
        ring
      rw [he, Real.exp_add]
    rw [h2, h1]
    field_simp [hε.ne', hε]
  have hsqrtpi : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have hpi := Real.pi_gt_three
    linarith
  have hu1 : (1 : ℝ) ≤ u := by
    have hsqrt2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.log (2 / ε)) := by
      rw [Real.le_sqrt (by norm_num) (by linarith [hL])]
      linarith
    linarith [hsqrt2, hu]
  have hden : (1 : ℝ) ≤ u * Real.sqrt Real.pi := by
    have h := mul_le_mul hu1 hsqrtpi (by norm_num) (by linarith [hu0])
    simpa using! h
  calc 1 - erf u ≤ Real.exp (-u ^ 2) / (u * Real.sqrt Real.pi) := hmain
    _ ≤ Real.exp (-2 * Real.log (2 / ε)) / (u * Real.sqrt Real.pi) :=
      div_le_div_of_nonneg_right hexp (by positivity)
    _ = (ε / 2) ^ 2 / (u * Real.sqrt Real.pi) := by rw [hexp2]
    _ ≤ (ε / 2) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ (ε / 2) ^ 2)
      rw [mul_one] at h
      exact (div_le_iff₀ (by positivity)).2 h
    _ ≤ ε := by
      have hone : (ε / 2) ^ 2 = ε ^ 2 / 4 := by ring
      rw [hone]
      have h1 : (0 : ℝ) ≤ ε := le_of_lt hε
      have h2 : ε * ε ≤ ε * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hε2 h1
      have h3 : ε * (1 / 2 : ℝ) ≤ ε := by linarith
      have h4 : ε * ε ≤ ε := le_trans h2 h3
      nlinarith [h4]

/-- The scaled error-function response erf(x/(σ√2)) used to smooth the sign function. -/
def smoothedSign (σ x : ℝ) : ℝ := erf (x / (σ * Real.sqrt 2))

/-- The smoothed sign response vanishes at zero. -/
@[simp] theorem smoothedSign_zero (σ : ℝ) : smoothedSign σ 0 = 0 := by
  simp [smoothedSign]

/-- The smoothed sign response is odd for every smoothing parameter. -/
theorem smoothedSign_neg (σ x : ℝ) : smoothedSign σ (-x) = -smoothedSign σ x := by
  unfold smoothedSign
  rw [neg_div, erf_neg]

/-- The smoothed sign response has absolute value at most one for every smoothing parameter and
input. -/
theorem abs_smoothedSign_le_one (σ x : ℝ) : |smoothedSign σ x| ≤ 1 :=
  abs_erf_le_one _

/-- The smoothed sign tail is at most `ε` when its normalized input is at least √(2 log(2/ε)),
for 0 < ε ≤ 1/2. -/
theorem one_sub_smoothedSign_le (ε σ x : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : Real.sqrt (2 * Real.log (2 / ε)) ≤ x / (σ * Real.sqrt 2)) :
    1 - smoothedSign σ x ≤ ε := by
  unfold smoothedSign
  exact one_sub_erf_le_eps (x / (σ * Real.sqrt 2)) ε hε hε2 hu

/-- The smoothing-width bound δ/(2√(log(2/ε))) used for approximation outside a gap. -/
def erfSmoothingWidth (δ ε : ℝ) : ℝ := δ / (2 * Real.sqrt (Real.log (2 / ε)))

/-- For 0 < ε ≤ 1/2, a positive smoothing width at most `erfSmoothingWidth δ ε` gives tail error
at most `ε` at every x ≥ δ. -/
theorem one_sub_smoothedSign_le_of_width (δ ε σ x : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hσ : 0 < σ) (hσw : σ ≤ erfSmoothingWidth δ ε) (hx : δ ≤ x) :
    1 - smoothedSign σ x ≤ ε := by
  have hL : (0 : ℝ) < Real.log (2 / ε) := by
    have h1 : (1 : ℝ) < 2 / ε := (lt_div_iff₀ hε).2 (by linarith [hε2])
    exact Real.log_pos h1
  have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by
    have h1 : (0 : ℝ) < σ := hσ
    have h2 : (0 : ℝ) < σ * σ := mul_pos h1 h1
    nlinarith
  have hmul : 2 * σ * Real.sqrt (Real.log (2 / ε)) ≤ δ := by
    have hsqrtL : (0 : ℝ) < Real.sqrt (Real.log (2 / ε)) := Real.sqrt_pos.2 hL
    have hpos : (0 : ℝ) < 2 * Real.sqrt (Real.log (2 / ε)) := by nlinarith [hsqrtL]
    have h1 : σ * (2 * Real.sqrt (Real.log (2 / ε))) ≤ δ := by
      rw [erfSmoothingWidth] at hσw
      calc σ * (2 * Real.sqrt (Real.log (2 / ε)))
          ≤ (δ / (2 * Real.sqrt (Real.log (2 / ε)))) * (2 * Real.sqrt (Real.log (2 / ε))) :=
            mul_le_mul_of_nonneg_right hσw (le_of_lt hpos)
        _ = δ := by field_simp [ne_of_gt hpos]
    nlinarith [h1]
  have hsq : (2 * σ * Real.sqrt (Real.log (2 / ε))) ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hmul
  have hid : (2 * σ * Real.sqrt (Real.log (2 / ε))) ^ 2
      = 4 * σ ^ 2 * Real.log (2 / ε) := by
    have hsqL : Real.sqrt (Real.log (2 / ε)) ^ 2 = Real.log (2 / ε) :=
      Real.sq_sqrt (by linarith [hL])
    rw [mul_pow, hsqL]
    ring
  have hsq' : 4 * σ ^ 2 * Real.log (2 / ε) ≤ δ ^ 2 := by
    rw [← hid]
    exact hsq
  have hx2 : δ ^ 2 ≤ x ^ 2 := (sq_le_sq₀ (by linarith [hδ]) (by linarith [hx])).2 hx
  have hu : Real.sqrt (2 * Real.log (2 / ε)) ≤ x / (σ * Real.sqrt 2) := by
    have hx0 : (0 : ℝ) ≤ x := le_trans (le_of_lt hδ) hx
    have hnonneg : (0 : ℝ) ≤ x / (σ * Real.sqrt 2) := by positivity
    rw [← Real.sqrt_sq hnonneg]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have hden : σ ^ 2 * 2 = 2 * σ ^ 2 := by ring
    rw [hden]
    apply (le_div_iff₀ hσ2).2
    nlinarith [hsq', hx2]
  exact one_sub_smoothedSign_le ε σ x hε hε2 hu

/-- Under the prescribed positive width bound, the smoothed sign lies in [1 − ε, 1] for x ≥ δ. -/
theorem smoothedSign_pos_le (δ ε σ x : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hσ : 0 < σ) (hσw : σ ≤ erfSmoothingWidth δ ε) (hx : δ ≤ x) :
    1 - ε ≤ smoothedSign σ x ∧ smoothedSign σ x ≤ 1 := by
  have hgap : 1 - smoothedSign σ x ≤ ε :=
    one_sub_smoothedSign_le_of_width δ ε σ x hδ hε hε2 hσ hσw hx
  have hnorm : |smoothedSign σ x| ≤ 1 := abs_smoothedSign_le_one σ x
  rcases abs_le.mp hnorm with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- Under the prescribed positive width bound, the smoothed sign lies in [−1, −1 + ε] for x ≤
−δ. -/
theorem smoothedSign_neg_le (δ ε σ x : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hσ : 0 < σ) (hσw : σ ≤ erfSmoothingWidth δ ε) (hx : x ≤ -δ) :
    -1 ≤ smoothedSign σ x ∧ smoothedSign σ x ≤ -1 + ε := by
  have hle : δ ≤ -x := by simpa using! (neg_le_neg hx)
  have hpos := smoothedSign_pos_le δ ε σ (-x) hδ hε hε2 hσ hσw hle
  have hodd : smoothedSign σ x = -smoothedSign σ (-x) := by
    rw [smoothedSign_neg]
    ring
  rcases hpos with ⟨hlo, hhi⟩
  constructor <;> linarith [hodd]

/-- With the prescribed positive width bound, the smoothed sign approximates `Real.sign` within
`ε` whenever |x| ≥ δ. -/
theorem abs_sub_smoothedSign_sign_le (δ ε σ x : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hσ : 0 < σ) (hσw : σ ≤ erfSmoothingWidth δ ε) (hx : δ ≤ |x|) :
    |smoothedSign σ x - Real.sign x| ≤ ε := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have habs : |x| = -x := abs_of_nonpos (le_of_lt hneg)
    have hle : x ≤ -δ := by linarith [habs, hx]
    have hneg' := smoothedSign_neg_le δ ε σ x hδ hε hε2 hσ hσw hle
    rw [Real.sign_of_neg hneg, abs_le]
    rcases hneg' with ⟨hlo, hhi⟩
    constructor <;> linarith
  · have hz : δ ≤ 0 := hx.trans (by rw [hzero]; simp)
    exact absurd hz (not_le_of_gt hδ)
  · have habs : |x| = x := abs_of_pos hpos
    have hle : δ ≤ x := by linarith [habs, hx]
    have hpos' := smoothedSign_pos_le δ ε σ x hδ hε hε2 hσ hσw hle
    rw [Real.sign_of_pos hpos, abs_le]
    rcases hpos' with ⟨hlo, hhi⟩
    constructor <;> linarith

/-- The natural ceiling of 4 log(1/ε)/δ used as a sign-approximation cutoff. -/
def nearOptimalSignCutoff (δ ε : ℝ) : ℕ := Nat.ceil (4 * Real.log (1 / ε) / δ)

/-- For positive gap and 0 < ε ≤ 1, twice the cutoff plus one is at most 8(1 + δ⁻¹ log(ε⁻¹)). -/
theorem nearOptimalSignCutoff_deg_le (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hε2 : ε ≤ 1) :
    (2 * nearOptimalSignCutoff δ ε + 1 : ℝ) ≤ 8 * (1 + (1 / δ) * Real.log (1 / ε)) := by
  have hone : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith [hε2])
  have hL : (0 : ℝ) ≤ Real.log (1 / ε) := Real.log_nonneg hone
  have hceil : (nearOptimalSignCutoff δ ε : ℝ) ≤ 4 * Real.log (1 / ε) / δ + 1 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * Real.log (1 / ε) / δ by positivity)
    rw [← nearOptimalSignCutoff] at h
    exact le_of_lt h
  have hmain : (2 : ℝ) * (nearOptimalSignCutoff δ ε : ℝ) + 1
      ≤ 8 * Real.log (1 / ε) / δ + 3 := by
    have h' : (2 : ℝ) * (nearOptimalSignCutoff δ ε : ℝ) + 1
        ≤ 2 * (4 * Real.log (1 / ε) / δ + 1) + 1 := by
      have hmul := mul_le_mul_of_nonneg_left hceil (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    calc (2 : ℝ) * (nearOptimalSignCutoff δ ε : ℝ) + 1
        ≤ 2 * (4 * Real.log (1 / ε) / δ + 1) + 1 := h'
      _ = 8 * Real.log (1 / ε) / δ + 3 := by ring
  calc (2 : ℝ) * (nearOptimalSignCutoff δ ε : ℝ) + 1
      ≤ 8 * Real.log (1 / ε) / δ + 3 := hmain
    _ ≤ 8 * Real.log (1 / ε) / δ + 8 := by linarith
    _ = 8 * (1 + (1 / δ) * Real.log (1 / ε)) := by ring

/-- Requires nonnegative amplitude `M`, positive rate `a`, and coefficient bounds |c j| ≤ M
exp(−a j²). -/
def chebyshevSaddleDecay (M a : ℝ) (c : ℕ → ℝ) : Prop :=
  0 ≤ M ∧ 0 < a ∧ ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2))

/-- For a real ratio different from one, the finite geometric sum equals (1 − rⁿ)/(1 − r). -/
theorem geom_sum_eq {r : ℝ} (hr : r ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i = (1 - r ^ n) / (1 - r) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hne : (1 - r) ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
      field_simp [hne]; ring

/-- A coefficient sequence bounded by M exp(−a j²) has finite tail after `J` bounded by 2M
exp(−a(J + 1)²) when a(2J + 1) ≥ log 2. -/
theorem chebyshevSaddleDecay_tail_le {M a : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    (hM : 0 ≤ M) (ha : 0 < a) (hJ : Real.log 2 ≤ a * (2 * (J : ℝ) + 1))
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2))) :
    ∑ i ∈ Finset.range n, |c (J + 1 + i)| ≤ 2 * M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) := by
  have hx : (0 : ℝ) < 2 * (J : ℝ) + 1 := by positivity
  have hax : (0 : ℝ) < a * (2 * (J : ℝ) + 1) := mul_pos ha hx
  have hsq : ∀ i : ℕ, ((J + 1 : ℝ) + i) ^ 2 ≥ (J + 1 : ℝ) ^ 2 + (2 * (J : ℝ) + 1) * i := by
    intro i
    have h1 : ((J + 1 : ℝ) + i) ^ 2 = (J + 1 : ℝ) ^ 2 + 2 * (J + 1 : ℝ) * i + i ^ 2 := by
      ring
    have h3 : (2 * (J + 1 : ℝ) * i + i ^ 2) - ((2 * (J : ℝ) + 1) * i) = i ^ 2 + i := by
      ring
    have h4 : (0 : ℝ) ≤ i ^ 2 + i := by positivity
    linarith
  have hexp : ∀ i : ℕ, Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2))
      ≤ Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * Real.exp (-(a * ((2 * (J : ℝ) + 1) * i))) := by
    intro i
    have hsq' := hsq i
    have ha0 : (0 : ℝ) ≤ a := ha.le
    have hmul := mul_le_mul_of_nonneg_left hsq' ha0
    have h1 : -(a * ((J + 1 : ℝ) + i) ^ 2)
        ≤ -(a * ((J + 1 : ℝ)) ^ 2) + -(a * ((2 * (J : ℝ) + 1) * i)) := by
      linarith
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_add] at h2
    exact h2
  have hmul : ∀ i : ℕ, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))
      = (Real.exp (-(a * (2 * (J : ℝ) + 1)))) ^ i := by
    intro i
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hstep : ∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))
      = ∑ i ∈ Finset.range n, (Real.exp (-(a * (2 * (J : ℝ) + 1)))) ^ i := by
    rw [Finset.sum_congr rfl (fun i _ => hmul i)]
  have hrlt : Real.exp (-(a * (2 * (J : ℝ) + 1))) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrne : Real.exp (-(a * (2 * (J : ℝ) + 1))) ≠ 1 := ne_of_lt hrlt
  have hden : (0 : ℝ) < 1 - Real.exp (-(a * (2 * (J : ℝ) + 1))) := by linarith
  have hnum : (1 : ℝ) - (Real.exp (-(a * (2 * (J : ℝ) + 1)))) ^ n ≤ 1 := by
    have hpow : (Real.exp (-(a * (2 * (J : ℝ) + 1)))) ^ n ≤ 1 := by
      rw [← Real.exp_nat_mul]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ha2 : (0 : ℝ) ≤ a * (2 * (J : ℝ) + 1) := hax.le
      have hmulnn : (0 : ℝ) ≤ (a * (2 * (J : ℝ) + 1)) * (n : ℝ) := mul_nonneg ha2 hn
      rw [show (n : ℝ) * (-(a * (2 * (J : ℝ) + 1))) = -((a * (2 * (J : ℝ) + 1)) * (n : ℝ)) by ring]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmulnn)
    have hpow0 : (0 : ℝ) ≤ (Real.exp (-(a * (2 * (J : ℝ) + 1)))) ^ n :=
      pow_nonneg (Real.exp_pos _).le n
    linarith
  have hhalf : Real.exp (-(a * (2 * (J : ℝ) + 1))) ≤ 1 / 2 := by
    have h1 : Real.exp (-(a * (2 * (J : ℝ) + 1))) ≤ Real.exp (-Real.log 2) := by
      exact Real.exp_le_exp.mpr (by linarith [hJ])
    have h2 : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    linarith
  have hsum : ∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))
      ≤ 1 / (1 - Real.exp (-(a * (2 * (J : ℝ) + 1)))) := by
    rw [hstep, geom_sum_eq hrne]
    exact div_le_div_of_nonneg_right hnum hden.le
  have h1div : 1 / (1 - Real.exp (-(a * (2 * (J : ℝ) + 1)))) ≤ 2 := by
    have hineq : (1 : ℝ) ≤ 2 * (1 - Real.exp (-(a * (2 * (J : ℝ) + 1)))) := by linarith
    exact (div_le_iff₀ hden).2 (by linarith)
  have htail : ∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i))) ≤ 2 :=
    hsum.trans h1div
  calc
    ∑ i ∈ Finset.range n, |c (J + 1 + i)|
        ≤ ∑ i ∈ Finset.range n, M * Real.exp (-(a * (((J + 1 : ℝ) + i) ^ 2))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hc (J + 1 + i)
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h
          exact h
    _ ≤ ∑ i ∈ Finset.range n,
          (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc M * Real.exp (-(a * (((J + 1 : ℝ) + i) ^ 2)))
              ≤ M * (Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))
                  * Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))) := by
                have hle := mul_le_mul_of_nonneg_left (hexp i) hM
                exact hle
            _ = M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))
                * Real.exp (-(a * ((2 * (J : ℝ) + 1) * i))) := by ring
    _ = (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)))
        * (∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i)))) := by
          rw [Finset.mul_sum]
    _ ≤ 2 * M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) := by
          have hnonneg : (0 : ℝ) ≤ M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) :=
            mul_nonneg hM (Real.exp_pos _).le
          calc (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)))
              * (∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 1) * i))))
              ≤ (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))) * 2 := by
                have hle := mul_le_mul_of_nonneg_left htail hnonneg
                exact hle
            _ = 2 * M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) := by ring

/-- The Chebyshev polynomial sum from order zero through order `J`, with coefficients supplied
by `c`. -/
def chebyshevSaddleTruncation (c : ℕ → ℝ) (J : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (J + 1), Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j : ℤ)

/-- The Chebyshev truncation through order `J` has natural degree at most `J`. -/
theorem chebyshevSaddleTruncation_degree_le (c : ℕ → ℝ) (J : ℕ) :
    (chebyshevSaddleTruncation c J).natDegree ≤ J := by
  unfold chebyshevSaddleTruncation
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C]
  have hT : (Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree ≤ J := by
    rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    simp only [Finset.mem_range] at hj
    omega
  omega

/-- Every integer-order Chebyshev polynomial has absolute value at most one on [−1, 1]. -/
theorem chebyshev_abs_eval_le_one (n : ℤ) (x : ℝ) (hx : |x| ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval x| ≤ 1 := by
  have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  rw [← Real.cos_arccos hx'.1 hx'.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- For a value represented by a Chebyshev truncation and a finite tail at |x| ≤ 1, the
truncation error is at most the sum of the absolute tail coefficients. -/
theorem chebyshevSaddleTruncation_error_le_of_repr {c : ℕ → ℝ} {J n : ℕ} {x : ℝ} {v : ℝ}
    (hx : |x| ≤ 1)
    (hrepr : v = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |v - (chebyshevSaddleTruncation c J).eval x| ≤ ∑ i ∈ Finset.range n, |c (J + 1 + i)| := by
  have hterm : ∀ i ∈ Finset.range n,
      -|c (J + 1 + i)| ≤ c (J + 1 + i)
        * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x ∧
      c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x ≤ |c (J + 1 + i)| := by
    intro i _
    have h2 := chebyshev_abs_eval_le_one ((J + 1 + i : ℕ) : ℤ) x hx
    have h3 : |c (J + 1 + i)| * |(Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x|
        ≤ |c (J + 1 + i)| := by
      calc |c (J + 1 + i)| * |(Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x|
          ≤ |c (J + 1 + i)| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = |c (J + 1 + i)| := by ring
    have h4 : |c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x|
        ≤ |c (J + 1 + i)| := by rw [abs_mul]; exact h3
    exact ⟨(abs_le.mp h4).1, (abs_le.mp h4).2⟩
  have hSneg : -(∑ i ∈ Finset.range n, |c (J + 1 + i)|)
      ≤ ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i hi => (hterm i hi).1
  have hSpos : (∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x)
      ≤ ∑ i ∈ Finset.range n, |c (J + 1 + i)| := by
    exact Finset.sum_le_sum fun i hi => (hterm i hi).2
  rw [hrepr, abs_le]
  constructor
  · linarith
  · linarith

/-- For a polynomial value represented by the stated truncation and finite Chebyshev tail, the
truncation error on [−1, 1] is bounded by the absolute coefficient tail. -/
theorem chebyshevSaddleTruncation_error_le {c : ℕ → ℝ} {J n : ℕ} {x : ℝ} {f : Polynomial ℝ}
    (hx : |x| ≤ 1)
    (hrepr : f.eval x = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |f.eval x - (chebyshevSaddleTruncation c J).eval x| ≤ ∑ i ∈ Finset.range n, |c (J + 1 + i)| := by
  exact chebyshevSaddleTruncation_error_le_of_repr hx hrepr

/-- The assumed finite Chebyshev representation has truncation error at most `ε` when Gaussian
coefficient decay and the stated cutoff and tail budget hold. -/
theorem chebyshevSaddleTruncation_error_of_budget_of_repr {M a ε : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    {x : ℝ} {v : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hJ : Real.log 2 ≤ a * (2 * (J : ℝ) + 1))
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)))
    (hbudget : 2 * M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) ≤ ε)
    (hx : |x| ≤ 1)
    (hrepr : v = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |v - (chebyshevSaddleTruncation c J).eval x| ≤ ε := by
  refine (chebyshevSaddleTruncation_error_le_of_repr hx hrepr).trans ?_
  exact (chebyshevSaddleDecay_tail_le hM ha hJ hc).trans hbudget

/-- A polynomial value with the stated finite Chebyshev representation has truncation error at
most `ε` under the Gaussian decay and tail-budget hypotheses. -/
theorem chebyshevSaddleTruncation_error_of_budget {M a ε : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    {x : ℝ} {f : Polynomial ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hJ : Real.log 2 ≤ a * (2 * (J : ℝ) + 1))
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)))
    (hbudget : 2 * M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) ≤ ε)
    (hx : |x| ≤ 1)
    (hrepr : f.eval x = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |f.eval x - (chebyshevSaddleTruncation c J).eval x| ≤ ε := by
  exact chebyshevSaddleTruncation_error_of_budget_of_repr hM ha hJ hc hbudget hx hrepr

/-- The integer sign power of an even natural number equals one. -/
theorem negOnePow_natCast_even (j : ℕ) (h : Even j) : ((j : ℤ).negOnePow : ℤ) = 1 := by
  obtain ⟨k, hk⟩ := h
  have hk' : j = 2 * k := hk.trans (Nat.two_mul k).symm
  have h' : (j : ℤ) = 2 * (k : ℤ) := by exact_mod_cast hk'
  rw [h', Int.negOnePow_two_mul]
  norm_num

/-- The integer sign power of an odd natural number equals negative one. -/
theorem negOnePow_natCast_odd (j : ℕ) (h : Odd j) : ((j : ℤ).negOnePow : ℤ) = -1 := by
  obtain ⟨k, hk⟩ := h
  have hk' : j = 2 * k + 1 := hk.trans (by omega)
  have h' : (j : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk'
  rw [h', Int.negOnePow_two_mul_add_one]
  norm_num

/-- A Chebyshev truncation is odd when every coefficient of even order vanishes. -/
theorem chebyshevSaddleTruncation_odd (c : ℕ → ℝ) (J : ℕ)
    (hodd : ∀ j, Even j → c j = 0) (y : ℝ) :
    (chebyshevSaddleTruncation c J).eval (-y) = -(chebyshevSaddleTruncation c J).eval y := by
  have hterm : ∀ j ∈ Finset.range (J + 1),
      (Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (-y)
        = -((Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j : ℤ)).eval y) := by
    intro j _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_eval_neg,
      Polynomial.eval_mul, Polynomial.eval_C]
    rcases Nat.even_or_odd j with hj | hj
    · have hc0 : c j = 0 := hodd j hj
      rw [hc0]
      ring
    · have hp : ((j : ℤ).negOnePow : ℤ) = -1 := negOnePow_natCast_odd j hj
      rw [hp]
      ring
  unfold chebyshevSaddleTruncation
  rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j hj => hterm j hj)

/-- The Gaussian coefficient-decay rate σ²/8 associated with a smoothing width. -/
def saddleDecayRate (σ : ℝ) : ℝ := σ ^ 2 / 8

/-- The width δ/(2√(log(6/ε))) used in the Chebyshev smoothing construction. -/
def erfSaddleWidth (δ ε : ℝ) : ℝ := δ / (2 * Real.sqrt (Real.log (6 / ε)))

/-- Half the saddle width equals `erfSmoothingWidth` with gap `δ / 2` and error `ε / 3`. -/
theorem erfSaddleWidth_half (δ ε : ℝ) :
    erfSaddleWidth δ ε / 2 = erfSmoothingWidth (δ / 2) (ε / 3) := by
  have hlog : Real.log (2 / (ε / 3)) = Real.log (6 / ε) := by
    congr 1
    field_simp
    ring
  calc erfSaddleWidth δ ε / 2 = δ / (2 * Real.sqrt (Real.log (6 / ε)) * 2) := by
        rw [erfSaddleWidth, div_div]
    _ = δ / (4 * Real.sqrt (Real.log (6 / ε))) := by
        rw [show 2 * Real.sqrt (Real.log (6 / ε)) * 2 = 4 * Real.sqrt (Real.log (6 / ε)) by ring]
    _ = (δ / 2) / (2 * Real.sqrt (Real.log (2 / (ε / 3)))) := by
        rw [← hlog, div_div]
        ring
    _ = erfSmoothingWidth (δ / 2) (ε / 3) := rfl

/-- Rescales the Chebyshev truncation to the input x/2 and normalizes its values by the factor
1/(1 + ε/3). -/
def nearOptimalSignTable (c : ℕ → ℝ) (J : ℕ) (ε : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 / (1 + ε / 3)) *
    (chebyshevSaddleTruncation c J).comp (Polynomial.C (1 / 2) * Polynomial.X)

/-- Evaluating the sign table gives the truncation at x/2 divided by 1 + ε/3. -/
theorem nearOptimalSignTable_eval (c : ℕ → ℝ) (J : ℕ) (ε x : ℝ) :
    (nearOptimalSignTable c J ε).eval x
      = (1 / (1 + ε / 3)) * (chebyshevSaddleTruncation c J).eval (x / 2) := by
  rw [nearOptimalSignTable, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  ring

/-- The normalized and rescaled sign table has natural degree at most its truncation level. -/
theorem nearOptimalSignTable_degree_le (c : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    (nearOptimalSignTable c J ε).natDegree ≤ J := by
  have hq2 : ((Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
  have h3 : ((chebyshevSaddleTruncation c J).comp
      (Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree ≤ J := by
    calc ((chebyshevSaddleTruncation c J).comp
        (Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree
        ≤ (chebyshevSaddleTruncation c J).natDegree
            * ((Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree :=
          Polynomial.natDegree_comp_le (R := ℝ)
            (p := chebyshevSaddleTruncation c J)
            (q := (Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ))
      _ ≤ J * ((Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree :=
          Nat.mul_le_mul_right _ (chebyshevSaddleTruncation_degree_le c J)
      _ ≤ J * 1 := Nat.mul_le_mul_left J hq2
      _ = J := Nat.mul_one _
  calc (nearOptimalSignTable c J ε).natDegree
      ≤ (Polynomial.C (1 / (1 + ε / 3))).natDegree
          + ((chebyshevSaddleTruncation c J).comp
              (Polynomial.C (1 / 2) * Polynomial.X : Polynomial ℝ)).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ J := by
      rw [Polynomial.natDegree_C]
      omega

/-- The sign table is odd when all even-order coefficients vanish. -/
theorem nearOptimalSignTable_odd (c : ℕ → ℝ) (J : ℕ) (ε : ℝ)
    (hodd : ∀ j, Even j → c j = 0) (x : ℝ) :
    (nearOptimalSignTable c J ε).eval (-x) = -(nearOptimalSignTable c J ε).eval x := by
  rw [nearOptimalSignTable_eval, nearOptimalSignTable_eval]
  have hp := chebyshevSaddleTruncation_odd c J hodd (x / 2)
  have hp' : (chebyshevSaddleTruncation c J).eval ((-x) / 2)
      = -(chebyshevSaddleTruncation c J).eval (x / 2) := by
    rw [show (-x) / 2 = -(x / 2) by ring]
    exact hp
  rw [hp']
  ring

/-- Dividing a nonzero real number by two preserves its sign. -/
theorem sign_div_two (x : ℝ) (h : x ≠ 0) : Real.sign (x / 2) = Real.sign x := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · rw [Real.sign_of_neg hneg, Real.sign_of_neg (by linarith)]
  · exact absurd hzero h
  · rw [Real.sign_of_pos hpos, Real.sign_of_pos (by linarith)]

/-- Constructs a near-optimal sign approximation from the assumed finite representation of the
smoothed sign, an absolute tail bound ε/3, vanishing even coefficients, and the stated
degree budget. -/
theorem nearOptimalSign_of_saddle {C δ ε : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    (hC : 0 < C) (hδ : 0 < δ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hrepr : ∀ y : ℝ, |y| ≤ 1 →
      smoothedSign (erfSaddleWidth δ ε / 2) y = (chebyshevSaddleTruncation c J).eval y
        + ∑ i ∈ Finset.range n,
            c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval y)
    (htail : ∑ i ∈ Finset.range n, |c (J + 1 + i)| ≤ ε / 3)
    (hodd : ∀ j : ℕ, Even j → c j = 0)
    (hdeg : (J : ℝ) ≤ C * (1 + (1 / δ) * Real.log (1 / ε))) :
    NearOptimalSignApproximation C δ ε (nearOptimalSignTable c J ε) := by
  have hσpos : 0 < erfSaddleWidth δ ε / 2 := by
    unfold erfSaddleWidth
    have h1 : (0 : ℝ) < Real.log (6 / ε) := by
      have h2 : (1 : ℝ) < 6 / ε := (lt_div_iff₀ hε).2 (by linarith [hε2])
      exact Real.log_pos h2
    have h2 : (0 : ℝ) < Real.sqrt (Real.log (6 / ε)) := Real.sqrt_pos.2 h1
    positivity

  have herr : ∀ y : ℝ, |y| ≤ 1 →
      |smoothedSign (erfSaddleWidth δ ε / 2) y - (chebyshevSaddleTruncation c J).eval y|
        ≤ ε / 3 := by
    intro y hy
    exact (chebyshevSaddleTruncation_error_le_of_repr
      (v := smoothedSign (erfSaddleWidth δ ε / 2) y) hy (hrepr y hy)).trans htail

  have hwidth : erfSaddleWidth δ ε / 2 ≤ erfSmoothingWidth (δ / 2) (ε / 3) := by
    rw [erfSaddleWidth_half]

  have hnorm : ∀ x : ℝ, |x| ≤ 2 → |(nearOptimalSignTable c J ε).eval x| ≤ 1 := by
    intro x hx
    have htwo : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
    have hx2 : |x / 2| ≤ 1 := by
      rw [abs_div, htwo]
      linarith
    have herr' := herr (x / 2) hx2
    have hsg : |smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)| ≤ 1 :=
      abs_smoothedSign_le_one _ _
    have hP : |(chebyshevSaddleTruncation c J).eval (x / 2)| ≤ 1 + ε / 3 := by
      have h1 := abs_add_le ((chebyshevSaddleTruncation c J).eval (x / 2)
          - smoothedSign (erfSaddleWidth δ ε / 2) (x / 2))
        (smoothedSign (erfSaddleWidth δ ε / 2) (x / 2))
      have h2 : (chebyshevSaddleTruncation c J).eval (x / 2)
          - smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)
          + smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)
          = (chebyshevSaddleTruncation c J).eval (x / 2) := by ring
      rw [h2] at h1
      have h3 : |(chebyshevSaddleTruncation c J).eval (x / 2)
          - smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)| ≤ ε / 3 := by
        have h := herr'
        rw [abs_sub_comm] at h
        exact h
      linarith
    rw [nearOptimalSignTable_eval, abs_mul, abs_of_pos (by positivity)]
    calc (1 / (1 + ε / 3)) * |(chebyshevSaddleTruncation c J).eval (x / 2)|
        ≤ (1 / (1 + ε / 3)) * (1 + ε / 3) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 1 := by field_simp

  have herr2 : ∀ x : ℝ, |x| ≤ 2 → δ ≤ |x| →
      |(nearOptimalSignTable c J ε).eval x - Real.sign x| ≤ ε := by
    intro x hx hδx
    have htwo : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
    have hx2 : |x / 2| ≤ 1 := by
      rw [abs_div, htwo]
      linarith
    have hδ2 : δ / 2 ≤ |x / 2| := by
      rw [abs_div, htwo]
      linarith
    have hgap : |smoothedSign (erfSaddleWidth δ ε / 2) (x / 2) - Real.sign (x / 2)| ≤ ε / 3 := by
      refine abs_sub_smoothedSign_sign_le (δ / 2) (ε / 3) (erfSaddleWidth δ ε / 2) (x / 2)
        ?_ ?_ ?_ ?_ ?_ hδ2
      · linarith
      · linarith
      · linarith
      · exact hσpos
      · exact hwidth
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, abs_zero] at hδx
      linarith
    have hsign : Real.sign (x / 2) = Real.sign x := sign_div_two x hx0
    have hsignabs : |Real.sign x| = 1 := by
      rcases lt_trichotomy x 0 with hneg | hzero | hpos
      · rw [Real.sign_of_neg hneg]; norm_num
      · exact absurd hzero hx0
      · rw [Real.sign_of_pos hpos]; norm_num
    have hPerr : |(chebyshevSaddleTruncation c J).eval (x / 2) - Real.sign x| ≤ 2 * (ε / 3) := by
      have h1 := abs_sub_le ((chebyshevSaddleTruncation c J).eval (x / 2))
        (smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)) (Real.sign x)
      have h2 : |(chebyshevSaddleTruncation c J).eval (x / 2)
          - smoothedSign (erfSaddleWidth δ ε / 2) (x / 2)| ≤ ε / 3 := by
        have h := herr (x / 2) hx2
        rw [abs_sub_comm] at h
        exact h
      have h3 : |smoothedSign (erfSaddleWidth δ ε / 2) (x / 2) - Real.sign x| ≤ ε / 3 := by
        rw [← hsign]
        exact hgap
      linarith
    rw [nearOptimalSignTable_eval]
    have hApos : (0 : ℝ) < 1 / (1 + ε / 3) := by positivity
    have hAle : 1 / (1 + ε / 3) ≤ 1 := by
      have h1 : (0 : ℝ) < 1 + ε / 3 := by linarith
      exact (div_le_iff₀ h1).2 (by linarith)
    calc |(1 / (1 + ε / 3)) * (chebyshevSaddleTruncation c J).eval (x / 2) - Real.sign x|
        = |(1 / (1 + ε / 3)) * ((chebyshevSaddleTruncation c J).eval (x / 2) - Real.sign x)
            + ((1 / (1 + ε / 3) - 1) * Real.sign x)| := by
              congr 1
              ring
      _ ≤ (1 / (1 + ε / 3)) * |(chebyshevSaddleTruncation c J).eval (x / 2) - Real.sign x|
            + |(1 / (1 + ε / 3) - 1) * Real.sign x| := by
              have h1 := abs_add_le ((1 / (1 + ε / 3))
                  * ((chebyshevSaddleTruncation c J).eval (x / 2) - Real.sign x))
                ((1 / (1 + ε / 3) - 1) * Real.sign x)
              rw [abs_mul, abs_of_pos hApos] at h1
              exact h1
      _ ≤ (1 / (1 + ε / 3)) * (2 * (ε / 3)) + (1 - 1 / (1 + ε / 3)) * 1 := by
              have h1 := mul_le_mul_of_nonneg_left hPerr hApos.le
              have h2 : |(1 / (1 + ε / 3) - 1) * Real.sign x|
                  = 1 - 1 / (1 + ε / 3) := by
                rw [abs_mul, abs_of_nonpos (by linarith), hsignabs]
                ring
              linarith
      _ = ε / (1 + ε / 3) := by field_simp; ring
      _ ≤ ε := by
        have h1 : (0 : ℝ) < 1 + ε / 3 := by linarith
        apply (div_le_iff₀ h1).2
        have hsq : 0 ≤ ε * ε := mul_nonneg hε.le hε.le
        nlinarith

  have hoddS : ∀ x : ℝ, (nearOptimalSignTable c J ε).eval (-x)
      = -(nearOptimalSignTable c J ε).eval x := by
    intro x
    exact nearOptimalSignTable_odd c J ε hodd x

  have hdegS : ((nearOptimalSignTable c J ε).natDegree : ℝ)
      ≤ C * (1 + (1 / δ) * Real.log (1 / ε)) := by
    have h1 := nearOptimalSignTable_degree_le c J ε
    have h2 : ((nearOptimalSignTable c J ε).natDegree : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast h1
    linarith
  unfold NearOptimalSignApproximation
  exact ⟨hC, hδ, hε, hnorm, herr2, hoddS, hdegS⟩

/-- Every `NearOptimalSignApproximation` satisfies the boundedness, gap error, and oddness
conditions of `SignApproximation`. -/
theorem nearOptimalSign_approximation {C δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ ε S) : SignApproximation S δ ε :=
  ⟨hS.2.2.2.1, hS.2.2.2.2.1, hS.2.2.2.2.2.1⟩

/-- A near-optimal sign approximation yields the printed rectangle bands when the translated
threshold and error parameters satisfy the stated interior and scaling conditions. -/
theorem nearOptimalSign_printedRectangle {C δ ε : ℝ} {S : Polynomial ℝ}
    (hS : NearOptimalSignApproximation C δ ε S) {ε' t : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε') (hε2 : ε' ≤ 1 / 2)
    (ht0 : δ ≤ t) (ht1 : t ≤ 1 - δ)
    (hσ : (1 - ε' / 2) * ε ≤ ε' / 2) :
    PrintedRectangleBand (rectanglePolynomial S (ε' / 2) t) ε' δ t :=
  twoTranslateRectanglePrintedBands (S := S) (δ' := δ) (ε' := ε') (σ := ε) (t := t)
    hδ hε hε2 ht0 ht1 hσ (nearOptimalSign_approximation hS)

/-- For positive `β`, the reciprocal 1/(1 − exp(−β)) is at most 1 + 1/β. -/
theorem one_div_one_sub_exp_le (β : ℝ) (hβ : 0 < β) :
    1 / (1 - Real.exp (-β)) ≤ 1 + 1 / β := by
  have hexp : 1 + β ≤ Real.exp β := by
    simpa only [_root_.add_comm] using! (Real.add_one_le_exp β)
  have hden : 0 < 1 - Real.exp (-β) := by
    have hlt : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hβ)
    linarith
  have h1 : Real.exp (-β) ≤ 1 / (1 + β) := by
    rw [Real.exp_neg]
    have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 1 + β) hexp
    simpa using! h
  have h3 : β / (1 + β) ≤ 1 - Real.exp (-β) := by
    have hmin : 1 - Real.exp (-β) ≥ 1 - 1 / (1 + β) := by linarith
    have hid : 1 - 1 / (1 + β) = β / (1 + β) := by
      field_simp
      ring
    linarith
  have h4 : β ≤ (1 - Real.exp (-β)) * (1 + β) := by
    have hpos : (0 : ℝ) ≤ 1 + β := by linarith
    have hmul := mul_le_mul_of_nonneg_right h3 hpos
    have hid : β / (1 + β) * (1 + β) = β := by
      field_simp
    nlinarith [hmul, hid]
  have h6 : (1 - Real.exp (-β)) * (1 + 1 / β) ≥ 1 := by
    have hid2 : (1 - Real.exp (-β)) * (1 + 1 / β)
        = ((1 - Real.exp (-β)) * (1 + β)) / β := by
      field_simp
      ring
    rw [hid2]
    have hz : 1 ≤ ((1 - Real.exp (-β)) * (1 + β)) / β :=
      (le_div_iff₀ hβ).mpr (by linarith [h4])
    linarith
  exact (div_le_iff₀' hden).mpr (by simpa [mul_comm] using! h6)

/-- Bounds every finite Gaussian coefficient tail after `J` by M exp(−a(J + 1)²)(1 + 1/(a(2J +
3))) for nonnegative `M` and positive `a`. -/
theorem chebyshevSaddleDecay_tail_le_uniform {M a : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    (hM : 0 ≤ M) (ha : 0 < a)
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2))) :
    ∑ i ∈ Finset.range n, |c (J + 1 + i)| ≤
      M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3))) := by
  have hstep : ∀ i : ℕ,
      ((J + 1 : ℝ) + i) ^ 2 ≥ (J + 1 : ℝ) ^ 2 + (2 * (J : ℝ) + 3) * i := by
    intro i
    have h1 : ((J + 1 : ℝ) + i) ^ 2 = (J + 1 : ℝ) ^ 2 + 2 * (J + 1 : ℝ) * i + i ^ 2 := by
      ring
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [hi]
      simp
    · have hle : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hmul : (0 : ℝ) ≤ i * (i - 1) :=
        mul_nonneg (by exact_mod_cast hi.le) (by linarith)
      have hsq : (0 : ℝ) ≤ i ^ 2 - i := by nlinarith
      linarith
  have hexp : ∀ i : ℕ, Real.exp (-(a * (((J + 1 : ℝ) + i) ^ 2)))
      ≤ Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * Real.exp (-(a * ((2 * (J : ℝ) + 3) * i))) := by
    intro i
    have hsq := hstep i
    have ha0 : (0 : ℝ) ≤ a := ha.le
    have hmul := mul_le_mul_of_nonneg_left hsq ha0
    have h1 : -(a * (((J + 1 : ℝ) + i) ^ 2))
        ≤ -(a * ((J + 1 : ℝ)) ^ 2) + -(a * ((2 * (J : ℝ) + 3) * i)) := by
      linarith
    have h2 := Real.exp_le_exp.mpr h1
    rw [Real.exp_add] at h2
    exact h2
  have hq : Real.exp (-(a * (2 * (J : ℝ) + 3))) < 1 := by
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos ha (by positivity)))
  have hqne : Real.exp (-(a * (2 * (J : ℝ) + 3))) ≠ 1 := ne_of_lt hq
  have hden : (0 : ℝ) < 1 - Real.exp (-(a * (2 * (J : ℝ) + 3))) := by linarith
  have hstep' : ∀ i : ℕ, Real.exp (-(a * ((2 * (J : ℝ) + 3) * i)))
      = (Real.exp (-(a * (2 * (J : ℝ) + 3)))) ^ i := by
    intro i
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsum : ∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 3) * i)))
      ≤ 1 / (1 - Real.exp (-(a * (2 * (J : ℝ) + 3)))) := by
    rw [Finset.sum_congr rfl (fun i _ => hstep' i), geom_sum_eq hqne]
    have hpow : (0 : ℝ) ≤ (Real.exp (-(a * (2 * (J : ℝ) + 3)))) ^ n :=
      pow_nonneg (Real.exp_pos _).le n
    refine div_le_div_of_nonneg_right (by linarith) hden.le
  have hnonneg : (0 : ℝ) ≤ M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) :=
    mul_nonneg hM (Real.exp_pos _).le
  calc
    ∑ i ∈ Finset.range n, |c (J + 1 + i)|
        ≤ ∑ i ∈ Finset.range n, M * Real.exp (-(a * (((J + 1 : ℝ) + i) ^ 2))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hc (J + 1 + i)
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h
          exact h
    _ ≤ ∑ i ∈ Finset.range n,
        (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * Real.exp (-(a * ((2 * (J : ℝ) + 3) * i)))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc M * Real.exp (-(a * (((J + 1 : ℝ) + i) ^ 2)))
              ≤ M * (Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))
                  * Real.exp (-(a * ((2 * (J : ℝ) + 3) * i)))) := by
                have hle := mul_le_mul_of_nonneg_left (hexp i) hM
                exact hle
            _ = M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))
                * Real.exp (-(a * ((2 * (J : ℝ) + 3) * i))) := by ring
    _ = (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)))
        * (∑ i ∈ Finset.range n, Real.exp (-(a * ((2 * (J : ℝ) + 3) * i)))) := by
          rw [Finset.mul_sum]
    _ ≤ (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)))
        * (1 / (1 - Real.exp (-(a * (2 * (J : ℝ) + 3))))) := by
          have hle := mul_le_mul_of_nonneg_left hsum hnonneg
          exact hle
    _ ≤ (M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)))
        * (1 + 1 / (a * (2 * (J : ℝ) + 3))) := by
          have hle := mul_le_mul_of_nonneg_left
            (one_div_one_sub_exp_le (a * (2 * (J : ℝ) + 3)) (by positivity)) hnonneg
          convert! hle using 1

/-- The assumed finite Chebyshev representation has truncation error at most `ε` when its
coefficients have Gaussian decay and the uniform tail budget holds. -/
theorem chebyshevSaddleTruncation_error_of_budget_uniform {M a ε : ℝ} {c : ℕ → ℝ}
    {J n : ℕ} {x : ℝ} {v : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a)
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)))
    (hbudget : M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3)))
      ≤ ε)
    (hx : |x| ≤ 1)
    (hrepr : v = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |v - (chebyshevSaddleTruncation c J).eval x| ≤ ε := by
  refine (chebyshevSaddleTruncation_error_le_of_repr hx hrepr).trans ?_
  exact (chebyshevSaddleDecay_tail_le_uniform hM ha hc).trans hbudget

/-- The logarithmic tail budget log(3M/ε) + log(1 + 1/(3a)) used to choose a truncation level. -/
def saddleLevelBudget (a M ε : ℝ) : ℝ :=
  Real.log (3 * M / ε) + Real.log (1 + 1 / (3 * a))

/-- The natural ceiling of the square root of `saddleLevelBudget a M ε / a`, plus one. -/
def saddleLevel (a M ε : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (saddleLevelBudget a M ε / a)) + 1

/-- For positive rate, amplitude, and error with 3M/ε ≥ 1, the chosen saddle level makes the
uniform Gaussian tail budget at most ε/3. -/
theorem saddleLevel_budget {a M ε : ℝ} (ha : 0 < a) (hM : 0 < M) (hε : 0 < ε)
    (h1 : 1 ≤ 3 * M / ε) :
    M * Real.exp (-(a * (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2)) *
      (1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3))) ≤ ε / 3 := by
  have hu0 : 0 ≤ saddleLevelBudget a M ε := by
    have hA : 0 ≤ Real.log (3 * M / ε) := Real.log_nonneg h1
    have hB : 0 ≤ Real.log (1 + 1 / (3 * a)) := by
      have hpos : (0 : ℝ) < 1 / (3 * a) := by positivity
      have hle : (1 : ℝ) ≤ 1 + 1 / (3 * a) := by linarith
      exact Real.log_nonneg hle
    simp only [saddleLevelBudget]
    linarith
  have hratio : 0 ≤ saddleLevelBudget a M ε / a :=
    div_nonneg hu0 ha.le
  have hsq0 : 0 ≤ Real.sqrt (saddleLevelBudget a M ε / a) := Real.sqrt_nonneg _
  have hceil : (Nat.ceil (Real.sqrt (saddleLevelBudget a M ε / a)) : ℝ)
      ≤ Real.sqrt (saddleLevelBudget a M ε / a) + 1 := by
    have h := Nat.ceil_lt_add_one hsq0
    exact le_of_lt h
  have hJge : Real.sqrt (saddleLevelBudget a M ε / a) ≤ (saddleLevel a M ε : ℝ) := by
    rw [saddleLevel, Nat.cast_add, Nat.cast_one]
    have h := Nat.le_ceil (Real.sqrt (saddleLevelBudget a M ε / a))
    linarith
  have hJ1 : Real.sqrt (saddleLevelBudget a M ε / a) + 2
      ≤ (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) := by
    rw [saddleLevel, Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    have h := Nat.le_ceil (Real.sqrt (saddleLevelBudget a M ε / a))
    linarith
  have hsq2 : (Real.sqrt (saddleLevelBudget a M ε / a) + 2) ^ 2
      ≤ (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hJ1
  have hsq3 : Real.sqrt (saddleLevelBudget a M ε / a) ^ 2
      = saddleLevelBudget a M ε / a := Real.sq_sqrt hratio
  have hmain : a * (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2
      ≥ saddleLevelBudget a M ε := by
    have hmul := mul_le_mul_of_nonneg_left hsq2 ha.le
    have hid : a * (Real.sqrt (saddleLevelBudget a M ε / a) + 2) ^ 2
        = saddleLevelBudget a M ε + 4 * a * Real.sqrt (saddleLevelBudget a M ε / a) + 4 * a := by
      have hsq' : (Real.sqrt (saddleLevelBudget a M ε / a) + 2) ^ 2
          = saddleLevelBudget a M ε / a + 4 * Real.sqrt (saddleLevelBudget a M ε / a) + 4 := by
        nlinarith [hsq3]
      rw [hsq']
      field_simp [ha.ne']
    have hpos : (0 : ℝ) ≤ a * Real.sqrt (saddleLevelBudget a M ε / a) :=
      mul_nonneg ha.le (Real.sqrt_nonneg _)
    linarith
  have hexp : Real.exp (-(a * (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2))
      ≤ Real.exp (-saddleLevelBudget a M ε) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpref : 1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3)) ≤ 1 + 1 / (3 * a) := by
    have hp : (0 : ℝ) < a * (2 * (saddleLevel a M ε : ℕ) + 3) := by positivity
    have h2 : 3 * a ≤ a * (2 * (saddleLevel a M ε : ℕ) + 3) := by
      have hle : (3 : ℝ) ≤ 2 * (saddleLevel a M ε : ℕ) + 3 := by
        have hn : (0 : ℝ) ≤ (saddleLevel a M ε : ℕ) := Nat.cast_nonneg _
        linarith
      nlinarith [ha.le]
    have h3 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 3 * a) h2
    linarith
  have hfinal : M * Real.exp (-saddleLevelBudget a M ε) * (1 + 1 / (3 * a)) = ε / 3 := by
    have hA : 0 < 3 * M / ε := by
      have h := div_pos (mul_pos (by norm_num : (0 : ℝ) < 3) hM) hε
      linarith
    have hB : 0 < 1 + 1 / (3 * a) := by positivity
    have h1 : Real.exp (-Real.log (3 * M / ε)) = ε / (3 * M) := by
      rw [Real.exp_neg, Real.exp_log hA]
      field_simp [hM.ne', hε.ne']
    have h2 : Real.exp (-Real.log (1 + 1 / (3 * a))) = 1 / (1 + 1 / (3 * a)) := by
      rw [Real.exp_neg, Real.exp_log hB, inv_eq_one_div]
    have h3 : Real.exp (-saddleLevelBudget a M ε)
        = Real.exp (-Real.log (3 * M / ε)) * Real.exp (-Real.log (1 + 1 / (3 * a))) := by
      rw [show -saddleLevelBudget a M ε
          = -Real.log (3 * M / ε) + -Real.log (1 + 1 / (3 * a)) by
        simp only [saddleLevelBudget]
        ring, Real.exp_add]
    rw [h3, h1, h2]
    field_simp [hM.ne', hε.ne']
  have hA : M * Real.exp (-(a * (((saddleLevel a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2)) *
          (1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3)))
      ≤ M * Real.exp (-saddleLevelBudget a M ε) *
          (1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3))) := by
    have hle := mul_le_mul_of_nonneg_left hexp hM.le
    have h2 := mul_le_mul_of_nonneg_right hle
      (by positivity : (0 : ℝ) ≤ 1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3)))
    exact h2
  have hB : M * Real.exp (-saddleLevelBudget a M ε) *
          (1 + 1 / (a * (2 * (saddleLevel a M ε : ℕ) + 3)))
      ≤ M * Real.exp (-saddleLevelBudget a M ε) * (1 + 1 / (3 * a)) := by
    have hnonneg : (0 : ℝ) ≤ M * Real.exp (-saddleLevelBudget a M ε) :=
      mul_nonneg hM.le (Real.exp_pos _).le
    have hle := mul_le_mul_of_nonneg_left hpref hnonneg
    exact hle
  exact hA.trans (hB.trans (le_of_eq hfinal))

/-- Under the stated rate and logarithm hypotheses, the saddle level is at most
√(`saddleLevelBudget a M ε / a`) + 2. -/
theorem saddleLevel_deg_le {a M ε : ℝ} (ha : 0 < a) (h1 : 1 ≤ 3 * M / ε) :
    (saddleLevel a M ε : ℝ) ≤
      Real.sqrt (saddleLevelBudget a M ε / a) + 2 := by
  have hratio : 0 ≤ saddleLevelBudget a M ε / a :=
    div_nonneg (by
      have hA : 0 ≤ Real.log (3 * M / ε) := Real.log_nonneg h1
      have hB : 0 ≤ Real.log (1 + 1 / (3 * a)) := by
        have hpos : (0 : ℝ) < 1 / (3 * a) := by positivity
        have hle : (1 : ℝ) ≤ 1 + 1 / (3 * a) := by linarith
        exact Real.log_nonneg hle
      simp only [saddleLevelBudget]
      linarith) ha.le
  have hsq0 : 0 ≤ Real.sqrt (saddleLevelBudget a M ε / a) := Real.sqrt_nonneg _
  have hceil : (Nat.ceil (Real.sqrt (saddleLevelBudget a M ε / a)) : ℝ)
      ≤ Real.sqrt (saddleLevelBudget a M ε / a) + 1 := by
    have h := Nat.ceil_lt_add_one hsq0
    exact le_of_lt h
  rw [saddleLevel, Nat.cast_add, Nat.cast_one]
  linarith

/-- The decay rate δ²/(128 log(6/ε)) associated with the selected smoothing width. -/
def saddleWidthDecayRate (δ ε : ℝ) : ℝ := δ ^ 2 / (128 * Real.log (6 / ε))

/-- For 0 < ε ≤ 1/2, the selected decay rate equals `saddleDecayRate` of half the saddle width. -/
theorem saddleWidthDecayRate_eq {δ ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    saddleWidthDecayRate δ ε = saddleDecayRate (erfSaddleWidth δ ε / 2) := by
  have hL6 : 0 < Real.log (6 / ε) := by
    have h1 : (1 : ℝ) < 6 / ε := (lt_div_iff₀ hε).2 (by linarith)
    exact Real.log_pos h1
  have hsq : (Real.sqrt (Real.log (6 / ε)) : ℝ) ^ 2 = Real.log (6 / ε) :=
    Real.sq_sqrt hL6.le
  unfold saddleWidthDecayRate saddleDecayRate erfSaddleWidth
  have hne : Real.log (6 / ε) ≠ 0 := ne_of_gt hL6
  field_simp [hne]
  nlinarith [hsq]

/-- At the selected width-dependent rate, the saddle level is at most √(128 log(6/ε)(log(3M/ε) +
log(1 + 128 log(6/ε)/(3δ²))))/δ + 2 under the stated hypotheses. -/
theorem saddleLevel_deg_le_of_width {δ ε M : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (h1 : 1 ≤ 3 * M / ε) :
    (saddleLevel (saddleWidthDecayRate δ ε) M ε : ℝ) ≤
      Real.sqrt (128 * Real.log (6 / ε) *
        (Real.log (3 * M / ε) +
          Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)))) / δ + 2 := by
  have hL6 : 0 < Real.log (6 / ε) := by
    have h1' : (1 : ℝ) < 6 / ε := (lt_div_iff₀ hε).2 (by linarith)
    exact Real.log_pos h1'
  have ha : 0 < saddleWidthDecayRate δ ε := by
    unfold saddleWidthDecayRate
    positivity
  have hbudget : saddleLevelBudget (saddleWidthDecayRate δ ε) M ε
      = Real.log (3 * M / ε) +
        Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)) := by
    simp only [saddleLevelBudget, saddleWidthDecayRate]
    have hne : (3 * δ ^ 2 : ℝ) ≠ 0 := by positivity
    have hL6ne : Real.log (6 / ε) ≠ 0 := ne_of_gt hL6
    congr 1
    field_simp
  have hB : 0 ≤ Real.log (3 * M / ε) +
      Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)) := by
    have hA : 0 ≤ Real.log (3 * M / ε) := Real.log_nonneg h1
    have hC : 0 ≤ Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)) := by
      have hpos : (0 : ℝ) < 128 * Real.log (6 / ε) / (3 * δ ^ 2) := by positivity
      have hle : (1 : ℝ) ≤ 1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2) := by linarith
      exact Real.log_nonneg hle
    linarith
  have hX : 0 ≤ 128 * Real.log (6 / ε) *
      (Real.log (3 * M / ε) + Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2))) :=
    mul_nonneg (by positivity) hB
  have hsqrt : Real.sqrt (saddleLevelBudget (saddleWidthDecayRate δ ε) M ε
        / saddleWidthDecayRate δ ε)
      = Real.sqrt (128 * Real.log (6 / ε) *
          (Real.log (3 * M / ε) +
            Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)))) / δ := by
    have hnum : 0 ≤ saddleLevelBudget (saddleWidthDecayRate δ ε) M ε := by
      rw [hbudget]
      exact hB
    have hRHS : 0 ≤ Real.sqrt (128 * Real.log (6 / ε) *
        (Real.log (3 * M / ε) +
          Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)))) / δ := by
      have hsq : (0 : ℝ) ≤ Real.sqrt (128 * Real.log (6 / ε) *
          (Real.log (3 * M / ε) +
            Real.log (1 + 128 * Real.log (6 / ε) / (3 * δ ^ 2)))) := Real.sqrt_nonneg _
      positivity
    rw [Real.sqrt_eq_iff_eq_sq (div_nonneg hnum ha.le) hRHS, div_pow, Real.sq_sqrt hX]
    rw [hbudget]
    unfold saddleWidthDecayRate
    rw [div_div_eq_mul_div]
    ring
  have hmain := saddleLevel_deg_le (a := saddleWidthDecayRate δ ε) (M := M) (ε := ε) ha h1
  rw [hsqrt] at hmain
  exact hmain

/-- States the weighted Gaussian coefficient bound |c j| ≤ M exp(−a j²)/(j + 1). -/
def chebyshevSaddleDecayWeighted (M a : ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)) / ((j : ℝ) + 1)

/-- The weighted Gaussian decay hypothesis bounds the finite tail after `J` by the uniform
Gaussian tail expression divided by J + 2. -/
theorem chebyshevSaddleDecayWeighted_tail_le {M a : ℝ} {c : ℕ → ℝ} {J n : ℕ}
    (hM : 0 ≤ M) (ha : 0 < a)
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)) / ((j : ℝ) + 1)) :
    ∑ i ∈ Finset.range n, |c (J + 1 + i)| ≤
      M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3)))
        / ((J + 2 : ℝ)) := by
  have hgauss : ∀ j : ℕ,
      |Real.exp (-(a * (j : ℝ) ^ 2))| ≤ 1 * Real.exp (-(a * (j : ℝ) ^ 2)) := by
    intro j
    rw [abs_of_nonneg (Real.exp_pos _).le]
    simp
  have hsum := chebyshevSaddleDecay_tail_le_uniform (M := 1) (a := a)
    (c := fun j : ℕ => Real.exp (-(a * (j : ℝ) ^ 2))) (J := J) (n := n)
    (by norm_num) ha hgauss
  have hterm : ∀ i ∈ Finset.range n,
      |c (J + 1 + i)|
        ≤ (M / ((J + 2 : ℝ))) * |Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2))| := by
    intro i _
    have h1 := hc (J + 1 + i)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one] at h1
    have hge : (J + 2 : ℝ) ≤ (J + 1 : ℝ) + i + 1 := by
      have hnat : J + 2 ≤ J + 1 + i + 1 := by omega
      exact_mod_cast hnat
    have hD1 : (0 : ℝ) < (J + 1 : ℝ) + i + 1 := by positivity
    have hD2 : (0 : ℝ) < (J + 2 : ℝ) := by positivity
    have h2 : M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 1 : ℝ) + i + 1)
        ≤ M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 2 : ℝ)) := by
      refine (div_le_iff₀ hD1).2 ?_
      have hid : (M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 2 : ℝ)))
          * ((J + 2 : ℝ)) = M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) := by
        field_simp
      have hmul : (M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 2 : ℝ)))
          * ((J + 2 : ℝ))
          ≤ (M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 2 : ℝ)))
          * ((J + 1 : ℝ) + i + 1) :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      linarith
    calc
      |c (J + 1 + i)|
          ≤ M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 1 : ℝ) + i + 1) := h1
      _ ≤ M * Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2)) / ((J + 2 : ℝ)) := h2
      _ = (M / ((J + 2 : ℝ)))
          * |Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2))| := by
        rw [abs_of_nonneg (Real.exp_pos _).le]
        ring
  calc
    ∑ i ∈ Finset.range n, |c (J + 1 + i)|
        ≤ ∑ i ∈ Finset.range n,
            (M / ((J + 2 : ℝ))) * |Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2))| := by
          refine Finset.sum_le_sum fun i hi => hterm i hi
    _ = (M / ((J + 2 : ℝ)))
          * ∑ i ∈ Finset.range n, |Real.exp (-(a * ((J + 1 : ℝ) + i) ^ 2))| := by
          rw [Finset.mul_sum]
    _ ≤ (M / ((J + 2 : ℝ)))
          * (1 * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          convert! hsum using 1
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          simp [Nat.cast_add]
    _ = M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3)))
          / ((J + 2 : ℝ)) := by ring

/-- The assumed finite Chebyshev representation has error at most `ε` when weighted Gaussian
decay and the stated weighted tail budget hold. -/
theorem chebyshevSaddleTruncation_error_of_budget_weighted {M a ε : ℝ} {c : ℕ → ℝ}
    {J n : ℕ} {x : ℝ} {v : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a)
    (hc : ∀ j : ℕ, |c j| ≤ M * Real.exp (-(a * (j : ℝ) ^ 2)) / ((j : ℝ) + 1))
    (hbudget : M * Real.exp (-(a * ((J + 1 : ℝ)) ^ 2))
          * (1 + 1 / (a * (2 * (J : ℝ) + 3))) / ((J + 2 : ℝ)) ≤ ε)
    (hx : |x| ≤ 1)
    (hrepr : v = (chebyshevSaddleTruncation c J).eval x
      + ∑ i ∈ Finset.range n,
          c (J + 1 + i) * (Polynomial.Chebyshev.T ℝ ((J + 1 + i : ℕ) : ℤ)).eval x) :
    |v - (chebyshevSaddleTruncation c J).eval x| ≤ ε := by
  refine (chebyshevSaddleTruncation_error_le_of_repr hx hrepr).trans ?_
  exact (chebyshevSaddleDecayWeighted_tail_le hM ha hc).trans hbudget

/-- The weighted logarithmic tail budget log(3M(1 + √a)/ε) + 1. -/
def saddleLevelBudgetWeighted (a M ε : ℝ) : ℝ :=
  Real.log (3 * M * (1 + Real.sqrt a) / ε) + 1

/-- The natural ceiling of the square root of the weighted tail budget divided by `a`, plus one. -/
def saddleLevelWeighted (a M ε : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (saddleLevelBudgetWeighted a M ε / a)) + 1

/-- For positive rate, amplitude, and error satisfying the logarithm hypothesis, the weighted
saddle level makes the weighted tail bound at most ε/3. -/
theorem saddleLevelWeighted_budget {a M ε : ℝ} (ha : 0 < a) (hM : 0 < M) (hε : 0 < ε)
    (h1 : 1 ≤ 3 * M * (1 + Real.sqrt a) / ε) :
    M * Real.exp (-(a * (((saddleLevelWeighted a M ε : ℕ) + 1 : ℕ) : ℝ) ^ 2)) *
      (1 + 1 / (a * (2 * (saddleLevelWeighted a M ε : ℕ) + 3)))
      / (((saddleLevelWeighted a M ε : ℕ) + 2 : ℕ) : ℝ) ≤ ε / 3 := by
  set J : ℕ := saddleLevelWeighted a M ε with hJ
  set u : ℝ := saddleLevelBudgetWeighted a M ε with hu
  have hu1 : 1 ≤ u := by
    have hlog : (0 : ℝ) ≤ Real.log (3 * M * (1 + Real.sqrt a) / ε) := Real.log_nonneg h1
    simp only [hu, saddleLevelBudgetWeighted]
    linarith
  have hratio : 0 ≤ u / a := div_nonneg (by linarith) ha.le
  have hsq0 : 0 ≤ Real.sqrt (u / a) := Real.sqrt_nonneg _
  have hJexact : (J : ℝ) = (Nat.ceil (Real.sqrt (u / a)) : ℝ) + 1 := by
    rw [hJ, saddleLevelWeighted, hu, Nat.cast_add, Nat.cast_one]
  have hJ1 : Real.sqrt (u / a) + 2 ≤ ((J + 1 : ℕ) : ℝ) := by
    have hle : Real.sqrt (u / a) ≤ (Nat.ceil (Real.sqrt (u / a)) : ℝ) := Nat.le_ceil _
    have hcast : ((J + 1 : ℕ) : ℝ) = (Nat.ceil (Real.sqrt (u / a)) : ℝ) + 2 := by
      rw [Nat.cast_add, hJexact]
      ring
    linarith
  have hsq2 : (Real.sqrt (u / a) + 2) ^ 2 ≤ ((J + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hJ1
  have hsq3 : Real.sqrt (u / a) ^ 2 = u / a := Real.sq_sqrt hratio
  have hmain : a * ((J + 1 : ℕ) : ℝ) ^ 2 ≥ u := by
    have hmul := mul_le_mul_of_nonneg_left hsq2 ha.le
    have hid : a * (Real.sqrt (u / a) + 2) ^ 2 = u + 4 * a * Real.sqrt (u / a) + 4 * a := by
      have hsq' : (Real.sqrt (u / a) + 2) ^ 2 = u / a + 4 * Real.sqrt (u / a) + 4 := by
        nlinarith [hsq3]
      rw [hsq']
      field_simp [ha.ne']
    have hpos : (0 : ℝ) ≤ a * Real.sqrt (u / a) :=
      mul_nonneg ha.le (Real.sqrt_nonneg _)
    linarith
  have hX : 1 ≤ a * ((J + 2 : ℕ) : ℝ) ^ 2 := by
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ ((J + 2 : ℕ) : ℝ) := by
      have hnat : J + 1 ≤ J + 2 := by omega
      exact_mod_cast hnat
    have hsq : ((J + 1 : ℕ) : ℝ) ^ 2 ≤ ((J + 2 : ℕ) : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 h2
    have hmul := mul_le_mul_of_nonneg_left hsq ha.le
    linarith
  have hsqrtX : 1 ≤ Real.sqrt (a * ((J + 2 : ℕ) : ℝ) ^ 2) := Real.one_le_sqrt.mpr hX
  have hsqrtX' : Real.sqrt (a * ((J + 2 : ℕ) : ℝ) ^ 2) = Real.sqrt a * ((J + 2 : ℕ) : ℝ) := by
    have hsq : a * ((J + 2 : ℕ) : ℝ) ^ 2 = (Real.sqrt a * ((J + 2 : ℕ) : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hone : 1 ≤ Real.sqrt a * ((J + 2 : ℕ) : ℝ) := by
    rw [← hsqrtX']
    exact hsqrtX
  have hdiv1 : 1 / ((J + 2 : ℕ) : ℝ) ≤ Real.sqrt a := by
    refine (div_le_iff₀ (by positivity : (0 : ℝ) < ((J + 2 : ℕ) : ℝ))).2 ?_
    linarith
  have hge : 2 * (J : ℝ) + 3 ≥ ((J + 2 : ℕ) : ℝ) := by
    have hnat : 2 * J + 3 ≥ J + 2 := by omega
    exact_mod_cast hnat
  have hden : (0 : ℝ) < a * (2 * (J : ℝ) + 3) * ((J + 2 : ℕ) : ℝ) := by positivity
  have hdiv2 : 1 / (a * (2 * (J : ℝ) + 3) * ((J + 2 : ℕ) : ℝ)) ≤ 1 := by
    refine (div_le_iff₀ hden).2 ?_
    have hle : 1 ≤ a * (2 * (J : ℝ) + 3) * ((J + 2 : ℕ) : ℝ) := by
      have h2 : ((J + 2 : ℕ) : ℝ) ≤ 2 * (J : ℝ) + 3 := hge
      have hmul := mul_le_mul_of_nonneg_left h2 ha.le
      have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ ((J + 2 : ℕ) : ℝ))
      linarith
    simpa using! hle
  have hpref : (1 + 1 / (a * (2 * (J : ℝ) + 3))) / ((J + 2 : ℕ) : ℝ) ≤ Real.sqrt a + 1 := by
    have hsplit : (1 + 1 / (a * (2 * (J : ℝ) + 3))) / ((J + 2 : ℕ) : ℝ)
        = 1 / ((J + 2 : ℕ) : ℝ) + 1 / (a * (2 * (J : ℝ) + 3) * ((J + 2 : ℕ) : ℝ)) := by
      field_simp
    rw [hsplit]
    exact add_le_add hdiv1 hdiv2
  have hexp : Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp (-u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hu0 : (0 : ℝ) < 3 * M * (1 + Real.sqrt a) / ε := by positivity
  have honexp : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_neg]
    have hge1 : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      norm_num at h
      linarith
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < Real.exp 1)).2 hge1
  have hexpu : M * Real.exp (-u) * (Real.sqrt a + 1) ≤ ε / 3 := by
    have hu' : u = Real.log (3 * M * (1 + Real.sqrt a) / ε) + 1 := by
      simp only [hu, saddleLevelBudgetWeighted]
    have hkey : Real.exp (-u)
        = (ε / (3 * M * (1 + Real.sqrt a))) * Real.exp (-1) := by
      rw [hu', show -(Real.log (3 * M * (1 + Real.sqrt a) / ε) + 1)
          = -Real.log (3 * M * (1 + Real.sqrt a) / ε) + (-1) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hu0, inv_eq_one_div]
      field_simp
    rw [hkey]
    have hmain2 : M * (ε / (3 * M * (1 + Real.sqrt a)) * Real.exp (-1))
          * (Real.sqrt a + 1) = ε * Real.exp (-1) / 3 := by
        field_simp
        ring
    rw [hmain2]
    have hle : ε * Real.exp (-1) ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left honexp (by positivity : (0 : ℝ) ≤ ε)
    have h1' : (ε * Real.exp (-1)) / 3 ≤ (ε * 1) / 3 :=
      div_le_div_of_nonneg_right hle (by norm_num)
    simpa using! h1'
  calc
    M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2)) * (1 + 1 / (a * (2 * (J : ℝ) + 3)))
        / ((J + 2 : ℕ) : ℝ)
        = M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2))
            * ((1 + 1 / (a * (2 * (J : ℝ) + 3))) / ((J + 2 : ℕ) : ℝ)) := by ring
    _ ≤ M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2)) * (Real.sqrt a + 1) := by
      exact mul_le_mul_of_nonneg_left hpref (mul_nonneg hM.le (Real.exp_pos _).le)
    _ ≤ M * Real.exp (-u) * (Real.sqrt a + 1) := by
      have h3 : M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2)) ≤ M * Real.exp (-u) :=
        mul_le_mul_of_nonneg_left hexp hM.le
      calc
        M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2)) * (Real.sqrt a + 1)
            = (Real.sqrt a + 1) * (M * Real.exp (-(a * ((J + 1 : ℕ) : ℝ) ^ 2))) := by ring
        _ ≤ (Real.sqrt a + 1) * (M * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = M * Real.exp (-u) * (Real.sqrt a + 1) := by ring
    _ ≤ ε / 3 := hexpu

/-- Under the stated positive-rate and logarithm hypotheses, the weighted saddle level is at
most the square root of its budget divided by `a`, plus two. -/
theorem saddleLevelWeighted_deg_le {a M ε : ℝ} (ha : 0 < a)
    (h1 : 1 ≤ 3 * M * (1 + Real.sqrt a) / ε) :
    (saddleLevelWeighted a M ε : ℝ) ≤ Real.sqrt (saddleLevelBudgetWeighted a M ε / a) + 2 := by
  have hratio : 0 ≤ saddleLevelBudgetWeighted a M ε / a :=
    div_nonneg (by
      have hlog : (0 : ℝ) ≤ Real.log (3 * M * (1 + Real.sqrt a) / ε) := Real.log_nonneg h1
      simp only [saddleLevelBudgetWeighted]
      linarith) ha.le
  have hsq0 : 0 ≤ Real.sqrt (saddleLevelBudgetWeighted a M ε / a) := Real.sqrt_nonneg _
  have hceil : (Nat.ceil (Real.sqrt (saddleLevelBudgetWeighted a M ε / a)) : ℝ)
      ≤ Real.sqrt (saddleLevelBudgetWeighted a M ε / a) + 1 := by
    have h := Nat.ceil_lt_add_one hsq0
    exact le_of_lt h
  rw [saddleLevelWeighted, Nat.cast_add, Nat.cast_one]
  linarith

/-- At the selected width-dependent rate, the weighted saddle level is at most √(128
log(6/ε)(log(3M(1 + δ/√(128 log(6/ε)))/ε) + 1))/δ + 2 under the stated hypotheses. -/
theorem saddleLevelWeighted_deg_le_of_width {δ ε M : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2)
    (h1 : 1 ≤ 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) :
    (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℝ) ≤
      Real.sqrt (128 * Real.log (6 / ε) *
        (Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1)) / δ + 2 := by
  have hL6 : 0 < Real.log (6 / ε) := by
    have h1' : (1 : ℝ) < 6 / ε := (lt_div_iff₀ hε).2 (by linarith)
    exact Real.log_pos h1'
  have ha : 0 < saddleWidthDecayRate δ ε := by
    unfold saddleWidthDecayRate
    positivity
  have hsqrtDecay : Real.sqrt (saddleWidthDecayRate δ ε)
      = δ / Real.sqrt (128 * Real.log (6 / ε)) := by
    unfold saddleWidthDecayRate
    rw [Real.sqrt_div (by positivity) (128 * Real.log (6 / ε)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hδ.le]
  have hbudget : saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
      = Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1 := by
    simp only [saddleLevelBudgetWeighted, hsqrtDecay]
  have hB : 0 ≤ Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1 := by
    have hA : 0 ≤ Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) :=
      Real.log_nonneg h1
    linarith
  have hX : 0 ≤ 128 * Real.log (6 / ε) *
      (Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1) :=
    mul_nonneg (by positivity) hB
  have hsqrt : Real.sqrt (saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
        / saddleWidthDecayRate δ ε)
      = Real.sqrt (128 * Real.log (6 / ε) *
          (Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1)) / δ := by
    have hnum : 0 ≤ saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε := by
      rw [hbudget]
      exact hB
    have hRHS : 0 ≤ Real.sqrt (128 * Real.log (6 / ε) *
        (Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1)) / δ := by
      have hsq : (0 : ℝ) ≤ Real.sqrt (128 * Real.log (6 / ε) *
          (Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1)) :=
        Real.sqrt_nonneg _
      positivity
    rw [Real.sqrt_eq_iff_eq_sq (div_nonneg hnum ha.le) hRHS, div_pow, Real.sq_sqrt hX]
    rw [hbudget]
    unfold saddleWidthDecayRate
    rw [div_div_eq_mul_div]
    ring
  have hmain := saddleLevelWeighted_deg_le (a := saddleWidthDecayRate δ ε) (M := M) (ε := ε)
    ha (by simpa [hsqrtDecay] using! h1)
  rw [hsqrt] at hmain
  exact hmain

/-- An explicit positive degree constant depending on the coefficient amplitude, defined as the
maximum of two and a logarithmic square-root expression. -/
noncomputable def nearOptimalSignConstant (M : ℝ) : ℝ :=
  max 2 (Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
    * (1 + (Real.log (6 * M) + 1) / Real.log 2)))

/-- The degree constant `nearOptimalSignConstant M` is positive for every real `M`. -/
theorem nearOptimalSignConstant_pos (M : ℝ) : 0 < nearOptimalSignConstant M := by
  unfold nearOptimalSignConstant
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- For M ≥ 1, 0 < δ ≤ 2, and 0 < ε ≤ 1/2, the weighted saddle level satisfies the degree budget
`nearOptimalSignConstant M` times 1 + δ⁻¹ log(ε⁻¹). -/
theorem saddleLevelWeighted_deg_le_contract {δ ε M : ℝ} (hM : 1 ≤ M)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℝ) ≤
      nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε)) := by
  have hMpos : 0 < M := by linarith
  have hlog2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]

  have hTge : Real.log 2 ≤ Real.log (1 / ε) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hε]
    nlinarith
  have hTpos : 0 < Real.log (1 / ε) := lt_of_lt_of_le hlog2 hTge

  have hLpos : 0 < Real.log (6 / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε]
    linarith
  have hLsplit : Real.log (6 / ε) = Real.log 6 + Real.log (1 / ε) := by
    rw [show (6 : ℝ) / ε = 6 * (1 / ε) by ring,
      Real.log_mul (by norm_num) (by positivity)]

  have hlog6pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hK2pos : 0 < 1 + Real.log 6 / Real.log 2 := by
    have hpos : 0 < Real.log 6 / Real.log 2 := div_pos hlog6pos hlog2
    linarith
  have hLle : Real.log (6 / ε) ≤ (1 + Real.log 6 / Real.log 2) * Real.log (1 / ε) := by
    rw [hLsplit]
    have hkey : Real.log 6 ≤ (Real.log 6 / Real.log 2) * Real.log (1 / ε) := by
      have hmul := mul_le_mul_of_nonneg_left hTge (div_pos hlog6pos hlog2).le
      rwa [div_mul_cancel₀ _ hlog2.ne'] at hmul
    have hexp : (1 + Real.log 6 / Real.log 2) * Real.log (1 / ε)
        = Real.log (1 / ε) + (Real.log 6 / Real.log 2) * Real.log (1 / ε) := by ring
    rw [hexp]
    linarith

  have hLbig : (1 : ℝ) / 32 ≤ Real.log (6 / ε) := by
    rw [hLsplit]
    have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith [Real.log_two_gt_d9, hTpos]
  have hsqrtL : (2 : ℝ) ≤ Real.sqrt (128 * Real.log (6 / ε)) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    refine Real.sqrt_le_sqrt ?_
    linarith
  have hsqrtLpos : 0 < Real.sqrt (128 * Real.log (6 / ε)) :=
    Real.sqrt_pos.2 (by linarith)
  have hx1 : δ / Real.sqrt (128 * Real.log (6 / ε)) ≤ 1 := by
    rw [div_le_one hsqrtLpos]
    linarith
  have hx0 : 0 ≤ δ / Real.sqrt (128 * Real.log (6 / ε)) :=
    div_nonneg hδ.le hsqrtLpos.le

  have h1 : 1 ≤ 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε := by
    have hN : (3 : ℝ) ≤ 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) := by
      have h3M : (3 : ℝ) ≤ 3 * M := by linarith
      have h1x : (1 : ℝ) ≤ 1 + δ / Real.sqrt (128 * Real.log (6 / ε)) := by linarith
      nlinarith
    rw [le_div_iff₀ hε]
    nlinarith

  have hsqrtDecay : Real.sqrt (saddleWidthDecayRate δ ε)
      = δ / Real.sqrt (128 * Real.log (6 / ε)) := by
    unfold saddleWidthDecayRate
    rw [Real.sqrt_div (by positivity) (128 * Real.log (6 / ε)),
      Real.sqrt_sq_eq_abs, abs_of_nonneg hδ.le]
  have hu_eq : saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
      = Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) + 1 := by
    simp only [saddleLevelBudgetWeighted, hsqrtDecay]

  have hlog6M0 : 0 ≤ Real.log (6 * M) := Real.log_nonneg (by nlinarith)
  have hu_le : saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
      ≤ (1 + (Real.log (6 * M) + 1) / Real.log 2) * Real.log (1 / ε) := by
    rw [hu_eq]
    have hargpos : 0 < 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε := by positivity
    have hx2 : 1 + δ / Real.sqrt (128 * Real.log (6 / ε)) ≤ 2 := by linarith
    have hmul : 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) ≤ 6 * M := by
      nlinarith [hMpos, hx0]
    have harg_le : 3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε ≤ 6 * M / ε :=
      div_le_div_of_nonneg_right hmul hε.le
    have hlog_le : Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε)
        ≤ Real.log (6 * M) + Real.log (1 / ε) := by
      have h := Real.log_le_log hargpos harg_le
      have hsplit : Real.log (6 * M / ε) = Real.log (6 * M) + Real.log (1 / ε) := by
        rw [show (6 : ℝ) * M / ε = (6 * M) * (1 / ε) by ring,
          Real.log_mul (by positivity) (by positivity)]
      linarith
    have hkey : Real.log (6 * M) + 1
        ≤ ((Real.log (6 * M) + 1) / Real.log 2) * Real.log (1 / ε) := by
      have hnonneg : 0 ≤ Real.log (6 * M) + 1 := by linarith
      have hmul2 := mul_le_mul_of_nonneg_left hTge (div_nonneg hnonneg hlog2.le)
      rwa [div_mul_cancel₀ _ hlog2.ne'] at hmul2
    have hexp : (1 + (Real.log (6 * M) + 1) / Real.log 2) * Real.log (1 / ε)
        = Real.log (1 / ε) + ((Real.log (6 * M) + 1) / Real.log 2) * Real.log (1 / ε) := by
      ring
    rw [hexp]
    linarith

  have hdeg := saddleLevelWeighted_deg_le_of_width (δ := δ) (ε := ε) (M := M) hδ hε hε2 h1
  rw [← hu_eq] at hdeg

  have hu0 : 0 ≤ saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε := by
    rw [hu_eq]
    have : 0 ≤ Real.log (3 * M * (1 + δ / Real.sqrt (128 * Real.log (6 / ε))) / ε) :=
      Real.log_nonneg h1
    linarith
  have hprod : Real.log (6 / ε) * saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
      ≤ (1 + Real.log 6 / Real.log 2) * (1 + (Real.log (6 * M) + 1) / Real.log 2)
        * Real.log (1 / ε) ^ 2 := by
    have h1' := mul_le_mul hLle hu_le hu0 (mul_nonneg hK2pos.le hTpos.le)
    have hEq : ((1 + Real.log 6 / Real.log 2) * Real.log (1 / ε))
        * ((1 + (Real.log (6 * M) + 1) / Real.log 2) * Real.log (1 / ε))
        = (1 + Real.log 6 / Real.log 2) * (1 + (Real.log (6 * M) + 1) / Real.log 2)
          * Real.log (1 / ε) ^ 2 := by ring
    linarith [h1', hEq]
  have hprod128 : 128 * Real.log (6 / ε)
        * saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε
      ≤ 128 * (1 + Real.log 6 / Real.log 2) * (1 + (Real.log (6 * M) + 1) / Real.log 2)
        * Real.log (1 / ε) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 128)
    linarith [hmul]
  have hKpos : 0 ≤ (1 + (Real.log (6 * M) + 1) / Real.log 2) := by
    have hdiv : 0 ≤ (Real.log (6 * M) + 1) / Real.log 2 := div_nonneg (by linarith) hlog2.le
    linarith
  have hK2K0 : 0 ≤ 128 * (1 + Real.log 6 / Real.log 2)
      * (1 + (Real.log (6 * M) + 1) / Real.log 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hK2pos.le) hKpos
  have hsqrtBound : Real.sqrt (128 * Real.log (6 / ε)
        * saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε)
      ≤ Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
          * (1 + (Real.log (6 * M) + 1) / Real.log 2)) * Real.log (1 / ε) := by
    have h := Real.sqrt_le_sqrt hprod128
    rw [Real.sqrt_mul hK2K0 (Real.log (1 / ε) ^ 2), Real.sqrt_sq hTpos.le] at h
    exact h

  have hC : Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
        * (1 + (Real.log (6 * M) + 1) / Real.log 2)) ≤ nearOptimalSignConstant M := by
    unfold nearOptimalSignConstant
    exact le_max_right _ _
  have h2le : (2 : ℝ) ≤ nearOptimalSignConstant M := by
    unfold nearOptimalSignConstant
    exact le_max_left _ _
  have hstep : Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
        * (1 + (Real.log (6 * M) + 1) / Real.log 2)) * Real.log (1 / ε) / δ + 2
      ≤ nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε)) := by
    have hmul := mul_le_mul_of_nonneg_right hC (div_nonneg hTpos.le hδ.le)
    have hEq : Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
          * (1 + (Real.log (6 * M) + 1) / Real.log 2)) * (Real.log (1 / ε) / δ)
        = Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
          * (1 + (Real.log (6 * M) + 1) / Real.log 2)) * Real.log (1 / ε) / δ := by ring
    have hfin : nearOptimalSignConstant M * (Real.log (1 / ε) / δ) + 2
        ≤ nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε)) := by
      have hEq3 : nearOptimalSignConstant M * (Real.log (1 / ε) / δ)
          = nearOptimalSignConstant M * ((1 / δ) * Real.log (1 / ε)) := by ring
      have hexp : nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε))
          = nearOptimalSignConstant M
            + nearOptimalSignConstant M * ((1 / δ) * Real.log (1 / ε)) := by ring
      rw [hEq3, hexp]
      linarith
    rw [← hEq]
    linarith [hmul, hfin]
  calc (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℝ)
      ≤ Real.sqrt (128 * Real.log (6 / ε)
          * saddleLevelBudgetWeighted (saddleWidthDecayRate δ ε) M ε) / δ + 2 := hdeg
    _ ≤ Real.sqrt (128 * (1 + Real.log 6 / Real.log 2)
          * (1 + (Real.log (6 * M) + 1) / Real.log 2)) * Real.log (1 / ε) / δ + 2 := by
        have hdiv := div_le_div_of_nonneg_right hsqrtBound hδ.le
        linarith
    _ ≤ nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε)) := hstep

/-- The assumed finite representation, weighted Gaussian coefficient decay, and vanishing even
coefficients yield a near-optimal sign table with degree constant `nearOptimalSignConstant
M`. -/
theorem nearOptimalSign_of_weightedDecay {c : ℕ → ℝ} {M δ ε : ℝ} {n : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hrepr : ∀ y : ℝ, |y| ≤ 1 →
      smoothedSign (erfSaddleWidth δ ε / 2) y =
        (chebyshevSaddleTruncation c
            (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε)).eval y
        + ∑ i ∈ Finset.range n,
            c (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε + 1 + i)
              * (Polynomial.Chebyshev.T ℝ
                  (((saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε + 1 + i : ℕ)) : ℤ)).eval y)
    (hdecay : chebyshevSaddleDecayWeighted M (saddleWidthDecayRate δ ε) c)
    (hodd : ∀ j : ℕ, Even j → c j = 0) :
    NearOptimalSignApproximation (nearOptimalSignConstant M) δ ε
      (nearOptimalSignTable c (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε) ε) := by
  have hMpos : 0 < M := by linarith
  have hlog6 : 0 < Real.log (6 / ε) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hε]
    linarith
  have ha : 0 < saddleWidthDecayRate δ ε := by
    unfold saddleWidthDecayRate
    positivity
  have h1 : 1 ≤ 3 * M * (1 + Real.sqrt (saddleWidthDecayRate δ ε)) / ε := by
    have hN : (3 : ℝ) ≤ 3 * M * (1 + Real.sqrt (saddleWidthDecayRate δ ε)) := by
      have h3M : (3 : ℝ) ≤ 3 * M := by linarith
      have h1x : (1 : ℝ) ≤ 1 + Real.sqrt (saddleWidthDecayRate δ ε) := by
        have hnn := Real.sqrt_nonneg (saddleWidthDecayRate δ ε)
        linarith
      nlinarith
    rw [le_div_iff₀ hε]
    nlinarith
  have htail : ∑ i ∈ Finset.range n,
      |c (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε + 1 + i)| ≤ ε / 3 := by
    have hdecay' : ∀ j : ℕ,
        |c j| ≤ M * Real.exp (-(saddleWidthDecayRate δ ε * (j : ℝ) ^ 2)) / ((j : ℝ) + 1) :=
      hdecay
    have hbudget := saddleLevelWeighted_budget (a := saddleWidthDecayRate δ ε) (M := M)
      (ε := ε) ha hMpos hε h1
    have hbudget' : M * Real.exp (-(saddleWidthDecayRate δ ε
          * (((saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℕ) : ℝ) + 1) ^ 2))
        * (1 + 1 / (saddleWidthDecayRate δ ε
            * (2 * (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℕ) + 3)))
        / (((saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℕ) : ℝ) + 2) ≤ ε / 3 := by
      simpa [Nat.cast_add, Nat.cast_one] using! hbudget
    have hsum := chebyshevSaddleDecayWeighted_tail_le (M := M)
      (a := saddleWidthDecayRate δ ε) (c := c)
      (J := saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε) (n := n)
      hMpos.le ha hdecay'
    exact hsum.trans hbudget'
  have hdeg : (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε : ℝ)
      ≤ nearOptimalSignConstant M * (1 + (1 / δ) * Real.log (1 / ε)) :=
    saddleLevelWeighted_deg_le_contract hM hδ hδ2 hε hε2
  exact nearOptimalSign_of_saddle (C := nearOptimalSignConstant M)
    (J := saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε) (n := n)
    (nearOptimalSignConstant_pos M) hδ hε hε2 hrepr htail hodd hdeg

/-- The squared norm of each natural-order Chebyshev polynomial with respect to
`Polynomial.Chebyshev.measureT` is positive. -/
theorem integral_T_sq_measureT_pos (j : ℕ) :
    0 < ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
      * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x ∂Polynomial.Chebyshev.measureT := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have h : (∫ x, (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x
        * (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x
          ∂Polynomial.Chebyshev.measureT) = Real.pi := by
      simpa using! Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    rw [h]
    exact Real.pi_pos
  · have h : (∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
        * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
          ∂Polynomial.Chebyshev.measureT) = Real.pi / 2 := by
      simpa using! Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hj.ne'
    rw [h]
    exact half_pos Real.pi_pos

/-- The coefficient obtained by projecting `g` onto the order-`j` Chebyshev polynomial and
dividing by its squared norm with respect to `measureT`. -/
noncomputable def chebyshevProjection (g : ℝ → ℝ) (j : ℕ) : ℝ :=
  (∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x * g x ∂Polynomial.Chebyshev.measureT) /
    ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
      * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x ∂Polynomial.Chebyshev.measureT

/-- The Chebyshev inner-product integral equals the projection coefficient times the squared
norm of the corresponding Chebyshev polynomial. -/
theorem integral_T_mul_eq_chebyshevProjection_mul (g : ℝ → ℝ) (j : ℕ) :
    ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x * g x ∂Polynomial.Chebyshev.measureT
      = chebyshevProjection g j
        * ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
            * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x ∂Polynomial.Chebyshev.measureT := by
  rw [chebyshevProjection]
  exact (div_mul_cancel₀ _ (ne_of_gt (integral_T_sq_measureT_pos j))).symm

/-- The projection coefficient times the Chebyshev squared norm equals the cosine-weighted
integral of `g (Real.cos θ)` over [0, π]. -/
theorem chebyshevProjection_mul_integral_T_sq (g : ℝ → ℝ) (j : ℕ) :
    chebyshevProjection g j
        * ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x
            * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x ∂Polynomial.Chebyshev.measureT
      = ∫ θ in (0 : ℝ)..Real.pi, g (Real.cos θ) * Real.cos ((j : ℝ) * θ) := by
  rw [← integral_T_mul_eq_chebyshevProjection_mul g j,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [Polynomial.Chebyshev.T_real_cos]
  push_cast
  ring

/-- A vanishing inner-product integral forces the corresponding Chebyshev projection coefficient
to vanish. -/
theorem chebyshevProjection_eq_zero_of_integral_eq_zero (g : ℝ → ℝ) (j : ℕ)
    (h : ∫ x, (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval x * g x
      ∂Polynomial.Chebyshev.measureT = 0) :
    chebyshevProjection g j = 0 := by
  rw [chebyshevProjection, h, zero_div]

/-- Every even-order Chebyshev projection coefficient of an odd real function vanishes. -/
theorem chebyshevProjection_eq_zero_of_odd_of_even {g : ℝ → ℝ}
    (hg : ∀ x, g (-x) = -g x) (j : ℕ) (hj : Even j) :
    chebyshevProjection g j = 0 := by
  refine chebyshevProjection_eq_zero_of_integral_eq_zero g j ?_
  rw [Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  have hanti : ∀ θ : ℝ,
      (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos (Real.pi - θ))
          * g (Real.cos (Real.pi - θ))
        = -((Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) * g (Real.cos θ)) := by
    intro θ
    have hcos : Real.cos (Real.pi - θ) = -Real.cos θ := Real.cos_pi_sub θ
    have hT : (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (-Real.cos θ)
        = (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) := by
      rw [Polynomial.Chebyshev.T_eval_neg]
      have h1 : (((j : ℤ).negOnePow : ℤ) : ℝ) = 1 := by
        rw [negOnePow_natCast_even j hj]
        norm_num
      rw [h1, one_mul]
    rw [hcos, hT, hg]
    ring
  have hcomp := intervalIntegral.integral_comp_sub_left
    (f := fun θ : ℝ => (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (Real.cos θ) * g (Real.cos θ))
    (a := (0 : ℝ)) (b := Real.pi) Real.pi
  simp_rw [hanti] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  simp only [sub_self, sub_zero] at hcomp
  linarith

/-- Every even-order Chebyshev projection coefficient of the smoothed sign vanishes. -/
theorem chebyshevProjection_smoothedSign_even (σ : ℝ) (j : ℕ) (hj : Even j) :
    chebyshevProjection (fun x => smoothedSign σ x) j = 0 :=
  chebyshevProjection_eq_zero_of_odd_of_even (fun x => smoothedSign_neg σ x) j hj

/-- The assumed finite representation by Chebyshev projections of the smoothed sign and their
weighted Gaussian decay yield a near-optimal sign table. Oddness supplies the vanishing even
coefficients. -/
theorem nearOptimalSign_of_weightedDecay_projections {M δ ε : ℝ} {n : ℕ}
    (hM : 1 ≤ M) (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hrepr : ∀ y : ℝ, |y| ≤ 1 →
      smoothedSign (erfSaddleWidth δ ε / 2) y =
        (chebyshevSaddleTruncation
            (chebyshevProjection (fun x => smoothedSign (erfSaddleWidth δ ε / 2) x))
            (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε)).eval y
        + ∑ i ∈ Finset.range n,
            chebyshevProjection (fun x => smoothedSign (erfSaddleWidth δ ε / 2) x)
                (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε + 1 + i)
              * (Polynomial.Chebyshev.T ℝ
                  ((saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε + 1 + i : ℕ) : ℤ)).eval y)
    (hdecay : chebyshevSaddleDecayWeighted M (saddleWidthDecayRate δ ε)
      (chebyshevProjection (fun x => smoothedSign (erfSaddleWidth δ ε / 2) x))) :
    NearOptimalSignApproximation (nearOptimalSignConstant M) δ ε
      (nearOptimalSignTable
        (chebyshevProjection (fun x => smoothedSign (erfSaddleWidth δ ε / 2) x))
        (saddleLevelWeighted (saddleWidthDecayRate δ ε) M ε) ε) :=
  nearOptimalSign_of_weightedDecay hM hδ hδ2 hε hε2 hrepr hdecay
    (fun j hj => chebyshevProjection_smoothedSign_even (erfSaddleWidth δ ε / 2) j hj)

end Qatlib.Concepts.QsvtCore.ApproxToolkit
