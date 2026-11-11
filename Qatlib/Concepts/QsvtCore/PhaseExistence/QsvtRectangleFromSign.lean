/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore
import Qatlib.Concepts.ChoiKraus.ChoiKrausChar.ChannelStructure
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.LinearAlgebra.Lagrange

/-!
# Rational Chebyshev rectangle approximations

`rectPoly` builds even rectangle approximants from a quantitative `SignFamily`. The module
controls degree and approximation bands, then rounds coefficients of an even Chebyshev expansion
to obtain rational coefficients with a bit-width bound.

`clause38_of_sign` packages the construction under a sign-family constant at most 32 and the
expansion hypothesis `EvenChebExpansionBound`. See [GilyenSuLowWiebe2019].

## Main statements

* `rect_of_sign`: construct rectangle bands from a sign family.
* `evenChebSeries_rounded_dist`: bound evaluation error from dyadic coefficient rounding.
* `clause38_of_sign`: produce rational Chebyshev coefficients within the degree and bit budgets.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped BigOperators

namespace Qatlib.Concepts.QsvtCore.PhaseExistence
/-- The ceiling binary logarithm of the sum of the absolute numerator and positive denominator
of a rational number. -/
def ratBitWidth (q : ℚ) : ℕ := Nat.clog 2 (q.num.natAbs + q.den)
/-- The finite Chebyshev series with coefficients `c k` on the even-indexed polynomials `T (2 *
k)` for `k < l`. -/
noncomputable def evenChebSeries (c : ℕ → ℝ) (l : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range l, Polynomial.C (c k) *
    (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ))
/-- The rectangle degree budget `64 * ceil (1 / δ') * (ceil (log₂ (1 / ε')) + 1)`. -/
noncomputable def rectangleDegreeBudget (δ' ε' : ℝ) : ℕ :=
  64 * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (1 / ε')) + 1)
/-- The coefficient bit budget obtained from the binary logarithms of `2 / ε` and `d + 2`, with
four additional bits. -/
noncomputable def familyCoeffBits (d : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (2 / ε)) + Nat.ceil (Real.logb 2 ((d : ℝ) + 2)) + 4
end Qatlib.Concepts.QsvtCore.PhaseExistence
namespace Qatlib.Concepts.QsvtCore.PhaseExistence.S1_QSVT_CORE
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
set_option autoImplicit false
open Polynomial Real
noncomputable section

/-- The existence, for positive gap and error parameters with error at most one half, of odd
sign approximants bounded on `[-2, 2]` with the prescribed logarithmic degree bound. -/
def SignFamily (Cs : ℕ) : Prop :=
  ∀ (μ θ : ℝ), 0 < μ → 0 < θ → θ ≤ 1 / 2 →
    ∃ S : Polynomial ℝ,
      S.natDegree ≤ Cs * Nat.ceil (1 / μ) * (Nat.ceil (Real.logb 2 (1 / θ)) + 1) ∧
      (∀ x : ℝ, S.eval (-x) = -S.eval x) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, |S.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, μ ≤ |x| → |S.eval x - Real.sign x| ≤ θ)
end
noncomputable section

/-- The polynomial `(1 - ε') / 2 * (S(X + t) + S(t - X)) + ε' / 2` used for rectangle
approximation. -/
def rectPoly (S : Polynomial ℝ) (t ε' : ℝ) : Polynomial ℝ :=
  C ((1 - ε') / 2) * (S.comp (X + C t) + S.comp (C t - X)) + C (ε' / 2)
end
noncomputable section

/-- Evaluation of `rectPoly` is the scaled sum of the two shifted evaluations of `S`, plus the
offset. -/
theorem rectPoly_eval {S : Polynomial ℝ} {t ε' x : ℝ} :
    (rectPoly S t ε').eval x =
      (1 - ε') / 2 * (S.eval (x + t) + S.eval (t - x)) + ε' / 2 := by
  simp only [rectPoly, eval_add, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
end
noncomputable section

/-- The polynomial `rectPoly S t ε'` is even as a function on the real line. -/
theorem rectPoly_eval_neg {S : Polynomial ℝ} {t ε' x : ℝ} :
    (rectPoly S t ε').eval (-x) = (rectPoly S t ε').eval x := by
  rw [rectPoly_eval, rectPoly_eval]
  have h1 : (-x + t : ℝ) = t - x := by ring
  have h2 : (t - -x : ℝ) = x + t := by ring
  rw [h1, h2]
  ring
end
noncomputable section

/-- The natural degree of `rectPoly S t ε'` is at most the natural degree of `S`. -/
theorem rectPoly_natDegree_le {S : Polynomial ℝ} {t ε' : ℝ} :
    (rectPoly S t ε').natDegree ≤ S.natDegree := by
  have hcomp : (S.comp (X + C t) + S.comp (C t - X)).natDegree ≤ S.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_comp]
      have h1 : (X + C t : Polynomial ℝ).natDegree = 1 := by
        rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp [natDegree_C]
      rw [h1, mul_one]
    · rw [natDegree_comp]
      have h1 : (C t - X : Polynomial ℝ).natDegree = 1 := by
        have h : C t - X = -(X - C t) := by ring
        rw [h, natDegree_neg, natDegree_X_sub_C]
      rw [h1, mul_one]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ (by simp [natDegree_C]))
  by_cases hε : ((1 - ε') / 2 : ℝ) = 0
  · have hC : (C ((1 - ε') / 2 : ℝ) : Polynomial ℝ) = 0 := by rw [hε]; simp
    rw [hC, zero_mul]
    exact Nat.zero_le _
  · rw [natDegree_C_mul hε]
    exact hcomp
end
noncomputable section

/-- The rectangle polynomial has absolute value at most one on `[-1, 1]` under the given bound
on `S` and parameter constraints. -/
theorem rectPoly_abs_le_one {S : Polynomial ℝ} {t ε' x : ℝ}
    (hbound : ∀ y ∈ Set.Icc (-2 : ℝ) 2, |S.eval y| ≤ 1)
    (ht : |t| ≤ 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hε'0 : 0 ≤ ε') (hε' : ε' ≤ 1 / 2) :
    |(rectPoly S t ε').eval x| ≤ 1 := by
  have ht1 : t ≤ 1 := (abs_le.mp ht).2
  have ht2 : -1 ≤ t := (abs_le.mp ht).1
  have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have b1 := abs_le.mp (hbound _ hmem1)
  have b2 := abs_le.mp (hbound _ hmem2)
  rw [rectPoly_eval]
  have hsum : S.eval (x + t) + S.eval (t - x) ≤ 2 := by linarith [b1.2, b2.2]
  have hsum' : -2 ≤ S.eval (x + t) + S.eval (t - x) := by linarith [b1.1, b2.1]
  have hc : 0 ≤ (1 - ε' : ℝ) / 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc
  have hmul' := mul_le_mul_of_nonneg_left hsum' hc
  have e1 : ((1 - ε') / 2 : ℝ) * 2 = 1 - ε' := by ring
  have e2 : ((1 - ε') / 2 : ℝ) * (-2) = -(1 - ε') := by ring
  rw [e1] at hmul
  rw [e2] at hmul'
  rw [abs_le]
  constructor <;> nlinarith
end
noncomputable section

/-- On the inner band `|x| ≤ t - δ'`, the rectangle polynomial lies between `1 - ε'` and one
under the stated sign approximation hypotheses. -/
theorem rectPoly_inner {S : Polynomial ℝ} {t δ' ε' x : ℝ}
    (hbound : ∀ y ∈ Set.Icc (-2 : ℝ) 2, |S.eval y| ≤ 1)
    (hsign : ∀ y ∈ Set.Icc (-2 : ℝ) 2, δ' ≤ |y| → |S.eval y - Real.sign y| ≤ ε' / 4)
    (hδ' : 0 < δ') (hδt : δ' ≤ t) (ht : |t| ≤ 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hband : |x| ≤ t - δ') (hc : 0 ≤ (1 - ε' : ℝ) / 2) :
    1 - ε' ≤ (rectPoly S t ε').eval x ∧ (rectPoly S t ε').eval x ≤ 1 := by
  have hxle : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hxt : δ' ≤ x + t := by
    rcases le_total 0 x with h | h
    · nlinarith [abs_le.mp hband, abs_le.mp hxle]
    · nlinarith [abs_le.mp hband, abs_le.mp hxle]
  have htx : δ' ≤ t - x := by
    rcases le_total 0 x with h | h
    · nlinarith [abs_le.mp hband, abs_le.mp hxle]
    · nlinarith [abs_le.mp hband, abs_le.mp hxle]
  have ht1 : t ≤ 1 := (abs_le.mp ht).2
  have ht2 : -1 ≤ t := (abs_le.mp ht).1
  have hxl : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hxle
  have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
  have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
  have hgap1 : δ' ≤ |x + t| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hgap2 : δ' ≤ |t - x| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hs1 := hsign _ hmem1 hgap1
  have hs2 := hsign _ hmem2 hgap2
  have hb1 := hbound _ hmem1
  have hb2 := hbound _ hmem2
  rw [Real.sign_of_pos (by linarith : (0:ℝ) < x + t)] at hs1
  rw [Real.sign_of_pos (by linarith : (0:ℝ) < t - x)] at hs2
  have h1lo : 1 - ε' / 4 ≤ S.eval (x + t) := by have := (abs_le.mp hs1).1; linarith
  have h2lo : 1 - ε' / 4 ≤ S.eval (t - x) := by have := (abs_le.mp hs2).1; linarith
  have h1hi : S.eval (x + t) ≤ 1 := (abs_le.mp hb1).2
  have h2hi : S.eval (t - x) ≤ 1 := (abs_le.mp hb2).2
  rw [rectPoly_eval]
  constructor
  · have hsum : (1 - ε' / 4) + (1 - ε' / 4) ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hc
    nlinarith
  · have hsum : S.eval (x + t) + S.eval (t - x) ≤ 1 + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hc
    nlinarith
end
noncomputable section

/-- On the outer bands `t + δ' ≤ |x|`, the rectangle polynomial lies between zero and `ε'` under
the stated sign approximation hypotheses. -/
theorem rectPoly_outer {S : Polynomial ℝ} {t δ' ε' x : ℝ}
    (hbound : ∀ y ∈ Set.Icc (-2 : ℝ) 2, |S.eval y| ≤ 1)
    (hsign : ∀ y ∈ Set.Icc (-2 : ℝ) 2, δ' ≤ |y| → |S.eval y - Real.sign y| ≤ ε' / 4)
    (hδ' : 0 < δ') (hδt : δ' ≤ t) (ht : |t| ≤ 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hband : t + δ' ≤ |x|) (hc : 0 ≤ (1 - ε' : ℝ) / 2) :
    0 ≤ (rectPoly S t ε').eval x ∧ (rectPoly S t ε').eval x ≤ ε' := by
  have hxle : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  rcases le_total 0 x with hpos | hneg
  · have hxg : t + δ' ≤ x := by rwa [abs_of_nonneg hpos] at hband
    have ht1 : t ≤ 1 := (abs_le.mp ht).2
    have ht2 : -1 ≤ t := (abs_le.mp ht).1
    have hxl : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hxle
    have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
    have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
    have hgap1 : δ' ≤ |x + t| := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x + t)]; linarith
    have hgap2 : δ' ≤ |t - x| := by
      rw [abs_of_nonpos (by linarith : t - x ≤ 0)]; linarith
    have hs1 := hsign _ hmem1 hgap1
    have hs2 := hsign _ hmem2 hgap2
    have hb1 := hbound _ hmem1
    have hb2 := hbound _ hmem2
    rw [Real.sign_of_pos (by linarith : (0:ℝ) < x + t)] at hs1
    rw [Real.sign_of_neg (by linarith : t - x < 0)] at hs2
    have h1lo : 1 - ε' / 4 ≤ S.eval (x + t) := by have := (abs_le.mp hs1).1; linarith
    have h1hi : S.eval (x + t) ≤ 1 := (abs_le.mp hb1).2
    have h2lo : -1 ≤ S.eval (t - x) := (abs_le.mp hb2).1
    have h2hi : S.eval (t - x) ≤ -1 + ε' / 4 := by have := (abs_le.mp hs2).2; linarith
    rw [rectPoly_eval]
    constructor
    · have hsum : -ε' / 4 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum hc
      nlinarith
    · have hsum : S.eval (x + t) + S.eval (t - x) ≤ ε' / 4 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum hc
      nlinarith
  · have hxg : x ≤ -(t + δ') := by
      have : |x| = -x := abs_of_nonpos hneg
      rw [this] at hband
      linarith
    have ht1 : t ≤ 1 := (abs_le.mp ht).2
    have ht2 : -1 ≤ t := (abs_le.mp ht).1
    have hxl : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hxle
    have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
    have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
        ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.1, hxl.2]⟩
    have hgap1 : δ' ≤ |x + t| := by
      rw [abs_of_nonpos (by linarith : x + t ≤ 0)]; linarith
    have hgap2 : δ' ≤ |t - x| := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - x)]; linarith
    have hs1 := hsign _ hmem1 hgap1
    have hs2 := hsign _ hmem2 hgap2
    have hb1 := hbound _ hmem1
    have hb2 := hbound _ hmem2
    rw [Real.sign_of_neg (by linarith : x + t < 0)] at hs1
    rw [Real.sign_of_pos (by linarith : (0:ℝ) < t - x)] at hs2
    have h1lo : -1 ≤ S.eval (x + t) := (abs_le.mp hb1).1
    have h1hi : S.eval (x + t) ≤ -1 + ε' / 4 := by have := (abs_le.mp hs1).2; linarith
    have h2lo : 1 - ε' / 4 ≤ S.eval (t - x) := by have := (abs_le.mp hs2).1; linarith
    have h2hi : S.eval (t - x) ≤ 1 := (abs_le.mp hb2).2
    rw [rectPoly_eval]
    constructor
    · have hsum : -ε' / 4 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum hc
      nlinarith
    · have hsum : S.eval (x + t) + S.eval (t - x) ≤ ε' / 4 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsum hc
      nlinarith
end
noncomputable section

/-- Evenness, a uniform bound on `[-1, 1]`, and the specified inner and outer rectangle
approximation bounds. -/
def RectBands (P : Polynomial ℝ) (δ' ε' t : ℝ) : Prop :=
  (∀ x : ℝ, P.eval (-x) = P.eval x) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, -t + δ' ≤ x → x ≤ t - δ' →
      1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≤ -t - δ' ∨ t + δ' ≤ x →
      0 ≤ P.eval x ∧ P.eval x ≤ ε')
end
noncomputable section

/-- The zero polynomial satisfies `RectBands` when the inner band is empty and the error
parameter is nonnegative. -/
theorem rectBands_zero {δ' ε' t : ℝ} (h : t < δ') (hε' : 0 ≤ ε') :
    RectBands 0 δ' ε' t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x _
    simp
  · intro x _ h1 h2
    exfalso
    nlinarith
  · intro x _ _
    simp [hε']
end
noncomputable section

/-- A quantitative sign family supplies a rectangle polynomial satisfying `RectBands` with the
stated degree bound for the given gap, error, and threshold. -/
theorem rect_of_sign {Cs : ℕ} (hs : SignFamily Cs)
    (δ' ε' t : ℝ) (hδ' : 0 < δ') (hδ'2 : δ' ≤ 1 / 2) (hε' : 0 < ε') (hε'2 : ε' ≤ 1 / 2)
    (ht : |t| ≤ 1) :
    ∃ P : Polynomial ℝ,
      P.natDegree ≤ Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) ∧
      RectBands P δ' ε' t := by
  rcases lt_or_ge t δ' with hlt | hge
  · refine ⟨0, ?_, rectBands_zero hlt (by linarith)⟩
    exact Nat.zero_le _
  · have hθ : (0:ℝ) < ε' / 4 := by linarith
    have hθ2 : (ε' / 4 : ℝ) ≤ 1 / 2 := by linarith
    obtain ⟨S, hdeg, hodd, hbound, hsign⟩ := hs δ' (ε' / 4) hδ' hθ hθ2
    refine ⟨rectPoly S t ε', ?_, ?_, ?_, ?_, ?_⟩
    · refine (rectPoly_natDegree_le).trans ?_
      refine le_trans hdeg ?_
      have hlog : (Real.logb 2 (1 / (ε' / 4)) : ℝ) = Real.logb 2 (4 / ε') := by
        rw [one_div_div]
      rw [hlog]
    · intro x
      exact rectPoly_eval_neg
    · intro x hx
      exact rectPoly_abs_le_one hbound ht hx (by linarith) (by linarith)
    · intro x hx h1 h2
      have hband : |x| ≤ t - δ' := by
        rw [abs_le]
        constructor <;> linarith
      exact rectPoly_inner hbound hsign hδ' hge ht hx hband (by linarith)
    · intro x hx hor
      have hband : t + δ' ≤ |x| := by
        rcases hor with h | h
        · rw [abs_of_nonpos (by linarith : x ≤ 0)]; linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ x)]; linarith
      exact rectPoly_outer hbound hsign hδ' hge ht hx hband (by linarith)
end
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
set_option autoImplicit false
open Polynomial Real
open scoped BigOperators
noncomputable section

/-- The evaluations of Chebyshev polynomials satisfy the three-term recurrence at natural
indices. -/
theorem chebyshev_T_eval_two_add (k : ℕ) (y : ℝ) :
    (Polynomial.Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ)).eval y
      = 2 * y * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y
        - (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval y := by
  have h : (Polynomial.Chebyshev.T ℝ ((k + 2 : ℕ) : ℤ))
      = 2 * X * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ))
          - (Polynomial.Chebyshev.T ℝ (k : ℤ)) :=
    Polynomial.Chebyshev.T_add_two ℝ (k : ℤ)
  rw [h]
  simp [eval_sub, eval_mul, eval_X]
end
noncomputable section

/-- Evaluation of the degree-`n` Chebyshev polynomial at `-x` equals its evaluation at `x`
multiplied by `(-1)^n`. -/
theorem chebyshev_T_eval_neg (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-x)
      = (-1 : ℝ) ^ n * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
  have key : ∀ m : ℕ,
      (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval (-x)
          = (-1 : ℝ) ^ m * (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x ∧
        (Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)).eval (-x)
          = (-1 : ℝ) ^ (m + 1) * (Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)).eval x := by
    intro m
    induction m with
    | zero =>
      show (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval (-x)
            = (-1 : ℝ) ^ 0 * (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x ∧
          (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval (-x)
            = (-1 : ℝ) ^ (0 + 1) * (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval x
      constructor
      · simp [Polynomial.Chebyshev.T_zero]
      · simp [Polynomial.Chebyshev.T_one]
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      show (Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)).eval (-x)
            = (-1 : ℝ) ^ (m + 1) * (Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)).eval x ∧
          (Polynomial.Chebyshev.T ℝ ((m + 1 + 1 : ℕ) : ℤ)).eval (-x)
            = (-1 : ℝ) ^ (m + 1 + 1)
              * (Polynomial.Chebyshev.T ℝ ((m + 1 + 1 : ℕ) : ℤ)).eval x
      constructor
      · exact h1
      · have hA : (-1 : ℝ) ^ (m + 1 + 1) = (-1 : ℝ) ^ m := by
          rw [pow_add, pow_add]
          norm_num
        have hB : (-1 : ℝ) ^ (m + 1) = (-1 : ℝ) ^ m * (-1) := by
          rw [pow_succ]
        have hstep : (m + 1 + 1 : ℕ) = m + 2 := by omega
        rw [hstep, chebyshev_T_eval_two_add m (-x), chebyshev_T_eval_two_add m x,
          h1, h0, hA, hB]
        ring
  exact (key n).1
end
noncomputable section

/-- Every Chebyshev polynomial of even natural index has equal evaluations at `x` and `-x`. -/
theorem chebyshev_T_eval_neg_even (k : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval (-x)
      = (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x := by
  rw [chebyshev_T_eval_neg]
  have h : (-1 : ℝ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [h, one_mul]
end
noncomputable section

/-- A Chebyshev polynomial of any integer index has absolute value at most one on `[-1, 1]`. -/
theorem abs_chebyshev_T_eval_le_one {n : ℤ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval x| ≤ 1 := by
  have hcos : x = Real.cos (Real.arccos x) :=
    (Real.cos_arccos hx.1 hx.2).symm
  rw [hcos, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _
end
noncomputable section

/-- Evaluation of an even Chebyshev series equals the finite sum of its coefficients times the
corresponding Chebyshev evaluations. -/
theorem evenChebSeries_eval (c : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries c l).eval x
      = ∑ k ∈ Finset.range l, c k * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x := by
  unfold Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries
  simp only [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [eval_mul, eval_C]
end
noncomputable section

/-- An even Chebyshev series has equal evaluations at `x` and `-x`. -/
theorem evenChebSeries_eval_neg (c : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries c l).eval (-x)
      = (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries c l).eval x := by
  rw [evenChebSeries_eval, evenChebSeries_eval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [chebyshev_T_eval_neg_even]
end
noncomputable section

/-- An even Chebyshev series with `l` terms has natural degree at most `2 * (l - 1)`. -/
theorem evenChebSeries_natDegree_le (c : ℕ → ℝ) (l : ℕ) :
    (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries c l).natDegree ≤ 2 * (l - 1) := by
  unfold Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries
  refine (natDegree_sum_le _ _).trans ?_
  have h : ∀ k ∈ Finset.range l,
      (Polynomial.C (c k) * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ))).natDegree
        ≤ 2 * (l - 1) := by
    intro k hk
    have hk' : k < l := Finset.mem_range.mp hk
    refine le_trans (natDegree_mul_le) ?_
    have hT : (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).natDegree = 2 * k := by
      rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
    have hC : (Polynomial.C (c k)).natDegree ≤ 0 := by simp
    have hkl : k ≤ l - 1 := Nat.le_pred_of_lt hk'
    rw [hT]
    omega
  exact Finset.sup_le h
end
noncomputable section

/-- The rectangle polynomial has absolute value at most `1 - ε' / 2` on `[-1, 1]` under the
given bounds. -/
theorem rectPoly_abs_le_one_half {S : Polynomial ℝ} {t ε' x : ℝ}
    (hbound : ∀ y ∈ Set.Icc (-2 : ℝ) 2, |S.eval y| ≤ 1)
    (ht : |t| ≤ 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hε' : 0 ≤ ε') (hε'2 : ε' ≤ 1 / 2) :
    |(rectPoly S t ε').eval x| ≤ 1 - ε' / 2 := by
  have ht1 : t ≤ 1 := (abs_le.mp ht).2
  have ht2 : -1 ≤ t := (abs_le.mp ht).1
  have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
    ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
    ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  obtain ⟨b1lo, b1hi⟩ := abs_le.mp (hbound _ hmem1)
  obtain ⟨b2lo, b2hi⟩ := abs_le.mp (hbound _ hmem2)
  rw [rectPoly_eval]
  have hc : 0 ≤ (1 - ε' : ℝ) / 2 := by linarith
  have hsum : S.eval (x + t) + S.eval (t - x) ≤ 2 := by linarith
  have hsum' : -2 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hc
  have hmul' := mul_le_mul_of_nonneg_left hsum' hc
  have e1 : ((1 - ε') / 2 : ℝ) * 2 = 1 - ε' := by ring
  have e2 : ((1 - ε') / 2 : ℝ) * (-2) = -(1 - ε') := by ring
  rw [e1] at hmul
  rw [e2] at hmul'
  rw [abs_le]
  constructor <;> nlinarith
end
noncomputable section

/-- The inner-band value lies between `(1 - ε') * (1 - ε' / 4) + ε' / 2` and `(1 - ε') * (1 + ε'
/ 4) + ε' / 2` under the stated sign approximation conditions. -/
theorem rectPoly_inner_sharp {S : Polynomial ℝ} {t δ' ε' x : ℝ}
    (hsign : ∀ y ∈ Set.Icc (-2 : ℝ) 2, δ' ≤ |y| → |S.eval y - Real.sign y| ≤ ε' / 4)
    (hδ' : 0 < δ') (ht : |t| ≤ 1) (hband : |x| ≤ t - δ') (hε'2 : ε' ≤ 1 / 2) :
    (1 - ε') * (1 - ε' / 4) + ε' / 2 ≤ (rectPoly S t ε').eval x ∧
      (rectPoly S t ε').eval x ≤ (1 - ε') * (1 + ε' / 4) + ε' / 2 := by
  have ht1 : t ≤ 1 := (abs_le.mp ht).2
  have ht2 : -1 ≤ t := (abs_le.mp ht).1
  have hx1 : x ≤ t - δ' := (abs_le.mp hband).2
  have hx2 : -(t - δ') ≤ x := (abs_le.mp hband).1
  have h1 : δ' ≤ x + t := by linarith
  have h2 : δ' ≤ t - x := by linarith
  have h1' : δ' ≤ |x + t| := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x + t)]
    exact h1
  have h2' : δ' ≤ |t - x| := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - x)]
    exact h2
  have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
    ⟨by linarith, by linarith⟩
  have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
    ⟨by linarith, by linarith⟩
  have hs1 := hsign _ hmem1 h1'
  have hs2 := hsign _ hmem2 h2'
  have sg1 : Real.sign (x + t) = 1 := Real.sign_of_pos (by linarith)
  have sg2 : Real.sign (t - x) = 1 := Real.sign_of_pos (by linarith)
  rw [sg1] at hs1
  rw [sg2] at hs2
  obtain ⟨u1, u2⟩ := abs_le.mp hs1
  obtain ⟨v1, v2⟩ := abs_le.mp hs2
  rw [rectPoly_eval]
  have hc : 0 ≤ (1 - ε' : ℝ) / 2 := by linarith
  have hsum_lo : 2 - ε' / 2 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
  have hsum_hi : S.eval (x + t) + S.eval (t - x) ≤ 2 + ε' / 2 := by linarith
  have hmul_lo := mul_le_mul_of_nonneg_left hsum_lo hc
  have hmul_hi := mul_le_mul_of_nonneg_left hsum_hi hc
  have e1 : ((1 - ε') / 2 : ℝ) * (2 - ε' / 2) = (1 - ε') * (1 - ε' / 4) := by ring
  have e2 : ((1 - ε') / 2 : ℝ) * (2 + ε' / 2) = (1 - ε') * (1 + ε' / 4) := by ring
  rw [e1] at hmul_lo
  rw [e2] at hmul_hi
  constructor <;> nlinarith
end
noncomputable section

/-- The outer-band value differs from `ε' / 2` by at most `(1 - ε') * (ε' / 4)` under the stated
sign approximation conditions. -/
theorem rectPoly_outer_sharp {S : Polynomial ℝ} {t δ' ε' x : ℝ}
    (hsign : ∀ y ∈ Set.Icc (-2 : ℝ) 2, δ' ≤ |y| → |S.eval y - Real.sign y| ≤ ε' / 4)
    (hδ' : 0 < δ') (hδt : δ' ≤ t) (ht : |t| ≤ 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hband : t + δ' ≤ |x|) (hε'2 : ε' ≤ 1 / 2) :
    ε' / 2 - (1 - ε') * (ε' / 4) ≤ (rectPoly S t ε').eval x ∧
      (rectPoly S t ε').eval x ≤ ε' / 2 + (1 - ε') * (ε' / 4) := by
  have ht1 : t ≤ 1 := (abs_le.mp ht).2
  have ht2 : -1 ≤ t := (abs_le.mp ht).1
  rcases le_total 0 x with hx0 | hx0
  · have hxle : t + δ' ≤ x := by rwa [abs_of_nonneg hx0] at hband
    have h1 : δ' ≤ x + t := by linarith
    have h1' : δ' ≤ |x + t| := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x + t)]
      exact h1
    have h2' : δ' ≤ |t - x| := by
      rw [abs_of_nonpos (by linarith : t - x ≤ 0)]
      linarith
    have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    have hs1 := hsign _ hmem1 h1'
    have hs2 := hsign _ hmem2 h2'
    have sg1 : Real.sign (x + t) = 1 := Real.sign_of_pos (by linarith)
    have sg2 : Real.sign (t - x) = -1 := Real.sign_of_neg (by linarith)
    rw [sg1] at hs1
    rw [sg2] at hs2
    obtain ⟨u1, u2⟩ := abs_le.mp hs1
    obtain ⟨v1, v2⟩ := abs_le.mp hs2
    rw [rectPoly_eval]
    have hc : 0 ≤ (1 - ε' : ℝ) / 2 := by linarith
    have hsum_lo : -ε' / 2 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hsum_hi : S.eval (x + t) + S.eval (t - x) ≤ ε' / 2 := by linarith
    have hmul_lo := mul_le_mul_of_nonneg_left hsum_lo hc
    have hmul_hi := mul_le_mul_of_nonneg_left hsum_hi hc
    have e1 : ((1 - ε') / 2 : ℝ) * (-ε' / 2) = -(1 - ε') * (ε' / 4) := by ring
    have e2 : ((1 - ε') / 2 : ℝ) * (ε' / 2) = (1 - ε') * (ε' / 4) := by ring
    rw [e1] at hmul_lo
    rw [e2] at hmul_hi
    constructor <;> nlinarith
  · have hxle : x ≤ -t - δ' := by
      have : |x| = -x := abs_of_nonpos hx0
      rw [this] at hband
      linarith
    have h1' : δ' ≤ |x + t| := by
      rw [abs_of_nonpos (by linarith : x + t ≤ 0)]
      linarith
    have h2 : δ' ≤ t - x := by linarith
    have h2' : δ' ≤ |t - x| := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - x)]
      exact h2
    have hmem1 : (x + t) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    have hmem2 : (t - x) ∈ Set.Icc (-2 : ℝ) 2 :=
      ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
    have hs1 := hsign _ hmem1 h1'
    have hs2 := hsign _ hmem2 h2'
    have sg1 : Real.sign (x + t) = -1 := Real.sign_of_neg (by linarith)
    have sg2 : Real.sign (t - x) = 1 := Real.sign_of_pos (by linarith)
    rw [sg1] at hs1
    rw [sg2] at hs2
    obtain ⟨u1, u2⟩ := abs_le.mp hs1
    obtain ⟨v1, v2⟩ := abs_le.mp hs2
    rw [rectPoly_eval]
    have hc : 0 ≤ (1 - ε' : ℝ) / 2 := by linarith
    have hsum_lo : -ε' / 2 ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hsum_hi : S.eval (x + t) + S.eval (t - x) ≤ ε' / 2 := by linarith
    have hmul_lo := mul_le_mul_of_nonneg_left hsum_lo hc
    have hmul_hi := mul_le_mul_of_nonneg_left hsum_hi hc
    have e1 : ((1 - ε') / 2 : ℝ) * (-ε' / 2) = -(1 - ε') * (ε' / 4) := by ring
    have e2 : ((1 - ε') / 2 : ℝ) * (ε' / 2) = (1 - ε') * (ε' / 4) := by ring
    rw [e1] at hmul_lo
    rw [e2] at hmul_hi
    constructor <;> nlinarith
end
noncomputable section

/-- Round a real number to a rational multiple of `2⁻ᴺ` using `floor (x * 2^N + 1 / 2)`. -/
private noncomputable def rectDyadicRound (x : ℝ) (N : ℕ) : ℚ :=
  ((Int.floor (x * (2 : ℝ) ^ N + 1 / 2) : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)
end
noncomputable section

/-- Dyadic rounding changes a real number by at most `1 / (2 * 2^N)`. -/
private theorem rectDyadicRound_near (x : ℝ) (N : ℕ) :
    |(rectDyadicRound x N : ℝ) - x| ≤ (1 / 2) / (2 : ℝ) ^ N := by
  have hzle := Int.floor_le (x * (2 : ℝ) ^ N + 1 / 2)
  have hzlt := Int.lt_floor_add_one (x * (2 : ℝ) ^ N + 1 / 2)
  have hcast : ((rectDyadicRound x N : ℚ) : ℝ)
      = ((Int.floor (x * (2 : ℝ) ^ N + 1 / 2) : ℤ) : ℝ) / (2 : ℝ) ^ N := by
    simp only [rectDyadicRound, Rat.cast_div, Rat.cast_intCast]
    push_cast
    congr 1
  have key : |((Int.floor (x * (2 : ℝ) ^ N + 1 / 2) : ℤ) : ℝ) - x * (2 : ℝ) ^ N| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc |(rectDyadicRound x N : ℝ) - x|
      = |(((Int.floor (x * (2 : ℝ) ^ N + 1 / 2) : ℤ) : ℝ) - x * (2 : ℝ) ^ N)
          / (2 : ℝ) ^ N| := by
        rw [hcast]
        congr 1
        field_simp
    _ = |((Int.floor (x * (2 : ℝ) ^ N + 1 / 2) : ℤ) : ℝ) - x * (2 : ℝ) ^ N| / (2 : ℝ) ^ N := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ N from pow_pos two_pos N)]
    _ ≤ (1 / 2) / (2 : ℝ) ^ N :=
        div_le_div_of_nonneg_right key (pow_nonneg (by norm_num) N)
end
noncomputable section

/-- For `|x| ≤ 2`, dyadic rounding has absolute numerator at most `2^(N + 1)` and denominator at
most `2^N`. -/
private theorem rectDyadicRound_num_den (x : ℝ) (N : ℕ) (hx : |x| ≤ 2) :
    (rectDyadicRound x N).num.natAbs ≤ 2 ^ (N + 1) ∧ (rectDyadicRound x N).den ≤ 2 ^ N := by
  set z : ℤ := Int.floor (x * (2 : ℝ) ^ N + 1 / 2) with hz
  have hzle : (z : ℝ) ≤ x * (2 : ℝ) ^ N + 1 / 2 := by
    rw [hz]; exact Int.floor_le _
  have hzlt : x * (2 : ℝ) ^ N + 1 / 2 < (z : ℝ) + 1 := by
    rw [hz]; exact Int.lt_floor_add_one _
  have hx2 : -2 ≤ x ∧ x ≤ 2 := abs_le.mp hx
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ N := pow_nonneg (by norm_num) N
  have hxle2 : x * (2 : ℝ) ^ N ≤ 2 * (2 : ℝ) ^ N :=
    mul_le_mul_of_nonneg_right hx2.2 hpow
  have hxlen2 : -2 * (2 : ℝ) ^ N ≤ x * (2 : ℝ) ^ N :=
    mul_le_mul_of_nonneg_right hx2.1 hpow
  have hupe : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by rw [pow_succ]; ring
  have hzp : (z : ℝ) < (2 : ℝ) ^ (N + 1) + 1 := by rw [hupe]; linarith
  have hzn : -(2 : ℝ) ^ (N + 1) - 1 < (z : ℝ) := by rw [hupe]; linarith
  have hzintp : z < ((2 ^ (N + 1) : ℕ) : ℤ) + 1 := by exact_mod_cast hzp
  have hzintn : -(((2 ^ (N + 1) : ℕ) : ℤ)) - 1 < z := by exact_mod_cast hzn
  have hzne : ((2 : ℤ) ^ N : ℤ) ≠ 0 := by positivity
  have hq : (rectDyadicRound x N) = ((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ) := rfl
  rw [hq]
  obtain ⟨c, hcnum, hcden⟩ :=
    Rat.exists_eq_mul_div_num_and_eq_mul_div_den z hzne
  have hcne : c ≠ 0 := by
    intro h0
    rw [hcden, h0, zero_mul] at hzne
    exact hzne rfl
  have hc1nat : 1 ≤ c.natAbs := by
    have : 0 < c.natAbs := Int.natAbs_pos.mpr hcne
    omega
  have hdpos : (0 : ℤ) < (((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den := by
    have := (((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).pos
    exact_mod_cast this
  have hcpos : (0 : ℤ) < c := by
    by_contra hcon
    push Not at hcon
    have hcden' : ((2 : ℤ) ^ N : ℤ)
        = c * ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ) := hcden
    have hcd2 : (1 : ℤ) ≤ ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ) := by
      have := hdpos
      omega
    have hbad : c * ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ) ≤ 0 := by
      nlinarith
    rw [← hcden'] at hbad
    exact absurd hbad (Int.not_le.mpr (by positivity))
  refine ⟨?_, ?_⟩
  · have hzabs : z.natAbs ≤ 2 ^ (N + 1) := by
      have hle1 : -(((2 ^ (N + 1) : ℕ) : ℤ)) ≤ z := by
        have h2 : -(((2 ^ (N + 1) : ℕ) : ℤ)) - 1 < z := hzintn
        omega
      have hle2 : z ≤ ((2 ^ (N + 1) : ℕ) : ℤ) := by
        have : z < ((2 ^ (N + 1) : ℕ) : ℤ) + 1 := hzintp
        omega
      omega
    have hmul : c.natAbs * (((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).num.natAbs
        = z.natAbs := by
      rw [← Int.natAbs_mul]
      congr 1
      exact hcnum.symm
    have hnumle : (((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).num.natAbs ≤ z.natAbs := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_left _ hc1nat
    exact hnumle.trans hzabs
  · have hc1 : (1 : ℤ) ≤ c := by omega
    have hdenz : ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ) ≤ (2 : ℤ) ^ N := by
      calc ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ)
          ≤ c * ((((z : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den : ℤ) := by nlinarith
        _ = (2 : ℤ) ^ N := hcden.symm
    have hcastn : ((2 ^ N : ℕ) : ℤ) = (2 : ℤ) ^ N := by push_cast; norm_num
    rw [← hcastn] at hdenz
    exact_mod_cast hdenz
end
noncomputable section

/-- For `|x| ≤ 2`, the rational bit width of the dyadic rounding is at most `N + 2`. -/
private theorem rectDyadicRound_bits (x : ℝ) (N : ℕ) (hx : |x| ≤ 2) :
    Qatlib.Concepts.QsvtCore.PhaseExistence.ratBitWidth (rectDyadicRound x N) ≤ N + 2 := by
  have hnd := rectDyadicRound_num_den x N hx
  have hsum : (rectDyadicRound x N).num.natAbs + (rectDyadicRound x N).den ≤ 2 ^ (N + 2) := by
    have e1 : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [Nat.pow_succ']
    have e2 : 2 ^ (N + 2) = 2 * 2 ^ (N + 1) := by rw [Nat.pow_succ']
    omega
  have hclog : Nat.clog 2 ((rectDyadicRound x N).num.natAbs + (rectDyadicRound x N).den) ≤ N + 2 :=
    Nat.clog_le_of_le_pow hsum
  unfold Qatlib.Concepts.QsvtCore.PhaseExistence.ratBitWidth
  exact hclog
end
noncomputable section

/-- Rounding `m` even Chebyshev coefficients at precision `N` changes evaluations on `[-1, 1]`
by at most `m / (2 * 2^N)`. -/
theorem evenChebSeries_rounded_dist (a : ℕ → ℝ) (m N : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries
        (fun k => ((rectDyadicRound (a k) N : ℚ) : ℝ)) m).eval x
      - (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries a m).eval x|
      ≤ (m : ℝ) * ((1 / 2) / (2 : ℝ) ^ N) := by
  have h1 : (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries
        (fun k => ((rectDyadicRound (a k) N : ℚ) : ℝ)) m).eval x
      = ∑ k ∈ Finset.range m,
          ((rectDyadicRound (a k) N : ℚ) : ℝ)
            * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x :=
    evenChebSeries_eval _ _ _
  have h2 : (Qatlib.Concepts.QsvtCore.PhaseExistence.evenChebSeries a m).eval x
      = ∑ k ∈ Finset.range m,
          a k * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x :=
    evenChebSeries_eval _ _ _
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have hshape : (∑ k ∈ Finset.range m,
        (((rectDyadicRound (a k) N : ℚ) : ℝ)
            * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x
          - a k * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x))
      = ∑ k ∈ Finset.range m,
          (((rectDyadicRound (a k) N : ℚ) : ℝ) - a k)
            * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hshape]
  have hterm : ∀ k ∈ Finset.range m,
      |(((rectDyadicRound (a k) N : ℚ) : ℝ) - a k)
          * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x|
        ≤ (1 / 2) / (2 : ℝ) ^ N := by
    intro k hk
    have hnear := rectDyadicRound_near (a k) N
    have hT : |(Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x| ≤ 1 :=
      abs_chebyshev_T_eval_le_one hx
    rw [abs_mul]
    calc |((rectDyadicRound (a k) N : ℚ) : ℝ) - a k|
            * |(Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x|
        ≤ |((rectDyadicRound (a k) N : ℚ) : ℝ) - a k| * 1 :=
          mul_le_mul_of_nonneg_left hT (abs_nonneg _)
      _ = |((rectDyadicRound (a k) N : ℚ) : ℝ) - a k| := by ring
      _ ≤ (1 / 2) / (2 : ℝ) ^ N := hnear
  have hupper : ∀ k ∈ Finset.range m,
      (((rectDyadicRound (a k) N : ℚ) : ℝ) - a k)
          * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x
        ≤ (1 / 2) / (2 : ℝ) ^ N := by
    intro k hk
    exact le_trans (le_abs_self _) (hterm k hk)
  have hlower : ∀ k ∈ Finset.range m,
      -((1 / 2) / (2 : ℝ) ^ N)
        ≤ (((rectDyadicRound (a k) N : ℚ) : ℝ) - a k)
            * (Polynomial.Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)).eval x := by
    intro k hk
    exact neg_le_of_abs_le (hterm k hk)
  have hsU := Finset.sum_le_sum hupper
  have hsL := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsU hsL
  rw [abs_le]
  constructor <;> linarith
end
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator Classical BigOperators
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Module Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
set_option autoImplicit false
open Polynomial Real
open scoped BigOperators
open Qatlib
set_option warningAsError false
noncomputable section

/-- The assertion that every even polynomial bounded by one on `[-1, 1]` has an even Chebyshev
expansion of the specified length with coefficients bounded by two. -/
def EvenChebExpansionBound : Prop :=
  ∀ (Q : Polynomial ℝ), (∀ x : ℝ, Q.eval (-x) = Q.eval x) →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1) →
    ∃ (a : ℕ → ℝ),
      Q = evenChebSeries a (Q.natDegree / 2 + 1) ∧
      (∀ k < Q.natDegree / 2 + 1, |a k| ≤ 2)
end
noncomputable section

/-- For positive `ε'`, `log₂ (4 / ε')` equals `log₂ (1 / ε') + 2`. -/
theorem logb_two_four_div (ε' : ℝ) (hε' : 0 < ε') :
    Real.logb 2 (4 / ε') = Real.logb 2 (1 / ε') + 2 := by
  have he : ε' ≠ 0 := ne_of_gt hε'
  have h4n : (4:ℝ) ≠ 0 := by norm_num
  have hone : (1:ℝ) / ε' ≠ 0 := by
    simp [he]
  have hsplit : (4:ℝ) / ε' = 4 * (1 / ε') := by rw [div_eq_mul_one_div]
  have h4b : Real.logb 2 (4:ℝ) = 2 := by
    have h42 : (4:ℝ) = 2 * 2 := by norm_num
    have hm : Real.logb 2 (2 * 2) = Real.logb 2 2 + Real.logb 2 2 :=
      Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
    rw [h42, hm]
    have hself : Real.logb 2 (2:ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    rw [hself]
    ring
  rw [hsplit, Real.logb_mul h4n hone, h4b]
  ring
end
noncomputable section

/-- For `0 < ε' ≤ 1 / 2`, the natural ceiling of `log₂ (1 / ε')` is at least one. -/
theorem ceil_logb_one_div_eps_ge_one (ε' : ℝ) (hε' : 0 < ε') (hε'2 : ε' ≤ 1 / 2) :
    1 ≤ Nat.ceil (Real.logb 2 (1 / ε')) := by
  by_contra hcon
  push Not at hcon
  have hzero : Nat.ceil (Real.logb 2 (1 / ε')) = 0 := by omega
  have hle := Nat.le_ceil (Real.logb 2 (1 / ε'))
  have hpos : (0:ℝ) < Real.logb 2 (1 / ε') := by
    have h1 : (1:ℝ) < 1 / ε' := by
      rw [lt_div_iff₀ hε']
      nlinarith
    have h2 : Real.log 1 < Real.log (1 / ε') :=
      (Real.log_lt_log_iff (by norm_num) (div_pos (by norm_num) hε')).mpr h1
    have h3 : (0:ℝ) < Real.log (1 / ε') := by simpa using! h2
    have hln2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [← Real.log_div_log]
    exact div_pos h3 hln2
  rw [hzero] at hle
  linarith
end
noncomputable section

/-- When `Cs ≤ 32`, the sign-derived rectangle degree bound is at most `rectangleDegreeBudget δ'
ε'` for the stated error range. -/
theorem rectDegree_budget_le {Cs : ℕ} (hCs : Cs ≤ 32) (δ' ε' : ℝ)
    (hε' : 0 < ε') (hε'2 : ε' ≤ 1 / 2) :
    Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1)
      ≤ rectangleDegreeBudget δ' ε' := by
  have hA1 : 1 ≤ Nat.ceil (Real.logb 2 (1 / ε')) :=
    ceil_logb_one_div_eps_ge_one ε' hε' hε'2
  have hceil : Nat.ceil (Real.logb 2 (4 / ε')) ≤ Nat.ceil (Real.logb 2 (1 / ε')) + 2 := by
    rw [logb_two_four_div ε' hε']
    refine Nat.ceil_le.mpr ?_
    have hle := Nat.le_ceil (Real.logb 2 (1 / ε'))
    push_cast at hle
    push_cast
    linarith
  have hB : Nat.ceil (Real.logb 2 (4 / ε')) + 1
      ≤ Nat.ceil (Real.logb 2 (1 / ε')) + 3 := by omega
  have hcore : Cs * (Nat.ceil (Real.logb 2 (4 / ε')) + 1)
      ≤ 64 * (Nat.ceil (Real.logb 2 (1 / ε')) + 1) := by
    have h1 : Cs * (Nat.ceil (Real.logb 2 (4 / ε')) + 1)
        ≤ Cs * (Nat.ceil (Real.logb 2 (1 / ε')) + 3) :=
      Nat.mul_le_mul_left _ hB
    have h2 : Cs * (Nat.ceil (Real.logb 2 (1 / ε')) + 3)
        ≤ 32 * (Nat.ceil (Real.logb 2 (1 / ε')) + 3) :=
      Nat.mul_le_mul_right _ hCs
    have h3 : (32:ℕ) * (Nat.ceil (Real.logb 2 (1 / ε')) + 3)
        ≤ 64 * (Nat.ceil (Real.logb 2 (1 / ε')) + 1) := by omega
    exact le_trans (le_trans h1 h2) h3
  have hmul : Cs * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) * Nat.ceil (1 / δ')
      ≤ 64 * (Nat.ceil (Real.logb 2 (1 / ε')) + 1) * Nat.ceil (1 / δ') :=
    Nat.mul_le_mul_right _ hcore
  have e1 : Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1)
      = Cs * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) * Nat.ceil (1 / δ') := by
    rw [Nat.mul_assoc, Nat.mul_comm (Nat.ceil (1 / δ')) _, ← Nat.mul_assoc]
  have e2 : rectangleDegreeBudget δ' ε'
      = 64 * (Nat.ceil (Real.logb 2 (1 / ε')) + 1) * Nat.ceil (1 / δ') := by
    unfold rectangleDegreeBudget
    rw [Nat.mul_assoc, Nat.mul_comm (Nat.ceil (1 / δ')) _, ← Nat.mul_assoc]
  rw [e1, e2]
  exact hmul
end
noncomputable section

/-- The stated bounds on the number of terms and dyadic precision ensure that the accumulated
coefficient rounding error is at most `ε' / 4`. -/
theorem rounding_error_budget (D m N : ℕ) (ε' : ℝ) (hε' : 0 < ε')
    (hm : m ≤ (D + 2) / 2)
    (hpow : 8 * (((D : ℝ) + 2)) / ε' ≤ (2 : ℝ) ^ (N + 1)) :
    (m : ℝ) * ((1 / 2) / (2 : ℝ) ^ N) ≤ ε' / 4 := by
  have hm2 : (m : ℝ) ≤ ((D : ℝ) + 2) / 2 := by
    have h1 : (m : ℝ) ≤ (((D + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast hm
    have h2 : (((((D + 2) / 2 : ℕ) : ℝ)) : ℝ) ≤ ((D : ℝ) + 2) / 2 := by
      have hdiv : (((D + 2) / 2 : ℕ) : ℝ) * 2 ≤ ((D : ℝ) + 2) := by
        have := Nat.div_mul_le_self (D + 2) 2
        exact_mod_cast this
      linarith
    linarith
  have h2N1 : (0:ℝ) < (2 : ℝ) ^ (N + 1) := pow_pos two_pos _
  have hmul : (8:ℝ) * ((D : ℝ) + 2) ≤ ε' * 2 ^ (N + 1) := by
    have := hpow
    rw [div_le_iff₀ hε'] at this
    nlinarith
  have h3 : (1:ℝ) / 2 ^ (N + 1) ≤ ε' / (8 * ((D : ℝ) + 2)) := by
    rw [div_le_div_iff₀ h2N1 (by positivity : (0:ℝ) < 8 * ((D : ℝ) + 2))]
    rw [one_mul]
    exact hmul
  have hle16 : ((D : ℝ) + 2) / 2 / 2 ^ (N + 1) ≤ ε' / 16 := by
    have hstep : ((D : ℝ) + 2) / 2 / 2 ^ (N + 1)
        = ((D : ℝ) + 2) / 2 * (1 / 2 ^ (N + 1)) := by
      rw [div_eq_mul_one_div]
    rw [hstep]
    have h4 : ((D : ℝ) + 2) / 2 * (1 / 2 ^ (N + 1))
        ≤ ((D : ℝ) + 2) / 2 * (ε' / (8 * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : ((D : ℝ) + 2) / 2 * (ε' / (8 * ((D : ℝ) + 2))) = ε' / 16 := by
      field_simp
      ring
    rw [h5] at h4
    exact h4
  have heq : (m : ℝ) * ((1 / 2) / (2 : ℝ) ^ N) = (m : ℝ) / 2 ^ (N + 1) := by
    rw [pow_succ]
    field_simp
  rw [heq]
  have h1 : (m : ℝ) / 2 ^ (N + 1) ≤ ((D : ℝ) + 2) / 2 / 2 ^ (N + 1) :=
    div_le_div_of_nonneg_right hm2 (le_of_lt h2N1)
  have h2 : ε' / 16 ≤ ε' / 4 := by
    have : (0:ℝ) ≤ ε' := le_of_lt hε'
    apply div_le_div_of_nonneg_left this (by norm_num) (by norm_num)
  linarith
end
noncomputable section

/-- An even Chebyshev series with all coefficients zero is the zero polynomial. -/
theorem evenChebSeries_zero (l : ℕ) :
    evenChebSeries (fun _ => (0:ℝ)) l = 0 := by
  unfold evenChebSeries
  simp
end
noncomputable section

/-- When `t < δ'`, rational even Chebyshev coefficients exist satisfying the degree, coefficient
bit, and rectangle band budgets. -/
theorem clause38_case_inner_empty (δ' ε' t : ℝ) (hε' : 0 < ε') (hlt : t < δ') :
    ∃ (cE : ℕ → ℚ) (l d : ℕ),
      let P : Polynomial ℝ := evenChebSeries (fun k => (cE k : ℝ)) l
      l ≤ d + 1 ∧
        P.natDegree ≤ d ∧
        d ≤ rectangleDegreeBudget δ' ε' ∧
        (∀ k < l, ratBitWidth (cE k) ≤ familyCoeffBits d ε') ∧
        (∀ x : ℝ, P.eval (-x) = P.eval x) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, -t + δ' ≤ x → x ≤ t - δ' →
          1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≤ -t - δ' ∨ t + δ' ≤ x →
          0 ≤ P.eval x ∧ P.eval x ≤ ε') := by
  refine ⟨fun _ => (0:ℚ), 1, 0, ?_⟩
  have hfun : (fun k : ℕ => (((fun _ => (0:ℚ)) k : ℚ) : ℝ)) = fun _ => (0:ℝ) := by
    funext k
    simp
  have hP0 : evenChebSeries (fun _ => (0:ℝ)) 1 = 0 := evenChebSeries_zero 1
  have hbw : ratBitWidth (0:ℚ) = 0 := by
    unfold ratBitWidth
    show Nat.clog 2 (0 + 1) = 0
    exact le_antisymm (Nat.clog_le_of_le_pow (by norm_num : (1:ℕ) ≤ 2 ^ 0))
      (Nat.zero_le _)
  simp only [hfun, hP0]
  constructor
  · norm_num
  constructor
  · simp
  constructor
  · exact Nat.zero_le _
  constructor
  · intro k hk
    interval_cases k
    rw [hbw]
    exact Nat.zero_le _
  constructor
  · intro x
    simp
  constructor
  · intro x hx
    simp
  constructor
  · intro x hx h1 h2
    exfalso
    nlinarith
  · intro x hx h
    simp [le_of_lt hε']
end
noncomputable section

/-- A sign family with constant at most 32 and bounded even Chebyshev expansions yields rational
rectangle approximants with the prescribed degree, coefficient bit, and band bounds. -/
theorem clause38_of_sign {Cs : ℕ} (hs : SignFamily Cs) (hCs : Cs ≤ 32)
    (hexp : EvenChebExpansionBound) :
    ∀ (δ' ε' t : ℝ), 0 < δ' → δ' ≤ 1 / 2 → 0 < ε' → ε' ≤ 1 / 2 →
      -1 ≤ t → t ≤ 1 →
      ∃ (cE : ℕ → ℚ) (l d : ℕ),
        let P : Polynomial ℝ := evenChebSeries (fun k => (cE k : ℝ)) l
        l ≤ d + 1 ∧
          P.natDegree ≤ d ∧
          d ≤ rectangleDegreeBudget δ' ε' ∧
          (∀ k < l, ratBitWidth (cE k) ≤ familyCoeffBits d ε') ∧
          (∀ x : ℝ, P.eval (-x) = P.eval x) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, -t + δ' ≤ x → x ≤ t - δ' →
            1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≤ -t - δ' ∨ t + δ' ≤ x →
            0 ≤ P.eval x ∧ P.eval x ≤ ε') := by
  intro δ' ε' t hδ' hδ'2 hε' hε'2 htlo hthi
  rcases lt_or_ge t δ' with hlt | hge
  · exact clause38_case_inner_empty δ' ε' t hε' hlt
  · have ht : |t| ≤ 1 := abs_le.mpr ⟨htlo, hthi⟩
    have hθ : (0:ℝ) < ε' / 4 := by linarith
    have hθ2 : (ε' / 4 : ℝ) ≤ 1 / 2 := by linarith
    obtain ⟨S, hSdeg, hSodd, hSbound, hSsign⟩ := hs δ' (ε' / 4) hδ' hθ hθ2
    set W := rectPoly S t ε' with hW
    have hWdeg : W.natDegree
        ≤ Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) := by
      rw [hW]
      refine le_trans rectPoly_natDegree_le ?_
      have hθeq : Real.logb 2 (1 / (ε' / 4)) = Real.logb 2 (4 / ε') := by
        rw [one_div_div]
      rw [hθeq] at hSdeg
      exact hSdeg
    have hWbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |W.eval x| ≤ 1 - ε' / 2 := by
      intro x hx
      rw [hW]
      exact rectPoly_abs_le_one_half hSbound ht hx (le_of_lt hε') hε'2
    have hWeven : ∀ x : ℝ, W.eval (-x) = W.eval x := by
      intro x
      rw [hW]
      exact rectPoly_eval_neg
    have hW1 : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |W.eval x| ≤ 1 := by
      intro x hx
      have := hWbnd x hx
      rw [abs_le] at this ⊢
      constructor <;> linarith
    obtain ⟨a, haQ, haB⟩ := hexp W hWeven hW1
    set m := W.natDegree / 2 + 1 with hm
    set D := rectangleDegreeBudget δ' ε' with hD
    set p := Nat.ceil (Real.logb 2 (2 / ε')) with hp
    set q := Nat.ceil (Real.logb 2 (((D : ℝ) + 2))) with hq
    set N := p + q + 1 with hN
    refine ⟨fun k => rectDyadicRound (a k) N, m, D, ?_⟩

    have hbits : N + 2 ≤ familyCoeffBits D ε' := by
      unfold familyCoeffBits
      omega

    have hD0 : Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) ≤ D := by
      rw [hD]
      exact rectDegree_budget_le hCs δ' ε' hε' hε'2
    have hmD : m ≤ (D + 2) / 2 := by
      have h1 : W.natDegree ≤ D := le_trans hWdeg hD0
      have h2 : W.natDegree / 2 + 1 ≤ D / 2 + 1 :=
        Nat.add_le_add_right (Nat.div_le_div_right h1) 1
      have h3 : (D:ℕ) / 2 + 1 = (D + 2) / 2 := by omega
      rw [← hm] at h2
      rw [h3] at h2
      exact h2

    have hpow1 : (2:ℝ) / ε' ≤ (2:ℝ) ^ p := by
      have hle : Real.logb 2 (2 / ε') ≤ (p:ℝ) := by
        rw [hp]
        exact_mod_cast Nat.le_ceil _
      have := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2)
        (by positivity : (0:ℝ) < 2 / ε')).mp hle
      rwa [Real.rpow_natCast] at this
    have hpow2 : ((D : ℝ) + 2) ≤ (2:ℝ) ^ q := by
      have hle : Real.logb 2 (((D : ℝ) + 2)) ≤ (q:ℝ) := by
        have h := Nat.le_ceil (Real.logb 2 (((D : ℝ) + 2)))
        rw [hq]
        exact_mod_cast h
      have := (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2)
        (by positivity : (0:ℝ) < (D : ℝ) + 2)).mp hle
      rwa [Real.rpow_natCast] at this
    have hpow : (8:ℝ) * ((D : ℝ) + 2) / ε' ≤ (2:ℝ) ^ (N + 1) := by
      have h2N1 : (2:ℝ) ^ (N + 1) = (2:ℝ) ^ p * (2:ℝ) ^ q * 4 := by
        rw [hN, show (p + q + 1 + 1 : ℕ) = p + (q + 2) from by omega,
          pow_add, pow_succ, pow_succ]
        ring
      have h1 : ((2:ℝ) / ε') * ((D : ℝ) + 2) ≤ (2:ℝ) ^ p * (2:ℝ) ^ q :=
        mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
      have h2 : ((2:ℝ) / ε') * ((D : ℝ) + 2) * 4 ≤ (2:ℝ) ^ p * (2:ℝ) ^ q * 4 :=
        mul_le_mul_of_nonneg_right h1 (by norm_num)
      have h3 : ((2:ℝ) / ε') * ((D : ℝ) + 2) * 4 = (8:ℝ) * ((D : ℝ) + 2) / ε' := by
        field_simp
        ring
      rw [h3] at h2
      rw [h2N1]
      exact h2

    have herr : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        |(evenChebSeries (fun k => ((rectDyadicRound (a k) N : ℚ) : ℝ)) m).eval x
          - W.eval x| ≤ ε' / 4 := by
      intro x hx
      have hdist := evenChebSeries_rounded_dist a m N x hx
      have hq' : W.eval x = (evenChebSeries a m).eval x := by
        rw [haQ, hm]
      rw [hq']
      exact le_trans hdist (rounding_error_budget D m N ε' hε' hmD hpow)

    constructor
    · have : (D:ℕ) / 2 + 1 ≤ D + 1 := by omega
      exact hmD.trans (by omega)
    constructor
    · refine le_trans (evenChebSeries_natDegree_le _ _) ?_
      have h1 : 2 * (m - 1) = 2 * (W.natDegree / 2) := by
        rw [hm]
        omega
      have h2 : 2 * (W.natDegree / 2) ≤ W.natDegree := by
        have := Nat.div_mul_le_self W.natDegree 2
        omega
      rw [h1]
      exact le_trans h2 (le_trans hWdeg hD0)
    constructor
    · exact le_rfl
    constructor
    · intro k hk
      have hkB : |a k| ≤ 2 := haB k hk
      exact le_trans (rectDyadicRound_bits (a k) N hkB) hbits
    constructor
    · intro x
      exact evenChebSeries_eval_neg _ _ _
    constructor
    · intro x hx
      obtain ⟨el, eu⟩ := abs_le.mp (herr x hx)
      obtain ⟨ql, qh⟩ := abs_le.mp (hWbnd x hx)
      rw [abs_le]
      constructor <;> nlinarith
    constructor
    · intro x hx hlo hhi
      have hband : |x| ≤ t - δ' := abs_le.mpr ⟨by linarith, by linarith⟩
      have hsharp := rectPoly_inner_sharp hSsign hδ' ht hband hε'2
      obtain ⟨el, eu⟩ := abs_le.mp (herr x hx)
      constructor <;> nlinarith [hsharp.1, hsharp.2, el, eu]
    · intro x hx hor
      have hband : t + δ' ≤ |x| := by
        rcases hor with h | h
        · rw [abs_of_nonpos (by linarith : x ≤ 0)]; linarith
        · rw [abs_of_nonneg (by linarith : 0 ≤ x)]; linarith
      have hsharp := rectPoly_outer_sharp hSsign hδ' hge ht hx hband hε'2
      obtain ⟨el, eu⟩ := abs_le.mp (herr x hx)
      constructor <;> nlinarith [hsharp.1, hsharp.2, el, eu]
end
end Qatlib.Concepts.QsvtCore.PhaseExistence.S1_QSVT_CORE
