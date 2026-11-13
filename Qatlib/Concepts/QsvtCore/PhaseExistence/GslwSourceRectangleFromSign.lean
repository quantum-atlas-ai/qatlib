/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.SpectralSketch.SketchSpectral.SvtGramTransferSamp
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Lagrange

/-!
# Rectangle polynomials from sign approximations

This module constructs even rectangle polynomials from a supplied `SignFamily`, using two
shifted copies of a sign approximation. The construction implements the polynomial filtering
pattern used in [GilyenSuLowWiebe2019].

The response is bounded by one on the unit interval, lies near one in the inner band, and lies
near zero in the outer bands. The final theorem expresses the degree bound as a constant times
the logarithm of the inverse error divided by the transition width.

## Main statements

* `rectPoly`: the shifted sign-polynomial construction.
* `rectPoly_inner` and `rectPoly_outer`: bounds on the inner and outer bands.
* `rect_of_sign`: existence with an explicit discrete degree bound.
* `clause48_of_sign`: the logarithmic degree estimate.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

set_option autoImplicit false

open Matrix Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt

open scoped Matrix.Norms.L2Operator Classical BigOperators

namespace Qatlib.Concepts.QsvtCore.PhaseExistence
open Matrix Module Polynomial
open Qatlib.Concepts.SpectralSketch.SketchSpectral
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator Classical BigOperators
set_option autoImplicit false
open Polynomial Real
noncomputable section

/-- States the existence of odd sign-approximating polynomials on `[-2, 2]` with the specified
degree bound and error away from zero. -/
def SignFamily (Cs : ℕ) : Prop :=
  ∀ (μ θ : ℝ), 0 < μ → 0 < θ → θ ≤ 1 / 2 →
    ∃ S : Polynomial ℝ,
      S.natDegree ≤ Cs * Nat.ceil (1 / μ) * (Nat.ceil (Real.logb 2 (1 / θ)) + 1) ∧
      (∀ x : ℝ, S.eval (-x) = -S.eval x) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, |S.eval x| ≤ 1) ∧
      (∀ x ∈ Set.Icc (-2 : ℝ) 2, μ ≤ |x| → |S.eval x - Real.sign x| ≤ θ)
end
noncomputable section

/-- The even rectangle polynomial formed by averaging two shifted evaluations of `S`, rescaling
by `(1 - ε') / 2`, and adding `ε' / 2`. -/
def rectPoly (S : Polynomial ℝ) (t ε' : ℝ) : Polynomial ℝ :=
  C ((1 - ε') / 2) * (S.comp (X + C t) + S.comp (C t - X)) + C (ε' / 2)
end
noncomputable section

/-- Evaluates the rectangle polynomial in terms of the two shifted values of `S`. -/
theorem rectPoly_eval {S : Polynomial ℝ} {t ε' x : ℝ} :
    (rectPoly S t ε').eval x =
      (1 - ε') / 2 * (S.eval (x + t) + S.eval (t - x)) + ε' / 2 := by
  simp only [rectPoly, eval_add, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
end
noncomputable section

/-- The rectangle polynomial evaluates equally at `x` and `-x`. -/
theorem rectPoly_eval_neg {S : Polynomial ℝ} {t ε' x : ℝ} :
    (rectPoly S t ε').eval (-x) = (rectPoly S t ε').eval x := by
  rw [rectPoly_eval, rectPoly_eval]
  have h1 : (-x + t : ℝ) = t - x := by ring
  have h2 : (t - -x : ℝ) = x + t := by ring
  rw [h1, h2]
  ring
end
noncomputable section

/-- The rectangle construction does not increase natural degree. -/
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

/-- If `S` is bounded by one on `[-2, 2]`, the rectangle polynomial is bounded by one on `[-1,
1]` under the stated parameter bounds. -/
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

/-- A bounded sign approximation gives a rectangle response between `1 - ε'` and `1` in the
inner band. -/
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

/-- A bounded sign approximation gives a rectangle response between `0` and `ε'` in the outer
bands. -/
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

/-- States that a polynomial is even, bounded by one on `[-1, 1]`, near one in the inner band,
and near zero in the outer bands. -/
def RectBands (P : Polynomial ℝ) (δ' ε' t : ℝ) : Prop :=
  (∀ x : ℝ, P.eval (-x) = P.eval x) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, -t + δ' ≤ x → x ≤ t - δ' →
      1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, x ≤ -t - δ' ∨ t + δ' ≤ x →
      0 ≤ P.eval x ∧ P.eval x ≤ ε')
end
noncomputable section

/-- The zero polynomial satisfies the rectangle band conditions when the inner band is empty and
`ε'` is nonnegative. -/
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

/-- A sign approximation family yields a rectangle polynomial with the specified degree bound
and band conditions. -/
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
noncomputable section

/-- Bounds the explicit rectangle degree expression times the transition width by `100 * (Cs +
1) * log (1 / ε')`. -/
theorem rectDegree_mul_le {Cs : ℕ} {δ' ε' : ℝ}
    (hδ' : 0 < δ') (hδ'2 : δ' ≤ 1 / 2) (hε' : 0 < ε') (hε'2 : ε' ≤ 1 / 2) :
    ((Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) : ℕ) : ℝ) * δ' ≤
      100 * ((Cs : ℝ) + 1) * Real.log (1 / ε') := by

  have hLpos : (0:ℝ) < Real.log (1 / ε') := by
    have h1 : (1:ℝ) < 1 / ε' := by
      rw [lt_div_iff₀ hε']
      nlinarith
    have h2 : Real.log 1 < Real.log (1 / ε') :=
      (Real.log_lt_log_iff (by norm_num) (div_pos (by norm_num) hε')).mpr h1
    simpa using! h2
  have h2lt : (2:ℝ) / 3 < Real.log 2 := by
    have h3 : (2:ℝ) / 3 < 0.6931471803 := by norm_num
    exact lt_of_lt_of_le h3 (le_of_lt Real.log_two_gt_d9)
  have hLb : (2:ℝ) / 3 < Real.log (1 / ε') := by
    have h4 : Real.log 2 ≤ Real.log (1 / ε') := by
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hε']
      nlinarith
    exact lt_of_lt_of_le h2lt h4
  have hL0 : (0:ℝ) ≤ Real.log (1 / ε') := le_of_lt hLpos

  have hceil1 : ((Nat.ceil (1 / δ' : ℝ) : ℝ)) * δ' ≤ 2 := by
    have h1 : ((Nat.ceil (1 / δ' : ℝ) : ℝ)) < 1 / δ' + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h3 : ((Nat.ceil (1 / δ' : ℝ) : ℝ)) * δ' < (1 / δ' + 1) * δ' :=
      mul_lt_mul_of_pos_right h1 hδ'
    have h2 : ((1:ℝ) / δ' + 1) * δ' ≤ 2 := by
      have heq : ((1:ℝ) / δ' + 1) * δ' = 1 + δ' := by
        rw [add_mul, one_div_mul_cancel (ne_of_gt hδ'), one_mul]
      rw [heq]
      nlinarith
    linarith

  have hlogb : Real.logb 2 (4 / ε') = Real.log (4 / ε') / Real.log 2 :=
    Real.log_div_log.symm
  have hlogb_nonneg : (0:ℝ) ≤ Real.logb 2 (4 / ε') := by
    rw [hlogb]
    apply div_nonneg
    · apply le_of_lt
      apply Real.log_pos
      rw [lt_div_iff₀ hε']
      nlinarith
    · exact le_of_lt (Real.log_pos (by norm_num))
  have hceil2 : ((Nat.ceil (Real.logb 2 (4 / ε')) : ℝ)) < Real.logb 2 (4 / ε') + 1 :=
    Nat.ceil_lt_add_one hlogb_nonneg
  have h4log : Real.log (4 / ε') = 2 * Real.log 2 + Real.log (1 / ε') := by
    have he : ε' ≠ 0 := ne_of_gt hε'
    have hsplit : (4:ℝ) / ε' = 4 * (1 / ε') := by
      rw [div_eq_mul_one_div]
    have h4b : Real.log 4 = 2 * Real.log 2 := by
      have h42 : (4:ℝ) = 2 * 2 := by norm_num
      rw [h42, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hsplit, Real.log_mul (by norm_num : (4:ℝ) ≠ 0) (by simp [he] : (1 / ε' : ℝ) ≠ 0),
      h4b]
  have hlogb_le : Real.logb 2 (4 / ε') ≤ 2 + 2 * Real.log (1 / ε') := by
    have hln2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [hlogb, h4log]
    have hre : (2 * Real.log 2 + Real.log (1 / ε')) / Real.log 2
        = 2 + Real.log (1 / ε') / Real.log 2 := by
      field_simp
    rw [hre]
    have h2ln2 : (1:ℝ) ≤ 2 * Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    have hle : Real.log (1 / ε') / Real.log 2 ≤ 2 * Real.log (1 / ε') := by
      rw [div_le_iff₀ hln2]
      have hmul : Real.log (1 / ε') * 1 ≤ Real.log (1 / ε') * (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_left h2ln2 hL0
      have e1 : Real.log (1 / ε') * (2 * Real.log 2)
          = 2 * Real.log (1 / ε') * Real.log 2 := by ring
      rw [← e1]
      simpa using! hmul
    linarith [hle]
  have hsum2 : ((Nat.ceil (Real.logb 2 (4 / ε')) : ℝ)) + 1 ≤ 8 * Real.log (1 / ε') := by
    have h42 : Real.logb 2 (4 / ε') + 2 ≤ 8 * Real.log (1 / ε') := by
      have h6 : (4:ℝ) + 2 * Real.log (1 / ε') ≤ 8 * Real.log (1 / ε') := by
        have h6L : (4:ℝ) < 6 * Real.log (1 / ε') := by nlinarith [hLb]
        nlinarith
      linarith
    have hlt : ((Nat.ceil (Real.logb 2 (4 / ε')) : ℝ)) + 1 < Real.logb 2 (4 / ε') + 2 := by
      linarith [hceil2]
    linarith

  have hB0 : (0:ℝ) ≤ ((Nat.ceil (Real.logb 2 (4 / ε')) : ℝ)) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (Nat.ceil (Real.logb 2 (4 / ε')))
    linarith
  have hprod : ((Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) : ℕ) : ℝ) * δ' ≤
      ((Cs:ℝ) * 2) * (8 * Real.log (1 / ε')) := by
    push_cast
    have hcs : (0:ℝ) ≤ Cs := Nat.cast_nonneg _
    calc
      ((Cs:ℝ) * ↑(Nat.ceil (1 / δ')) * (↑(Nat.ceil (Real.logb 2 (4 / ε'))) + 1) * δ')
          = ((Cs:ℝ) * (↑(Nat.ceil (Real.logb 2 (4 / ε'))) + 1))
              * (↑(Nat.ceil (1 / δ')) * δ') := by ring
      _ ≤ ((Cs:ℝ) * (↑(Nat.ceil (Real.logb 2 (4 / ε'))) + 1)) * 2 :=
        mul_le_mul_of_nonneg_left hceil1 (mul_nonneg hcs hB0)
      _ = ((Cs:ℝ) * 2) * (↑(Nat.ceil (Real.logb 2 (4 / ε'))) + 1) := by ring
      _ ≤ ((Cs:ℝ) * 2) * (8 * Real.log (1 / ε')) :=
        mul_le_mul_of_nonneg_left hsum2 (mul_nonneg hcs (by norm_num))
  have hmain : ((Cs:ℝ) * 2) * (8 * Real.log (1 / ε')) ≤
      100 * ((Cs:ℝ) + 1) * Real.log (1 / ε') := by
    have hcs : (0:ℝ) ≤ Cs := Nat.cast_nonneg _
    nlinarith [hLpos, mul_nonneg hcs (le_of_lt hLpos)]
  linarith
end
noncomputable section

/-- A sign approximation family yields even rectangle polynomials of degree at most `ceil (C *
log (1 / ε') / δ')` with the stated inner and outer band bounds, for one universal constant
depending on the family. -/
theorem clause48_of_sign {Cs : ℕ} (hs : SignFamily Cs) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (δ' ε' t : ℝ), 0 < δ' → δ' ≤ 1 / 2 → 0 < ε' → ε' ≤ 1 / 2 →
        t ∈ Set.Icc (-1 : ℝ) 1 →
        ∃ P : Polynomial ℝ,
          P.natDegree ≤ Nat.ceil (C * Real.log (1 / ε') / δ') ∧
          (∀ x : ℝ, P.eval (-x) = P.eval x) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, |x| ≤ t - δ' →
            1 - ε' ≤ P.eval x ∧ P.eval x ≤ 1) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, t + δ' ≤ |x| →
            0 ≤ P.eval x ∧ P.eval x ≤ ε') := by
  refine ⟨100 * ((Cs : ℝ) + 1), ?_, ?_⟩
  · have : (0:ℝ) ≤ Cs := Nat.cast_nonneg _
    nlinarith
  · intro δ' ε' t hδ' hδ'2 hε' hε'2 ht
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    obtain ⟨P, hdeg, hb⟩ := rect_of_sign hs δ' ε' t hδ' hδ'2 hε' hε'2 ht'
    have hcast : ((Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) : ℕ) : ℝ) ≤
        100 * ((Cs:ℝ) + 1) * Real.log (1 / ε') / δ' :=
      (le_div_iff₀ hδ').mpr (rectDegree_mul_le hδ' hδ'2 hε' hε'2)
    have hdeg' : P.natDegree ≤ Nat.ceil (100 * ((Cs:ℝ) + 1) * Real.log (1 / ε') / δ') := by
      have h1 : (P.natDegree : ℝ) ≤
          (100 * ((Cs:ℝ) + 1) * Real.log (1 / ε') / δ' : ℝ) := by
        have h2 : (P.natDegree : ℝ) ≤
            ((Cs * Nat.ceil (1 / δ') * (Nat.ceil (Real.logb 2 (4 / ε')) + 1) : ℕ) : ℝ) :=
          Nat.cast_le.mpr hdeg
        exact le_trans h2 hcast
      exact Nat.cast_le.mp (le_trans h1 (Nat.le_ceil _))
    refine ⟨P, hdeg', ?_, ?_, ?_, ?_⟩
    · exact hb.1
    · exact hb.2.1
    · intro x hx hband
      apply hb.2.2.1 x hx
      · have habs := abs_le.mp hband
        nlinarith [abs_nonneg x]
      · exact (abs_le.mp hband).2
    · intro x hx hband
      apply hb.2.2.2 x hx
      rcases le_total 0 x with h | h
      · exact Or.inr (by rwa [abs_of_nonneg h] at hband)
      · rw [abs_of_nonpos h] at hband
        exact Or.inl (by nlinarith)
end
end Qatlib.Concepts.QsvtCore.PhaseExistence
