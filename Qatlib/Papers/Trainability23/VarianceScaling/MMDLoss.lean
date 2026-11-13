/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Haar variance formulas for product kernel losses

This module defines single-qubit Born weights and a two-outcome Gaussian kernel, then computes
the Haar moments of the self-term `sOne` and cross-term `xOne`. Product Haar integration gives
exact first moments, second moments, and variance formulas for `sN` and the full product loss
`mmdN`. See [RudolphEtAl2024].

## Main statements

* `mmdOne_variance_eq_BC`: a single-qubit variance decomposition into a target-independent term
  and a squared target-bias term.
* `sN_variance_eq`: the variance of the product self-term is a difference of powers.
* `mmdN_variance_eq`: the full product-loss variance combines self-term variance, covariance,
  and cross-term variance.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Papers.Trainability23.HaarAverages

open Qatlib.Papers.Trainability23.HaarAverages MeasureTheory

namespace Qatlib.Papers.Trainability23.VarianceScaling

noncomputable section

local instance instMeasurableSpaceMatrix₂ (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelSpaceMatrix₂ (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

/-- The single-qubit off-diagonal kernel factor `Real.exp (-(1 / (2 * σ)))`. -/
def kernOne (σ : ℝ) : ℝ := Real.exp (-(1 / (2 * σ)))

/-- The two-outcome kernel with value one on equal outcomes and `kernOne σ` on distinct
outcomes. -/
def gaussKernelOne (σ : ℝ) (x y : Fin 2) : ℝ := if x = y then 1 else kernOne σ

/-- The squared norm of entry `(x, 0)` of a single-qubit unitary, giving its Born probability
from the zero input state. -/
def bornProbOne (V : Matrix.unitaryGroup (Fin 2) ℂ) (x : Fin 2) : ℝ :=
  ‖(V : Matrix (Fin 2) (Fin 2) ℂ) x 0‖ ^ 2

/-- The two real outcome weights `t` at zero and `1 - t` at one. -/
def pTildeOne (t : ℝ) (x : Fin 2) : ℝ := if x = 0 then t else 1 - t

/-- The single-qubit quadratic kernel loss comparing the Born probabilities of `V` with the
weights `pTildeOne t`. -/
def mmdOne (σ t : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  ∑ x, ∑ y, bornProbOne V x * bornProbOne V y * gaussKernelOne σ x y
    - 2 * ∑ x, ∑ y, bornProbOne V x * pTildeOne t y * gaussKernelOne σ x y
    + ∑ x, ∑ y, pTildeOne t x * pTildeOne t y * gaussKernelOne σ x y

/-- The two Born probabilities `bornProbOne V 0` and `bornProbOne V 1` sum to one. -/
theorem unitary_col_norm_sq' (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    bornProbOne V 0 + bornProbOne V 1 = 1 := by
  have h := unitary_col_norm_sq V
  unfold bornProbOne at h ⊢
  linarith

/-- Expands the single-qubit kernel loss as a quadratic polynomial in `bornProbOne V 0` with
coefficients determined by `σ` and `t`. -/
theorem mmdOne_eq (σ t : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    mmdOne σ t V
      = 2 * (1 - kernOne σ) * (bornProbOne V 0)^2
        + ((-4 * t * (1 - kernOne σ)) * bornProbOne V 0
          + (1 - 2 * ((1 - t) + kernOne σ * t)
            + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))) := by
  have hcol : bornProbOne V 1 = 1 - bornProbOne V 0 := by
    have h := unitary_col_norm_sq' V
    linarith
  simp [mmdOne, Fin.sum_univ_two, gaussKernelOne, pTildeOne]
  rw [hcol]
  ring

/-- Every natural power of the zero-outcome Born probability is Haar integrable. -/
theorem integrable_bornPow (k : ℕ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (bornProbOne V 0)^k)
      (haarUnitaryGroup (Fin 2)) := by
  refine (integrable_symMoment k 0).congr (Filter.Eventually.of_forall fun V => ?_)
  simp only [bornProbOne, ← pow_mul, show (2:ℕ) * 0 = 0 from rfl, pow_zero, mul_one]

/-- The Haar integral of the `k`th power of the zero-outcome Born probability is `symMoment k
0`. -/
theorem integral_bornPow (k : ℕ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (bornProbOne V 0)^k ∂haarUnitaryGroup (Fin 2)
      = symMoment k 0 := by
  unfold symMoment
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only [bornProbOne, ← pow_mul, show (2:ℕ) * 0 = 0 from rfl, pow_zero, mul_one]

/-- Integrates a quadratic polynomial in the zero-outcome Born probability using its first two
Haar moments. -/
theorem integral_poly (a2 a1 a0 : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
        (a2 * (bornProbOne V 0)^2 + (a1 * bornProbOne V 0 + a0)) ∂haarUnitaryGroup (Fin 2)
      = a2 * symMoment 2 0 + (a1 * symMoment 1 0 + a0) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  haveI i2 : Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      a2 * (bornProbOne V 0)^2) (haarUnitaryGroup (Fin 2)) :=
    (integrable_bornPow 2).const_mul a2
  haveI i1 : Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      a1 * bornProbOne V 0) (haarUnitaryGroup (Fin 2)) := by
    refine ((integrable_bornPow 1).const_mul a1).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact congrArg (a1 * ·) (pow_one _)
  haveI i0 : Integrable (fun _ : Matrix.unitaryGroup (Fin 2) ℂ => a0)
      (haarUnitaryGroup (Fin 2)) := integrable_const _
  have e2 : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a2 * (bornProbOne V 0)^2
      ∂haarUnitaryGroup (Fin 2) = a2 * symMoment 2 0 := by
    rw [integral_const_mul a2 (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (bornProbOne V 0)^2),
      integral_bornPow 2]
  have e1 : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a1 * bornProbOne V 0
      ∂haarUnitaryGroup (Fin 2) = a1 * symMoment 1 0 := by
    rw [show (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a1 * bornProbOne V 0
        ∂haarUnitaryGroup (Fin 2))
        = ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a1 * (bornProbOne V 0)^(1:ℕ)
          ∂haarUnitaryGroup (Fin 2) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      exact congrArg (a1 * ·) (pow_one _).symm,
      integral_const_mul a1 (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (bornProbOne V 0)^(1:ℕ)),
      integral_bornPow 1]
  have e0 : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a0 ∂haarUnitaryGroup (Fin 2) = a0 := by
    rw [integral_const, haarUnitaryGroup_real_univ, one_smul]
  calc ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
        (a2 * (bornProbOne V 0)^2 + (a1 * bornProbOne V 0 + a0)) ∂haarUnitaryGroup (Fin 2)
      = (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a2 * (bornProbOne V 0)^2
          ∂haarUnitaryGroup (Fin 2))
        + (∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
            (a1 * bornProbOne V 0 + a0) ∂haarUnitaryGroup (Fin 2)) :=
        integral_add i2 (i1.add i0)
    _ = (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a2 * (bornProbOne V 0)^2
          ∂haarUnitaryGroup (Fin 2))
        + ((∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a1 * bornProbOne V 0
            ∂haarUnitaryGroup (Fin 2))
          + (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a0 ∂haarUnitaryGroup (Fin 2))) :=
        congrArg (fun X => (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, a2 * (bornProbOne V 0)^2
            ∂haarUnitaryGroup (Fin 2)) + X) (integral_add i1 i0)
    _ = a2 * symMoment 2 0 + (a1 * symMoment 1 0 + a0) := by rw [e2, e1, e0]

/-- Integrates a quartic polynomial in the zero-outcome Born probability using its first four
Haar moments. -/
theorem integral_poly4 (a4 a3 a2 a1 a0 : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
        (a4 * (bornProbOne V 0)^4 + (a3 * (bornProbOne V 0)^3 + (a2 * (bornProbOne V 0)^2
          + (a1 * (bornProbOne V 0)^(1:ℕ) + a0)))) ∂haarUnitaryGroup (Fin 2)
      = a4 * symMoment 4 0 + (a3 * symMoment 3 0 + (a2 * symMoment 2 0
        + (a1 * symMoment 1 0 + a0))) := by
  have hfun : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        a4 * (bornProbOne V 0)^4 + (a3 * (bornProbOne V 0)^3 + (a2 * (bornProbOne V 0)^2
          + (a1 * (bornProbOne V 0)^(1:ℕ) + a0))))
      = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∑ i : Fin 5, (if i = 0 then a4 else if i = 1 then a3 else if i = 2 then a2
          else if i = 3 then a1 else a0)
          * (bornProbOne V 0)^(if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2
            else if i = 3 then 1 else 0) := by
    funext V
    rw [Fin.sum_univ_five]
    simp
    ring
  rw [hfun]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
    ((integrable_bornPow (if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2
      else if i = 3 then 1 else 0))).const_mul
      (if i = 0 then a4 else if i = 1 then a3 else if i = 2 then a2
        else if i = 3 then a1 else a0))]
  rw [Fin.sum_univ_five]
  simp
  have key (k : ℕ) (c : ℝ) : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ,
      c * (bornProbOne V 0)^k ∂haarUnitaryGroup (Fin 2) = c * symMoment k 0 := by
    haveI : MeasureTheory.Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        c * (bornProbOne V 0)^k) (haarUnitaryGroup (Fin 2)) :=
      (integrable_bornPow k).const_mul c
    rw [integral_const_mul c (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (bornProbOne V 0)^k),
      integral_bornPow k]
  have key1 (c : ℝ) : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, c * bornProbOne V 0
      ∂haarUnitaryGroup (Fin 2) = c * symMoment 1 0 := by
    rw [show (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, c * bornProbOne V 0
        ∂haarUnitaryGroup (Fin 2))
        = ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, c * (bornProbOne V 0)^(1:ℕ)
          ∂haarUnitaryGroup (Fin 2) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
      exact congrArg (c * ·) (pow_one _).symm,
      key 1 c]
  rw [key 4 a4, key 3 a3, key 2 a2, key1 a1, haarUnitaryGroup_real_univ]
  ring

/-- For positive `σ`, the Haar variance expression for `mmdOne σ t` is `(1 - kernOne σ)^2 * (1 /
45 + (2 * t - 1)^2 / 3)`. -/
theorem mmdOne_variance_eq (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (mmdOne σ t V)^2 ∂haarUnitaryGroup (Fin 2))
      - (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, mmdOne σ t V ∂haarUnitaryGroup (Fin 2))^2
      = (1 - kernOne σ)^2 * (1/45 + (2*t - 1)^2/3) := by
  have hL : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ,
      mmdOne σ t V
        = 2 * (1 - kernOne σ) * (bornProbOne V 0)^2
          + ((-4 * t * (1 - kernOne σ)) * bornProbOne V 0
            + (1 - 2 * ((1 - t) + kernOne σ * t)
              + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))) := fun V => mmdOne_eq σ t V
  have hE1 : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, mmdOne σ t V ∂haarUnitaryGroup (Fin 2)
      = 2 * (1 - kernOne σ) * symMoment 2 0 + ((-4 * t * (1 - kernOne σ)) * symMoment 1 0
        + (1 - 2 * ((1 - t) + kernOne σ * t)
            + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL)]
    exact integral_poly _ _ _
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (mmdOne σ t V)^2
      = (2 * (1 - kernOne σ))^2 * (bornProbOne V 0)^4
        + (2 * (2 * (1 - kernOne σ)) * (-4 * t * (1 - kernOne σ)) * (bornProbOne V 0)^3
          + (((-4 * t * (1 - kernOne σ))^2 + 2 * (2 * (1 - kernOne σ))
              * (1 - 2 * ((1 - t) + kernOne σ * t)
                + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))) * (bornProbOne V 0)^2
            + (2 * (-4 * t * (1 - kernOne σ))
                * (1 - 2 * ((1 - t) + kernOne σ * t)
                  + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ)) * (bornProbOne V 0)^(1:ℕ)
              + (1 - 2 * ((1 - t) + kernOne σ * t)
                  + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))^2))) := by
    intro V
    rw [hL V]
    ring
  have hE2 : ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (mmdOne σ t V)^2 ∂haarUnitaryGroup (Fin 2)
      = (2 * (1 - kernOne σ))^2 * symMoment 4 0
        + (2 * (2 * (1 - kernOne σ)) * (-4 * t * (1 - kernOne σ)) * symMoment 3 0
          + (((-4 * t * (1 - kernOne σ))^2 + 2 * (2 * (1 - kernOne σ))
              * (1 - 2 * ((1 - t) + kernOne σ * t)
                + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))) * symMoment 2 0
            + (2 * (-4 * t * (1 - kernOne σ))
                * (1 - 2 * ((1 - t) + kernOne σ * t)
                  + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ)) * symMoment 1 0
              + (1 - 2 * ((1 - t) + kernOne σ * t)
                  + (t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ))^2))) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL2)]
    exact integral_poly4 _ _ _ _ _
  rw [hE1, hE2, symMoment_one.1, symMoment_two.1, symMoment_three.1, symMoment_four.1]
  ring

/-- Half of the single-qubit kernel gap, defined as `(1 - kernOne σ) / 2`. -/
def pSigmaOne (σ : ℝ) : ℝ := (1 - kernOne σ) / 2

/-- For positive bandwidth, the single-qubit loss variance is `(1 - kernOne σ)^2 / 45 + 4 *
(pSigmaOne σ)^2 * (2 * t - 1)^2 / 3`. See [RudolphEtAl2024]. -/
theorem mmdOne_variance_eq_BC (σ : ℝ) (hσ : 0 < σ) (t : ℝ) :
    (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (mmdOne σ t V)^2 ∂haarUnitaryGroup (Fin 2))
      - (∫ V : Matrix.unitaryGroup (Fin 2) ℂ, mmdOne σ t V ∂haarUnitaryGroup (Fin 2))^2
      = (1 - kernOne σ)^2 / 45 + 4 * ((pSigmaOne σ)^2 / 3) * (2*t - 1)^2 := by
  rw [mmdOne_variance_eq σ hσ t]
  unfold pSigmaOne
  ring

/-- The single-qubit model self-term obtained by averaging `gaussKernelOne` against two copies
of the Born probabilities. -/
def sOne (σ : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  ∑ x, ∑ y, bornProbOne V x * bornProbOne V y * gaussKernelOne σ x y

/-- The self-term `sOne` is a quadratic polynomial in the zero-outcome Born probability. -/
theorem sOne_eq (σ : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    sOne σ V = 2 * (1 - kernOne σ) * (bornProbOne V 0)^2
      + ((2 * kernOne σ - 2) * bornProbOne V 0 + 1) := by
  have hcol : bornProbOne V 1 = 1 - bornProbOne V 0 := by
    have h := unitary_col_norm_sq' V
    linarith
  simp [sOne, Fin.sum_univ_two, gaussKernelOne]
  rw [hcol]
  ring

/-- The Haar mean of `sOne σ` is `(2 + kernOne σ) / 3`. -/
theorem sOne_integral (σ : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, sOne σ V ∂haarUnitaryGroup (Fin 2)
      = (2 + kernOne σ) / 3 := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun V => sOne_eq σ V))]
  rw [integral_poly]
  rw [symMoment_two.1, symMoment_one.1]
  ring

/-- Every quartic polynomial in the zero-outcome Born probability is Haar integrable. -/
theorem integrable_quartic (a4 a3 a2 a1 a0 : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      a4 * (bornProbOne V 0)^4 + (a3 * (bornProbOne V 0)^3 + (a2 * (bornProbOne V 0)^2
        + (a1 * (bornProbOne V 0)^(1:ℕ) + a0)))) (haarUnitaryGroup (Fin 2)) := by
  have hfun : (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      a4 * (bornProbOne V 0)^4 + (a3 * (bornProbOne V 0)^3 + (a2 * (bornProbOne V 0)^2
        + (a1 * (bornProbOne V 0)^(1:ℕ) + a0))))
      = fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
        ∑ i : Fin 5, (if i = 0 then a4 else if i = 1 then a3 else if i = 2 then a2
          else if i = 3 then a1 else a0)
          * (bornProbOne V 0)^(if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2
            else if i = 3 then 1 else 0) := by
    funext V
    rw [Fin.sum_univ_five]
    simp
    ring
  rw [hfun]
  exact MeasureTheory.integrable_finsetSum Finset.univ (fun i _ =>
    ((integrable_bornPow (if i = 0 then 4 else if i = 1 then 3 else if i = 2 then 2
      else if i = 3 then 1 else 0))).const_mul
      (if i = 0 then a4 else if i = 1 then a3 else if i = 2 then a2
        else if i = 3 then a1 else a0))

/-- The Haar second moment of `sOne σ` is `(7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15`. -/
theorem sOne_sq_integral (σ : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (sOne σ V)^2 ∂haarUnitaryGroup (Fin 2)
      = (7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15 := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (sOne σ V)^2
      = (2 * (1 - kernOne σ))^2 * (bornProbOne V 0)^4
        + (2 * (2 * (1 - kernOne σ)) * (2 * kernOne σ - 2) * (bornProbOne V 0)^3
          + (((2 * kernOne σ - 2)^2 + 2 * (2 * (1 - kernOne σ))) * (bornProbOne V 0)^2
            + (2 * (2 * kernOne σ - 2) * (bornProbOne V 0)^(1:ℕ) + 1))) := by
    intro V
    rw [sOne_eq σ V]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL2)]
  rw [integral_poly4]
  rw [symMoment_four.1, symMoment_three.1, symMoment_two.1, symMoment_one.1]
  ring

/-- The single-qubit model self-term is Haar integrable. -/
theorem integrable_sOne (σ : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V)
      (haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have h2 : Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      2 * (1 - kernOne σ) * (bornProbOne V 0)^2) (haarUnitaryGroup (Fin 2)) :=
    (integrable_bornPow 2).const_mul (2 * (1 - kernOne σ))
  have h1 : Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      (2 * kernOne σ - 2) * bornProbOne V 0) (haarUnitaryGroup (Fin 2)) := by
    refine ((integrable_bornPow 1).const_mul (2 * kernOne σ - 2)).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact congrArg ((2 * kernOne σ - 2) * ·) (pow_one _)
  have h0 : Integrable (fun _ : Matrix.unitaryGroup (Fin 2) ℂ => (1 : ℝ))
      (haarUnitaryGroup (Fin 2)) := integrable_const _
  exact (h2.add (h1.add h0)).congr
    (Filter.Eventually.of_forall fun V => (sOne_eq σ V).symm)

/-- The square of the single-qubit model self-term is Haar integrable. -/
theorem integrable_sOne_sq (σ : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (sOne σ V)^2)
      (haarUnitaryGroup (Fin 2)) := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (sOne σ V)^2
      = (2 * (1 - kernOne σ))^2 * (bornProbOne V 0)^4
        + (2 * (2 * (1 - kernOne σ)) * (2 * kernOne σ - 2) * (bornProbOne V 0)^3
          + (((2 * kernOne σ - 2)^2 + 2 * (2 * (1 - kernOne σ))) * (bornProbOne V 0)^2
            + (2 * (2 * kernOne σ - 2) * (bornProbOne V 0)^(1:ℕ) + 1))) := by
    intro V
    rw [sOne_eq σ V]
    ring
  exact (integrable_quartic _ _ _ _ _).congr
    (Filter.Eventually.of_forall fun V => (hL2 V).symm)

/-- The two-qubit product Born probability formed from the two single-qubit Born probabilities. -/
def bornProbTwo (V₁ V₂ : Matrix.unitaryGroup (Fin 2) ℂ) (x : Fin 2 × Fin 2) : ℝ :=
  bornProbOne V₁ x.1 * bornProbOne V₂ x.2

/-- The product of the two single-qubit kernel factors on paired outcomes. -/
def gaussKernelTwo (σ : ℝ) (x y : Fin 2 × Fin 2) : ℝ :=
  gaussKernelOne σ x.1 y.1 * gaussKernelOne σ x.2 y.2

/-- The two-qubit product-model self-term obtained by summing the two-copy kernel against
product Born probabilities. -/
def sTwo (σ : ℝ) (V₁ V₂ : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2,
    bornProbTwo V₁ V₂ x * bornProbTwo V₁ V₂ y * gaussKernelTwo σ x y

/-- The two-qubit self-term factors into the product of its two single-qubit self-terms. -/
theorem sTwo_eq (σ : ℝ) (V₁ V₂ : Matrix.unitaryGroup (Fin 2) ℂ) :
    sTwo σ V₁ V₂ = sOne σ V₁ * sOne σ V₂ := by
  simp [sTwo, sOne, bornProbTwo, gaussKernelTwo, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The product-Haar mean of `sTwo σ` is `((2 + kernOne σ) / 3)^2`. -/
theorem sTwo_integral (σ : ℝ) :
    ∫ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
        sTwo σ p.1 p.2 ∂((haarUnitaryGroup (Fin 2)).prod (haarUnitaryGroup (Fin 2)))
      = ((2 + kernOne σ) / 3)^2 := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hcongr : ∀ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
      sTwo σ p.1 p.2 = sOne σ p.1 * sOne σ p.2 := fun p => sTwo_eq σ p.1 p.2
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_prod_mul (μ := haarUnitaryGroup (Fin 2))
      (ν := haarUnitaryGroup (Fin 2))
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V)
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V),
    sOne_integral]
  ring

/-- The product-Haar second moment of `sTwo σ` is the square of `(7 + 6 * kernOne σ + 2 *
(kernOne σ)^2) / 15`. -/
theorem sTwo_sq_integral (σ : ℝ) :
    ∫ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
        (sTwo σ p.1 p.2)^2 ∂((haarUnitaryGroup (Fin 2)).prod (haarUnitaryGroup (Fin 2)))
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^2 := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hp : ∀ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
      (sTwo σ p.1 p.2)^2 = (sOne σ p.1)^2 * (sOne σ p.2)^2 := by
    intro p
    rw [sTwo_eq σ p.1 p.2, mul_pow]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp),
    MeasureTheory.integral_prod_mul (μ := haarUnitaryGroup (Fin 2))
      (ν := haarUnitaryGroup (Fin 2))
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (sOne σ V)^2)
      (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (sOne σ V)^2),
    sOne_sq_integral]
  ring

/-- The product-Haar variance expression for `sTwo σ` is the square of its single-qubit
second-moment base minus the square of its single-qubit squared-mean base. See
[RudolphEtAl2024]. -/
theorem sTwo_variance_eq (σ : ℝ) :
    (∫ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
        (sTwo σ p.1 p.2)^2 ∂((haarUnitaryGroup (Fin 2)).prod (haarUnitaryGroup (Fin 2))))
      - (∫ p : Matrix.unitaryGroup (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ,
          sTwo σ p.1 p.2 ∂((haarUnitaryGroup (Fin 2)).prod (haarUnitaryGroup (Fin 2))))^2
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^2
        - ((4 + 4 * kernOne σ + (kernOne σ)^2) / 9)^2 := by
  rw [sTwo_sq_integral, sTwo_integral]
  ring

/-- The product of `n` single-qubit model self-terms. -/
def sN (σ : ℝ) (n : ℕ) (V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  ∏ i, sOne σ (V i)

/-- The mean of `sN σ n` under independent Haar unitaries is `((2 + kernOne σ) / 3)^n`. -/
theorem sN_integral (σ : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, sN σ n V
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((2 + kernOne σ) / 3)^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, sOne_integral] at h
  simp only [sN]
  exact h

/-- The second moment of `sN σ n` under independent Haar unitaries is the `n`th power of `(7 + 6
* kernOne σ + 2 * (kernOne σ)^2) / 15`. -/
theorem sN_sq_integral (σ : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (sN σ n V)^2
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hexp : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ,
      (sN σ n V)^2 = ∏ i, (sOne σ (V i))^2 := by
    intro V
    rw [sN]
    exact (Finset.prod_pow Finset.univ 2 (fun i => sOne σ (V i))).symm
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => (sOne σ V)^2)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, sOne_sq_integral] at h
  exact h

/-- The product-Haar variance of `sN σ n` is the difference of the `n`th powers of the
single-qubit second moment and squared mean. See [RudolphEtAl2024]. -/
theorem sN_variance_eq (σ : ℝ) (n : ℕ) :
    (∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (sN σ n V)^2
        ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)))
      - (∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, sN σ n V
          ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)))^2
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^n
        - ((4 + 4 * kernOne σ + (kernOne σ)^2) / 9)^n := by
  rw [sN_sq_integral, sN_integral]
  have hpow : ∀ x : ℝ, (x^n)^2 = (x^2)^n := by
    intro x
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ x n, pow_succ (x^2) n, ← ih]; ring
  have hsq : ((2 + kernOne σ) / 3)^2 = (4 + 4 * kernOne σ + (kernOne σ)^2) / 9 := by ring
  rw [hpow ((2 + kernOne σ) / 3), hsq]

/-- The product self-term with zero qubits has zero Haar variance expression. -/
theorem sN_variance_zero (σ : ℝ) :
    (∫ V : Fin 0 → Matrix.unitaryGroup (Fin 2) ℂ, (sN σ 0 V)^2
        ∂(Measure.pi fun _ : Fin 0 => haarUnitaryGroup (Fin 2)))
      - (∫ V : Fin 0 → Matrix.unitaryGroup (Fin 2) ℂ, sN σ 0 V
          ∂(Measure.pi fun _ : Fin 0 => haarUnitaryGroup (Fin 2)))^2
      = 0 := by
  rw [sN_variance_eq σ 0]
  norm_num

/-- The single-qubit kernel cross-term between the Born probabilities and the target weights
`pTildeOne t`. -/
def xOne (σ t : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  ∑ x, ∑ y, bornProbOne V x * pTildeOne t y * gaussKernelOne σ x y

/-- The single-qubit target self-term formed from two copies of the weights `pTildeOne t`. -/
def gOne (σ t : ℝ) : ℝ :=
  ∑ x, ∑ y, pTildeOne t x * pTildeOne t y * gaussKernelOne σ x y

/-- The cross-term `xOne σ t` is affine in the zero-outcome Born probability, with slope `(2 * t
- 1) * (1 - kernOne σ)`. -/
theorem xOne_eq (σ t : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    xOne σ t V
      = (1 - t + t * kernOne σ) + ((2*t - 1) * (1 - kernOne σ)) * bornProbOne V 0 := by
  have hcol : bornProbOne V 1 = 1 - bornProbOne V 0 := by
    have h := unitary_col_norm_sq' V
    linarith
  simp [xOne, Fin.sum_univ_two, gaussKernelOne, pTildeOne]
  rw [hcol]
  ring

/-- The target self-term is `t^2 + (1 - t)^2 + 2 * t * (1 - t) * kernOne σ`. -/
theorem gOne_eq (σ t : ℝ) :
    gOne σ t = t^2 + ((1 - t)^2 + 2 * t * (1 - t) * kernOne σ) := by
  simp [gOne, Fin.sum_univ_two, gaussKernelOne, pTildeOne]
  ring

/-- The Haar mean of `xOne σ t` is `(1 + kernOne σ) / 2`, independently of `t`. -/
theorem xOne_integral (σ t : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, xOne σ t V ∂haarUnitaryGroup (Fin 2)
      = (1 + kernOne σ) / 2 := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, xOne σ t V
      = 0 * (bornProbOne V 0)^2
        + (((2*t - 1) * (1 - kernOne σ)) * bornProbOne V 0
          + (1 - t + t * kernOne σ)) := by
    intro V
    rw [xOne_eq σ t V]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL2)]
  rw [integral_poly]
  rw [symMoment_two.1, symMoment_one.1]
  ring

/-- For the affine expression of `xOne`, its Haar second moment is the squared slope divided by
three plus the intercept-slope product and the squared intercept. -/
theorem xOne_sq_integral (σ t : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, (xOne σ t V)^2 ∂haarUnitaryGroup (Fin 2)
      = ((2*t - 1) * (1 - kernOne σ))^2 / 3
        + ((1 - t + t * kernOne σ) * ((2*t - 1) * (1 - kernOne σ))
          + (1 - t + t * kernOne σ)^2) := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (xOne σ t V)^2
      = ((2*t - 1) * (1 - kernOne σ))^2 * (bornProbOne V 0)^2
        + ((2 * ((2*t - 1) * (1 - kernOne σ)) * (1 - t + t * kernOne σ)) * bornProbOne V 0
          + (1 - t + t * kernOne σ)^2) := by
    intro V
    rw [xOne_eq σ t V]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL2)]
  rw [integral_poly]
  rw [symMoment_two.1, symMoment_one.1]
  ring

/-- Expands the product of the single-qubit self-term and cross-term as a cubic polynomial in
the zero-outcome Born probability. -/
theorem sOne_mul_xOne_eq (σ t : ℝ) (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    sOne σ V * xOne σ t V
      = (2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^3
        + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
            + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^2
          + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
              + ((2*t - 1) * (1 - kernOne σ))) * bornProbOne V 0
            + (1 - t + t * kernOne σ))) := by
  rw [sOne_eq σ V, xOne_eq σ t V]
  ring

/-- Evaluates the mixed Haar moment of `sOne σ` and `xOne σ t` by weighting their cubic
expansion with moments `1 / 4`, `1 / 3`, `1 / 2`, and one. -/
theorem sOne_xOne_integral (σ t : ℝ) :
    ∫ V : Matrix.unitaryGroup (Fin 2) ℂ, sOne σ V * xOne σ t V ∂haarUnitaryGroup (Fin 2)
      = (2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) / 4
        + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
            + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) / 3
          + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
              + ((2*t - 1) * (1 - kernOne σ))) / 2
            + (1 - t + t * kernOne σ))) := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, sOne σ V * xOne σ t V
      = 0 * (bornProbOne V 0)^4
        + ((2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^3
          + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
              + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^2
            + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
                + ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^(1:ℕ)
              + (1 - t + t * kernOne σ)))) := by
    intro V
    rw [sOne_eq σ V, xOne_eq σ t V]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hL2)]
  rw [integral_poly4]
  rw [symMoment_four.1, symMoment_three.1, symMoment_two.1, symMoment_one.1]
  ring

/-- The single-qubit cross-term `xOne σ t` is Haar integrable. -/
theorem integrable_xOne (σ t : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => xOne σ t V)
      (haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, xOne σ t V
      = ((2*t - 1) * (1 - kernOne σ)) * bornProbOne V 0 + (1 - t + t * kernOne σ) := by
    intro V
    rw [xOne_eq σ t V]
    ring
  have h2 : Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ =>
      ((2*t - 1) * (1 - kernOne σ)) * bornProbOne V 0) (haarUnitaryGroup (Fin 2)) := by
    refine ((integrable_bornPow 1).const_mul ((2*t - 1) * (1 - kernOne σ))).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact congrArg (((2*t - 1) * (1 - kernOne σ)) * ·) (pow_one _)
  have h0 : Integrable (fun _ : Matrix.unitaryGroup (Fin 2) ℂ =>
      (1 - t + t * kernOne σ : ℝ)) (haarUnitaryGroup (Fin 2)) := integrable_const _
  exact (h2.add h0).congr
    (Filter.Eventually.of_forall fun V => (hL2 V).symm)

/-- The square of the single-qubit cross-term is Haar integrable. -/
theorem integrable_xOne_sq (σ t : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => (xOne σ t V)^2)
      (haarUnitaryGroup (Fin 2)) := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, (xOne σ t V)^2
      = 0 * (bornProbOne V 0)^4
        + (0 * (bornProbOne V 0)^3
          + (((2*t - 1) * (1 - kernOne σ))^2 * (bornProbOne V 0)^2
            + ((2 * ((2*t - 1) * (1 - kernOne σ)) * (1 - t + t * kernOne σ)) * (bornProbOne V 0)^(1:ℕ)
              + (1 - t + t * kernOne σ)^2))) := by
    intro V
    rw [xOne_eq σ t V]
    ring
  exact (integrable_quartic 0 0 _ _ _).congr
    (Filter.Eventually.of_forall fun V => (hL2 V).symm)

/-- The product of the single-qubit self-term and cross-term is Haar integrable. -/
theorem integrable_sOne_mul_xOne (σ t : ℝ) :
    Integrable (fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V * xOne σ t V)
      (haarUnitaryGroup (Fin 2)) := by
  have hL2 : ∀ V : Matrix.unitaryGroup (Fin 2) ℂ, sOne σ V * xOne σ t V
      = 0 * (bornProbOne V 0)^4
        + ((2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^3
          + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
              + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^2
            + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
                + ((2*t - 1) * (1 - kernOne σ))) * (bornProbOne V 0)^(1:ℕ)
              + (1 - t + t * kernOne σ)))) := by
    intro V
    rw [sOne_eq σ V, xOne_eq σ t V]
    ring
  exact (integrable_quartic 0 _ _ _ _).congr
    (Filter.Eventually.of_forall fun V => (hL2 V).symm)

/-- The integral of the product of `n` self-terms under product Haar measure is `((2 + kernOne
σ) / 3)^n`. -/
theorem int_prodS (σ : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (∏ i, sOne σ (V i))
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((2 + kernOne σ) / 3)^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, sOne_integral] at h
  exact h

/-- The second moment of the product of `n` self-terms is the `n`th power of the single-qubit
self-term second moment. -/
theorem int_prodS2 (σ : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (∏ i, sOne σ (V i))^2
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hp : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ,
      (∏ i, sOne σ (V i))^2 = ∏ i, (sOne σ (V i))^2 := fun V =>
    (Finset.prod_pow Finset.univ 2 (fun i => sOne σ (V i))).symm
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp)]
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => (sOne σ V)^2)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, sOne_sq_integral] at h
  exact h

/-- The integral of the product of `n` cross-terms under product Haar measure is `((1 + kernOne
σ) / 2)^n`. -/
theorem int_prodX (σ t : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (∏ i, xOne σ t (V i))
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((1 + kernOne σ) / 2)^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => xOne σ t V)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, xOne_integral] at h
  exact h

/-- The second moment of the product of `n` cross-terms is the `n`th power of the single-qubit
cross-term second moment. -/
theorem int_prodX2 (σ t : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (∏ i, xOne σ t (V i))^2
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = (((2*t - 1) * (1 - kernOne σ))^2 / 3
          + ((1 - t + t * kernOne σ) * ((2*t - 1) * (1 - kernOne σ))
            + (1 - t + t * kernOne σ)^2))^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hp : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ,
      (∏ i, xOne σ t (V i))^2 = ∏ i, (xOne σ t (V i))^2 := fun V =>
    (Finset.prod_pow Finset.univ 2 (fun i => xOne σ t (V i))).symm
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp)]
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => (xOne σ t V)^2)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, xOne_sq_integral] at h
  exact h

/-- The product-Haar integral of the product self-term times the product cross-term is the `n`th
power of their single-qubit mixed moment. -/
theorem int_prodSX (σ t : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ,
        (∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i))
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) / 4
          + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
              + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) / 3
            + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
                + ((2*t - 1) * (1 - kernOne σ))) / 2
              + (1 - t + t * kernOne σ))))^n := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  have hp : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ,
      (∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i))
        = ∏ i, (sOne σ (V i) * xOne σ t (V i)) := fun V =>
    Finset.prod_mul_distrib.symm
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hp)]
  have h := MeasureTheory.integral_fintype_prod_eq_pow
    (ι := Fin n) (f := fun V : Matrix.unitaryGroup (Fin 2) ℂ => sOne σ V * xOne σ t V)
    (μ := haarUnitaryGroup (Fin 2))
  rw [Fintype.card_fin, sOne_xOne_integral] at h
  exact h

/-- The product of `n` single-qubit self-terms is integrable under product Haar measure. -/
theorem integrable_prodS (σ : ℝ) (n : ℕ) :
    Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ∏ i, sOne σ (V i))
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  haveI hSig : ∀ i : Fin n, SigmaFinite ((fun _ : Fin n => haarUnitaryGroup (Fin 2)) i) :=
    fun _ => inferInstance
  exact @MeasureTheory.Integrable.fintype_prod ℝ (Fin n) (Fin.fintype n) _
    (Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => fun V => sOne σ V)
    (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ))
    (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hSig (fun _ => integrable_sOne σ)

/-- The product of `n` single-qubit cross-terms is integrable under product Haar measure. -/
theorem integrable_prodX (σ t : ℝ) (n : ℕ) :
    Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ∏ i, xOne σ t (V i))
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  haveI hSig : ∀ i : Fin n, SigmaFinite ((fun _ : Fin n => haarUnitaryGroup (Fin 2)) i) :=
    fun _ => inferInstance
  exact @MeasureTheory.Integrable.fintype_prod ℝ (Fin n) (Fin.fintype n) _
    (Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => fun V => xOne σ t V)
    (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ))
    (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hSig (fun _ => integrable_xOne σ t)

/-- The product kernel loss given by the product self-term minus twice the product cross-term
plus the `n`th power of the target self-term. -/
def mmdN (σ t : ℝ) (n : ℕ) (V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  (∏ i, sOne σ (V i)) - 2 * (∏ i, xOne σ t (V i)) + (gOne σ t)^n

/-- The explicit scalar expression for the mixed Haar moment of the single-qubit self-term and
cross-term. -/
def sXVal (σ t : ℝ) : ℝ :=
  (2 * (1 - kernOne σ) * ((2*t - 1) * (1 - kernOne σ))) / 4
    + ((2 * (1 - kernOne σ) * (1 - t + t * kernOne σ)
        + (2 * kernOne σ - 2) * ((2*t - 1) * (1 - kernOne σ))) / 3
      + (((2 * kernOne σ - 2) * (1 - t + t * kernOne σ)
          + ((2*t - 1) * (1 - kernOne σ))) / 2
        + (1 - t + t * kernOne σ)))

/-- The explicit scalar expression for the Haar second moment of the single-qubit cross-term. -/
def x2Val (σ t : ℝ) : ℝ :=
  ((2*t - 1) * (1 - kernOne σ))^2 / 3
    + ((1 - t + t * kernOne σ) * ((2*t - 1) * (1 - kernOne σ))
      + (1 - t + t * kernOne σ)^2)

/-- The finite product of normalized single-qubit Haar measures is a probability measure. -/
theorem piHaar_isProbability (n : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
  have hProbI : ∀ i : Fin n, MeasureTheory.IsProbabilityMeasure
      ((fun _ : Fin n => haarUnitaryGroup (Fin 2)) i) :=
    fun _ => ⟨haarUnitaryGroup_univ (Fin 2)⟩
  exact @Measure.pi.instIsProbabilityMeasure (Fin n) (fun _ => Matrix.unitaryGroup (Fin 2) ℂ)
    (Fin.fintype n)
    (fun _ : Fin n => (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ)))
    (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hProbI

/-- The product-Haar mean of `mmdN` is `((2 + kernOne σ) / 3)^n - 2 * ((1 + kernOne σ) / 2)^n +
(gOne σ t)^n`. -/
theorem mmdN_integral (σ t : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, mmdN σ t n V
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((2 + kernOne σ) / 3)^n
        + (-(2 * (((1 + kernOne σ) / 2)^n)) + (gOne σ t)^n) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  haveI : MeasureTheory.IsProbabilityMeasure (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) :=
    piHaar_isProbability n
  have hA := integrable_prodS σ n
  have hB := integrable_prodX σ t n
  have hC : Integrable (fun _ : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => (gOne σ t)^n)
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := integrable_const _
  have hpoint : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, mmdN σ t n V
      = (∏ i, sOne σ (V i)) + (-(2 * (∏ i, xOne σ t (V i))) + (gOne σ t)^n) := by
    intro V
    rw [mmdN]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ∏ i, sOne σ (V i))
    (g := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      -(2 * (∏ i, xOne σ t (V i))) + (gOne σ t)^n) hA (((hB.const_mul 2).neg).add hC)]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => -(2 * (∏ i, xOne σ t (V i))))
    (g := fun _ : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => (gOne σ t)^n)
    ((hB.const_mul 2).neg) hC]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, int_prodS, int_prodX]
  rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
    MeasureTheory.measure_univ, ENNReal.toReal_one, one_smul]

/-- The second moment of the full product loss expands into powers of the self-term second
moment, `sXVal`, `x2Val`, the target self-term, and the self-term and cross-term means. -/
theorem mmdN_sq_integral (σ t : ℝ) (n : ℕ) :
    ∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (mmdN σ t n V)^2
      ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2))
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^n
        + (-(4 * (sXVal σ t)^n)
          + (4 * (x2Val σ t)^n
            + (2 * (gOne σ t)^n * (((2 + kernOne σ) / 3)^n)
              + (-(4 * ((gOne σ t)^n * (((1 + kernOne σ) / 2)^n)))
                + ((gOne σ t)^n)^2)))) := by
  haveI : MeasureTheory.IsFiniteMeasure (haarUnitaryGroup (Fin 2)) :=
    ⟨by rw [haarUnitaryGroup_univ (Fin 2)]; exact ENNReal.one_lt_top⟩
  haveI : MeasureTheory.IsProbabilityMeasure (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) :=
    piHaar_isProbability n
  haveI hSig : ∀ i : Fin n, SigmaFinite ((fun _ : Fin n => haarUnitaryGroup (Fin 2)) i) :=
    fun _ => inferInstance
  have hA := integrable_prodS σ n
  have hB := integrable_prodX σ t n
  have hA2 : Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (∏ i, sOne σ (V i))^2) (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
    refine (@MeasureTheory.Integrable.fintype_prod ℝ (Fin n) (Fin.fintype n) _
      (Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => fun V => (sOne σ V)^2)
      (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ))
      (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hSig
      (fun _ => integrable_sOne_sq σ)).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact Finset.prod_pow Finset.univ 2 (fun i => sOne σ (V i))
  have hB2 : Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (∏ i, xOne σ t (V i))^2) (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
    refine (@MeasureTheory.Integrable.fintype_prod ℝ (Fin n) (Fin.fintype n) _
      (Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => fun V => (xOne σ t V)^2)
      (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ))
      (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hSig
      (fun _ => integrable_xOne_sq σ t)).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact Finset.prod_pow Finset.univ 2 (fun i => xOne σ t (V i))
  have hAB : Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i)))
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := by
    refine (@MeasureTheory.Integrable.fintype_prod ℝ (Fin n) (Fin.fintype n) _
      (Matrix.unitaryGroup (Fin 2) ℂ) (fun _ => fun V => sOne σ V * xOne σ t V)
      (inferInstance : MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ))
      (fun _ : Fin n => haarUnitaryGroup (Fin 2)) hSig
      (fun _ => integrable_sOne_mul_xOne σ t)).congr
      (Filter.Eventually.of_forall fun V => ?_)
    exact Finset.prod_mul_distrib
  have hC : Integrable (fun _ : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => (gOne σ t)^n)
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) := integrable_const _
  have hCA : Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (2 * (gOne σ t)^n) * (∏ i, sOne σ (V i)))
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) :=
    hA.const_mul (2 * (gOne σ t)^n)
  have hCB : Integrable (fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (gOne σ t)^n * (∏ i, xOne σ t (V i)))
      (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) :=
    hB.const_mul ((gOne σ t)^n)
  have hC2 : Integrable (fun _ : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      ((gOne σ t)^n)^2) (Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)) :=
    integrable_const _
  have hpoint : ∀ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (mmdN σ t n V)^2
      = (∏ i, sOne σ (V i))^2
        + (-(4 * ((∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i))))
          + (4 * (∏ i, xOne σ t (V i))^2
            + ((2 * (gOne σ t)^n) * (∏ i, sOne σ (V i))
              + (-(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i))))
                + ((gOne σ t)^n)^2)))) := by
    intro V
    rw [mmdN]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => (∏ i, sOne σ (V i))^2)
    (g := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      -(4 * ((∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i))))
        + (4 * (∏ i, xOne σ t (V i))^2
          + ((2 * (gOne σ t)^n) * (∏ i, sOne σ (V i))
            + (-(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i))))
              + ((gOne σ t)^n)^2))))
    hA2 (((hAB.const_mul 4).neg).add ((hB2.const_mul 4).add (hCA.add
      (((hCB.const_mul 4).neg).add hC2))))]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      -(4 * ((∏ i, sOne σ (V i)) * (∏ i, xOne σ t (V i)))))
    (g := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      4 * (∏ i, xOne σ t (V i))^2
        + ((2 * (gOne σ t)^n) * (∏ i, sOne σ (V i))
          + (-(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i))))
            + ((gOne σ t)^n)^2)))
    ((hAB.const_mul 4).neg) ((hB2.const_mul 4).add (hCA.add
      (((hCB.const_mul 4).neg).add hC2)))]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul, int_prodS2, int_prodSX]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      4 * (∏ i, xOne σ t (V i))^2)
    (g := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (2 * (gOne σ t)^n) * (∏ i, sOne σ (V i))
        + (-(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i))))
          + ((gOne σ t)^n)^2))
    (hB2.const_mul 4) (hCA.add (((hCB.const_mul 4).neg).add hC2))]
  rw [MeasureTheory.integral_const_mul, int_prodX2]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      (2 * (gOne σ t)^n) * (∏ i, sOne σ (V i)))
    (g := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      -(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i))))
        + ((gOne σ t)^n)^2)
    hCA (((hCB.const_mul 4).neg).add hC2)]
  rw [MeasureTheory.integral_const_mul, int_prodS]
  rw [MeasureTheory.integral_add
    (f := fun V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ =>
      -(4 * ((gOne σ t)^n * (∏ i, xOne σ t (V i)))))
    (g := fun _ : Fin n → Matrix.unitaryGroup (Fin 2) ℂ => ((gOne σ t)^n)^2)
    ((hCB.const_mul 4).neg) hC2]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul, int_prodX]
  rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
    MeasureTheory.measure_univ, ENNReal.toReal_one, one_smul]
  simp only [sXVal, x2Val]

/-- The product-Haar variance of the full kernel loss equals the self-term variance minus four
times the self-term/cross-term covariance plus four times the cross-term variance, with all
three expressed by powers of the single-qubit moments. See [RudolphEtAl2024]. -/
theorem mmdN_variance_eq (σ t : ℝ) (n : ℕ) :
    (∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, (mmdN σ t n V)^2
        ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)))
      - (∫ V : Fin n → Matrix.unitaryGroup (Fin 2) ℂ, mmdN σ t n V
          ∂(Measure.pi fun _ : Fin n => haarUnitaryGroup (Fin 2)))^2
      = ((7 + 6 * kernOne σ + 2 * (kernOne σ)^2) / 15)^n
        - (((2 + kernOne σ) / 3)^n)^2
        - 4 * ((sXVal σ t)^n
            - (((2 + kernOne σ) / 3)^n) * (((1 + kernOne σ) / 2)^n))
        + 4 * ((x2Val σ t)^n - (((1 + kernOne σ) / 2)^n)^2) := by
  rw [mmdN_sq_integral, mmdN_integral]
  simp only [sXVal, x2Val]
  ring
end

end Qatlib.Papers.Trainability23.VarianceScaling
