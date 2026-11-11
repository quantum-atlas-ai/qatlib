/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.TruncDyson18.MainResults.SourceParameters
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveDysonParameters
import Qatlib.Concepts.InteractionEvo.SegmentProduct.EffectiveProductPerturbationHami

set_option backward.isDefEq.respectTransparency false

/-!
# Truncation and precision budget of the truncated-Dyson simulator

Paper: M. Kieferová, A. Scherer, D. W. Berry, arXiv:1805.00582v1, §IV--VI.

Two ingredients of the headline complexity are isolated here.

* **Per-segment accuracy.** §VI (paragraph between Eqs. (35) and (36)) fixes the
  dyadic precision `k` so that the truncation-plus-discretization error of *one*
  segment is `O(ε/r)`. The frozen layer already proves the corresponding concrete
  bound `‖truncated grid sum - ordered evolution‖ ≤ 2^{-(k+6)}`
  (`effectiveDysonParameters_error`, from Eqs. (13)/(14) and the computed grid of
  Eq. (41)); the bridges below turn it into the paper's `ε/r` budget.

* **Arithmetic of the logarithmic scale.** Eqs. (2)--(3) need `log d ≤ L/2`,
  `log₂(r/ε) ≤ 4L` and `k + 2 ≤ 8L`, where `L = log(dHmaxT/ε)` and `k` is the
  segment precision. These bounds feed the query and gate ledgers of §VI.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.TruncDyson18.MainResults.TruncationBudget

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Papers.TruncDyson18.MainResults
open Qatlib.Papers.TruncDyson18.MainResults.SourceParameters

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## Per-segment accuracy: bridge to the frozen truncated-grid estimate -/

/-- Bridge (paper §VI, Eqs. (13)--(14) and the paragraph after Eq. (35)): for any
frozen segment parameter set satisfying the frozen domain and field conditions, the
truncated grid sum approximates the exact ordered evolution to `2^{-(k+6)}`, where
`k` is the segment precision. This is the frozen reusable theorem
`QuantumAlgorithm.Concepts.InteractionEvo.MeanDerivGrid.effectiveDysonParameters_error`
restated in the paper layer. -/
theorem perSegmentTruncationError_le_half_pow (q : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg q.ns) (Reg q.ns) ℂ)
    (hdom : effectiveSegmentDomain q) (hF : EffectiveField q H Hd) :
    ‖dysonGridTruncatedSum H (q.time : ℝ) (effectiveSegmentM q) (effectiveSegmentK q) -
      orderedEvolution (fun u => Complex.I • H u) 0 (q.time : ℝ)‖ ≤
      (1 / 2 : ℝ) ^ (q.precision + 6) :=
  effectiveDysonParameters_error q H Hd hdom hF

/-- The `ε/r` reading of the per-segment accuracy: if the dyadic precision `k`
dominates `log₂(r/ε)` (i.e. `2^k ≥ r/ε`), the per-segment error is at most `ε/(64r)`.
Paper §VI, Eqs. (14) and (35). -/
theorem perSegmentTruncationError_le_eps_div (q : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg q.ns) (Reg q.ns) ℂ)
    (hdom : effectiveSegmentDomain q) (hF : EffectiveField q H Hd)
    {E R : ℝ} (hR : 0 < R) (hE : 0 < E)
    (hprec : R / E ≤ (2 : ℝ) ^ q.precision) :
    ‖dysonGridTruncatedSum H (q.time : ℝ) (effectiveSegmentM q) (effectiveSegmentK q) -
      orderedEvolution (fun u => Complex.I • H u) 0 (q.time : ℝ)‖ ≤ E / (64 * R) := by
  have hbase := perSegmentTruncationError_le_half_pow q H Hd hdom hF
  have hpow : ((1 : ℝ) / 2) ^ (q.precision + 6) = ((1 : ℝ) / 2) ^ q.precision / 64 := by
    rw [pow_add]
    norm_num
    ring
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ q.precision := by positivity
  have hinv : ((1 : ℝ) / 2) ^ q.precision = 1 / (2 : ℝ) ^ q.precision := by
    rw [one_div, inv_pow, one_div]
  have hsmall : ((1 : ℝ) / 2) ^ q.precision ≤ E / R := by
    rw [hinv]
    rw [div_le_div_iff₀ hkpos hR]
    have h2 : R ≤ (2 : ℝ) ^ q.precision * E := (div_le_iff₀ hE).mp hprec
    nlinarith [h2]
  have hscaled : ((1 : ℝ) / 2) ^ q.precision * R ≤ E := by
    have := mul_le_mul_of_nonneg_right hsmall hR.le
    rwa [div_mul_cancel₀ E hR.ne'] at this
  calc ‖dysonGridTruncatedSum H (q.time : ℝ) (effectiveSegmentM q) (effectiveSegmentK q) -
        orderedEvolution (fun u => Complex.I • H u) 0 (q.time : ℝ)‖
      ≤ ((1 : ℝ) / 2) ^ q.precision / 64 := by rw [← hpow]; exact hbase
    _ ≤ E / (64 * R) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) (by positivity : (0 : ℝ) < 64 * R)]
        nlinarith [hscaled]

/-! ## Arithmetic of the logarithmic scale -/

/-- `log(dHmaxT/ε) ≥ 2`: the regime hypothesis `exp 2 ≤ dHmaxT/ε`. -/
theorem logScale_ge_two (p : SourceParameters) (h : p.Regime) : 2 ≤ p.logScale := by
  unfold logScale
  calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
    _ ≤ Real.log ((p.d : ℝ) * p.Hmax * p.T / p.eps) :=
        Real.log_le_log (Real.exp_pos 2) h.error_small

/-- The `logScale_pos` result for the TruncDyson18 paper model. -/
theorem logScale_pos (p : SourceParameters) (h : p.Regime) : 0 < p.logScale := by
  linarith [logScale_ge_two p h]

/-- The double logarithm of Eq. (2) is positive. -/
theorem logLog_pos (p : SourceParameters) (h : p.Regime) :
    0 < Real.log p.logScale := by
  exact Real.log_pos (by linarith [logScale_ge_two p h])

/-- `log d ≤ log(dHmaxT/ε)/2`: the regime hypothesis `dε ≤ HmaxT` keeps the sparsity
factor inside the logarithm under control. -/
theorem log_d_le_half (p : SourceParameters) (h : p.Regime) :
    Real.log (p.d : ℝ) ≤ p.logScale / 2 := by
  have hdpos := p.d_cast_pos h
  have hZ : (0 : ℝ) < (p.d : ℝ) * p.Hmax * p.T / p.eps :=
    div_pos (mul_pos (mul_pos hdpos h.Hmax_pos) h.T_pos) h.eps_pos
  have h1 : (p.d : ℝ) ≤ p.Hmax * p.T / p.eps := by
    rw [le_div_iff₀ h.eps_pos]
    exact h.sparse_regime
  have h2 : Real.log (p.d : ℝ) ≤ Real.log (p.Hmax * p.T / p.eps) :=
    Real.log_le_log hdpos h1
  have hsplit : Real.log (p.Hmax * p.T / p.eps) = p.logScale - Real.log (p.d : ℝ) := by
    have hEq : p.Hmax * p.T / p.eps = ((p.d : ℝ) * p.Hmax * p.T / p.eps) / (p.d : ℝ) := by
      field_simp
    rw [hEq, Real.log_div hZ.ne' hdpos.ne']
    unfold logScale
    rfl
  linarith

/-- `1 ≤ r/ε`: the segment count dominates the target error, so `log(r/ε) ≥ 0`.
This is the regime consequence `r ≥ 2λT ≥ dHmaxT ≥ e²ε` used in Eqs. (2)--(3). -/
theorem one_le_ratio_div_eps (p : SourceParameters) (h : p.Regime) :
    (1 : ℝ) ≤ (p.segmentCount : ℝ) / p.eps := by
  rw [le_div_iff₀ h.eps_pos]
  have hsmall : Real.exp 2 * p.eps ≤ (p.d : ℝ) * p.Hmax * p.T :=
    (le_div_iff₀ h.eps_pos).mp h.error_small
  have hexp1 : (1 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have hr := p.segmentCount_ge h
  have hl := p.le_lcuWeight h
  have hd1 := p.one_le_d h
  nlinarith [hsmall, hexp1, hr, hl, h.eps_pos, h.Hmax_pos, h.T_pos,
    mul_pos (mul_pos (p.d_cast_pos h) h.Hmax_pos) h.T_pos]

/-- `L ≤ k`: the dyadic precision dominates the logarithmic scale, because
`r ≥ dHmaxT` makes `log₂(r/ε) ≥ log₂(dHmaxT/ε) ≥ log(dHmaxT/ε)`. -/
theorem logScale_le_segmentPrecision (p : SourceParameters) (h : p.Regime) :
    p.logScale ≤ (p.segmentPrecision : ℝ) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hZ : (0 : ℝ) < (p.d : ℝ) * p.Hmax * p.T / p.eps :=
    div_pos (mul_pos (mul_pos (p.d_cast_pos h) h.Hmax_pos) h.T_pos) h.eps_pos
  have hr : (p.d : ℝ) * p.Hmax * p.T / p.eps ≤ (p.segmentCount : ℝ) / p.eps := by
    apply div_le_div_of_nonneg_right _ h.eps_pos.le
    have hl := p.le_lcuWeight h
    have hs := p.segmentCount_ge h
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := (p.d_cast_pos h).le
    have hsq : (p.d : ℝ) ≤ (p.d : ℝ)^2 := by nlinarith [hd0, p.one_le_d h]
    have hstep1 : (p.d : ℝ) * p.Hmax ≤ (p.d : ℝ)^2 * p.Hmax :=
      mul_le_mul_of_nonneg_right hsq h.Hmax_pos.le
    have hstep : (p.d : ℝ) * p.Hmax * p.T ≤ 2 * p.T * ((p.d : ℝ)^2 * p.Hmax) := by
      have h1 : (p.d : ℝ) * p.Hmax * p.T ≤ (p.d : ℝ)^2 * p.Hmax * p.T :=
        mul_le_mul_of_nonneg_right hstep1 h.T_pos.le
      have hnn : (0 : ℝ) ≤ (p.d : ℝ)^2 * p.Hmax * p.T :=
        mul_nonneg (mul_nonneg (pow_nonneg hd0 2) h.Hmax_pos.le) h.T_pos.le
      have h2 : 2 * p.T * ((p.d : ℝ)^2 * p.Hmax) = 2 * ((p.d : ℝ)^2 * p.Hmax * p.T) := by
        ring
      linarith [h1, hnn, h2]
    have h2T : (0 : ℝ) ≤ 2 * p.T := by linarith [h.T_pos]
    have hmult : 2 * p.T * ((p.d : ℝ)^2 * p.Hmax) ≤ 2 * p.T * p.lcuWeight :=
      mul_le_mul_of_nonneg_left hl h2T
    have heq : 2 * p.T * p.lcuWeight = 2 * p.lcuWeight * p.T := by ring
    linarith [hs, hstep, hmult, heq]
  have hlog : p.logScale ≤ Real.log ((p.segmentCount : ℝ) / p.eps) :=
    Real.log_le_log hZ hr
  have hnonneg : (0 : ℝ) ≤ Real.log ((p.segmentCount : ℝ) / p.eps) :=
    Real.log_nonneg (one_le_ratio_div_eps p h)
  calc p.logScale ≤ Real.log ((p.segmentCount : ℝ) / p.eps) := hlog
    _ ≤ Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2 := by
        rw [le_div_iff₀' hlog2pos]
        nlinarith [Real.log_two_lt_d9.le, hnonneg]
    _ ≤ (p.segmentPrecision : ℝ) := p.le_segmentPrecision h

/-- `log₂(r/ε) ≤ 4L`: the segment count is at most `8 d²HmaxT` and `log d ≤ L/2`. -/
theorem log_ratio_le (p : SourceParameters) (h : p.Regime) :
    Real.log ((p.segmentCount : ℝ) / p.eps) ≤ 4 * p.logScale := by
  have hZ : (0 : ℝ) < (p.d : ℝ) * p.Hmax * p.T / p.eps :=
    div_pos (mul_pos (mul_pos (p.d_cast_pos h) h.Hmax_pos) h.T_pos) h.eps_pos
  have hZ2 : (0 : ℝ) < (p.d : ℝ)^2 * p.Hmax * p.T / p.eps :=
    div_pos (mul_pos (mul_pos (pow_pos (p.d_cast_pos h) 2) h.Hmax_pos) h.T_pos) h.eps_pos
  have hrpos : (0 : ℝ) < (p.segmentCount : ℝ) / p.eps :=
    div_pos (by exact_mod_cast p.segmentCount_pos h) h.eps_pos
  have hr_le : (p.segmentCount : ℝ) / p.eps ≤ 8 * ((p.d : ℝ)^2 * p.Hmax * p.T / p.eps) := by
    have hmain : (p.segmentCount : ℝ) ≤ 8 * ((p.d : ℝ)^2 * p.Hmax * p.T) := by
      have hup := p.segmentCount_le h
      have hlam := p.lcuWeight_lt_two h
      have hP : (0 : ℝ) < (p.d : ℝ)^2 * p.Hmax :=
        mul_pos (pow_pos (p.d_cast_pos h) 2) h.Hmax_pos
      nlinarith [hup, hlam, hP, h.Hmax_pos, h.T_pos]
    calc (p.segmentCount : ℝ) / p.eps
        ≤ (8 * ((p.d : ℝ)^2 * p.Hmax * p.T)) / p.eps :=
          div_le_div_of_nonneg_right hmain h.eps_pos.le
      _ = 8 * ((p.d : ℝ)^2 * p.Hmax * p.T / p.eps) := mul_div_assoc _ _ _
  have hlog := Real.log_le_log hrpos hr_le
  have hmul : Real.log (8 * ((p.d : ℝ)^2 * p.Hmax * p.T / p.eps))
      = Real.log 8 + Real.log ((p.d : ℝ)^2 * p.Hmax * p.T / p.eps) :=
    Real.log_mul (by norm_num) hZ2.ne'
  have hlog8 : Real.log 8 ≤ 2.1 := by
    have heq : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    nlinarith [Real.log_two_lt_d9]
  have hsq : Real.log ((p.d : ℝ)^2 * p.Hmax * p.T / p.eps)
      = Real.log (p.d : ℝ) + p.logScale := by
    have hEq : (p.d : ℝ)^2 * p.Hmax * p.T / p.eps
        = (p.d : ℝ) * ((p.d : ℝ) * p.Hmax * p.T / p.eps) := by
      field_simp
    rw [hEq, Real.log_mul (p.d_cast_pos h).ne' hZ.ne']
    unfold logScale
    rfl
  have hd := log_d_le_half p h
  have hL := logScale_ge_two p h
  linarith [hlog, hmul, hlog8, hsq, hd, hL]

/-- `k + 2 ≤ 8L`: the explicit form of the `k ≤ log₂(r/ε) + 1` ceiling. -/
theorem segmentPrecision_le_eight (p : SourceParameters) (h : p.Regime) :
    (p.segmentPrecision : ℝ) + 2 ≤ 8 * p.logScale := by
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hle := p.segmentPrecision_le h
  have hratio := log_ratio_le p h
  have hnonneg : (0 : ℝ) ≤ Real.log ((p.segmentCount : ℝ) / p.eps) :=
    Real.log_nonneg (one_le_ratio_div_eps p h)
  have hA : Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2
      ≤ 4 * p.logScale / 0.69 := by
    have hdiv : Real.log ((p.segmentCount : ℝ) / p.eps) / Real.log 2
        ≤ Real.log ((p.segmentCount : ℝ) / p.eps) / 0.69 := by
      rw [div_le_div_iff₀ hlog2pos (by norm_num)]
      nlinarith [hnonneg, hlog2]
    have h2 : Real.log ((p.segmentCount : ℝ) / p.eps) / 0.69
        ≤ 4 * p.logScale / 0.69 :=
      div_le_div_of_nonneg_right hratio (by norm_num)
    linarith
  have hkey : 4 * p.logScale / 0.69 + 3 ≤ 8 * p.logScale := by
    have hq : 4 * p.logScale / 0.69 ≤ 8 * p.logScale - 3 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.69)]
      nlinarith [logScale_ge_two p h]
    linarith
  linarith [hle, hA, hkey]

end Qatlib.Papers.TruncDyson18.MainResults.TruncationBudget
