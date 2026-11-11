/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowRankMatrix19.SQFramework.GeneralSvtDefs
import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow

/-!
# General singular-value transformation estimates

This module proves spectral identities, threshold-transform bounds, and algebraic runtime and
sample-count estimates for the sample/query framework of [ChiaEtAl2022]. The `clause16_endpoint`
through `clause28_endpoint` results collect these estimates, including polynomial bounds for the
even and odd scalar cost expressions.

## Main statements

* `clause17_endpoint`: Collects polynomial bounds for the even and odd classical and quantum
  cost expressions.
* `clause18_endpoint`: Combines threshold-transform norm control with the leading runtime
  identity.
* `clause28_endpoint`: Collects regularized square-root and inverse branches and a sample-budget
  identity.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Call
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CacheOp
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.EvenSVT
open Qatlib.Papers.LowRankMatrix19.SDPTrace
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS.SqBitLedger
open Qatlib.Papers.LowRankMatrix19.SQFramework.ConstructionStageB.StageBSQGENERALSVT
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.LowRankMatrix19.SQFramework
namespace ConstructionStageB
namespace StageBSQGENERALSVT

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

/-- For `φ ≥ 1`, positive `ε`, and `0 < δ ≤ 1/4`, the unified sample count is bounded by both
`128 * φ ^ 2 * log (1 / δ) * E ^ 2 / ε ^ 2` and `64 * E ^ 2 * sqUnifiedRate φ ε δ`. -/
theorem clause16_endpoint {φ ε δ E : ℝ} (hφ : 1 ≤ φ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    sqUnifiedSampleCount φ ε δ E ≤ 128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2 / ε ^ 2 ∧
      sqUnifiedSampleCount φ ε δ E ≤ 64 * E ^ 2 * sqUnifiedRate φ ε δ :=
  ⟨sqUnifiedSampleCount_le_log hφ hε hδ hδ4,
    sqUnifiedSampleCount_le_rate hφ hε hδ (by linarith [hδ4])⟩

/-- Positive row and column budgets meeting their respective sample thresholds make each of the
two stated stage-error expressions at most `ε / 2`. -/
theorem clause16_two_stage_budget {φ ε δ E : ℝ} {r c : ℕ} (hε : 0 < ε)
    (hE : 0 < E) (hr : 0 < r) (hc : 0 < c)
    (hrow : sqRowStageSamples ε δ E ≤ (r : ℝ))
    (hcol : sqColStageSamples φ ε δ E ≤ (c : ℝ)) :
    Real.sqrt (8 * Real.log (2 / (δ / 2)) / (r : ℝ)) * E ≤ ε / 2 ∧
      Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ)) * E ≤ ε / 2 :=
  ⟨sqRowStageSamples_sufficient hE hε hr hrow,
    sqColStageSamples_sufficient hE hε hc hcol⟩

/-- When `perSample ≥ 1`, both sampler reads and probability reads in the two-stage ledger are
bounded by `sqSketchRuntime`, which equals `(r + c) * perSample`. -/
theorem clause16_access_runtime (r c perSample : ℕ) (h : 1 ≤ perSample) :
    (sqTwoStageLedger r c).samplerReads ≤ sqSketchRuntime r c perSample ∧
      (sqTwoStageLedger r c).probReads ≤ sqSketchRuntime r c perSample ∧
        sqSketchRuntime r c perSample = (r + c) * perSample :=
  ⟨sqSketchRuntime_ge_ledger r c perSample h,
    sqSketchRuntime_ge_probReads r c perSample h,
    sqSketchRuntime_eq r c perSample⟩

/-- For word width at least two and a positive total of reads and multiplications, the sketch
ledger's bit-time count is strictly larger than its RAM operation count. -/
theorem clause16_bit_time_separation (n r c q : ℕ) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < (sketchArithmeticLedger n r c q).reads
        + (sketchArithmeticLedger n r c q).multiplies) :
    (sketchArithmeticLedger n r c q).ramOps < (sketchArithmeticLedger n r c q).bitTime w :=
  SqBitLedger.bitTime_gt_ramOps _ w hw hpos

/-- Applying the constant-one spectral function to a Hermitian matrix gives the identity matrix. -/
theorem hermitianFunction_const_one {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    hermitianFunction A hA (fun _ => (1 : ℂ)) = 1 := by
  unfold hermitianFunction spectralDiagonal
  rw [Matrix.diagonal_one, Matrix.mul_one, basisColumns_mul_adjoint]

/-- Applying the constant-zero spectral function to a Hermitian matrix gives the zero matrix. -/
theorem hermitianFunction_const_zero {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) :
    hermitianFunction A hA (fun _ => (0 : ℂ)) = 0 := by
  have h : Matrix.diagonal (fun i => (fun x => (0 : ℂ)) (orderedHermitianValues hA i))
      = (0 : Matrix (Fin (Fintype.card I)) (Fin (Fintype.card I)) ℂ) := by
    ext i j
    simp [Matrix.diagonal_apply]
  unfold hermitianFunction spectralDiagonal
  rw [h, Matrix.mul_zero, Matrix.zero_mul]

/-- The real square root of a number in `[0, 1]` is at most one. -/
theorem sqrt_le_one_of_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.sqrt x ≤ 1 := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt h0
  have hnonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  nlinarith

/-- Left multiplication by a nonnegative real number preserves a weak inequality. -/
theorem mulLeftMono {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left h hc

/-- Right multiplication by a nonnegative real number preserves a weak inequality. -/
theorem mulRightMono {a b c : ℝ} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right h hc

/-- For a real base at least one, natural powers are monotone in the exponent. -/
theorem pow_le_pow_of_one_le {x : ℝ} (hx1 : 1 ≤ x) {m n : ℕ} (hmn : m ≤ n) :
    x ^ m ≤ x ^ n := by
  have hge : 1 ≤ x ^ (n - m) := one_le_pow₀ hx1
  calc
    x ^ m = x ^ m * 1 := by ring
    _ ≤ x ^ m * x ^ (n - m) := mulLeftMono hge (by positivity : (0:ℝ) ≤ x ^ m)
    _ = x ^ n := by rw [← pow_add, Nat.add_sub_of_le hmn]

/-- If `a ≤ b`, `c ≤ d`, `b ≥ 0`, and `c ≥ 0`, then `a * c ≤ b * d`. -/
theorem mul_mono3 {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ b) (h4 : 0 ≤ c) :
    a * c ≤ b * d := by
  calc
    a * c ≤ b * c := mulRightMono h1 h4
    _ ≤ b * d := mulLeftMono h2 h3

/-- The squared complex norm of a real scalar equals its real square. -/
theorem complexOfReal_norm_sq (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- For positive denominators, the cross-product inequality `a * d ≤ c * b` implies `a / b ≤ c /
d`. -/
theorem div_le_div_of_mul_le {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [div_le_div_iff₀ hb hd]
  exact h

/-- The ordered eigenvalues of `Aᴴ * A` equal the squares of the corresponding matrix singular
values. -/
theorem clause17_gram_spectrum {O I : Type} [Fintype O] [DecidableEq O] [Fintype I]
    [DecidableEq I] (A : Matrix O I ℂ) (i : Fin (Fintype.card I)) :
    orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self A) i
      = (matrixSingularValues A i) ^ 2 :=
  (singular_gram_ordered A).2 i

/-- Evaluating the even quotient at a squared singular value gives `p` evaluated at that
singular value. -/
theorem clause17_even_quotient_on_spectrum {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (p : ℝ → ℝ)
    (i : Fin (Fintype.card I)) :
    qvQuotientEven p ((matrixSingularValues A i) ^ 2) = p (matrixSingularValues A i) := by
  rw [qvQuotientEven]
  congr 1
  exact Real.sqrt_sq (matrixSingularValues_nonneg A i)

/-- If `p` is bounded in absolute value by one on `[-1, 1]`, its even quotient is bounded by one
on `[0, 1]`. -/
theorem clause17_even_quotient_abs_le_one {p : ℝ → ℝ}
    (hp : ∀ y : ℝ, -1 ≤ y → y ≤ 1 → |p y| ≤ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |qvQuotientEven p x| ≤ 1 := by
  rw [qvQuotientEven]
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq1 : Real.sqrt x ≤ 1 := sqrt_le_one_of_le hx0 hx1
  exact hp (Real.sqrt x) (by linarith) hsq1

/-- At a nonzero argument, the odd quotient equals `p (Real.sqrt x) / Real.sqrt x`. -/
theorem clause17_odd_quotient_formula {p : ℝ → ℝ} {x : ℝ} (hx : x ≠ 0) :
    qvQuotientOdd p x = p (Real.sqrt x) / Real.sqrt x := by
  simp [qvQuotientOdd, hx]

/-- For `0 < x ≤ 1`, a function bounded by one on `[-1, 1]` has odd quotient bounded in absolute
value by `1 / Real.sqrt x`. -/
theorem clause17_odd_quotient_abs_le_inv_sqrt {p : ℝ → ℝ}
    (hp : ∀ y : ℝ, -1 ≤ y → y ≤ 1 → |p y| ≤ 1) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |qvQuotientOdd p x| ≤ 1 / Real.sqrt x := by
  rw [clause17_odd_quotient_formula (ne_of_gt hx0), abs_div,
    abs_of_nonneg (Real.sqrt_nonneg x)]
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq1 : Real.sqrt x ≤ 1 := sqrt_le_one_of_le hx0.le hx1
  have hp' := hp (Real.sqrt x) (by linarith) hsq1
  exact div_le_div_of_nonneg_right hp' hsq0

/-- If the singular values of `A` are at most one and `p` is bounded by one on `[-1, 1]`, the
even transform has operator norm at most one. -/
theorem clause17_even_transform_opNorm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : ℝ → ℝ)
    (hp : ∀ y : ℝ, -1 ≤ y → y ≤ 1 → |p y| ≤ 1)
    (hsv : ∀ i : Fin (Fintype.card I), matrixSingularValues A i ≤ 1) :
    ‖qvTransformEven A p‖ ≤ 1 := by
  have hgr := Matrix.isHermitian_conjTranspose_mul_self A
  have henv : ∀ i : Fin (Fintype.card I),
      ‖(qvQuotientEven p (orderedHermitianValues hgr i) : ℂ)‖ ≤ 1 := by
    intro i
    rw [clause17_gram_spectrum A i]
    have hnonneg := matrixSingularValues_nonneg A i
    have hsq0 : 0 ≤ (matrixSingularValues A i) ^ 2 := sq_nonneg _
    have hsq1 : (matrixSingularValues A i) ^ 2 ≤ 1 := by
      have h2 : (matrixSingularValues A i) ^ 2 ≤ matrixSingularValues A i := by
        have hmul : 0 ≤ matrixSingularValues A i * (1 - matrixSingularValues A i) :=
          mul_nonneg hnonneg (by linarith [hsv i] : (0:ℝ) ≤ 1 - matrixSingularValues A i)
        nlinarith [hmul]
      linarith [h2, hsv i]
    have habs : |qvQuotientEven p ((matrixSingularValues A i) ^ 2)| ≤ 1 :=
      clause17_even_quotient_abs_le_one hp hsq0 hsq1
    have hsq : (qvQuotientEven p ((matrixSingularValues A i) ^ 2)) ^ 2 ≤ 1 := by
      have h1 : (qvQuotientEven p ((matrixSingularValues A i) ^ 2)) ^ 2
          = |qvQuotientEven p ((matrixSingularValues A i) ^ 2)| ^ 2 := (sq_abs _).symm
      rw [h1]
      have hmul : 0 ≤ |qvQuotientEven p ((matrixSingularValues A i) ^ 2)|
          * (1 - |qvQuotientEven p ((matrixSingularValues A i) ^ 2)|) :=
        mul_nonneg (abs_nonneg _) (by linarith)
      nlinarith [hmul]
    have hnorm : 0 ≤ ‖(qvQuotientEven p ((matrixSingularValues A i) ^ 2) : ℂ)‖ :=
      norm_nonneg _
    have hsq' : ‖(qvQuotientEven p ((matrixSingularValues A i) ^ 2) : ℂ)‖ ^ 2
        = (qvQuotientEven p ((matrixSingularValues A i) ^ 2)) ^ 2 :=
      complexOfReal_norm_sq _
    nlinarith [hsq, hnorm, hsq']
  have h := hermitian_function_op_norm_le_spectral_envelope (Aᴴ * A) hgr
    (fun x => (qvQuotientEven p x : ℂ)) 1 (by norm_num) henv
  simpa [qvTransformEven] using! h

/-- For nonnegative `x`, the even quotient of `fun y => p (y * y)` evaluates to `p x`. -/
theorem clause17_density_operator_quotient {p : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    qvQuotientEven (fun y => p (y * y)) x = p x := by
  rw [qvQuotientEven]
  congr 1
  have hsq := Real.sq_sqrt hx
  nlinarith

/-- For nonnegative `sigma` and `0 ≤ eta ≤ 1`, the threshold function equals the input above the
upper threshold, zero below the lower threshold, and the stated linear ramp between them. -/
theorem clause18_thresholdSvt_branches (sigma eta lam : ℝ) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) :
    (sigma * (1 + eta) ≤ lam → thresholdSvt sigma eta lam = lam) ∧
      (lam < sigma * (1 - eta) → thresholdSvt sigma eta lam = 0) ∧
      (sigma * (1 - eta) ≤ lam → lam < sigma * (1 + eta) →
        thresholdSvt sigma eta lam
          = (sigma * (1 + eta)) * (lam - sigma * (1 - eta))
            / (sigma * (1 + eta) - sigma * (1 - eta))) := by
  constructor
  · intro h
    rw [thresholdSvt]
    simp [h]
  constructor
  · intro h
    have hnot : ¬ (sigma * (1 + eta) ≤ lam) := by
      have hkey : sigma * (1 - eta) ≤ sigma * (1 + eta) := by
        have h1m : 0 ≤ 1 - eta := by linarith
        have hmul : (1 - eta) * sigma ≤ (1 + eta) * sigma :=
          mulRightMono (show (1:ℝ) - eta ≤ 1 + eta by linarith) hsigma
        convert! hmul using 1 <;> ring
      linarith
    rw [thresholdSvt]
    simp [hnot, h]
  · intro h1 h2
    have hnot : ¬ (sigma * (1 + eta) ≤ lam) := by linarith
    have hnot2 : ¬ (lam < sigma * (1 - eta)) := by linarith
    rw [thresholdSvt]
    simp [hnot, hnot2]

/-- For nonnegative `sigma` and `lam` and `0 ≤ eta ≤ 1`, the threshold function lies between
zero and `lam`. -/
theorem clause18_thresholdSvt_bounds (sigma eta lam : ℝ) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) (hlam : 0 ≤ lam) :
    0 ≤ thresholdSvt sigma eta lam ∧ thresholdSvt sigma eta lam ≤ lam := by
  have hupper : 0 ≤ sigma * (1 + eta) := by
    have := mul_nonneg hsigma (by linarith : 0 ≤ 1 + eta)
    linarith
  by_cases h1 : sigma * (1 + eta) ≤ lam
  · rw [thresholdSvt, if_pos h1]
    constructor
    · linarith
    · exact le_rfl
  · by_cases h2 : lam < sigma * (1 - eta)
    · rw [thresholdSvt, if_neg h1, if_pos h2]
      constructor <;> linarith
    · rw [thresholdSvt, if_neg h1, if_neg h2]
      have hmid : sigma * (1 - eta) ≤ lam := by linarith
      have hden : 0 < sigma * (1 + eta) - sigma * (1 - eta) := by linarith
      have hnum : 0 ≤ (sigma * (1 + eta)) * (lam - sigma * (1 - eta)) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hkey : (sigma * (1 + eta)) * (lam - sigma * (1 - eta))
          ≤ lam * (sigma * (1 + eta) - sigma * (1 - eta)) := by
        have hprod : 0 ≤ sigma * (1 - eta) * (sigma * (1 + eta) - lam) := by
          have h1m : 0 ≤ 1 - eta := by linarith
          have hgap : 0 ≤ sigma * (1 + eta) - lam := by linarith
          positivity
        nlinarith [hprod]
      constructor
      · exact div_nonneg hnum hden.le
      · exact (div_le_iff₀ hden).2 hkey

/-- For nonnegative `sigma` and `x` and `0 ≤ eta ≤ 1`, the threshold ratio lies in `[0, 1]`. -/
theorem clause18_thresholdRatio_bounds (sigma eta x : ℝ) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) (hx0 : 0 ≤ x) :
    0 ≤ thresholdRatio sigma eta x ∧ thresholdRatio sigma eta x ≤ 1 := by
  by_cases hx : x = 0
  · rw [thresholdRatio, if_pos hx]
    constructor <;> linarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    rw [thresholdRatio, if_neg hx]
    have hb := clause18_thresholdSvt_bounds sigma eta (Real.sqrt x) hsigma heta heta1 hsqrt.le
    constructor
    · exact div_nonneg hb.1 hsqrt.le
    · exact (div_le_iff₀ hsqrt).2 (by linarith [hb.2])

/-- For nonnegative `sigma` and `0 ≤ eta ≤ 1`, the threshold singular-value operator has norm at
most the norm of the original matrix. -/
theorem clause18_threshold_operator_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (sigma eta : ℝ) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) :
    ‖thresholdSvtOperator A sigma eta‖ ≤ ‖A‖ := by
  have hgr := Matrix.isHermitian_conjTranspose_mul_self A
  have henv : ∀ i : Fin (Fintype.card I),
      ‖(thresholdRatio sigma eta (orderedHermitianValues hgr i) : ℂ)‖ ≤ 1 := by
    intro i
    rw [clause17_gram_spectrum A i]
    have hnonneg := matrixSingularValues_nonneg A i
    have hsq0 : 0 ≤ (matrixSingularValues A i) ^ 2 := sq_nonneg _
    have habs : |thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)| ≤ 1 := by
      have hb := clause18_thresholdRatio_bounds sigma eta _ hsigma heta heta1 hsq0
      exact abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
    have hsq : (thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)) ^ 2 ≤ 1 := by
      have h1 : (thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)) ^ 2
          = |thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)| ^ 2 := (sq_abs _).symm
      rw [h1]
      have hmul : 0 ≤ |thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)|
          * (1 - |thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)|) :=
        mul_nonneg (abs_nonneg _) (by linarith)
      nlinarith [hmul]
    have hnorm : 0 ≤ ‖(thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2) : ℂ)‖ := by
      positivity
    have hsq' : ‖(thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2) : ℂ)‖ ^ 2
        = (thresholdRatio sigma eta ((matrixSingularValues A i) ^ 2)) ^ 2 :=
      complexOfReal_norm_sq _
    nlinarith [hsq, hnorm, hsq']
  have h := hermitian_function_op_norm_le_spectral_envelope (Aᴴ * A) hgr
    (fun x => (thresholdRatio sigma eta x : ℂ)) 1 (by norm_num) henv
  have hH : ‖hermitianFunction (Aᴴ * A) hgr (fun x => (thresholdRatio sigma eta x : ℂ))‖ ≤ 1 := h
  calc
    ‖thresholdSvtOperator A sigma eta‖
        = ‖A * hermitianFunction (Aᴴ * A) hgr (fun x => (thresholdRatio sigma eta x : ℂ))‖ := by
          rfl
    _ ≤ ‖A‖ * ‖hermitianFunction (Aᴴ * A) hgr (fun x => (thresholdRatio sigma eta x : ℂ))‖ :=
          Matrix.l2_opNorm_mul _ _
    _ ≤ ‖A‖ * 1 := by
      have hA : 0 ≤ ‖A‖ := by
        rw [Matrix.l2_opNorm_def]
        exact norm_nonneg _
      exact mulLeftMono hH hA
    _ = ‖A‖ := by ring

/-- For positive `sigma`, substituting `cor67K` and `cor67Kappa` expands the leading runtime
term to `normAF ^ 6 * normA ^ 10 / (sigma ^ 16 * eta ^ 6 * eps ^ 6)` times the logarithmic
cube. -/
theorem clause18_first_term_expansion (normAF normA sigma eps eta delta : ℝ) (hsigma : 0 < sigma) :
    (cor67K normAF sigma) ^ 3 * (cor67Kappa normA sigma) ^ 5 / (eta ^ 6 * eps ^ 6)
      * (Real.log delta⁻¹) ^ 3
      = normAF ^ 6 * normA ^ 10 / (sigma ^ 16 * eta ^ 6 * eps ^ 6)
        * (Real.log delta⁻¹) ^ 3 := by
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  simp only [cor67K, cor67Kappa]
  field_simp

/-- The squared-norm inequality `normA ^ 2 ≤ normAF ^ 2` implies `cor67Kappa normA sigma ≤
cor67K normAF sigma`. -/
theorem clause18_K_ge_kappa (normAF normA sigma : ℝ) (hle : normA ^ 2 ≤ normAF ^ 2) :
    cor67Kappa normA sigma ≤ cor67K normAF sigma := by
  have h := div_le_div_of_nonneg_right hle (sq_nonneg sigma)
  simpa [cor67K, cor67Kappa] using! h

/-- Multiplying the Corollary 6.7 row budget by the stated per-row factor gives the second
runtime term with logarithmic square. -/
theorem clause18_row_budget_second_term (K kappa rowRatio eps eta delta : ℝ) :
    cor67RowBudget K eps delta * (K * kappa * rowRatio * (Real.log delta⁻¹) / eta ^ 2)
      = K ^ 2 * kappa * rowRatio / (eta ^ 2 * eps ^ 2) * (Real.log delta⁻¹) ^ 2 := by
  simp [cor67RowBudget]
  ring

/-- The Corollary 6.10 runtime expression equals the square of `cor610TensorNorms`, divided by
`eps ^ 2` and multiplied by `log delta⁻¹`. -/
theorem clause19_samples_from_tensor_norms (normMF normW eps delta : ℝ) :
    cor610Runtime normMF normW eps delta
      = (cor610TensorNorms normMF normW) ^ 2 / eps ^ 2 * Real.log delta⁻¹ := by
  simp only [cor610Runtime, cor610TensorNorms]
  field_simp

/-- The Corollary 6.10 classical runtime expression equals the square of its quantum runtime
expression times `log delta⁻¹`. -/
theorem clause19_classical_is_quantum_square (normMF normW eps delta : ℝ) :
    cor610Runtime normMF normW eps delta
      = (cor610QuantumRuntime normMF normW eps) ^ 2 * Real.log delta⁻¹ := by
  simp only [cor610Runtime, cor610QuantumRuntime]
  field_simp

/-- At Frobenius parameter `Real.sqrt 2`, the Corollary 6.10 runtime expression is `4 * normW ^
4 / eps ^ 2 * log delta⁻¹`. -/
theorem clause19_instance_norm_two (normW eps delta : ℝ) :
    cor610Runtime (Real.sqrt 2) normW eps delta
      = 4 * normW ^ 4 / eps ^ 2 * Real.log delta⁻¹ := by
  have h4 : (Real.sqrt 2 : ℝ) ^ 4 = 4 := by
    have hsq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      (Real.sqrt 2 : ℝ) ^ 4 = (Real.sqrt 2 : ℝ) ^ 2 * (Real.sqrt 2 : ℝ) ^ 2 := by ring
      _ = 2 * 2 := by rw [hsq]
      _ = 4 := by norm_num
  simp only [cor610Runtime, h4]

/-- For positive `lambdaK` and `normX ^ 2 ≤ traceX`, the parameter `cor612Kappa` is at most
`cor612K`. -/
theorem clause20_K_ge_kappa (traceX normX lambdaK : ℝ) (hK : 0 < lambdaK)
    (htrace : normX ^ 2 ≤ traceX) :
    cor612Kappa normX lambdaK ≤ cor612K traceX lambdaK := by
  have h := div_le_div_of_nonneg_right htrace hK.le
  simpa [cor612K, cor612Kappa] using! h

/-- The Corollary 6.12 spectral filter takes values in `[0, 1]` for all real parameters and
inputs. -/
theorem clause20_spectralFilter_bounds (lambdaHat gap x : ℝ) :
    0 ≤ cor612SpectralFilter lambdaHat gap x ∧ cor612SpectralFilter lambdaHat gap x ≤ 1 := by
  by_cases h1 : |x - lambdaHat| ≤ gap / 8
  · rw [cor612SpectralFilter, if_pos h1]
    constructor <;> linarith
  · by_cases h2 : gap / 4 ≤ |x - lambdaHat|
    · rw [cor612SpectralFilter, if_neg h1, if_pos h2]
      constructor <;> linarith
    · rw [cor612SpectralFilter, if_neg h1, if_neg h2]
      have hnum : 0 ≤ gap / 4 - |x - lambdaHat| := by linarith
      have hden : 0 < gap / 4 - gap / 8 := by linarith
      constructor
      · exact div_nonneg hnum hden.le
      · refine (div_le_iff₀ hden).2 ?_
        linarith

/-- Multiplying the worst-case Corollary 6.15 runtime expression by `kappa ^ 3` gives the
general runtime expression. -/
theorem clause21_worst_case_saves_kappa_cubed (phi K kappa eps eta delta : ℝ) :
    cor615WorstRuntime phi K kappa eps eta delta * kappa ^ 3
      = cor615Runtime phi K kappa eps eta delta := by
  simp [cor615WorstRuntime, cor615Runtime]
  ring

/-- Multiplying the worst-case Corollary 6.15 sample expression by `kappa` gives the general
sample expression at unit norm parameters. -/
theorem clause21_worst_case_saves_kappa (phi K kappa eps eta delta : ℝ) :
    cor615WorstSamples phi K kappa eps eta delta * kappa
      = cor615Samples phi K kappa eps eta delta 1 1 := by
  simp [cor615WorstSamples, cor615Samples]
  ring

/-- If `0 < eps ≤ 99/100`, `normXStar > 0`, and `normXHat ≥ (1 - eps) * normXStar`, then
`normXStar / normXHat ≤ 100`. -/
theorem clause21_relative_error_100 {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 99 / 100)
    {normXStar normXHat : ℝ} (hstar : 0 < normXStar)
    (herr : normXHat ≥ (1 - eps) * normXStar) :
    normXStar / normXHat ≤ 100 := by
  have hone : 1 / 100 ≤ 1 - eps := by linarith
  have hhat : 0 < normXHat := by
    have hone' : 0 < 1 - eps := by linarith
    have hpos : 0 < (1 - eps) * normXStar := mul_pos hone' hstar
    linarith
  have hstep : (1 / 100) * normXStar ≤ normXHat := by
    calc
      (1 / 100) * normXStar ≤ (1 - eps) * normXStar := mulRightMono hone (by linarith)
      _ ≤ normXHat := herr
  have h100 : normXStar ≤ 100 * normXHat := by
    have h := mulRightMono hstep (by norm_num : (0:ℝ) ≤ 100)
    linarith
  exact (div_le_iff₀ hhat).2 h100

/-- For positive `m` and `traceF ≥ Real.sqrt m`, the parameter `cor617MNorm normF traceF` is at
most `normF ^ 2 / m`. -/
theorem clause22_M_norm_bound (normF traceF m : ℝ) (hm : 0 < m) (htrace : Real.sqrt m ≤ traceF) :
    cor617MNorm normF traceF ≤ normF ^ 2 / m := by
  have hsqrt0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have htrace0 : 0 ≤ traceF := by linarith
  have hsq : m ≤ traceF ^ 2 := by
    have h := Real.sq_sqrt (le_of_lt hm)
    nlinarith
  have hnum : normF ^ 2 * m ≤ normF ^ 2 * traceF ^ 2 := by
    have h := mulRightMono hsq (sq_nonneg normF)
    linarith
  have hposTrace : 0 < traceF ^ 2 := by nlinarith
  simp only [cor617MNorm]
  exact (div_le_div_iff₀ hposTrace (by positivity : (0:ℝ) < m)).2 hnum

/-- Substituting `cor618DimensionFreeGamma normXF` into the Corollary 6.18 runtime expression
yields the displayed formula with factor `(1 / normXF ^ 2) ^ 11`. -/
theorem clause23_dimension_free (normXF normX eps delta : ℝ) :
    cor618Runtime normXF normX (cor618DimensionFreeGamma normXF) eps delta
      = normXF ^ 6 * normX ^ 16 * (1 / normXF ^ 2) ^ 11 / eps ^ 6
        * (Real.log delta⁻¹) ^ 3 := by
  simp [cor618Runtime, cor618DimensionFreeGamma]

/-- The ordered eigenvalues of `Xᴴ * X` are the squares of the corresponding singular values of
`X`. -/
theorem clause23_gram_spectrum_X {O I : Type} [Fintype O] [DecidableEq O] [Fintype I]
    [DecidableEq I] (X : Matrix O I ℂ) (i : Fin (Fintype.card I)) :
    orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self X) i
      = (matrixSingularValues X i) ^ 2 :=
  clause17_gram_spectrum X i

/-- The ordered eigenvalues of the Gram matrix of `Xᴴ` are the squares of the corresponding
singular values of `Xᴴ`. -/
theorem clause23_gram_spectrum_Xt {O I : Type} [Fintype O] [DecidableEq O] [Fintype I]
    [DecidableEq I] (X : Matrix O I ℂ) (j : Fin (Fintype.card O)) :
    orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self Xᴴ) j
      = (matrixSingularValues Xᴴ j) ^ 2 :=
  clause17_gram_spectrum Xᴴ j

/-- For nonzero `sigma` and `eps`, the Corollary 6.20 runtime expression equals its
natural-error variant multiplied by `normH ^ 6`. -/
theorem clause24_natural_error_ratio (normHF normH sigma eps delta : ℝ)
    (hsigma : sigma ≠ 0) (heps : eps ≠ 0) :
    cor620Runtime normHF normH sigma eps delta
      = cor620NaturalRuntime normHF normH sigma eps delta * normH ^ 6 := by
  simp only [cor620Runtime, cor620NaturalRuntime]
  field_simp

/-- The natural-error Corollary 6.20 runtime expands to `normHF ^ 6 * normH ^ 10 / (sigma ^ 16 *
eps ^ 6)` times the logarithmic cube. -/
theorem clause24_natural_error_dimension_free (normHF normH sigma eps delta : ℝ) :
    cor620NaturalRuntime normHF normH sigma eps delta
      = normHF ^ 6 * normH ^ 10 / (sigma ^ 16 * eps ^ 6) * (Real.log delta⁻¹) ^ 3 := by
  rfl

/-- For every real `lam`, `fCos (lam ^ 2) + lam * fSinc (lam ^ 2)` equals `cos lam + sin lam`. -/
theorem clause25_even_odd_scalar (lam : ℝ) :
    fCos (lam ^ 2) + lam * fSinc (lam ^ 2) = Real.cos lam + Real.sin lam := by
  by_cases h : lam = 0
  · subst h
    simp [fCos, fSinc]
  · have hne : lam ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_ne_zero h)
    rw [fCos, fSinc, if_neg hne]
    have hsqrt : Real.sqrt (lam ^ 2) = |lam| := Real.sqrt_sq_eq_abs lam
    rw [hsqrt]
    rcases lt_or_gt_of_ne h with hneg | hpos
    · rw [abs_of_neg hneg, Real.cos_neg, Real.sin_neg]
      have hdiv : (-Real.sin lam) / (-lam) = Real.sin lam / lam := by
        field_simp
      rw [hdiv]
      field_simp
    · rw [abs_of_pos hpos]
      field_simp

/-- The Corollary 6.25 round and step expressions equal `16 * log n / eps ^ 2` and `eps / 4`,
respectively. -/
theorem clause26_mmw_parameters (n eps : ℝ) :
    cor625Rounds n eps = 16 * Real.log n / eps ^ 2 ∧ cor625Step eps = eps / 4 :=
  ⟨rfl, rfl⟩

/-- For `0 ≤ theta ≤ 1`, numerator and denominator errors at most `(theta / 3) * Z`, with
numerator norm at most `Z`, give ratio error at most `theta`. -/
theorem clause27_lemma626_reduction {theta : ℝ} (a aHat : ℂ) (Z : ℝ) (Zhat : ℂ)
    (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (ha : ‖a‖ ≤ Z)
    (haa : ‖a - aHat‖ ≤ (theta / 3) * Z) (hZZ : ‖(Z : ℂ) - Zhat‖ ≤ (theta / 3) * Z) :
    ‖aHat / Zhat - a / (Z : ℂ)‖ ≤ theta :=
  sampling_based_low_rank_lemma_6_27 theta a aHat Z Zhat hθ0 hθ1 ha haa hZZ

/-- The precision parameter for the normalized-ratio reduction is `theta / 3`. -/
theorem clause27_precision_reduction (theta : ℝ) :
    lemma626Precision theta = theta / 3 := rfl

/-- For positive `sigma`, the regularized square root is zero below `sigma ^ 2 / 2`, linear up
to `sigma ^ 2`, and equal to `Real.sqrt x` above it. -/
theorem clause28_fsqrt_branches (sigma x : ℝ) (hsigma : 0 < sigma) :
    (x < sigma ^ 2 / 2 → fSqrt sigma x = 0) ∧
      (sigma ^ 2 / 2 ≤ x → x < sigma ^ 2 → fSqrt sigma x = 2 * x / sigma - sigma) ∧
      (sigma ^ 2 ≤ x → fSqrt sigma x = Real.sqrt x) := by
  have hhalf : sigma ^ 2 / 2 < sigma ^ 2 := by nlinarith [sq_pos_of_pos hsigma]
  constructor
  · intro h
    rw [fSqrt, if_pos h]
  constructor
  · intro h1 h2
    rw [fSqrt, if_neg (not_lt_of_ge h1), if_pos h2]
  · intro h1
    rw [fSqrt, if_neg (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hhalf h1))), if_neg (not_lt_of_ge h1)]

/-- For positive `sigma`, the regularized inverse is zero below `sigma ^ 2 / 2`, follows the
stated linear formula up to `sigma ^ 2`, and equals `1 / x` above it. -/
theorem clause28_finv_branches (sigma x : ℝ) (hsigma : 0 < sigma) :
    (x < sigma ^ 2 / 2 → fInv sigma x = 0) ∧
      (sigma ^ 2 / 2 ≤ x → x < sigma ^ 2 →
        fInv sigma x = 2 * x / sigma ^ 4 - 1 / sigma ^ 2) ∧
      (sigma ^ 2 ≤ x → fInv sigma x = 1 / x) := by
  have hhalf : sigma ^ 2 / 2 < sigma ^ 2 := by nlinarith [sq_pos_of_pos hsigma]
  constructor
  · intro h
    rw [fInv, if_pos h]
  constructor
  · intro h1 h2
    rw [fInv, if_neg (not_lt_of_ge h1), if_pos h2]
  · intro h1
    rw [fInv, if_neg (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hhalf h1))), if_neg (not_lt_of_ge h1)]

/-- For nonzero `eps` and `sigma`, the Corollary 6.31 sample expression equals the square of its
row budget multiplied by `eps ^ 2`. -/
theorem clause28_samples_vs_row_budget (normBF eps sigma delta : ℝ) (heps : eps ≠ 0) (hsigma : sigma ≠ 0) :
    cor631Samples normBF eps sigma delta
      = (cor631RowBudget normBF eps sigma delta) ^ 2 * eps ^ 2 := by
  simp only [cor631Samples, cor631RowBudget]
  field_simp

/-- A nonnegative real number is at most its product with any real number at least one. -/
theorem le_mul_of_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ a * b := by
  have h := mul_le_mul_of_nonneg_left hb ha
  rwa [mul_one] at h

/-- The inverse of a real number in `(0, 1]` is at least one. -/
theorem one_le_inv_of_le_one {a : ℝ} (ha : 0 < a) (h1 : a ≤ 1) : 1 ≤ a⁻¹ := by
  have h : a * a⁻¹ ≤ 1 * a⁻¹ :=
    mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (le_of_lt ha))
  have h2 : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  rw [h2, one_mul] at h
  exact h

/-- The product of two real numbers each at least one is at least one. -/
theorem one_le_mul' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h := mul_le_mul ha hb (by norm_num) (by linarith)
  linarith [h]

/-- If five real factors are at least one, their product is at least the first factor. -/
theorem factor_le_prod5 {a b c d e : ℝ} (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c)
    (h4 : 1 ≤ d) (h5 : 1 ≤ e) : a ≤ a * b * c * d * e := by
  calc a ≤ a * b := le_mul_of_one_le (by linarith) h2
    _ ≤ a * b * c := le_mul_of_one_le (by positivity) h3
    _ ≤ a * b * c * d := le_mul_of_one_le (by positivity) h4
    _ ≤ a * b * c * d * e := le_mul_of_one_le (by positivity) h5

/-- If four real factors are at least one, their product is at least the first factor. -/
theorem factor_le_prod4 {a b c d : ℝ} (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c)
    (h4 : 1 ≤ d) : a ≤ a * b * c * d := by
  calc a ≤ a * b := le_mul_of_one_le (by linarith) h2
    _ ≤ a * b * c := le_mul_of_one_le (by positivity) h3
    _ ≤ a * b * c * d := le_mul_of_one_le (by positivity) h4

/-- Two nonnegative bases bounded by nonnegative `S` have a product of powers at most `S` raised
to the sum of the exponents. -/
theorem monomial2_le {S x y : ℝ} (hS0 : 0 ≤ S) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ S) (hy : y ≤ S) (m n : ℕ) : x ^ m * y ^ n ≤ S ^ (m + n) := by
  calc x ^ m * y ^ n ≤ S ^ m * S ^ n :=
        mul_le_mul (pow_le_pow_left₀ hx0 hx m) (pow_le_pow_left₀ hy0 hy n)
          (pow_nonneg hy0 n) (pow_nonneg hS0 m)
    _ = S ^ (m + n) := by rw [← pow_add]

/-- Five nonnegative bases bounded by nonnegative `S` have a product of powers at most `S`
raised to the sum of their exponents. -/
theorem monomial5_le {S x1 x2 x3 x4 x5 : ℝ} (hS0 : 0 ≤ S) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2)
    (h3 : 0 ≤ x3) (h4 : 0 ≤ x4) (h5 : 0 ≤ x5) (e1 : x1 ≤ S) (e2 : x2 ≤ S) (e3 : x3 ≤ S)
    (e4 : x4 ≤ S) (e5 : x5 ≤ S) (n1 n2 n3 n4 n5 : ℕ) :
    x1 ^ n1 * x2 ^ n2 * x3 ^ n3 * x4 ^ n4 * x5 ^ n5 ≤ S ^ (n1 + n2 + n3 + n4 + n5) := by
  calc x1 ^ n1 * x2 ^ n2 * x3 ^ n3 * x4 ^ n4 * x5 ^ n5
      ≤ S ^ n1 * S ^ n2 * S ^ n3 * S ^ n4 * S ^ n5 := by
        have p1 : 0 ≤ S ^ n1 := pow_nonneg hS0 n1
        have p2 : 0 ≤ S ^ n1 * S ^ n2 := mul_nonneg p1 (pow_nonneg hS0 n2)
        have p3 : 0 ≤ (S ^ n1 * S ^ n2) * S ^ n3 := mul_nonneg p2 (pow_nonneg hS0 n3)
        have p4 : 0 ≤ ((S ^ n1 * S ^ n2) * S ^ n3) * S ^ n4 :=
          mul_nonneg p3 (pow_nonneg hS0 n4)
        exact mul_le_mul
          (mul_le_mul
            (mul_le_mul
              (mul_le_mul (pow_le_pow_left₀ h1 e1 n1) (pow_le_pow_left₀ h2 e2 n2)
                (pow_nonneg h2 n2) p1)
              (pow_le_pow_left₀ h3 e3 n3) (pow_nonneg h3 n3) p2)
            (pow_le_pow_left₀ h4 e4 n4) (pow_nonneg h4 n4) p3)
            (pow_le_pow_left₀ h5 e5 n5) (pow_nonneg h5 n5) p4
    _ = S ^ (n1 + n2 + n3 + n4 + n5) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]

/-- Under the stated nonnegative parameter bounds by factors at least one, the even runtime
polynomial is at most three times the product bound to power 35, and the quantum expression
is at most twice that product to power 3. -/
theorem even_headline_bound {D A u L m a b c e f : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hu : 0 ≤ u) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hDa : D ≤ a) (hAb : A ≤ b) (huc : u ≤ c) (hLe : L ≤ e) (hmf : m ≤ f)
    (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c) (h4 : 1 ≤ e) (h5 : 1 ≤ f) :
    D ^ 16 * A ^ 10 * u ^ 6 * L ^ 3 + (D ^ 12 * A ^ 8 + D ^ 6 * A ^ 2) * u ^ 4 * L ^ 2 * m
        ≤ 3 * (a * b * c * e * f) ^ 35 ∧
      D * u * (m + L) ≤ 2 * (a * b * c * e * f) ^ 3 := by
  set S : ℝ := a * b * c * e * f with hSdef
  have hS1 : 1 ≤ S := by
    rw [hSdef]
    exact one_le_mul' (one_le_mul' (one_le_mul' (one_le_mul' h1 h2) h3) h4) h5
  have hS0 : 0 ≤ S := le_of_lt (lt_of_lt_of_le zero_lt_one hS1)
  have haS : a ≤ S := by
    rw [hSdef]
    exact factor_le_prod5 h1 h2 h3 h4 h5
  have hbS : b ≤ S := by
    rw [hSdef]
    calc b ≤ b * a * c * e * f :=
          factor_le_prod5 (a := b) (b := a) (c := c) (d := e) (e := f) h2 h1 h3 h4 h5
      _ = a * b * c * e * f := by ring
  have hcS : c ≤ S := by
    rw [hSdef]
    calc c ≤ c * a * b * e * f :=
          factor_le_prod5 (a := c) (b := a) (c := b) (d := e) (e := f) h3 h1 h2 h4 h5
      _ = a * b * c * e * f := by ring
  have heS : e ≤ S := by
    rw [hSdef]
    calc e ≤ e * a * b * c * f :=
          factor_le_prod5 (a := e) (b := a) (c := b) (d := c) (e := f) h4 h1 h2 h3 h5
      _ = a * b * c * e * f := by ring
  have hfS : f ≤ S := by
    rw [hSdef]
    calc f ≤ f * a * b * c * e :=
          factor_le_prod5 (a := f) (b := a) (c := b) (d := c) (e := e) h5 h1 h2 h3 h4
      _ = a * b * c * e * f := by ring
  have hDS : D ≤ S := hDa.trans haS
  have hAS : A ≤ S := hAb.trans hbS
  have huS : u ≤ S := huc.trans hcS
  have hLS : L ≤ S := hLe.trans heS
  have hmS : m ≤ S := hmf.trans hfS
  have hterm1 : D ^ 16 * A ^ 10 * u ^ 6 * L ^ 3 ≤ S ^ 35 := by
    have e1 : D ^ 16 ≤ S ^ 16 := pow_le_pow_left₀ hD hDS 16
    have e2 : A ^ 10 ≤ S ^ 10 := pow_le_pow_left₀ hA hAS 10
    have e3 : u ^ 6 ≤ S ^ 6 := pow_le_pow_left₀ hu huS 6
    have e4 : L ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ hL hLS 3
    have s1 : S ^ 16 * S ^ 10 * S ^ 6 * S ^ 3 = S ^ 35 := by
      rw [← pow_add, ← pow_add, ← pow_add]
    have p1 : 0 ≤ S ^ 16 := pow_nonneg hS0 16
    have p2 : 0 ≤ S ^ 16 * S ^ 10 := mul_nonneg p1 (pow_nonneg hS0 10)
    have p3 : 0 ≤ (S ^ 16 * S ^ 10) * S ^ 6 := mul_nonneg p2 (pow_nonneg hS0 6)
    refine le_trans ?_ s1.le
    exact mul_le_mul
      (mul_le_mul (mul_le_mul e1 e2 (pow_nonneg hA 10) p1) e3 (pow_nonneg hu 6) p2)
      e4 (pow_nonneg hL 3) p3
  have hterm2 : (D ^ 12 * A ^ 8 + D ^ 6 * A ^ 2) * u ^ 4 * L ^ 2 * m ≤ S ^ 27 + S ^ 15 := by
    have e1 : D ^ 12 * A ^ 8 ≤ S ^ 20 :=
      (monomial2_le hS0 hD hA hDS hAS 12 8).trans (le_of_eq (by rfl))
    have e2 : D ^ 6 * A ^ 2 ≤ S ^ 8 :=
      (monomial2_le hS0 hD hA hDS hAS 6 2).trans (le_of_eq (by rfl))
    have hsum : D ^ 12 * A ^ 8 + D ^ 6 * A ^ 2 ≤ S ^ 20 + S ^ 8 := add_le_add e1 e2
    have eu : u ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hu huS 4
    have eL : L ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hL hLS 2
    have p1 : 0 ≤ S ^ 20 + S ^ 8 := add_nonneg (pow_nonneg hS0 20) (pow_nonneg hS0 8)
    have p2 : 0 ≤ (S ^ 20 + S ^ 8) * S ^ 4 := mul_nonneg p1 (pow_nonneg hS0 4)
    have p3 : 0 ≤ ((S ^ 20 + S ^ 8) * S ^ 4) * S ^ 2 := mul_nonneg p2 (pow_nonneg hS0 2)
    have hmain : (D ^ 12 * A ^ 8 + D ^ 6 * A ^ 2) * u ^ 4 * L ^ 2 * m
        ≤ (S ^ 20 + S ^ 8) * S ^ 4 * S ^ 2 * S := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul hsum eu (pow_nonneg hu 4) p1)
          eL (pow_nonneg hL 2) p2)
        hmS hm p3
    have heq1 : S ^ 20 * S ^ 4 * S ^ 2 * S = S ^ 27 := by
      calc S ^ 20 * S ^ 4 * S ^ 2 * S = S ^ 20 * S ^ 4 * S ^ 2 * S ^ 1 := by
              simp [pow_one]
        _ = S ^ (20 + 4 + 2 + 1) := by rw [← pow_add, ← pow_add, ← pow_add]
        _ = S ^ 27 := by rfl
    have heq2 : S ^ 8 * S ^ 4 * S ^ 2 * S = S ^ 15 := by
      calc S ^ 8 * S ^ 4 * S ^ 2 * S = S ^ 8 * S ^ 4 * S ^ 2 * S ^ 1 := by
              simp [pow_one]
        _ = S ^ (8 + 4 + 2 + 1) := by rw [← pow_add, ← pow_add, ← pow_add]
        _ = S ^ 15 := by rfl
    refine hmain.trans (le_of_eq ?_)
    calc (S ^ 20 + S ^ 8) * S ^ 4 * S ^ 2 * S = S ^ 20 * S ^ 4 * S ^ 2 * S
            + S ^ 8 * S ^ 4 * S ^ 2 * S := by ring
      _ = S ^ 27 + S ^ 15 := by rw [heq1, heq2]
  have hsum3 : S ^ 35 + (S ^ 27 + S ^ 15) ≤ 3 * S ^ 35 := by
    have h27 : S ^ 27 ≤ S ^ 35 := pow_le_pow_right₀ hS1 (by omega)
    have h15 : S ^ 15 ≤ S ^ 35 := pow_le_pow_right₀ hS1 (by omega)
    nlinarith
  refine ⟨le_trans (add_le_add hterm1 hterm2) hsum3, ?_⟩
  have hq1 : D * u ≤ S * S := mul_le_mul hDS huS hu hS0
  have hq2 : m + L ≤ 2 * S := by
    have := add_le_add hmS hLS
    nlinarith [this]
  have hq3 : S * S * (2 * S) = 2 * S ^ 3 := by
    calc S * S * (2 * S) = 2 * (S * S * S) := by ring
      _ = 2 * (S ^ 1 * S ^ 1 * S ^ 1) := by simp [pow_one]
      _ = 2 * S ^ 3 := by rw [← pow_add, ← pow_add]
  have pq : 0 ≤ S * S := mul_nonneg hS0 hS0
  calc D * u * (m + L) ≤ S * S * (2 * S) := by
        exact mul_le_mul hq1 hq2 (add_nonneg hm hL) pq
    _ = 2 * S ^ 3 := hq3

/-- Under the stated nonnegative parameter bounds by factors at least one, the odd runtime
polynomial is at most three times the product bound to power 44, and the quantum expression
is at most that product to power 4. -/
theorem odd_headline_bound {D A u di m a b c e f : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hu : 0 ≤ u) (hdi : 0 ≤ di) (hm : 0 ≤ m)
    (hDa : D ≤ a) (hAb : A ≤ b) (huc : u ≤ c) (hdie : di ≤ e) (hmf : m ≤ f)
    (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c) (h4 : 1 ≤ e) (h5 : 1 ≤ f) :
    D ^ 22 * A ^ 16 * u ^ 6 + (D ^ 16 * A ^ 12 + D ^ 10 * A ^ 4 * di) * u ^ 4 * m
        ≤ 3 * (a * b * c * e * f) ^ 44 ∧
      D * u * m * di ≤ (a * b * c * e * f) ^ 4 := by
  set S : ℝ := a * b * c * e * f with hSdef
  have hS1 : 1 ≤ S := by
    rw [hSdef]
    exact one_le_mul' (one_le_mul' (one_le_mul' (one_le_mul' h1 h2) h3) h4) h5
  have hS0 : 0 ≤ S := le_of_lt (lt_of_lt_of_le zero_lt_one hS1)
  have haS : a ≤ S := by
    rw [hSdef]
    exact factor_le_prod5 h1 h2 h3 h4 h5
  have hbS : b ≤ S := by
    rw [hSdef]
    calc b ≤ b * a * c * e * f :=
          factor_le_prod5 (a := b) (b := a) (c := c) (d := e) (e := f) h2 h1 h3 h4 h5
      _ = a * b * c * e * f := by ring
  have hcS : c ≤ S := by
    rw [hSdef]
    calc c ≤ c * a * b * e * f :=
          factor_le_prod5 (a := c) (b := a) (c := b) (d := e) (e := f) h3 h1 h2 h4 h5
      _ = a * b * c * e * f := by ring
  have heS : e ≤ S := by
    rw [hSdef]
    calc e ≤ e * a * b * c * f :=
          factor_le_prod5 (a := e) (b := a) (c := b) (d := c) (e := f) h4 h1 h2 h3 h5
      _ = a * b * c * e * f := by ring
  have hfS : f ≤ S := by
    rw [hSdef]
    calc f ≤ f * a * b * c * e :=
          factor_le_prod5 (a := f) (b := a) (c := b) (d := c) (e := e) h5 h1 h2 h3 h4
      _ = a * b * c * e * f := by ring
  have hDS : D ≤ S := hDa.trans haS
  have hAS : A ≤ S := hAb.trans hbS
  have huS : u ≤ S := huc.trans hcS
  have hdiS : di ≤ S := hdie.trans heS
  have hmS : m ≤ S := hmf.trans hfS
  have hterm1 : D ^ 22 * A ^ 16 * u ^ 6 ≤ S ^ 44 := by
    have e1 : D ^ 22 ≤ S ^ 22 := pow_le_pow_left₀ hD hDS 22
    have e2 : A ^ 16 ≤ S ^ 16 := pow_le_pow_left₀ hA hAS 16
    have e3 : u ^ 6 ≤ S ^ 6 := pow_le_pow_left₀ hu huS 6
    have s1 : S ^ 22 * S ^ 16 * S ^ 6 = S ^ 44 := by
      rw [← pow_add, ← pow_add]
    have p1 : 0 ≤ S ^ 22 := pow_nonneg hS0 22
    have p2 : 0 ≤ S ^ 22 * S ^ 16 := mul_nonneg p1 (pow_nonneg hS0 16)
    refine le_trans ?_ s1.le
    exact mul_le_mul (mul_le_mul e1 e2 (pow_nonneg hA 16) p1)
      e3 (pow_nonneg hu 6) p2
  have hterm2 : (D ^ 16 * A ^ 12 + D ^ 10 * A ^ 4 * di) * u ^ 4 * m ≤ S ^ 33 + S ^ 20 := by
    have e1 : D ^ 16 * A ^ 12 ≤ S ^ 28 :=
      (monomial2_le hS0 hD hA hDS hAS 16 12).trans (le_of_eq (by rfl))
    have e2 : D ^ 10 * A ^ 4 * di ≤ S ^ 15 := by
      have h1 : D ^ 10 * A ^ 4 ≤ S ^ (10 + 4) :=
        monomial2_le hS0 hD hA hDS hAS 10 4
      have h2 : D ^ 10 * A ^ 4 * di ≤ S ^ (10 + 4) * S :=
        mul_le_mul h1 hdiS hdi (pow_nonneg hS0 14)
      refine le_trans h2 (le_of_eq ?_)
      calc S ^ (10 + 4) * S = S ^ (10 + 4) * S ^ 1 := by simp [pow_one]
        _ = S ^ (10 + 4 + 1) := by rw [← pow_add]
        _ = S ^ 15 := by rfl
    have hsum : D ^ 16 * A ^ 12 + D ^ 10 * A ^ 4 * di ≤ S ^ 28 + S ^ 15 :=
      add_le_add e1 e2
    have eu : u ^ 4 ≤ S ^ 4 := pow_le_pow_left₀ hu huS 4
    have p1 : 0 ≤ S ^ 28 + S ^ 15 := add_nonneg (pow_nonneg hS0 28) (pow_nonneg hS0 15)
    have p2 : 0 ≤ (S ^ 28 + S ^ 15) * S ^ 4 := mul_nonneg p1 (pow_nonneg hS0 4)
    have hmain : (D ^ 16 * A ^ 12 + D ^ 10 * A ^ 4 * di) * u ^ 4 * m
        ≤ (S ^ 28 + S ^ 15) * S ^ 4 * S := by
      exact mul_le_mul
        (mul_le_mul hsum eu (pow_nonneg hu 4) p1)
        hmS hm p2
    have heq1 : S ^ 28 * S ^ 4 * S = S ^ 33 := by
      calc S ^ 28 * S ^ 4 * S = S ^ 28 * S ^ 4 * S ^ 1 := by simp [pow_one]
        _ = S ^ (28 + 4 + 1) := by rw [← pow_add, ← pow_add]
        _ = S ^ 33 := by rfl
    have heq2 : S ^ 15 * S ^ 4 * S = S ^ 20 := by
      calc S ^ 15 * S ^ 4 * S = S ^ 15 * S ^ 4 * S ^ 1 := by simp [pow_one]
        _ = S ^ (15 + 4 + 1) := by rw [← pow_add, ← pow_add]
        _ = S ^ 20 := by rfl
    refine hmain.trans (le_of_eq ?_)
    calc (S ^ 28 + S ^ 15) * S ^ 4 * S = S ^ 28 * S ^ 4 * S + S ^ 15 * S ^ 4 * S := by ring
      _ = S ^ 33 + S ^ 20 := by rw [heq1, heq2]
  have hsum3 : S ^ 44 + (S ^ 33 + S ^ 20) ≤ 3 * S ^ 44 := by
    have h33 : S ^ 33 ≤ S ^ 44 := pow_le_pow_right₀ hS1 (by omega)
    have h20 : S ^ 20 ≤ S ^ 44 := pow_le_pow_right₀ hS1 (by omega)
    nlinarith
  refine ⟨le_trans (add_le_add hterm1 hterm2) hsum3, ?_⟩
  have hq1 : D * u ≤ S * S := mul_le_mul hDS huS hu hS0
  have hq3 : S * S * S * S = S ^ 4 := by
    calc S * S * S * S = S ^ 1 * S ^ 1 * S ^ 1 * S ^ 1 := by simp [pow_one]
      _ = S ^ 4 := by rw [← pow_add, ← pow_add, ← pow_add]
  have p1 : 0 ≤ S * S := mul_nonneg hS0 hS0
  have p2 : 0 ≤ S * S * S := mul_nonneg p1 hS0
  calc D * u * m * di ≤ S * S * S * S := by
        exact mul_le_mul
          (mul_le_mul hq1 hmS hm p1)
          hdiS hdi p2
    _ = S ^ 4 := hq3

/-- Under the stated positivity and probability bounds, the even classical runtime expression is
at most `3 * qvEvenScale ^ 35`, and the quantum total expression is at most `2 * qvEvenScale
^ 3`. -/
theorem clause17_even_no_exponential_advantage (d : ℕ) (normA normPv eps delta logMN : ℝ)
    (hA : 0 ≤ normA) (hPv : 0 ≤ normPv) (heps : 0 < eps) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hlog : 0 ≤ logMN) :
    qvEvenRuntime d normA normPv eps delta logMN
        ≤ 3 * (qvEvenScale d normA normPv eps delta logMN) ^ 35 ∧
      qvQuantumTotal d normPv eps (qvPolylog logMN delta)
        ≤ 2 * (qvEvenScale d normA normPv eps delta logMN) ^ 3 := by
  have hbound := even_headline_bound (D := (d : ℝ)) (A := normA)
    (u := (eps * normPv)⁻¹) (L := Real.log delta⁻¹) (m := logMN)
    (a := max 1 (d : ℝ)) (b := max 1 normA) (c := max 1 ((eps * normPv)⁻¹))
    (e := max 1 (Real.log delta⁻¹)) (f := max 1 logMN)
    (by positivity) hA (inv_nonneg.mpr (mul_nonneg heps.le hPv))
    (Real.log_nonneg (one_le_inv_of_le_one hdelta hdelta1)) hlog
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · unfold qvEvenRuntime
    exact hbound.1
  · unfold qvQuantumTotal qvPolylog
    calc (d : ℝ) * normPv⁻¹ * eps⁻¹ * (logMN + Real.log delta⁻¹)
        = (d : ℝ) * (eps * normPv)⁻¹ * (logMN + Real.log delta⁻¹) := by
            rw [_root_.mul_inv_rev]
            ring
      _ ≤ 2 * (qvEvenScale d normA normPv eps delta logMN) ^ 3 := hbound.2

/-- Under the stated positivity bounds, the odd classical runtime expression is at most `3 *
qvOddScale ^ 44`, and the quantum total expression is at most `qvOddScale ^ 4`. -/
theorem clause17_odd_no_exponential_advantage (d : ℕ) (normA normPv eps delta logMN : ℝ)
    (hA : 0 ≤ normA) (hPv : 0 ≤ normPv) (heps : 0 < eps) (hdelta : 0 < delta)
    (hlog : 0 ≤ logMN) :
    qvOddRuntime d normA normPv eps delta logMN
        ≤ 3 * (qvOddScale d normA normPv eps delta logMN) ^ 44 ∧
      qvQuantumTotalOdd d normPv eps delta logMN
        ≤ (qvOddScale d normA normPv eps delta logMN) ^ 4 := by
  have hbound := odd_headline_bound (D := (d : ℝ)) (A := normA)
    (u := (eps * normPv)⁻¹) (di := delta⁻¹) (m := logMN)
    (a := max 1 (d : ℝ)) (b := max 1 normA) (c := max 1 ((eps * normPv)⁻¹))
    (e := max 1 (delta⁻¹)) (f := max 1 logMN)
    (by positivity) hA (inv_nonneg.mpr (mul_nonneg heps.le hPv))
    (inv_nonneg.mpr (le_of_lt hdelta)) hlog
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (le_max_left _ _)
  refine ⟨?_, ?_⟩
  · unfold qvOddRuntime
    exact hbound.1
  · unfold qvQuantumTotalOdd
    calc (d : ℝ) * normPv⁻¹ * eps⁻¹ * logMN * delta⁻¹
        = (d : ℝ) * (eps * normPv)⁻¹ * logMN * delta⁻¹ := by
            rw [_root_.mul_inv_rev]
            ring
      _ ≤ (qvOddScale d normA normPv eps delta logMN) ^ 4 := hbound.2

/-- Under the stated nonnegative bounds by five factors at least one, `D ^ 12 * A ^ 4 * W * m *
L ^ 3` is at most their product to power 21. -/
theorem even_samples_bound {D A W L m a b c e f : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (hDa : D ≤ a) (hAb : A ≤ b) (hWc : W ≤ c) (hLe : L ≤ e) (hmf : m ≤ f)
    (h1 : 1 ≤ a) (h2 : 1 ≤ b) (h3 : 1 ≤ c) (h4 : 1 ≤ e) (h5 : 1 ≤ f) :
    D ^ 12 * A ^ 4 * W * m * L ^ 3 ≤ (a * b * c * e * f) ^ 21 := by
  set S : ℝ := a * b * c * e * f with hSdef
  have hS1 : 1 ≤ S := by
    rw [hSdef]
    exact one_le_mul' (one_le_mul' (one_le_mul' (one_le_mul' h1 h2) h3) h4) h5
  have hS0 : 0 ≤ S := le_of_lt (lt_of_lt_of_le zero_lt_one hS1)
  have haS : a ≤ S := by
    rw [hSdef]
    exact factor_le_prod5 h1 h2 h3 h4 h5
  have hbS : b ≤ S := by
    rw [hSdef]
    calc b ≤ b * a * c * e * f :=
          factor_le_prod5 (a := b) (b := a) (c := c) (d := e) (e := f) h2 h1 h3 h4 h5
      _ = a * b * c * e * f := by ring
  have hcS : c ≤ S := by
    rw [hSdef]
    calc c ≤ c * a * b * e * f :=
          factor_le_prod5 (a := c) (b := a) (c := b) (d := e) (e := f) h3 h1 h2 h4 h5
      _ = a * b * c * e * f := by ring
  have heS : e ≤ S := by
    rw [hSdef]
    calc e ≤ e * a * b * c * f :=
          factor_le_prod5 (a := e) (b := a) (c := b) (d := c) (e := f) h4 h1 h2 h3 h5
      _ = a * b * c * e * f := by ring
  have hfS : f ≤ S := by
    rw [hSdef]
    calc f ≤ f * a * b * c * e :=
          factor_le_prod5 (a := f) (b := a) (c := b) (d := c) (e := e) h5 h1 h2 h3 h4
      _ = a * b * c * e * f := by ring
  have hDS : D ≤ S := hDa.trans haS
  have hAS : A ≤ S := hAb.trans hbS
  have hWS : W ≤ S := hWc.trans hcS
  have hLS : L ≤ S := hLe.trans heS
  have hmS : m ≤ S := hmf.trans hfS
  have h := monomial5_le hS0 hD hA hW hm hL hDS hAS hWS hmS hLS 12 4 1 1 3
  simpa only [hSdef, pow_one] using! h

/-- Under the stated bounds with `D`, `W`, and `m` nonnegative and the four comparison factors
at least one, `D ^ 8 * W * m` is at most the comparison product to power 10. -/
theorem odd_samples_bound {D W di m a c e f : ℝ}
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hm : 0 ≤ m)
    (hDa : D ≤ a) (hWc : W ≤ c) (hdie : di ≤ e) (hmf : m ≤ f)
    (h1 : 1 ≤ a) (h2 : 1 ≤ c) (h3 : 1 ≤ e) (h4 : 1 ≤ f) :
    D ^ 8 * W * m ≤ (a * c * e * f) ^ 10 := by
  set S : ℝ := a * c * e * f with hSdef
  have hS1 : 1 ≤ S := by
    rw [hSdef]
    exact one_le_mul' (one_le_mul' (one_le_mul' h1 h2) h3) h4
  have hS0 : 0 ≤ S := le_of_lt (lt_of_lt_of_le zero_lt_one hS1)
  have haS : a ≤ S := by
    rw [hSdef]
    exact factor_le_prod4 h1 h2 h3 h4
  have hcS : c ≤ S := by
    rw [hSdef]
    calc c ≤ c * a * e * f := factor_le_prod4 (a := c) (b := a) (c := e) (d := f) h2 h1 h3 h4
      _ = a * c * e * f := by ring
  have heS : e ≤ S := by
    rw [hSdef]
    calc e ≤ e * a * c * f := factor_le_prod4 (a := e) (b := a) (c := c) (d := f) h3 h1 h2 h4
      _ = a * c * e * f := by ring
  have hfS : f ≤ S := by
    rw [hSdef]
    calc f ≤ f * a * c * e := factor_le_prod4 (a := f) (b := a) (c := c) (d := e) h4 h1 h2 h3
      _ = a * c * e * f := by ring
  have hDS : D ≤ S := hDa.trans haS
  have hWS : W ≤ S := hWc.trans hcS
  have hdiS : di ≤ S := hdie.trans heS
  have hmS : m ≤ S := hmf.trans hfS
  have e1 : D ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ hD hDS 8
  have e2 : W ≤ S := hWS
  have e3 : m ≤ S := hmS
  have s1 : S ^ 8 * S * S = S ^ 10 := by
    calc S ^ 8 * S * S = S ^ 8 * S ^ 1 * S ^ 1 := by simp [pow_one]
      _ = S ^ 10 := by rw [← pow_add, ← pow_add]
  have p1 : 0 ≤ S ^ 8 := pow_nonneg hS0 8
  have p2 : 0 ≤ S ^ 8 * S := mul_nonneg p1 hS0
  have h1 : D ^ 8 * W * m ≤ S ^ 8 * S * S := by
    exact mul_le_mul (mul_le_mul e1 e2 hW p1)
      e3 hm p2
  have h3 := h1.trans s1.le
  rw [hSdef] at h3
  exact h3

/-- For positive `normPv` and `eps`, `0 < delta ≤ 1`, and the stated nonnegative norm and
dimension parameters, the even sample expression is at most `qvEvenSampleScale ^ 21`. -/
theorem clause17_even_samples_poly_dominance (d : ℕ) (normA normPv eps delta logMN : ℝ)
    (hA : 0 ≤ normA) (hPv : 0 < normPv) (heps : 0 < eps) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hlog : 0 ≤ logMN) :
    qvEvenSamples d normA normPv eps delta logMN
      ≤ (qvEvenSampleScale d normA normPv eps delta logMN) ^ 21 := by
  have hW : 0 < (eps ^ 4 * normPv ^ 6)⁻¹ := by positivity
  have hbound := even_samples_bound (D := (d : ℝ)) (A := normA)
    (W := (eps ^ 4 * normPv ^ 6)⁻¹) (L := Real.log delta⁻¹) (m := logMN)
    (a := max 1 (d : ℝ)) (b := max 1 normA) (c := max 1 ((eps ^ 4 * normPv ^ 6)⁻¹))
    (e := max 1 (Real.log delta⁻¹)) (f := max 1 logMN)
    (by positivity) hA (le_of_lt hW) (Real.log_nonneg (one_le_inv_of_le_one hdelta hdelta1)) hlog
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    (le_max_right _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (le_max_left _ _)
  unfold qvEvenSamples
  exact hbound

/-- For positive `normPv`, `eps`, and `delta` and nonnegative `logMN`, the odd sample expression
is at most `qvOddSampleScale ^ 10`. -/
theorem clause17_odd_samples_poly_dominance (d : ℕ) (normPv eps delta logMN : ℝ)
    (hPv : 0 < normPv) (heps : 0 < eps) (hdelta : 0 < delta) (hlog : 0 ≤ logMN) :
    qvOddSamples d normPv eps delta logMN
      ≤ (qvOddSampleScale d normPv eps delta logMN) ^ 10 := by
  have hW : 0 < (eps ^ 2 * delta * normPv ^ 4)⁻¹ := by positivity
  have hbound := odd_samples_bound (D := (d : ℝ))
    (W := (eps ^ 2 * delta * normPv ^ 4)⁻¹) (di := delta⁻¹) (m := logMN)
    (a := max 1 (d : ℝ)) (c := max 1 ((eps ^ 2 * delta * normPv ^ 4)⁻¹))
    (e := max 1 (delta⁻¹)) (f := max 1 logMN)
    (by positivity) (le_of_lt hW) hlog
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
  unfold qvOddSamples
  exact hbound

/-- The Gram matrix operator norm is at most its spectral Frobenius norm, and the squared
spectral Frobenius norm of `A` equals the real trace of `Aᴴ * A`. -/
theorem clause17_gram_opNorm_le_frobenius {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) :
    ‖Aᴴ * A‖ ≤ spectralFrobenius (Aᴴ * A) ∧
      spectralFrobenius A ^ 2 = (Matrix.trace (Aᴴ * A)).re := by
  exact ⟨spectral_operator_norm_le_frobenius _, spectralFrobenius_sq_trace _⟩

/-- Under the stated parameter bounds, the even and odd classical runtime expressions and
corresponding quantum totals satisfy the four explicit polynomial bounds in `qvEvenScale`
and `qvOddScale` [ChiaEtAl2022]. -/
theorem clause17_endpoint (d : ℕ) (normA normPv eps delta logMN : ℝ)
    (hA : 0 ≤ normA) (hPv : 0 ≤ normPv) (heps : 0 < eps) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hlog : 0 ≤ logMN) :
    qvEvenRuntime d normA normPv eps delta logMN
        ≤ 3 * (qvEvenScale d normA normPv eps delta logMN) ^ 35 ∧
      qvQuantumTotal d normPv eps (qvPolylog logMN delta)
        ≤ 2 * (qvEvenScale d normA normPv eps delta logMN) ^ 3 ∧
      qvOddRuntime d normA normPv eps delta logMN
        ≤ 3 * (qvOddScale d normA normPv eps delta logMN) ^ 44 ∧
      qvQuantumTotalOdd d normPv eps delta logMN
        ≤ (qvOddScale d normA normPv eps delta logMN) ^ 4 := by
  have heven := clause17_even_no_exponential_advantage d normA normPv eps delta logMN
    hA hPv heps hdelta hdelta1 hlog
  have hodd := clause17_odd_no_exponential_advantage d normA normPv eps delta logMN
    hA hPv heps hdelta hlog
  exact ⟨heven.1, heven.2, hodd.1, hodd.2⟩

/-- Under the stated threshold hypotheses, the scalar threshold lies in `[0, lam]`, the
threshold operator has norm at most `‖A‖`, and the leading Corollary 6.7 runtime term has
the displayed norm expansion [ChiaEtAl2022]. -/
theorem clause18_endpoint {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (sigma eta lam : ℝ) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hlam : 0 ≤ lam) (normAF normA eps delta : ℝ) (hsigma2 : 0 < sigma) :
    0 ≤ thresholdSvt sigma eta lam ∧ thresholdSvt sigma eta lam ≤ lam ∧
      ‖thresholdSvtOperator A sigma eta‖ ≤ ‖A‖ ∧
      (cor67K normAF sigma) ^ 3 * (cor67Kappa normA sigma) ^ 5 / (eta ^ 6 * eps ^ 6)
        * (Real.log delta⁻¹) ^ 3
          = normAF ^ 6 * normA ^ 10 / (sigma ^ 16 * eta ^ 6 * eps ^ 6)
            * (Real.log delta⁻¹) ^ 3 := by
  obtain ⟨hb, ht⟩ := clause18_thresholdSvt_bounds sigma eta lam hsigma heta heta1 hlam
  exact ⟨hb, ht, clause18_threshold_operator_norm_le A sigma eta hsigma heta heta1,
    clause18_first_term_expansion normAF normA sigma eps eta delta hsigma2⟩

/-- The Corollary 6.10 runtime expression equals both the squared tensor-norm expression divided
by `eps ^ 2` and the squared quantum runtime expression, each with its logarithmic factor
[ChiaEtAl2022]. -/
theorem clause19_endpoint (normMF normW eps delta : ℝ) :
    cor610Runtime normMF normW eps delta
        = (cor610TensorNorms normMF normW) ^ 2 / eps ^ 2 * Real.log delta⁻¹ ∧
      cor610Runtime normMF normW eps delta
        = (cor610QuantumRuntime normMF normW eps) ^ 2 * Real.log delta⁻¹ := by
  exact ⟨clause19_samples_from_tensor_norms normMF normW eps delta,
    clause19_classical_is_quantum_square normMF normW eps delta⟩

/-- Under the trace and positive-eigenvalue hypotheses, `cor612Kappa ≤ cor612K`, and the
associated scalar spectral filter lies in `[0, 1]` [ChiaEtAl2022]. -/
theorem clause20_endpoint (traceX normX lambdaK : ℝ) (hK : 0 < lambdaK)
    (htrace : normX ^ 2 ≤ traceX) (lambdaHat gap x : ℝ) :
    cor612Kappa normX lambdaK ≤ cor612K traceX lambdaK ∧
      0 ≤ cor612SpectralFilter lambdaHat gap x ∧ cor612SpectralFilter lambdaHat gap x ≤ 1 := by
  obtain ⟨hb, ht⟩ := clause20_spectralFilter_bounds lambdaHat gap x
  exact ⟨clause20_K_ge_kappa traceX normX lambdaK hK htrace, hb, ht⟩

/-- The worst-case Corollary 6.15 runtime and sample expressions differ from the general
expressions by factors `kappa ^ 3` and `kappa`, respectively, and the stated relative-error
hypotheses bound the norm ratio by 100 [ChiaEtAl2022]. -/
theorem clause21_endpoint (phi K kappa eps eta delta : ℝ) {normXStar normXHat : ℝ}
    (heps : 0 < eps) (heps1 : eps ≤ 99 / 100) (hstar : 0 < normXStar)
    (herr : normXHat ≥ (1 - eps) * normXStar) :
    cor615WorstRuntime phi K kappa eps eta delta * kappa ^ 3
        = cor615Runtime phi K kappa eps eta delta ∧
      cor615WorstSamples phi K kappa eps eta delta * kappa
        = cor615Samples phi K kappa eps eta delta 1 1 ∧
      normXStar / normXHat ≤ 100 := by
  exact ⟨clause21_worst_case_saves_kappa_cubed phi K kappa eps eta delta,
    clause21_worst_case_saves_kappa phi K kappa eps eta delta,
    clause21_relative_error_100 heps heps1 hstar herr⟩

/-- For `m > 0` and `traceF ≥ Real.sqrt m`, the Corollary 6.17 norm parameter is at most `normF
^ 2 / m` [ChiaEtAl2022]. -/
theorem clause22_endpoint (normF traceF m : ℝ) (hm : 0 < m) (htrace : Real.sqrt m ≤ traceF) :
    cor617MNorm normF traceF ≤ normF ^ 2 / m := by
  exact clause22_M_norm_bound normF traceF m hm htrace

/-- Both Gram spectra of `X` and `Xᴴ` are given by squared singular values, and substituting the
dimension-free gamma parameter gives the displayed Corollary 6.18 runtime formula
[ChiaEtAl2022]. -/
theorem clause23_endpoint {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (X : Matrix O I ℂ) (i : Fin (Fintype.card I)) (j : Fin (Fintype.card O))
    (normXF normX eps delta : ℝ) :
    orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self X) i
        = (matrixSingularValues X i) ^ 2 ∧
      orderedHermitianValues (Matrix.isHermitian_conjTranspose_mul_self Xᴴ) j
        = (matrixSingularValues Xᴴ j) ^ 2 ∧
      cor618Runtime normXF normX (cor618DimensionFreeGamma normXF) eps delta
        = normXF ^ 6 * normX ^ 16 * (1 / normXF ^ 2) ^ 11 / eps ^ 6
          * (Real.log delta⁻¹) ^ 3 := by
  exact ⟨clause23_gram_spectrum_X X i, clause23_gram_spectrum_Xt X j,
    clause23_dimension_free normXF normX eps delta⟩

/-- For nonzero `sigma` and `eps`, the Corollary 6.20 runtime is its natural-error variant times
`normH ^ 6`, and that variant has the stated norm expansion [ChiaEtAl2022]. -/
theorem clause24_endpoint (normHF normH sigma eps delta : ℝ) (hsigma : sigma ≠ 0)
    (heps : eps ≠ 0) :
    cor620Runtime normHF normH sigma eps delta
        = cor620NaturalRuntime normHF normH sigma eps delta * normH ^ 6 ∧
      cor620NaturalRuntime normHF normH sigma eps delta
        = normHF ^ 6 * normH ^ 10 / (sigma ^ 16 * eps ^ 6) * (Real.log delta⁻¹) ^ 3 := by
  exact ⟨clause24_natural_error_ratio normHF normH sigma eps delta hsigma heps,
    clause24_natural_error_dimension_free normHF normH sigma eps delta⟩

/-- The even and odd scalar profiles at `lam ^ 2` combine as `fCos (lam ^ 2) + lam * fSinc (lam
^ 2) = cos lam + sin lam` [ChiaEtAl2022]. -/
theorem clause25_endpoint (lam : ℝ) :
    fCos (lam ^ 2) + lam * fSinc (lam ^ 2) = Real.cos lam + Real.sin lam := by
  exact clause25_even_odd_scalar lam

/-- The Corollary 6.25 parameter expressions give `16 * log n / eps ^ 2` rounds and step size
`eps / 4` [ChiaEtAl2022]. -/
theorem clause26_endpoint (n eps : ℝ) :
    cor625Rounds n eps = 16 * Real.log n / eps ^ 2 ∧ cor625Step eps = eps / 4 := by
  exact clause26_mmw_parameters n eps

/-- The normalized-ratio error is at most `theta` under the stated numerator and denominator
bounds, with precision parameter `theta / 3` [ChiaEtAl2022]. -/
theorem clause27_endpoint {theta : ℝ} (a aHat : ℂ) (Z : ℝ) (Zhat : ℂ)
    (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (ha : ‖a‖ ≤ Z)
    (haa : ‖a - aHat‖ ≤ (theta / 3) * Z) (hZZ : ‖(Z : ℂ) - Zhat‖ ≤ (theta / 3) * Z) :
    ‖aHat / Zhat - a / (Z : ℂ)‖ ≤ theta ∧ lemma626Precision theta = theta / 3 := by
  exact ⟨clause27_lemma626_reduction a aHat Z Zhat hθ0 hθ1 ha haa hZZ,
    clause27_precision_reduction theta⟩

/-- For positive `sigma`, the regularized square-root and inverse functions have the stated
three branches, and the Corollary 6.31 sample expression equals its squared row budget times
`eps ^ 2` [ChiaEtAl2022]. -/
theorem clause28_endpoint (sigma x : ℝ) (hsigma : 0 < sigma) (normBF eps delta : ℝ)
    (heps : eps ≠ 0) (hsigma2 : sigma ≠ 0) :
    (x < sigma ^ 2 / 2 → fSqrt sigma x = 0) ∧
        (sigma ^ 2 / 2 ≤ x → x < sigma ^ 2 → fSqrt sigma x = 2 * x / sigma - sigma) ∧
        (sigma ^ 2 ≤ x → fSqrt sigma x = Real.sqrt x) ∧
      (x < sigma ^ 2 / 2 → fInv sigma x = 0) ∧
        (sigma ^ 2 / 2 ≤ x → x < sigma ^ 2 →
          fInv sigma x = 2 * x / sigma ^ 4 - 1 / sigma ^ 2) ∧
        (sigma ^ 2 ≤ x → fInv sigma x = 1 / x) ∧
      cor631Samples normBF eps sigma delta
        = (cor631RowBudget normBF eps sigma delta) ^ 2 * eps ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := clause28_fsqrt_branches sigma x hsigma
  obtain ⟨h4, h5, h6⟩ := clause28_finv_branches sigma x hsigma
  exact ⟨h1, h2, h3, h4, h5, h6, clause28_samples_vs_row_budget normBF eps sigma delta heps hsigma2⟩

end

end StageBSQGENERALSVT
