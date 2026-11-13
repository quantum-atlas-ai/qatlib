/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpDualCertificateMacroStat
import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpDualPayoffRangeQuan
import Qatlib.Concepts.MatrixWeights.LambdaMin
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Dual certificates from matrix multiplicative weights

`sdpDualCertificateMacro` derives a nonnegative, dual feasible certificate with objective at
most (1 + δ)α from successful oracle responses along the Gibbs history. Trace identities and a
comparator threshold convert the matrix multiplicative weights estimate into positive
semidefiniteness of the certificate slack.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpDualCertificateMacro`: Under the normalized input and oracle hypotheses, the averaged dual
  certificate is nonnegative, has objective at most (1 + δ)α, and has positive semidefinite
  slack. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.LambdaMin
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.SdpMmwSolver.SdpContract

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- Evaluates a linear functional on `sdpDualCertificate` as the distinguished-coordinate
correction plus the time average of the response functionals. -/
private theorem dualOutputEval (m T : ℕ) (delta alpha R : ℝ) (j0 : Fin m)
    (y : ℕ → Fin m → ℝ) (f : Fin m → ℝ) :
    (∑ i, sdpDualCertificate m delta alpha R j0 y T i * f i) =
      delta * alpha / (2 * R) * f j0 + (∑ t ∈ Finset.range T, ∑ i, y t i * f i) / T := by
  simp only [sdpDualCertificate, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  simp only [Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]

/-- Expands the real trace of an SDP dual payoff against a density operator into the weighted
constraint traces, objective trace, and scalar offset. -/
private theorem payoffTrace (D m : ℕ) (A : Fin m → Operator D) (C : Operator D)
    (alpha : ℝ) (y : ℕ → Fin m → ℝ) (s : ℕ) (sigma : Operator D)
    (hsigma : IsDensityOperator sigma) :
    (Matrix.trace (sdpDualPayoff D m A C alpha y s * sigma)).re =
      ((∑ i, y s i * (Matrix.trace (A i * sigma)).re) -
        (Matrix.trace (C * sigma)).re + 2 * alpha) / (4 * alpha) := by
  simp only [sdpDualPayoff, Matrix.smul_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.sum_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_sum, Complex.re_sum, Complex.add_re,
    Complex.sub_re, Complex.smul_re, smul_eq_mul, hsigma.2, Complex.one_re, mul_one]
  ring

/-- Sums the payoff trace identity over the first `T` rounds, expressing the result through
cumulative constraint traces. -/
private theorem payoffTraceSum (D m T : ℕ) (A : Fin m → Operator D) (C : Operator D)
    (alpha : ℝ) (y : ℕ → Fin m → ℝ) (sigma : Operator D)
    (hsigma : IsDensityOperator sigma) :
    (∑ t ∈ Finset.range T, (Matrix.trace (sdpDualPayoff D m A C alpha y t * sigma)).re) =
      ((∑ t ∈ Finset.range T, ∑ i, y t i * (Matrix.trace (A i * sigma)).re) -
        T * (Matrix.trace (C * sigma)).re + T * (2 * alpha)) / (4 * alpha) := by
  simp_rw [payoffTrace D m A C alpha y _ sigma hsigma]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Expresses the certificate slack trace against a density operator in terms of cumulative
payoff traces when the distinguished constraint is the identity. -/
private theorem certificateTrace (D m T : ℕ) (A : Fin m → Operator D) (C : Operator D)
    (delta alpha R : ℝ) (j0 : Fin m) (y : ℕ → Fin m → ℝ) (sigma : Operator D)
    (ha : 0 < alpha) (hT : 0 < T) (hA0 : A j0 = 1) (hsigma : IsDensityOperator sigma) :
    (Matrix.trace (((∑ i, sdpDualCertificate m delta alpha R j0 y T i • A i) - C) * sigma)).re =
      (4 * alpha / T) * (∑ t ∈ Finset.range T,
        (Matrix.trace (sdpDualPayoff D m A C alpha y t * sigma)).re) +
        delta * alpha / (2 * R) - 2 * alpha := by
  simp only [Matrix.sub_mul, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_sum, Complex.sub_re, Complex.re_sum, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul]
  rw [dualOutputEval, payoffTraceSum D m T A C alpha y sigma hsigma]
  rw [hA0, Matrix.one_mul, hsigma.2, Complex.one_re, mul_one]
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp [ha.ne', hTr]
  ring

/-- Derives the comparator lower bound T(1/2 − δ/(8R)) from the stated regret bound,
actual-payoff lower bound, and parameter inequalities. -/
private theorem comparatorThreshold (R delta eps eta T L S actual : ℝ)
    (hR : 0 < R) (hd : 0 < delta) (heta : 0 < eta) (hT : 0 < T)
    (hsmall : eta + eps ≤ delta / (8 * R)) (hround : 16 * R * L ≤ T * delta * eta)
    (hreg : actual ≤ (1 + eta) * S + (1 + eta) * L / eta)
    (hlower : T * (1 - eps) / 2 ≤ actual) :
    T * (1 / 2 - delta / (8 * R)) ≤ S := by
  let q := delta / (16 * R)
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmall' : eta + eps ≤ 2 * q := by
    convert! hsmall using 1
    dsimp [q]
    ring
  have hlog : L / eta ≤ T * q := by
    apply (div_le_iff₀ heta).mpr
    have h : L ≤ (T * delta * eta) / (16 * R) :=
      (le_div_iff₀ (by positivity : 0 < 16 * R)).mpr (by nlinarith [hround])
    convert! h using 1
    dsimp [q]
    ring
  have hupper : actual ≤ (1 + eta) * S + (1 + eta) * (T * q) := by
    apply hreg.trans
    rw [mul_div_assoc]
    exact add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 1 + eta))
  have hgap : (1 + eta) * (T * (1 / 2 - 2 * q)) + (1 + eta) * (T * q) ≤ T * (1 - eps) / 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall' hT.le
    nlinarith [mul_nonneg heta.le (mul_nonneg hT.le hq.le)]
  have hs : T * (1 / 2 - 2 * q) ≤ S := by
    by_contra hbad
    have hstrict := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) (by positivity : 0 < 1 + eta)
    linarith
  convert! hs using 1
  dsimp [q]
  ring

/-- Identifies the trace of `A` times the outer product of `v` with the inner product of `v` and
`A *ᵥ v`. -/
private theorem traceOuterEval {D : ℕ} (A : Operator D) (v : QState (Fin D)) :
    Matrix.trace (A * outerProduct v) = Qatlib.Foundations.PureStateMath.Inner v (A *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct, Matrix.of_apply, Qatlib.Foundations.PureStateMath.Inner,
    dotProduct, Matrix.mulVec, Pi.star_apply, starRingEnd_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A Hermitian operator is positive semidefinite if its real trace pairing with every density
operator is nonnegative. -/
private theorem psdOfDensityTrace {D : ℕ} (A : Operator D) (hA : A.IsHermitian)
    (h : ∀ sigma : Operator D, IsDensityOperator sigma → 0 ≤ (Matrix.trace (A * sigma)).re) :
    A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg]
  intro i
  let v : QState (Fin D) := ⇑(hA.eigenvectorBasis i)
  have hv : Normalized v := (normalized_iff_norm_toEuclidean_fromVec v).mpr
    (hA.eigenvectorBasis.orthonormal.1 i)
  have he : A *ᵥ v = (hA.eigenvalues i : ℂ) • v := by
    simpa only [RCLike.real_smul_eq_coe_smul] using! hA.mulVec_eigenvectorBasis i
  have ht := h (outerProduct v) (isDensityOperator_outerProduct hv)
  rw [traceOuterEval, he, Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul] at ht
  change 0 ≤ ((hA.eigenvalues i : ℂ) * Qatlib.Foundations.PureStateMath.Inner v v).re at ht
  rwa [(normalized_iff_inner_self v).mp hv, mul_one, Complex.ofReal_re] at ht

/-- Under the normalized input and oracle hypotheses, the averaged dual certificate is
nonnegative, has objective at most (1 + δ)α, and has positive semidefinite slack. See
[BrandaoSvore2017]. -/
theorem sdpDualCertificateMacro : SdpDualCertificateMacro := by
  intro D m A Cv b y j0 alpha R delta eps eta hD ha ha1 hR hd he heta hsmall hA hCv hb hA0 hb0 hy
  let T := sdpDualCertRounds D R delta eta
  let M := sdpDualPayoff D m A Cv alpha y
  let Z := (∑ i, sdpDualCertificate m delta alpha R j0 y T i • A i) - Cv
  have hT : 0 < T := Nat.succ_pos _
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hrange := sdpDualPayoffRange D m A Cv b y alpha hD ha ha1 hA hCv hb
    (fun t => ⟨(hy t).1, (hy t).2.1⟩)
  have hM : ∀ s, (M s).PosSemidef ∧ M s ≤ 1 := by
    intro s
    refine ⟨?_, (hrange s).2.2⟩
    have h := Matrix.le_iff.mp (hrange s).2.1
    simpa only [sub_zero] using! h
  have hround : 16 * R * Real.log D ≤ (T : ℝ) * delta * eta := by
    have hc := Nat.le_ceil (16 * R * Real.log D / (delta * eta))
    have ht : 16 * R * Real.log D / (delta * eta) ≤ (T : ℝ) := by
      dsimp [T, sdpDualCertRounds]
      push_cast
      linarith
    have h := (div_le_iff₀ (mul_pos hd heta)).mp ht
    nlinarith
  have hactual : (T : ℝ) * (1 - eps) / 2 ≤
      ∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re := by
    have hpoint (t : ℕ) : (1 - eps) / 2 ≤ (Matrix.trace (M t * mmwState D M eta t)).re := by
      have hdensity := (matrix_mw_actual_gibbs_iterates_density D M eta t hD
        (fun s => (hM s).1.isHermitian)).2
      rw [payoffTrace D m A Cv alpha y t _ hdensity]
      apply (le_div_iff₀ (by positivity : 0 < 4 * alpha)).mpr
      have h := (hy t).2.2
      nlinarith
    have h := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hpoint t)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc] using! h
  have hZ : Z.IsHermitian :=
    (isSelfAdjoint_sum _ (fun i _ => (hA i).1.smul (by simp [IsSelfAdjoint]))).sub hCv.1
  have hpsd : Z.PosSemidef := by
    apply psdOfDensityTrace Z hZ
    intro sigma hsigma
    have hreg := matrix_mw_sum_trace_le_scaled_comparator D T M eta sigma hD heta hM hsigma
    have hthreshold := comparatorThreshold R delta eps eta (T : ℝ) (Real.log D)
      (∑ t ∈ Finset.range T, (Matrix.trace (M t * sigma)).re)
      (∑ t ∈ Finset.range T, (Matrix.trace (M t * mmwState D M eta t)).re)
      hR hd heta hTr hsmall hround hreg hactual
    have hscaled := mul_le_mul_of_nonneg_left hthreshold
      (by positivity : 0 ≤ 4 * alpha / (T : ℝ))
    have hidentity : (4 * alpha / (T : ℝ)) * ((T : ℝ) * (1 / 2 - delta / (8 * R))) +
        delta * alpha / (2 * R) - 2 * alpha = 0 := by
      field_simp [hR.ne', hTr.ne']
      ring
    rw [certificateTrace D m T A Cv delta alpha R j0 y sigma ha hT hA0 hsigma]
    nlinarith
  refine ⟨?_, ?_, hpsd⟩
  · intro i
    unfold sdpDualCertificate
    apply add_nonneg
    · split_ifs <;> positivity
    · apply div_nonneg _ (Nat.cast_nonneg T)
      exact Finset.sum_nonneg (fun t _ => (hy t).1 i)
  · rw [dualOutputEval, hb0]
    have hwidth : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) ≤ (T : ℝ) * alpha := by
      have h := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => (hy t).2.1)
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using! h
    have havg : (∑ t ∈ Finset.range T, ∑ i, y t i * b i) / (T : ℝ) ≤ alpha :=
      (div_le_iff₀ hTr).mpr (by simpa only [mul_comm] using! hwidth)
    have hoff : delta * alpha / (2 * R) * R = delta * alpha / 2 := by field_simp
    rw [hoff]
    nlinarith

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
