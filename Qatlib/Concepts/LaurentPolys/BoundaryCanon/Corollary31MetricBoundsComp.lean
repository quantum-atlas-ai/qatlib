/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.Corollary31MetricBoundsStat
public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.MetricLossEquivalenceComp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Complex Polynomial MeasureTheory Filter
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator Polynomial Topology

/-- Every extended coefficient of a polynomial bounded by one on the unit circle has norm at
most one. -/
private theorem coeff_norm_le_one_of_circle_le_one (Q : Polynomial ℂ) (d : ℕ)
    (hq : Q.natDegree ≤ d) (hQ : ∀ z : ℂ, ‖z‖ = 1 → ‖Q.eval z‖ ≤ 1) (k : ℤ) :
    ‖sourceCoeffAt Q k‖ ≤ 1 := by
  by_cases hk : 0 ≤ k ∧ k.toNat ≤ d
  · rcases hk with ⟨hk0, hkd⟩
    have hcoeff : sourceCoeffAt Q k = Q.coeff k.toNat := by
      simp [sourceCoeffAt, hk0]
    rw [hcoeff]
    let N := d + 1
    have hN : 0 < N := Nat.succ_pos d
    have hQN : Q.natDegree < N := Nat.lt_succ_of_le hq
    let ω := Complex.exp ((2 * Real.pi / (N : ℝ) : ℝ) * Complex.I)
    have hω : IsPrimitiveRoot ω N := by
      convert Complex.isPrimitiveRoot_exp N hN.ne' using 1
      dsimp [ω]
      congr 1
      push_cast
      ring
    have hdft := canonicalComplement_polynomial_dft_exact Q N hN hQN ω hω k.toNat
      (Nat.lt_succ_of_le hkd)
    rw [← hdft, norm_mul, norm_inv, Complex.norm_natCast]
    have hNR : (0 : ℝ) < (N : ℝ) := by positivity
    have hω_norm : ‖ω‖ = 1 := by
      dsimp [ω]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsum : ‖∑ j : Fin N, Q.eval (ω ^ j.val) * ω ^ (-((k.toNat : ℤ) * (j.val : ℤ)))‖ ≤ (N : ℝ) := by
      calc
        ‖∑ j : Fin N, Q.eval (ω ^ j.val) * ω ^ (-((k.toNat : ℤ) * (j.val : ℤ)))‖
          ≤ ∑ j : Fin N, ‖Q.eval (ω ^ j.val) * ω ^ (-((k.toNat : ℤ) * (j.val : ℤ)))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _j : Fin N, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            rw [norm_mul, norm_zpow, hω_norm, one_zpow, mul_one]
            exact hQ (ω ^ j.val) (by rw [norm_pow, hω_norm, one_pow])
        _ = (N : ℝ) := by simp
    exact (inv_mul_le_iff₀ hNR).mpr (by linarith)
  · have hzero : sourceCoeffAt Q k = 0 := by
      by_cases hk0 : 0 ≤ k
      · exact sourceCoeffAt_eq_zero_of_gt_deg Q hq (by omega)
      · exact sourceCoeffAt_eq_zero_of_lt_zero Q (by omega)
    rw [hzero, norm_zero]
    norm_num

/-- Coefficient errors below `ε` give the stated degree dependent upper bounds for both
complementarity loss metrics. -/
theorem corollary_3_1_metric_bounds (P Q Q' : Polynomial ℂ) (d : ℕ) (ε : ℝ)
    (hp : P.natDegree ≤ d) (hq : Q.natDegree ≤ d) (hq' : Q'.natDegree ≤ d)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hQc : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1)
    (hcoeff : ∀ n : ℕ, n ≤ d → ‖Q.coeff n - Q'.coeff n‖ < ε) :
    sourcePhiUniform P Q' < ((d : ℝ) + 1) * ((d : ℝ) + 3) * ε ∧
    sourcePhiTilde P Q' d < 3 * ((d : ℝ) + 1) * (2 * (d : ℝ) + 1) * ε := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hQ_circle (z : ℂ) (hz : ‖z‖ = 1) : ‖Q.eval z‖ ≤ 1 := by
    have h1 := hQc z hz
    have h2 : 0 ≤ ‖P.eval z‖ ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg (Q.eval z)]
  have hdiff_eval (z : ℂ) (hz : ‖z‖ = 1) : ‖Q.eval z - Q'.eval z‖ ≤ ((d : ℝ) + 1) * ε := by
    have hdeg_sub : (Q - Q').natDegree < d + 1 :=
      Nat.lt_succ_of_le ((Polynomial.natDegree_sub_le Q Q').trans (max_le hq hq'))
    rw [← Polynomial.eval_sub, Polynomial.eval_eq_sum_range' hdeg_sub]
    calc
      ‖∑ i ∈ Finset.range (d + 1), (Q - Q').coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range (d + 1), ‖(Q - Q').coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (d + 1), ε := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Polynomial.coeff_sub, norm_mul, norm_pow, hz, one_pow, mul_one]
          exact (hcoeff i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).le
      _ = ((d : ℝ) + 1) * ε := by simp [Nat.cast_add, Nat.cast_one]
  let B : ℝ := ((d : ℝ) + 1) * (2 + ((d : ℝ) + 1) * ε) * ε
  have hunif_le (z : ℂ) (hz : ‖z‖ = 1) : circleResidual P Q' z ≤ B := by
    have h1 := hQc z hz
    have hQ'z : ‖Q'.eval z‖ ≤ 1 + ((d : ℝ) + 1) * ε := by
      have htri := norm_add_le (Q.eval z) (Q'.eval z - Q.eval z)
      rw [add_sub_cancel, norm_sub_rev] at htri
      linarith [hQ_circle z hz, hdiff_eval z hz]
    have hres_eq : circleResidual P Q' z = |‖Q'.eval z‖ ^ 2 - ‖Q.eval z‖ ^ 2| := by
      unfold circleResidual
      congr 1
      linarith
    rw [hres_eq]
    have hnonneg : 0 ≤ ‖Q'.eval z‖ + ‖Q.eval z‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : |‖Q'.eval z‖ ^ 2 - ‖Q.eval z‖ ^ 2| =
        |‖Q'.eval z‖ - ‖Q.eval z‖| * (‖Q'.eval z‖ + ‖Q.eval z‖) := by
      have hfactor : ‖Q'.eval z‖ ^ 2 - ‖Q.eval z‖ ^ 2 =
          (‖Q'.eval z‖ - ‖Q.eval z‖) * (‖Q'.eval z‖ + ‖Q.eval z‖) := by ring
      rw [hfactor, abs_mul, abs_of_nonneg hnonneg]
    rw [hsq]
    have habs_diff : |‖Q'.eval z‖ - ‖Q.eval z‖| ≤ ((d : ℝ) + 1) * ε := by
      rw [abs_sub_comm]
      exact (abs_norm_sub_norm_le (Q.eval z) (Q'.eval z)).trans (hdiff_eval z hz)
    have hsum_norm : ‖Q'.eval z‖ + ‖Q.eval z‖ ≤ 2 + ((d : ℝ) + 1) * ε := by
      linarith [hQ_circle z hz]
    have hmul : |‖Q'.eval z‖ - ‖Q.eval z‖| * (‖Q'.eval z‖ + ‖Q.eval z‖) ≤
        (((d : ℝ) + 1) * ε) * (2 + ((d : ℝ) + 1) * ε) :=
      mul_le_mul habs_diff hsum_norm hnonneg (by positivity)
    dsimp [B]
    linarith
  have hphi_le : sourcePhiUniform P Q' ≤ B := by
    unfold sourcePhiUniform
    apply csSup_le
    · exact ⟨circleResidual P Q' 1, ⟨1, by simp, rfl⟩⟩
    · rintro y ⟨z, hz, rfl⟩
      exact hunif_le z hz
  have hB_lt : B < ((d : ℝ) + 1) * ((d : ℝ) + 3) * ε := by
    dsimp [B]
    have hstep1 : ((d : ℝ) + 1) * ε < (d : ℝ) + 1 := by
      simpa using mul_lt_mul_of_pos_left hε1 (by linarith : (0 : ℝ) < (d : ℝ) + 1)
    have hstep2 : 2 + ((d : ℝ) + 1) * ε < (d : ℝ) + 3 := by linarith
    have hstep3 := mul_lt_mul_of_pos_left hstep2 (by linarith : (0 : ℝ) < (d : ℝ) + 1)
    have hstep4 := mul_lt_mul_of_pos_right hstep3 hε
    linarith
  refine ⟨hphi_le.trans_lt hB_lt, ?_⟩
  have hQ_coeff (k : ℤ) : ‖sourceCoeffAt Q k‖ ≤ 1 :=
    coeff_norm_le_one_of_circle_le_one Q d hq hQ_circle k
  have hdiff_coeff (k : ℤ) : ‖sourceCoeffAt Q k - sourceCoeffAt Q' k‖ ≤ ε := by
    by_cases hk : 0 ≤ k ∧ k.toNat ≤ d
    · rcases hk with ⟨hk0, hkd⟩
      simp only [sourceCoeffAt, hk0]
      exact (hcoeff k.toNat hkd).le
    · have hQ0 : sourceCoeffAt Q k = 0 := by
        by_cases hk0 : 0 ≤ k
        · exact sourceCoeffAt_eq_zero_of_gt_deg Q hq (by omega)
        · exact sourceCoeffAt_eq_zero_of_lt_zero Q (by omega)
      have hQ'0 : sourceCoeffAt Q' k = 0 := by
        by_cases hk0 : 0 ≤ k
        · exact sourceCoeffAt_eq_zero_of_gt_deg Q' hq' (by omega)
        · exact sourceCoeffAt_eq_zero_of_lt_zero Q' (by omega)
      rw [hQ0, hQ'0, sub_self, norm_zero]
      exact hε.le
  have hQ'_coeff (k : ℤ) : ‖sourceCoeffAt Q' k‖ ≤ 1 + ε := by
    have htri := norm_add_le (sourceCoeffAt Q k) (sourceCoeffAt Q' k - sourceCoeffAt Q k)
    rw [add_sub_cancel, norm_sub_rev] at htri
    linarith [hQ_coeff k, hdiff_coeff k]
  have hcn_zero (n : ℤ) (hn : n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ)) :
      sourceAutocorrDefect P Q d n = 0 := by
    have hnorm0 : ‖sourceAutocorrDefect P Q d n‖ ≤ 0 := by
      refine (norm_sourceAutocorrDefect_le_sourcePhiUniform P Q d hp hq n hn).trans ?_
      unfold sourcePhiUniform
      apply csSup_le
      · exact ⟨circleResidual P Q 1, ⟨1, by simp, rfl⟩⟩
      · rintro y ⟨z, hz, rfl⟩
        unfold circleResidual
        rw [hQc z hz, sub_self, abs_zero]
    exact norm_le_zero_iff.mp hnorm0
  let C : ℝ := ((d : ℝ) + 1) * (2 + ε) * ε
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have hcn_bound (n : ℤ) (hn : n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ)) :
      ‖sourceAutocorrDefect P Q' d n‖ ≤ C := by
    have hdiff_cn : sourceAutocorrDefect P Q' d n =
        sourceAutocorrDefect P Q' d n - sourceAutocorrDefect P Q d n := by
      rw [hcn_zero n hn, sub_zero]
    rw [hdiff_cn]
    have hsum_eq : sourceAutocorrDefect P Q' d n - sourceAutocorrDefect P Q d n =
        ∑ m ∈ Finset.range (d + 1),
          ((sourceCoeffAt Q' (n + m) - sourceCoeffAt Q (n + m)) * star (sourceCoeffAt Q' m) +
           sourceCoeffAt Q (n + m) * star (sourceCoeffAt Q' m - sourceCoeffAt Q m)) := by
      unfold sourceAutocorrDefect
      rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _
      rw [star_sub]
      ring
    rw [hsum_eq]
    calc
      ‖∑ m ∈ Finset.range (d + 1),
          ((sourceCoeffAt Q' (n + m) - sourceCoeffAt Q (n + m)) * star (sourceCoeffAt Q' m) +
           sourceCoeffAt Q (n + m) * star (sourceCoeffAt Q' m - sourceCoeffAt Q m))‖
        ≤ ∑ m ∈ Finset.range (d + 1),
            ‖(sourceCoeffAt Q' (n + m) - sourceCoeffAt Q (n + m)) * star (sourceCoeffAt Q' m) +
             sourceCoeffAt Q (n + m) * star (sourceCoeffAt Q' m - sourceCoeffAt Q m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.range (d + 1), ((2 + ε) * ε) := by
          apply Finset.sum_le_sum
          intro m _
          have h1 : ‖(sourceCoeffAt Q' (n + m) - sourceCoeffAt Q (n + m)) * star (sourceCoeffAt Q' m)‖ ≤
              ε * (1 + ε) := by
            rw [norm_mul, norm_star, norm_sub_rev]
            exact mul_le_mul (hdiff_coeff (n + m)) (hQ'_coeff m) (by positivity) (by positivity)
          have h2 : ‖sourceCoeffAt Q (n + m) * star (sourceCoeffAt Q' m - sourceCoeffAt Q m)‖ ≤
              1 * ε := by
            rw [norm_mul, norm_star, norm_sub_rev]
            exact mul_le_mul (hQ_coeff (n + m)) (hdiff_coeff m) (by positivity) (by positivity)
          have h3 := (norm_add_le _ _).trans (add_le_add h1 h2)
          linarith
      _ = C := by
          dsimp [C]
          simp [Nat.cast_add, Nat.cast_one]
          ring
  unfold sourcePhiTilde
  have hsum_sq : ∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q' d n‖ ^ 2 ≤
      ((2 : ℝ) * d + 1) * C ^ 2 := by
    calc
      ∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q' d n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), C ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          exact pow_le_pow_left₀ (norm_nonneg _) (hcn_bound n hn) 2
      _ = ((2 : ℝ) * d + 1) * C ^ 2 := by
          rw [Finset.sum_const, card_Icc_neg_pos, nsmul_eq_mul]
          push_cast
          ring
  have hle_sqrt : Real.sqrt (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q' d n‖ ^ 2) ≤
      Real.sqrt ((2 : ℝ) * d + 1) * C := by
    calc
      Real.sqrt (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q' d n‖ ^ 2)
        ≤ Real.sqrt (((2 : ℝ) * d + 1) * C ^ 2) :=
          Real.sqrt_le_sqrt hsum_sq
      _ = Real.sqrt ((2 : ℝ) * d + 1) * C := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC_nonneg]
  have hsqrt_le : Real.sqrt ((2 : ℝ) * d + 1) ≤ 2 * (d : ℝ) + 1 := by
    have hle : (2 : ℝ) * d + 1 ≤ (2 * (d : ℝ) + 1) ^ 2 := by nlinarith
    exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq (by positivity))
  have hC_lt : C < 3 * ((d : ℝ) + 1) * ε := by
    dsimp [C]
    have h2e : 2 + ε < 3 := by linarith
    have hstep1 := mul_lt_mul_of_pos_left h2e (by linarith : (0 : ℝ) < (d : ℝ) + 1)
    have hstep2 := mul_lt_mul_of_pos_right hstep1 hε
    linarith
  have hle2 : Real.sqrt ((2 : ℝ) * d + 1) * C ≤ (2 * (d : ℝ) + 1) * C :=
    mul_le_mul_of_nonneg_right hsqrt_le hC_nonneg
  have hlt2 : (2 * (d : ℝ) + 1) * C < 3 * ((d : ℝ) + 1) * (2 * (d : ℝ) + 1) * ε := by
    have hstep := mul_lt_mul_of_pos_left hC_lt (by linarith : (0 : ℝ) < 2 * (d : ℝ) + 1)
    linarith
  exact hle_sqrt.trans_lt (hle2.trans_lt hlt2)

/-- Establishes the coefficient error bounds for the uniform and autocorrelation complementarity
loss metrics specified by `Corollary31MetricBounds`. -/
theorem corollary31MetricBounds : Corollary31MetricBounds := corollary_3_1_metric_bounds

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
