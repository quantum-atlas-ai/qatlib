/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.BoundaryCanon.MetricLossEquivalenceStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Complex Polynomial MeasureTheory Filter
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator Polynomial Topology

/-- At a natural index, the extended coefficient equals the ordinary polynomial coefficient. -/
@[simp]
theorem sourceCoeffAt_natCast (A : Polynomial ℂ) (m : ℕ) :
    sourceCoeffAt A (m : ℤ) = A.coeff m := by
  simp [sourceCoeffAt]

/-- Extended polynomial coefficients vanish at negative integer indices. -/
theorem sourceCoeffAt_eq_zero_of_lt_zero (A : Polynomial ℂ) {k : ℤ} (hk : k < 0) :
    sourceCoeffAt A k = 0 := by
  unfold sourceCoeffAt
  rw [ite_eq_right (not_le.mpr hk)]

/-- Extended polynomial coefficients vanish above the given degree bound. -/
theorem sourceCoeffAt_eq_zero_of_gt_deg (A : Polynomial ℂ) {d : ℕ}
    (hA : A.natDegree ≤ d) {k : ℤ} (hk : (d : ℤ) < k) :
    sourceCoeffAt A k = 0 := by
  by_cases hk0 : 0 ≤ k
  · unfold sourceCoeffAt
    rw [ite_eq_left hk0]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  · unfold sourceCoeffAt
    rw [ite_eq_right hk0]

/-- Expresses an extended coefficient as a finite sum selecting its matching natural index. -/
private theorem sourceCoeffAt_eq_sum_ite (A : Polynomial ℂ) (d : ℕ)
    (hA : A.natDegree ≤ d) (j : ℤ) :
    sourceCoeffAt A j =
      ∑ k ∈ Finset.range (d + 1), if ((k : ℕ) : ℤ) = j then A.coeff k else 0 := by
  by_cases hj : 0 ≤ j ∧ j ≤ d
  · have hmem : j.toNat ∈ Finset.range (d + 1) := by
      rw [Finset.mem_range]; omega
    have heq : ∀ k ∈ Finset.range (d + 1),
        (if ((k : ℕ) : ℤ) = j then A.coeff k else 0) =
          if k = j.toNat then A.coeff k else 0 := by
      intro k _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq']
    simp [sourceCoeffAt, hj.1, hmem]
  · rw [Finset.sum_eq_zero]
    · by_cases hj0 : 0 ≤ j
      · exact sourceCoeffAt_eq_zero_of_gt_deg A hA (by omega)
      · exact sourceCoeffAt_eq_zero_of_lt_zero A (by omega)
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [ite_eq_right (by omega)]

/-- The Laurent polynomial of coefficient autocorrelations equals the squared evaluation norm on
the unit circle. -/
private theorem single_poly_autocorr_laurent (A : Polynomial ℂ) (d : ℕ)
    (hA : A.natDegree ≤ d) (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ),
        (∑ m ∈ Finset.range (d + 1),
          sourceCoeffAt A (n + (m : ℤ)) * star (sourceCoeffAt A (m : ℤ))) * z ^ n) =
      ((‖A.eval z‖ ^ 2 : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hinv : z⁻¹ = star z := Complex.inv_eq_conj hz
  have hinner (n : ℤ) :
      (∑ m ∈ Finset.range (d + 1),
          sourceCoeffAt A (n + (m : ℤ)) * star (sourceCoeffAt A (m : ℤ))) * z ^ n =
        ∑ m ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (d + 1),
          if (k : ℤ) - (m : ℤ) = n then A.coeff k * star (A.coeff m) * z ^ n else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [sourceCoeffAt_eq_sum_ite A d hA (n + (m : ℤ)), sourceCoeffAt_natCast,
      Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    have hiff : ((k : ℤ) = n + (m : ℤ)) ↔ ((k : ℤ) - (m : ℤ) = n) := by omega
    simp [hiff, ite_mul]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun m _ => Finset.sum_comm))
  have hcollapse :
      (∑ m ∈ Finset.range (d + 1), ∑ k ∈ Finset.range (d + 1),
        ∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ),
          if (k : ℤ) - (m : ℤ) = n then A.coeff k * star (A.coeff m) * z ^ n else 0) =
      (∑ k ∈ Finset.range (d + 1), A.coeff k * z ^ k) *
        star (∑ m ∈ Finset.range (d + 1), A.coeff m * z ^ m) := by
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hm hk
    have hmem : (k : ℤ) - (m : ℤ) ∈ Finset.Icc (-(d : ℤ)) (d : ℤ) := by
      rw [Finset.mem_Icc]; omega
    simp only [Finset.sum_ite_eq, hmem, ite_true]
    rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, div_eq_mul_inv,
      ← inv_pow, hinv, star_mul, star_pow]
    ring
  rw [hcollapse, ← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hA),
    Complex.star_def, Complex.mul_conj']
  norm_cast

/-- The Laurent sum of the autocorrelation defect equals the sum of squared polynomial
evaluation norms minus one on the unit circle. -/
theorem sourceAutocorrDefect_laurent_circle (P Q : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hq : Q.natDegree ≤ d) (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), sourceAutocorrDefect P Q d n * z ^ n) =
      ((‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 - 1 : ℝ) : ℂ) := by
  have hsplit (n : ℤ) :
      sourceAutocorrDefect P Q d n * z ^ n =
        ((∑ m ∈ Finset.range (d + 1),
            sourceCoeffAt P (n + (m : ℤ)) * star (sourceCoeffAt P (m : ℤ))) * z ^ n +
          (∑ m ∈ Finset.range (d + 1),
            sourceCoeffAt Q (n + (m : ℤ)) * star (sourceCoeffAt Q (m : ℤ))) * z ^ n) -
        (if n = 0 then (1 : ℂ) * z ^ n else 0) := by
    unfold sourceAutocorrDefect
    rw [Finset.sum_add_distrib]
    split_ifs <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    single_poly_autocorr_laurent P d hp z hz,
    single_poly_autocorr_laurent Q d hq z hz]
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(d : ℤ)) (d : ℤ) := by
    rw [Finset.mem_Icc]; omega
  simp [Finset.sum_ite_eq', h0]

/-- The circle residual is a continuous function. -/
private theorem continuous_circleResidual (P Q : Polynomial ℂ) :
    Continuous (circleResidual P Q) := by
  unfold circleResidual
  fun_prop

/-- The complex unit circle equals the sphere centered at zero with radius one. -/
private theorem unitCircle_eq_sphere :
    {z : ℂ | ‖z‖ = 1} = Metric.sphere (0 : ℂ) 1 := by
  ext z
  simp

/-- The uniform complementarity loss is attained at a point of the unit circle. -/
theorem sourcePhiUniform_attained (P Q : Polynomial ℂ) :
    ∃ z₀ : ℂ, ‖z₀‖ = 1 ∧ circleResidual P Q z₀ = sourcePhiUniform P Q := by
  unfold sourcePhiUniform
  have hcomp : IsCompact (circleResidual P Q '' {z : ℂ | ‖z‖ = 1}) := by
    rw [unitCircle_eq_sphere]
    exact (isCompact_sphere (0 : ℂ) 1).image (continuous_circleResidual P Q)
  have hne : (circleResidual P Q '' {z : ℂ | ‖z‖ = 1}).Nonempty :=
    ⟨circleResidual P Q 1, 1, by simp, rfl⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hcomp.sSup_mem hne
  exact ⟨z₀, hz₀, hmax⟩

/-- The circle residual at any unit circle point is bounded by the uniform complementarity loss. -/
theorem circleResidual_le_sourcePhiUniform (P Q : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    circleResidual P Q z ≤ sourcePhiUniform P Q := by
  unfold sourcePhiUniform
  have hcomp : IsCompact (circleResidual P Q '' {z : ℂ | ‖z‖ = 1}) := by
    rw [unitCircle_eq_sphere]
    exact (isCompact_sphere (0 : ℂ) 1).image (continuous_circleResidual P Q)
  exact le_csSup hcomp.bddAbove ⟨z, hz, rfl⟩

/-- The uniform complementarity loss is nonnegative. -/
theorem sourcePhiUniform_nonneg (P Q : Polynomial ℂ) :
    0 ≤ sourcePhiUniform P Q := by
  have h1 : 0 ≤ circleResidual P Q 1 := by unfold circleResidual; positivity
  exact h1.trans (circleResidual_le_sourcePhiUniform P Q 1 (by simp))

/-- The integer interval from minus `d` to `d` has cardinality `2*d+1`. -/
theorem card_Icc_neg_pos (d : ℕ) :
    (Finset.Icc (-(d : ℤ)) (d : ℤ)).card = 2 * d + 1 := by
  rw [Int.card_Icc]
  omega

/-- The sum of integer powers of a primitive root over its period is the period when it divides
the exponent, and zero otherwise. -/
private theorem root_orthogonality_int (N : ℕ) (k : ℤ)
    (ω : ℂ) (hω : IsPrimitiveRoot ω N) :
    (∑ j : Fin N, ω ^ (k * (j.val : ℤ))) = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hpower (j : ℕ) : ω ^ (k * (j : ℤ)) = (ω ^ k) ^ j := by
    rw [← zpow_natCast (ω ^ k), ← zpow_mul]
  simp_rw [hpower]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (ω ^ k) ^ j) N]
  by_cases hk : (N : ℤ) ∣ k
  · rw [(hω.zpow_eq_one_iff_dvd k).mpr hk]
    simp [hk]
  · rw [ite_eq_right hk, geom_sum_eq]
    · have he : (ω ^ k) ^ N = 1 := by
        rw [← zpow_natCast (ω ^ k), ← zpow_mul, mul_comm, zpow_mul, hω.zpow_eq_one]
        simp
      rw [he, sub_self, zero_div]
    · exact fun he => hk ((hω.zpow_eq_one_iff_dvd k).mp he)

/-- Each autocorrelation defect coefficient in the degree range has norm at most the uniform
complementarity loss. -/
theorem norm_sourceAutocorrDefect_le_sourcePhiUniform (P Q : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hq : Q.natDegree ≤ d)
    (n : ℤ) (hn : n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ)) :
    ‖sourceAutocorrDefect P Q d n‖ ≤ sourcePhiUniform P Q := by
  let N : ℕ := 2 * d + 1
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hω_norm : ‖ω‖ = 1 := by
    have heq : 2 * Real.pi * Complex.I / (N : ℂ) = ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [show ω = Complex.exp (((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * Complex.I) from
      congrArg Complex.exp heq]
    exact Complex.norm_exp_ofReal_mul_I _
  have hω_pow_norm (j : ℕ) : ‖ω ^ j‖ = 1 := by rw [norm_pow, hω_norm, one_pow]
  have hω_zpow_norm (m : ℤ) : ‖ω ^ m‖ = 1 := by rw [norm_zpow, hω_norm, one_zpow]
  have hω0 : ω ≠ 0 := norm_ne_zero_iff.mp (by rw [hω_norm]; norm_num)
  have hdft :
      (∑ j : Fin N,
          ((‖P.eval (ω ^ j.val)‖ ^ 2 + ‖Q.eval (ω ^ j.val)‖ ^ 2 - 1 : ℝ) : ℂ) *
            ω ^ (-(n * (j.val : ℤ)))) =
        sourceAutocorrDefect P Q d n * (N : ℂ) := by
    have hterm (j : Fin N) :
        ((‖P.eval (ω ^ j.val)‖ ^ 2 + ‖Q.eval (ω ^ j.val)‖ ^ 2 - 1 : ℝ) : ℂ) *
            ω ^ (-(n * (j.val : ℤ))) =
          ∑ k ∈ Finset.Icc (-(d : ℤ)) (d : ℤ),
            sourceAutocorrDefect P Q d k * ω ^ ((k - n) * (j.val : ℤ)) := by
      rw [← sourceAutocorrDefect_laurent_circle P Q d hp hq (ω ^ j.val) (hω_pow_norm j.val),
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc]
      congr 1
      rw [← zpow_natCast ω j.val, ← zpow_mul, ← zpow_add₀ hω0]
      congr 1
      ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hinner (k : ℤ) (hk : k ∈ Finset.Icc (-(d : ℤ)) (d : ℤ)) :
        (∑ j : Fin N, sourceAutocorrDefect P Q d k * ω ^ ((k - n) * (j.val : ℤ))) =
          if k = n then sourceAutocorrDefect P Q d k * (N : ℂ) else 0 := by
      rw [← Finset.mul_sum, root_orthogonality_int N (k - n) ω hω]
      rw [Finset.mem_Icc] at hk hn
      have hdvd : ((N : ℤ) ∣ (k - n)) ↔ k = n := by
        constructor
        · rintro ⟨q, hq_eq⟩
          have hN_def : (N : ℤ) = 2 * (d : ℤ) + 1 := by omega
          rw [hN_def] at hq_eq
          have hq0 : q = 0 := by nlinarith [hk.1, hk.2, hn.1, hn.2, hq_eq]
          rw [hq0, mul_zero] at hq_eq
          omega
        · rintro rfl
          simp
      simp [hdvd, mul_ite]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
    simp [hn]
  have hnorm_sum :
      ‖sourceAutocorrDefect P Q d n‖ * (N : ℝ) ≤ (N : ℝ) * sourcePhiUniform P Q := by
    calc
      ‖sourceAutocorrDefect P Q d n‖ * (N : ℝ)
        = ‖sourceAutocorrDefect P Q d n * (N : ℂ)‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ j : Fin N,
            ((‖P.eval (ω ^ j.val)‖ ^ 2 + ‖Q.eval (ω ^ j.val)‖ ^ 2 - 1 : ℝ) : ℂ) *
              ω ^ (-(n * (j.val : ℤ)))‖ := by rw [← hdft]
      _ ≤ ∑ j : Fin N,
            ‖((‖P.eval (ω ^ j.val)‖ ^ 2 + ‖Q.eval (ω ^ j.val)‖ ^ 2 - 1 : ℝ) : ℂ) *
              ω ^ (-(n * (j.val : ℤ)))‖ := norm_sum_le _ _
      _ = ∑ j : Fin N, circleResidual P Q (ω ^ j.val) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, hω_zpow_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
          rfl
      _ ≤ ∑ _j : Fin N, sourcePhiUniform P Q := by
          apply Finset.sum_le_sum
          intro j _
          exact circleResidual_le_sourcePhiUniform P Q (ω ^ j.val) (hω_pow_norm j.val)
      _ = (N : ℝ) * sourcePhiUniform P Q := by
          simp
  exact le_of_mul_le_mul_right (by linarith) hNR

/-- The uniform and autocorrelation complementarity loss metrics bound each other with factor
`Real.sqrt (2*d+1)`. -/
theorem metric_loss_equivalence (P Q : Polynomial ℂ) (d : ℕ)
    (hp : P.natDegree ≤ d) (hq : Q.natDegree ≤ d) :
    (1 / Real.sqrt (2 * (d : ℝ) + 1)) * sourcePhiUniform P Q ≤ sourcePhiTilde P Q d ∧
      sourcePhiTilde P Q d ≤ Real.sqrt (2 * (d : ℝ) + 1) * sourcePhiUniform P Q := by
  have h2d1_pos : (0 : ℝ) < 2 * (d : ℝ) + 1 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * (d : ℝ) + 1) := Real.sqrt_pos.mpr h2d1_pos
  constructor
  · obtain ⟨z₀, hz₀, hmax⟩ := sourcePhiUniform_attained P Q
    have hbound : sourcePhiUniform P Q ≤
        sourcePhiTilde P Q d * Real.sqrt (2 * (d : ℝ) + 1) := by
      calc
        sourcePhiUniform P Q = circleResidual P Q z₀ := hmax.symm
        _ = ‖((‖P.eval z₀‖ ^ 2 + ‖Q.eval z₀‖ ^ 2 - 1 : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]; rfl
        _ = ‖∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), sourceAutocorrDefect P Q d n * z₀ ^ n‖ := by
            rw [sourceAutocorrDefect_laurent_circle P Q d hp hq z₀ hz₀]
        _ ≤ ∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n * z₀ ^ n‖ :=
            norm_sum_le _ _
        _ = ∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n‖ * 1 := by
            apply Finset.sum_congr rfl
            intro n _
            rw [norm_mul, norm_zpow, hz₀, one_zpow]
        _ ≤ Real.sqrt (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n‖ ^ 2) *
              Real.sqrt (∑ _n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), (1 : ℝ) ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = sourcePhiTilde P Q d * Real.sqrt (2 * (d : ℝ) + 1) := by
            congr 2
            rw [Finset.sum_const, card_Icc_neg_pos, nsmul_eq_mul]
            push_cast
            ring
    have hdiv : sourcePhiUniform P Q / Real.sqrt (2 * (d : ℝ) + 1) ≤ sourcePhiTilde P Q d :=
      (div_le_iff₀ hsqrt_pos).mpr hbound
    linarith [show (1 / Real.sqrt (2 * (d : ℝ) + 1)) * sourcePhiUniform P Q =
      sourcePhiUniform P Q / Real.sqrt (2 * (d : ℝ) + 1) by ring]
  · unfold sourcePhiTilde
    have hsum :
        (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n‖ ^ 2) ≤
          (2 * (d : ℝ) + 1) * (sourcePhiUniform P Q) ^ 2 := by
      calc
        (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n‖ ^ 2)
          ≤ ∑ _n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), (sourcePhiUniform P Q) ^ 2 := by
            apply Finset.sum_le_sum
            intro n hn
            exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_sourceAutocorrDefect_le_sourcePhiUniform P Q d hp hq n hn) 2
        _ = (2 * (d : ℝ) + 1) * (sourcePhiUniform P Q) ^ 2 := by
            rw [Finset.sum_const, card_Icc_neg_pos, nsmul_eq_mul]
            push_cast
            ring
    calc
      Real.sqrt (∑ n ∈ Finset.Icc (-(d : ℤ)) (d : ℤ), ‖sourceAutocorrDefect P Q d n‖ ^ 2)
        ≤ Real.sqrt ((2 * (d : ℝ) + 1) * (sourcePhiUniform P Q) ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (2 * (d : ℝ) + 1) * sourcePhiUniform P Q := by
          rw [Real.sqrt_mul h2d1_pos.le, Real.sqrt_sq (sourcePhiUniform_nonneg P Q)]

/-- Establishes the uniform and autocorrelation loss comparison specified by
`MetricLossEquivalence`. -/
theorem metricLossEquivalence : MetricLossEquivalence := metric_loss_equivalence

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
