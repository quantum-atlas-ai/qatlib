/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.EmpiricalWeight
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskActualAccessLedgerFiniteQuan

/-!
# Empirical preparation and quantum risk estimates

This module connects empirical loss tables to ideal and numerical quantum preparations. It
identifies ideal Born probabilities with empirical frequencies, bounds numerical preparation
bias by `64 * n / 2 ^ bits`, and combines sampling and estimation errors for CDF, VaR, and
conditional-risk quantities in the framework of [WoernerEgger2019].

The module also defines the sampling-based `empiricalCVaRProgram` and records the forward,
inverse, and comparison costs of its amplitude-estimation preparation source. Probability bounds
distinguish empirical sampling error, numerical preparation error, and repeated-estimation
failure.

## Main statements

* `empirical_actual_preparation_cdf_bias`: unitarity and the numerical CDF bias bound.
* `empirical_uniform_cdf_sampling_bound`: a simultaneous sampling bound for a finite threshold
  list.
* `empirical_same_sample_adaptive_var`: a population-CDF bracket for the same-sample VaR
  program.
* `empirical_tail_ratio_stability` and `empiricalCVaR_target_error`: conditional-risk ratio and
  program error bounds.
* `empirical_ae_source_ledger`: exact source-gate and table-comparison counts.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.RiskEstimation.CDFEstimation Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal
set_option warningAsError false

/-- The rational fraction of the sampled losses at most the threshold `t`. -/
def empiricalCDF {n N : ℕ} (ω : Fin N→Option (Fin n)) (loss : Option (Fin n)→ℚ) (t : ℚ) : ℚ :=
  (((List.ofFn ω).filter (fun a => loss a≤t)).length:ℚ)/N

/-- The probability, under `p`, that the rational loss is at most `t`. -/
noncomputable def populationCDF {n : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n)→ℚ) (t : ℚ) : ℝ :=
  ∑ a,p.prob a*(if loss a≤t then 1 else 0)

/-- The count-weighted sum of a predicate's indicator equals the length of the list filtered by
that predicate. -/
theorem empirical_indicator_sum {α : Type} [Fintype α] [BEq α] [LawfulBEq α]
    (xs : List α) (P : α → Prop) [DecidablePred P] :
    (∑ a, (xs.count a : ℚ) * (if P a then 1 else 0)) = (xs.filter P).length := by
  classical
  rw [empirical_count_sum]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : P a <;> simp [h, ih, add_comm]

/-- The empirical CDF equals the sample average of the threshold-indicator payoff. -/
theorem empiricalCDF_avg {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) :
    (empiricalCDF ω loss t : ℝ) = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (riskCDFPayoff loss t) ω := by
  unfold empiricalCDF Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg riskCDFPayoff
  have hf : ((List.ofFn ω).filter (fun a => loss a ≤ t)).length =
      ((List.ofFn ω).map (fun a => if loss a ≤ t then (1 : ℝ) else 0)).sum := by
    have hlist (xs : List (Option (Fin n))) : (xs.filter (fun a => loss a ≤ t)).length =
        (xs.map (fun a => if loss a ≤ t then (1 : ℝ) else 0)).sum := by
      induction xs with
      | nil => simp
      | cons a xs ih => by_cases h : loss a ≤ t <;> simp [h, ih, add_comm]
    exact hlist _
  push_cast
  rw [hf, List.map_ofFn, List.sum_ofFn]
  rfl

/-- For a nonempty sample, ideal preparation assigns Born probability equal to each outcome's
empirical frequency. -/
theorem empirical_ideal_born {n N : ℕ} (ω : Fin N → Option (Fin n)) (hN : 0 < N)
    (a : Option (Fin n)) :
    BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none) a =
      (empiricalWeight ω a / N : ℚ) := by
  have hw := empiricalWeight_nonneg ω
  have hm := (empirical_native_weights_and_work n N 0 ω).2.1
  have hZ : 0 < rationalWeightMass (empiricalWeight ω) := by rw [hm]; exact_mod_cast hN
  rw [(rational_weight_ideal_preparation_exact n _ hw hZ).2.1]
  simp only [BornProb, rationalWeightTarget, hm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt]
  exact_mod_cast div_nonneg (hw a) (Nat.cast_nonneg N : (0 : ℚ) ≤ N)

/-- For a nonempty sample, the risk CDF of ideal empirical preparation equals the empirical CDF. -/
theorem empirical_ideal_cdf {n N : ℕ} (ω : Fin N → Option (Fin n)) (hN : 0 < N)
    (loss : Option (Fin n) → ℚ) (t : ℚ) :
    riskCDF (idealWeightPrepare (empiricalWeight ω)) none loss t = (empiricalCDF ω loss t : ℝ) := by
  rw [riskCDF_eq]
  simp only [empirical_ideal_born ω hN, riskCDFPayoff]
  have h := empirical_indicator_sum (List.ofFn ω) (fun a => loss a ≤ t)
  simp only [empiricalCDF]
  rw [← h]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : loss a ≤ t <;> simp [ha, empiricalWeight]

/-- For normalized states and a payoff in `[0, 1]`, the difference of Born-weighted expectations
is at most twice the Euclidean distance between the states. -/
theorem empirical_payoff_l2_error {I : Type} [Fintype I] [DecidableEq I]
    (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ)
    (f : I → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    |(∑ i, BornProb ψ i*f i) - ∑ i, BornProb φ i*f i| ≤
      2*‖toEuclidean_fromVec (ψ-φ)‖ := by
  have hentry i : |BornProb ψ i-BornProb φ i| ≤
      (‖ψ i‖+‖φ i‖)*‖ψ i-φ i‖ := by
    simp only [BornProb]
    have he : ‖ψ i‖^2-‖φ i‖^2 = (‖ψ i‖+‖φ i‖)*(‖ψ i‖-‖φ i‖) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by positivity)
  have hcs (χ : QState I) :
      (∑ i, ‖χ i‖*‖ψ i-φ i‖) ≤
        ‖toEuclidean_fromVec χ‖*‖toEuclidean_fromVec (ψ-φ)‖ := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖χ i‖) (fun i => ‖ψ i-φ i‖)
    have hδ : (∑ i, ‖ψ i-φ i‖^2) = ‖toEuclidean_fromVec (ψ-φ)‖^2 := by
      simpa only [Pi.sub_apply] using! (norm_toEuclidean_fromVec_sq (ψ-φ)).symm
    rw [← norm_toEuclidean_fromVec_sq χ, hδ, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)] at h
    exact h
  calc
    _ = |∑ i, (BornProb ψ i-BornProb φ i)*f i| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |(BornProb ψ i-BornProb φ i)*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (‖ψ i‖+‖φ i‖)*‖ψ i-φ i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hf i).1]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hf i).2).trans (hentry i)
    _ = (∑ i, ‖ψ i‖*‖ψ i-φ i‖) + (∑ i, ‖φ i‖*‖ψ i-φ i‖) := by
      simp only [add_mul, Finset.sum_add_distrib]
    _ ≤ 2*‖toEuclidean_fromVec (ψ-φ)‖ := by
      have h1 := hcs ψ
      have h2 := hcs φ
      rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ] at h1
      rw [(normalized_iff_norm_toEuclidean_fromVec φ).mp hφ] at h2
      linarith

/-- For a nonempty sample and a payoff in `[0, 1]`, numerical empirical preparation changes its
expectation from the ideal preparation by at most `64 * n / 2 ^ bits`. This bounds
preparation bias in the expectation construction of [Woerner and Egger, Section
II][WoernerEgger2019]. -/
theorem empirical_prepare_payoff_bias {n N : ℕ} (ω : Fin N → Option (Fin n)) (bits : ℕ)
    (hN : 0 < N) (f : Option (Fin n) → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    |(∑ a, BornProb (empiricalPrepare ω bits *ᵥ Ket none) a * f a) -
      ∑ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none) a * f a| ≤
      64*(n : ℝ)/2^bits := by
  have hw := empiricalWeight_nonneg ω
  have hn := rational_weight_numerical_word_unitary_and_error n bits _ hw
  have hZ : 0 < rationalWeightMass (empiricalWeight ω) := by
    rw [(empirical_native_weights_and_work n N bits ω).2.1]
    exact_mod_cast hN
  have hi := rational_weight_ideal_preparation_exact n _ hw hZ
  have hb := empirical_payoff_l2_error
    (empiricalPrepare ω bits *ᵥ Ket none)
    (idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none)
    (normalized_applyGate hn.2.1 (normalized_ket none))
    (normalized_applyGate hi.1 (normalized_ket none)) f hf
  have hop : ‖toEuclidean_fromVec
      (empiricalPrepare ω bits *ᵥ Ket none - idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none)‖ ≤
      ‖empiricalPrepare ω bits-idealWeightPrepare (empiricalWeight ω)‖ := by
    rw [← Matrix.sub_mulVec]
    change ‖toEuclidean_fromVec (ApplyGate
      (empiricalPrepare ω bits-idealWeightPrepare (empiricalWeight ω)) (Ket none))‖ ≤ _
    rw [← toEuclideanCLM_applyGate]
    have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Option (Fin n)) (Option (Fin n)) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Option (Fin n)) →L[ℂ] EuclideanSpace ℂ (Option (Fin n))))
      (empiricalPrepare ω bits-idealWeightPrepare (empiricalWeight ω))).le_opNorm
      (toEuclidean_fromVec (Ket none))
    simpa only [(normalized_iff_norm_toEuclidean_fromVec (Ket none)).mp (normalized_ket none),
      mul_one, Matrix.l2_opNorm_def] using! h
  have he : ‖empiricalPrepare ω bits-idealWeightPrepare (empiricalWeight ω)‖ ≤
      32*(n : ℝ)/2^bits := hn.2.2
  calc
    _ ≤ 2*‖toEuclidean_fromVec
      (empiricalPrepare ω bits *ᵥ Ket none - idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none)‖ := hb
    _ ≤ 2*‖empiricalPrepare ω bits-idealWeightPrepare (empiricalWeight ω)‖ := by linarith
    _ ≤ 2*(32*(n : ℝ)/2^bits) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

/-- For a nonempty sample, empirical preparation is unitary and its risk CDF differs from the
empirical CDF by at most `64 * n / 2 ^ bits`. This supplies a numerical preparation bound
for the CDF construction in [WoernerEgger2019]. -/
theorem empirical_actual_preparation_cdf_bias :
    ∀ (n N bits : ℕ) (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℚ) (t : ℚ),
      0 < N → empiricalPrepare ω bits ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ ∧
      |riskCDF (empiricalPrepare ω bits) none loss t-(empiricalCDF ω loss t : ℝ)| ≤
        64*(n : ℝ)/2^bits := by
  intro n N bits ω loss t hN
  refine ⟨(rational_weight_numerical_word_unitary_and_error n bits _ (empiricalWeight_nonneg ω)).2.1, ?_⟩
  rw [← empirical_ideal_cdf ω hN loss t, riskCDF_eq, riskCDF_eq]
  exact empirical_prepare_payoff_bias ω bits hN (riskCDFPayoff loss t) (riskCDFPayoff_bounds loss t)

/-- The variance of the loss-threshold indicator is at most one quarter. -/
theorem empirical_indicator_variance {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) :
    p.variance (riskCDFPayoff loss t) ≤ 1/4 := by
  let f := riskCDFPayoff loss t
  let μ := p.expect f
  have hsq a : (f a)^2 = f a := by
    dsimp [f, riskCDFPayoff]
    split_ifs <;> norm_num
  have he a : p.prob a*(f a-μ)^2 =
      p.prob a*f a-(2*μ)*(p.prob a*f a)+μ^2*p.prob a := by
    calc
      _ = p.prob a*(f a)^2-(2*μ)*(p.prob a*f a)+μ^2*p.prob a := by ring
      _ = _ := by rw [hsq a]
  have hv : p.variance f = μ-μ^2 := by
    change (∑ a, p.prob a*(f a-μ)^2) = _
    simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, p.sum_one]
    change μ-(2*μ)*μ+μ^2*1=μ-μ^2
    ring
  rw [hv]
  nlinarith [sq_nonneg (μ-1/2)]

/-- For positive sample size and tolerance `ν`, the probability of empirical CDF error exceeding
`ν` is at most `1 / (4 * N * ν ^ 2)`. -/
theorem empirical_cdf_sampling_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (ν : ℝ) (hN : 0 < N) (hν : 0 < ν) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent p (fun ω : Fin N → Option (Fin n) =>
      ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|) ≤
      1/(4*(N : ℝ)*ν^2) := by
  have h := p.chebyshev_avg (riskCDFPayoff loss t) hN ν hν
  simp only [← empiricalCDF_avg, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect,
      riskCDFPayoff] at h
  apply h.trans
  have hd : 0 < (N : ℝ)*ν^2 := mul_pos (by exact_mod_cast hN) (sq_pos_of_pos hν)
  calc
    _ ≤ (1/4 : ℝ)/((N : ℝ)*ν^2) :=
      div_le_div_of_nonneg_right (empirical_indicator_variance p loss t) hd.le
    _ = _ := by ring

/-- For positive sample size and tolerance, the probability that any threshold in `xs` has CDF
error exceeding `ν` is at most `xs.length / (4 * N * ν ^ 2)`. -/
theorem empirical_uniform_cdf_sampling_bound :
    ∀ (n N : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
      (xs : List ℚ) (ν : ℝ), 0 < N → 0 < ν →
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|),
        (independentSampleLaw (fun _ : Fin N => p)).prob ω) ≤
        (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  intro n N p loss xs ν hN hν
  classical
  let E : Fin xs.length → (Fin N → Option (Fin n)) → Prop := fun i ω =>
    ν < |(empiricalCDF ω loss (xs.get i) : ℝ)-populationCDF p loss (xs.get i)|
  have he ω : (∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|) ↔
      ∃ i : Fin xs.length, E i ω := by
    constructor
    · rintro ⟨t, ht, hv⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ht
      exact ⟨i, hv⟩
    · rintro ⟨i, hi⟩
      exact ⟨xs.get i, List.get_mem _ _, hi⟩
  have h := p.union_bound E
  have hs : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent p (fun ω : Fin N → Option (Fin n) =>
      ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|) =
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent p (fun ω => ∃ i, E i ω) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  change Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent p (fun ω : Fin N → Option (Fin n) =>
    ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|) ≤ _
  rw [hs]
  apply h.trans
  calc
    (∑ i : Fin xs.length, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent p (E i)) ≤
      ∑ i : Fin xs.length, 1/(4*(N : ℝ)*ν^2) :=
      Finset.sum_le_sum (fun i _ => empirical_cdf_sampling_bound p loss (xs.get i) ν hN hν)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- For a nonempty sample, the ideal prepared expectation of a rational payoff equals its
empirical count-weighted average. -/
theorem empirical_ideal_payoff {n N : ℕ} (ω : Fin N → Option (Fin n)) (hN : 0 < N)
    (f : Option (Fin n) → ℚ) :
    (∑ a, BornProb (idealWeightPrepare (empiricalWeight ω) *ᵥ Ket none) a * (f a : ℝ)) =
      ((∑ a, empiricalWeight ω a*f a)/(N : ℚ) : ℚ) := by
  simp only [empirical_ideal_born ω hN]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- If numerator and denominator estimates are within `δ` of `μ` and positive `p`, with `2 * δ <
p` and `0 ≤ a ≤ φ`, their ratio differs from `μ / p` by at most `4 * δ / p`. -/
theorem empirical_ratio_error (p μ φ a δ : ℝ) (hδ : 0 ≤ δ) (hp : 0 < p)
    (hgap : 2*δ < p) (hφ : |φ-p| ≤ δ) (ha : |a-μ| ≤ δ)
    (ha0 : 0 ≤ a) (haφ : a ≤ φ) : |a/φ-μ/p| ≤ 4*δ/p := by
  have hφ0 : 0 < φ := by have h := abs_le.mp hφ; linarith
  have he : a/φ-μ/p = (a*(p-φ)+(a-μ)*φ)/(φ*p) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hφ0 hp)]
  apply (div_le_iff₀ (mul_pos hφ0 hp)).mpr
  calc
    _ ≤ |a*(p-φ)|+|(a-μ)*φ| := abs_add_le _ _
    _ = a*|φ-p|+|a-μ| * φ := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_pos hφ0, abs_sub_comm p φ]
    _ ≤ a*δ+δ*φ := add_le_add (mul_le_mul_of_nonneg_left hφ ha0)
      (mul_le_mul_of_nonneg_right ha hφ0.le)
    _ ≤ 4*δ*φ := by nlinarith
    _ = (4*δ/p)*(φ*p) := by field_simp

/-- For a nonempty sample with losses in `[0, 1]`, empirical CDF and tail-payoff errors at most
`η` imply tail-mean error at most `4 * (η + 64 * n / 2 ^ bits) / p` when twice the combined
error is below positive `p`. This controls the conditional-risk ratio used in [Woerner and
Egger, Section II][WoernerEgger2019]. -/
theorem empirical_tail_ratio_stability :
    ∀ (n N bits : ℕ) (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℚ)
      (t : ℚ) (p μ η : ℝ), 0 < N → (∀ a, 0 ≤ loss a ∧ loss a ≤ 1) →
      0 ≤ η → |(empiricalCDF ω loss t : ℝ)-p| ≤ η →
      |((∑ a, empiricalWeight ω a*riskTailPayoff loss t a)/(N : ℚ) : ℚ)-μ| ≤ η →
      0 < p → 2*(η+64*(n : ℝ)/2^bits) < p →
      |riskTailMean (empiricalPrepare ω bits) none loss t-μ/p| ≤
        4*(η+64*(n : ℝ)/2^bits)/p := by
  intro n N bits ω loss t p μ η hN hloss hη hc hm hp hgap
  let A := empiricalPrepare ω bits
  let a := ∑ i, BornProb (A *ᵥ Ket none) i*(riskTailPayoff loss t i : ℝ)
  let φ := riskCDF A none loss t
  let δ := η+64*(n : ℝ)/2^bits
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hb := (empirical_actual_preparation_cdf_bias n N bits ω loss t hN).2
  have hφ : |φ-p| ≤ δ := by
    have h := abs_sub_le φ (empiricalCDF ω loss t : ℝ) p
    have ht := h.trans (add_le_add hb hc)
    simpa only [δ, add_comm] using! ht
  have hf : ∀ i, 0 ≤ (riskTailPayoff loss t i : ℝ) ∧ (riskTailPayoff loss t i : ℝ) ≤ 1 := by
    intro i
    exact ⟨by exact_mod_cast (riskTailPayoff_bounds loss t hloss i).1,
      by exact_mod_cast (riskTailPayoff_bounds loss t hloss i).2⟩
  have hn := empirical_prepare_payoff_bias ω bits hN
    (fun i => (riskTailPayoff loss t i : ℝ)) hf
  rw [empirical_ideal_payoff ω hN] at hn
  have ha : |a-μ| ≤ δ := by
    have h := abs_sub_le a
      (((∑ i, empiricalWeight ω i*riskTailPayoff loss t i)/(N : ℚ) : ℚ) : ℝ) μ
    have ht := h.trans (add_le_add hn hm)
    simpa only [δ, add_comm] using! ht
  have hbounds := risk_tail_numerator_bounds A none loss t hloss
  rw [riskTailMean_eq]
  exact empirical_ratio_error p μ φ a δ hδ hp hgap hφ ha hbounds.1 hbounds.2

/-- For a nonempty sorted threshold list containing the loss support and the stated positive
parameters and phase-estimation accuracy, the same-sample VaR output brackets the population
CDF within `E = eps + ν + 64 * n / 2 ^ bits` except with probability at most `xs.length / (4
* N * ν ^ 2) + (Nat.clog 2 xs.length + 1) * (8 / 9) ^ r`. This quantifies the bisection
construction in [Woerner and Egger, Section II][WoernerEgger2019]. -/
theorem empirical_same_sample_adaptive_var : ∀ (n N bits M r : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n)→ℚ)
  (xs : List ℚ) (q eps ν : ℝ), 0 < N → xs≠[] → xs.SortedLE →
  (∀ a,loss a∈xs) → 0 < q → q < 1 → 0 < eps → 0 < ν →
  Real.pi/(M:ℝ)+Real.pi^2/(M:ℝ)^2≤eps → ∀ hM : 2≤M,
  ∃ hP : ∀ ω : Fin N→Option (Fin n),empiricalPrepare ω bits∈Matrix.unitaryGroup (Option (Fin n)) ℂ,
  let law := (closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind
    (fun ω => riskVaR (empiricalPrepare ω bits) none loss xs q M r (hP ω) hM)
  let E := eps+ν+64*(n:ℝ)/2^bits
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event law (fun z => z.1≥xs.length ∨ populationCDF p loss (xs.getD z.1 0) < q-E ∨
    (z.1≠0 ∧ q+E < populationCDF p loss (xs.getD (z.1-1) 0)))≤
    ENNReal.ofReal ((xs.length:ℝ)/(4*(N:ℝ)*ν^2)+(Nat.clog 2 xs.length+1)*(8/9:ℝ)^r) := by
  intro n N bits M r p loss xs q eps ν hN hxs hsorted hsupport hq0 hq1 heps hν hwindow hM
  classical
  let hP : ∀ ω : Fin N → Option (Fin n),
      empiricalPrepare ω bits ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ :=
    fun ω => (empirical_actual_preparation_cdf_bias n N bits ω loss 0 hN).1
  refine ⟨hP, ?_⟩
  (try dsimp only)
  let B : (Fin N → Option (Fin n)) → Prop := fun ω =>
    ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|
  let E : ℕ × ℕ → Prop := fun z =>
    z.1 ≥ xs.length ∨ populationCDF p loss (xs.getD z.1 0) < q-(eps+ν+64*(n : ℝ)/2^bits) ∨
      (z.1 ≠ 0 ∧ q+(eps+ν+64*(n : ℝ)/2^bits) < populationCDF p loss (xs.getD (z.1-1) 0))
  have hgood (ω : Fin N → Option (Fin n)) (hω : ¬ B ω) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskVaR (empiricalPrepare ω bits) none loss xs q M r (hP ω) hM) E ≤
      ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r) := by
    have hclose (i : ℕ) (hi : i < xs.length) :
        |riskCDF (empiricalPrepare ω bits) none loss (xs.getD i 0) -
          populationCDF p loss (xs.getD i 0)| ≤ ν+64*(n : ℝ)/2^bits := by
      have hm : xs.getD i 0 ∈ xs := by
        rw [List.getD_eq_getElem xs 0 hi]
        exact List.getElem_mem hi
      have hs : |(empiricalCDF ω loss (xs.getD i 0) : ℝ)-
          populationCDF p loss (xs.getD i 0)| ≤ ν := by
        by_contra h
        apply hω
        exact ⟨xs.getD i 0, hm, lt_of_not_ge h⟩
      have hb := (empirical_actual_preparation_cdf_bias n N bits ω loss (xs.getD i 0) hN).2
      have ht := abs_sub_le (riskCDF (empiricalPrepare ω bits) none loss (xs.getD i 0))
        (empiricalCDF ω loss (xs.getD i 0) : ℝ) (populationCDF p loss (xs.getD i 0))
      linarith
    apply (risk_event_mono _ (fun z hz => ?_)).trans
      (riskVaRAlgorithmFinite (Option (Fin n)) (empiricalPrepare ω bits) none loss xs q eps M r
        (hP ω) hM hxs hsorted hsupport hq0 hq1 heps hwindow)
    change E z at hz
    rcases hz with hlen | hlow | ⟨hne, hhigh⟩
    · exact Or.inl hlen
    · by_cases hi : z.1 < xs.length
      · right; left
        have hh := abs_le.mp (hclose z.1 hi)
        linarith
      · exact Or.inl (by omega)
    · by_cases hi : z.1 < xs.length
      · right; right
        refine ⟨hne, ?_⟩
        have hh := abs_le.mp (hclose (z.1-1) (by omega))
        linarith
      · exact Or.inl (by omega)
  have hb := risk_bind_failure
    (closurePMF (independentSampleLaw (fun _ : Fin N => p)))
    (fun ω => riskVaR (empiricalPrepare ω bits) none loss xs q M r (hP ω) hM)
    B E (ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r)) hgood
  apply hb.trans
  rw [risk_closure_event]
  have hs := empirical_uniform_cdf_sampling_bound n N p loss xs ν hN hν
  have hsn : 0 ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by positivity
  have han : 0 ≤ (Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r := by positivity
  rw [ENNReal.ofReal_add hsn han]
  have hs' : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p)) B ≤
      (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
    simpa only [Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass, B] using! hs
  exact add_le_add (ENNReal.ofReal_le_ofReal hs') le_rfl

/-- Numerical empirical preparation is unitary for every sample and bit precision. -/
theorem empiricalPrepare_unitary {n N : ℕ} (ω : Fin N → Option (Fin n)) (bits : ℕ) :
    empiricalPrepare ω bits ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ :=
  (rational_weight_numerical_word_unitary_and_error n bits _ (empiricalWeight_nonneg ω)).2.1

/-- The joint sampling and conditional-risk program that draws `N` independent outcomes from `p`
and runs `riskCVaR` using their empirical preparation. -/
noncomputable def empiricalCVaRProgram {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    (xs : List ℚ) (q eps : ℝ) (bits payoffBits M r : ℕ) (hM : 2 ≤ M) :
    PMF (ℕ × ℝ × ℕ) :=
  (closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind (fun ω =>
    riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
      (empiricalPrepare_unitary ω bits) hloss hM)

/-- Every supported result of `empiricalCVaRProgram` has recorded call count at most `Nat.clog 2
xs.length + 3`. -/
theorem empiricalCVaRProgram_calls {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    (xs : List ℚ) (q eps : ℝ) (bits payoffBits M r : ℕ) (hM : 2 ≤ M) :
    ∀ z ∈ (empiricalCVaRProgram (N := N) p loss hloss xs q eps bits payoffBits M r hM).support,
      z.2.2 ≤ Nat.clog 2 xs.length+3 := by
  intro z hz
  obtain ⟨ω, _, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
  exact riskCVaR_support_calls (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
    (empiricalPrepare_unitary ω bits) hloss hM z hz

/-- For positive `M`, the empirical preparation source ledger has `M * n` forward gates, `(M -
1) * n` inverse gates, and `2 * n * bits` table comparisons. -/
theorem empirical_ae_source_ledger {n N : ℕ} (ω : Fin N → Option (Fin n)) (bits M : ℕ)
    (hM : 0 < M) :
    aeForwardAccesses (aeAccessWord (I := Option (Fin n) × Bool) M) *
      adjointGateCount (rationalWeightWord (empiricalWeight ω) bits) = M*n ∧
    aeBackwardAccesses (aeAccessWord (I := Option (Fin n) × Bool) M) *
      adjointGateCount (adjointCircuit (rationalWeightWord (empiricalWeight ω) bits)) = (M-1)*n ∧
    rationalWeightComparisons (empiricalWeight ω) bits = 2*n*bits := by
  have h := prepared_ae_separate_access_counts (I := Option (Fin n) × Bool) M hM
  have hw := empirical_native_weights_and_work n N bits ω
  simp only [h.1, h.2.1, adjointGateCount_adjointCircuit, hw.2.2.2, hw.2.2.1]
  exact ⟨trivial, trivial, trivial⟩

/-- Under the threshold-separation, accuracy, bounded-loss, and positive-denominator hypotheses,
the probability of a wrong threshold index or error from `μ / p` exceeding `4 * eps /
riskCDF + 4 * (η + 64 * n / 2 ^ bits) / p` is at most `(Nat.clog 2 xs.length + 3) * (8 / 9)
^ r`. This combines preparation and estimation errors for conditional risk as in
[WoernerEgger2019]. -/
theorem empiricalCVaR_target_error {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (p μ η eps : ℝ) (xs : List ℚ) (q : ℝ)
    (bits payoffBits M r v : ℕ) (hN : 0 < N) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    (hM : 2 ≤ M) (hxs : xs ≠ []) (hsorted : xs.SortedLE) (hsupport : ∀ a, loss a ∈ xs)
    (hq0 : 0 < q) (hq1 : q < 1) (heps : 0 < eps) (hv : v < xs.length)
    (ht : xs.getD v 0 = t)
    (hwindow : Real.pi/M+Real.pi^2/(M : ℝ)^2+64/(2 : ℝ)^payoffBits ≤ eps)
    (habove : q+eps < riskCDF (empiricalPrepare ω bits) none loss t)
    (hbelow : ∀ u : ℕ, u < v → riskCDF (empiricalPrepare ω bits) none loss (xs.getD u 0) < q-eps)
    (hden : 2*eps < riskCDF (empiricalPrepare ω bits) none loss t)
    (hη : 0 ≤ η) (hc : |(empiricalCDF ω loss t : ℝ)-p| ≤ η)
    (hm : |((∑ a, empiricalWeight ω a*riskTailPayoff loss t a)/(N : ℚ) : ℚ)-μ| ≤ η)
    (hp : 0 < p) (hgap : 2*(η+64*(n : ℝ)/2^bits) < p) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskCVaR (empiricalPrepare ω bits) none loss xs q eps payoffBits M r
      (empiricalPrepare_unitary ω bits) hloss hM)
      (fun z => z.1 ≠ v ∨
        4*eps/riskCDF (empiricalPrepare ω bits) none loss t+
          4*(η+64*(n : ℝ)/2^bits)/p < |z.2.1-μ/p|) ≤
      ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r) := by
  have hbase := riskCVaRAlgorithmFinite (Option (Fin n)) (empiricalPrepare ω bits) none loss xs q eps
    payoffBits M r v (empiricalPrepare_unitary ω bits) hloss hM hxs hsorted hsupport hq0 hq1 heps hv
    hwindow (by simpa only [ht] using! habove) hbelow (by simpa only [ht] using! hden)
  have htail := empirical_tail_ratio_stability n N bits ω loss t p μ η hN hloss hη hc hm hp hgap
  apply (risk_event_mono _ (fun z hz => ?_)).trans hbase
  rcases hz with hbad | herr
  · exact Or.inl hbad
  · right
    rw [ht]
    have htri := abs_sub_le z.2.1 (riskTailMean (empiricalPrepare ω bits) none loss t) (μ/p)
    linarith

end Qatlib.Concepts.NativeNumerics.EmpiricalRisk
