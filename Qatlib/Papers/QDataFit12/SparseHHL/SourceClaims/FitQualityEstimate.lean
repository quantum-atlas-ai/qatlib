/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims.SourceCostModel
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c001 — Algorithm 2 (Estimating Fit Quality), Eq. (14)

Fixed paper: Wiebe–Braun–Lloyd, *Quantum Data Fitting*, arXiv:1204.5242v2 (3 Jul 2012).

Source: p.4, §2 "Estimating Fit Quality".

* Eq. (14) states the query complexity `Õ(log(N) · s³κ⁴/(εδ²))`.
* Eq. (15)–(16) show that the state `I(F)A⁻¹I(F†)|y⟩` is prepared within error `O(ε)` at
  cost `Õ(log(N) s³κ⁴/ε)`, and the swap test is then sampled `O(1/δ²)` times (p.4).
* p.4: "the probability of observing an outcome of '1' is `(1 − |⟨y|I(F)|λ⟩|²)/2`".
* p.4: "`E = ||y⟩ − I(F)|λ⟩|²`" and "`E` … is also `O(δ)`".

This module states and proves the pieces of the claim that are exact mathematics:

* §1 the Eq.-(14) cost, its decomposition into (16)·`1/δ²`, and its monotonicity;
* §2 the fit error identity `E = ‖ |y⟩ − |ψ⟩ ‖² = 2 − 2·Re⟨y,ψ⟩` and its phase-aligned
  form `E = 2(1 − |⟨y,ψ⟩|)`;
* §3 the swap-test outcome-1 probability bounds `0 ≤ (1−|⟨y,ψ⟩|²)/2 ≤ 1/2`;
* §4 the Chebyshev `O(1/δ²)` sample-count bound used to estimate the mean overlap.

The end-to-end oracle program realising Eq. (14) is *not* modelled here; this is the same
residual recorded by the `SparseHHL` block.  The module contains no `sorry`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims

open Qatlib.Papers.QDataFit12.SparseHHL
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-! ## §1 The Eq.-(14) cost -/

/-- **c001 cost decomposition.**  The Eq.-(14) cost is the Eq.-(16) inversion cost
`log(N)·s³κ⁴/ε` multiplied by the `1/δ²` swap-test sampling factor. -/
theorem fitQualityCost_eq_inversion_mul_inv_delta_sq
    (N s κ : ℕ) (ε δ : ℝ) :
    fitQualityCost N s κ ε δ
      = (Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4 / ε) * (1 / δ ^ 2) := by
  unfold fitQualityCost
  ring

/-- Inversion reverses the order of positive real parameters. -/
private theorem fq_inv_mono (a b : ℝ) (ha : 0 < a) (hle : a ≤ b) (c : ℝ) (hc : 0 ≤ c) :
    c / b ≤ c / a := by
  have hinv : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hle
  have h2 : b⁻¹ ≤ a⁻¹ := by simpa [one_div] using hinv
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h2 hc

/-- The logarithm of a real number at least one is nonnegative. -/
private theorem fq_log_nonneg (N : ℕ) : 0 ≤ Real.log (N + 1) := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have h2 : (1 : ℕ) ≤ N + 1 := by omega
    exact_mod_cast h2
  exact Real.log_nonneg h1

/-- **c001 cost monotonicity in the dimension, sparsity and condition number.** -/
theorem fitQualityCost_mono (N N' s s' κ κ' : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hN : N ≤ N') (hs : s ≤ s') (hκ : κ ≤ κ') :
    fitQualityCost N s κ ε δ ≤ fitQualityCost N' s' κ' ε δ := by
  have hle : (N + 1 : ℝ) ≤ (N' + 1 : ℝ) := by
    have h1 : N + 1 ≤ N' + 1 := by omega
    exact_mod_cast h1
  have hlog : Real.log (N + 1) ≤ Real.log (N' + 1) := Real.log_le_log (by positivity) hle
  have h3 : (s : ℝ) ^ 3 ≤ (s' : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg s) (by exact_mod_cast hs) 3
  have h4 : (κ : ℝ) ^ 4 ≤ (κ' : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg κ) (by exact_mod_cast hκ) 4
  have hnum : Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4
      ≤ Real.log (N' + 1) * (s' : ℝ) ^ 3 * (κ' : ℝ) ^ 4 := by
    have hleft : Real.log (N + 1) * (s : ℝ) ^ 3 ≤ Real.log (N' + 1) * (s' : ℝ) ^ 3 :=
      mul_le_mul hlog h3 (by positivity) (fq_log_nonneg N')
    exact mul_le_mul hleft h4 (by positivity)
      (mul_nonneg (fq_log_nonneg N') (by positivity))
  unfold fitQualityCost
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-- **c001 cost is non-increasing in the target precision `ε`.** -/
theorem fitQualityCost_anti_mono_eps (N s κ : ℕ) (ε ε' δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hle : ε ≤ ε') :
    fitQualityCost N s κ ε' δ ≤ fitQualityCost N s κ ε δ := by
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4 :=
    mul_nonneg (mul_nonneg (fq_log_nonneg N) (by positivity)) (by positivity)
  have hden : ε * δ ^ 2 ≤ ε' * δ ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg δ)
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  unfold fitQualityCost
  exact fq_inv_mono (ε * δ ^ 2) (ε' * δ ^ 2) hεδ hden _ hC

/-- **c001 cost is non-increasing in the fit-quality tolerance `δ`.** -/
theorem fitQualityCost_anti_mono_delta (N s κ : ℕ) (ε δ δ' : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hle : δ ≤ δ') :
    fitQualityCost N s κ ε δ' ≤ fitQualityCost N s κ ε δ := by
  have hC : 0 ≤ Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4 :=
    mul_nonneg (mul_nonneg (fq_log_nonneg N) (by positivity)) (by positivity)
  have hsq : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ.le hle 2
  have hden : ε * δ ^ 2 ≤ ε * δ' ^ 2 := mul_le_mul_of_nonneg_left hsq hε.le
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  unfold fitQualityCost
  exact fq_inv_mono (ε * δ ^ 2) (ε * δ' ^ 2) hεδ hden _ hC

/-! ## §2 The fit error `E = ‖ |y⟩ − |ψ⟩ ‖²` -/

/-- **c001 fit error identity (p.4).**  For unit vectors, the squared distance
`E = ‖ |y⟩ − |ψ⟩ ‖²` is `2 − 2·Re⟨y,ψ⟩`. -/
theorem fitError_eq_norm_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y ψ : E) (hy : ‖y‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖y - ψ‖ ^ 2 = 2 - 2 * RCLike.re (inner ℂ y ψ) := by
  rw [norm_sub_sq (𝕜 := ℂ), hy, hψ]
  ring

/-- **c001 phase-aligned fit error (p.4).**  When the overlap is phase-aligned — the
convention used in the paper to pass from `E = ‖ |y⟩ − I(F)|λ⟩ ‖²` to the overlap — the fit
error is `E = 2(1 − |⟨y,ψ⟩|)`. -/
theorem fitError_eq_two_one_sub_abs_of_phase_aligned
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y ψ : E) (hy : ‖y‖ = 1) (hψ : ‖ψ‖ = 1)
    (halign : inner ℂ y ψ = ((‖inner ℂ y ψ‖ : ℝ) : ℂ)) :
    ‖y - ψ‖ ^ 2 = 2 * (1 - ‖inner ℂ y ψ‖) := by
  rw [fitError_eq_norm_sub_sq y ψ hy hψ, halign]
  simp
  ring

/-! ## §3 The swap-test outcome-1 probability -/

/-- **c001 the swap-test outcome-1 probability `(1 − |⟨y,ψ⟩|²)/2` is non-negative.** -/
theorem swapTestOneProbability_nonneg {c : ℝ} (hc : c ≤ 1) :
    0 ≤ swapTestOneProbability c := by
  unfold swapTestOneProbability
  linarith

/-- **c001 the swap-test outcome-1 probability is at most `1/2`.** -/
theorem swapTestOneProbability_le_half {c : ℝ} (hc : 0 ≤ c) :
    swapTestOneProbability c ≤ 1 / 2 := by
  unfold swapTestOneProbability
  linarith

/-- **c001 overlap squared of unit vectors lies in `[0,1]`** (Cauchy–Schwarz). -/
theorem inner_norm_sq_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y ψ : E) (hy : ‖y‖ = 1) (hψ : ‖ψ‖ = 1) :
    ‖inner ℂ y ψ‖ ^ 2 ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) y ψ
  rw [hy, hψ, mul_one] at h
  nlinarith [norm_nonneg (inner ℂ y ψ), h]

/-- **c001 the swap-test probability of outcome 1 for unit vectors is `(1 − |⟨y,ψ⟩|²)/2`
and lies in `[0, 1/2]`.** -/
theorem swapTest_probability_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (y ψ : E) (hy : ‖y‖ = 1) (hψ : ‖ψ‖ = 1) :
    swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) = (1 - ‖inner ℂ y ψ‖ ^ 2) / 2 ∧
      0 ≤ swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) ∧
      swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) ≤ 1 / 2 := by
  refine ⟨rfl, ?_, ?_⟩
  · exact swapTestOneProbability_nonneg (inner_norm_sq_le_one y ψ hy hψ)
  · exact swapTestOneProbability_le_half (sq_nonneg _)

/-! ## §4 The `O(1/δ²)` sample-count bound -/

/-- **c001 Chebyshev: `1/(4mδ²) ≤ η` from `m ≥ 1/(4δ²η)`.** -/
theorem one_div_four_mul_le_of_sample {m δ η : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hη : 0 < η)
    (hlarge : 1 / (4 * δ ^ 2 * η) ≤ m) :
    1 / (4 * m * δ ^ 2) ≤ η := by
  have hkey : 1 ≤ 4 * m * δ ^ 2 * η := by
    have h := (div_le_iff₀ (by positivity : 0 < 4 * δ ^ 2 * η)).mp hlarge
    nlinarith [h]
  rw [div_le_iff₀ (by positivity : 0 < 4 * m * δ ^ 2)]
  nlinarith [hkey]

/-- **c001 the `O(1/δ²)` sample count is non-increasing in `δ`.** -/
theorem sampleCountForDelta_anti_mono_delta {δ δ' η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hle : δ ≤ δ') :
    sampleCountForDelta δ' η ≤ sampleCountForDelta δ η := by
  unfold sampleCountForDelta
  have hden : 4 * δ ^ 2 * η ≤ 4 * δ' ^ 2 * η := by
    have hsq : δ ^ 2 ≤ δ' ^ 2 := pow_le_pow_left₀ hδ.le hle 2
    nlinarith [hsq]
  exact one_div_le_one_div_of_le (by positivity) hden

/-- **c001 Chebyshev sample-mean bound (p.4).**  If the swap-test sample mean `X` over `m`
independent `[0,1]`-valued outcomes has variance at most `1/(4m)` (the standard variance of
an average of `m` bounded variables), then `m ≥ 1/(4δ²η)` samples estimate the mean to
within `δ` with failure probability at most `η`.  This is exactly the `O(1/δ²)` sampling
statement of p.4, made explicit with Chebyshev's inequality. -/
theorem chebyshev_sample_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (m : ℕ) (hm : 0 < m)
    (hvar : variance X μ ≤ 1 / (4 * (m : ℝ)))
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hlarge : sampleCountForDelta δ η ≤ (m : ℝ)) :
    μ {ω | δ ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal η := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcheb := meas_ge_le_variance_div_sq (μ := μ) hX hδ
  have hbound : variance X μ / δ ^ 2 ≤ η := by
    have hdiv : variance X μ / δ ^ 2 ≤ (1 / (4 * (m : ℝ))) / δ ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg δ)
    have harith : 1 / (4 * m * δ ^ 2) ≤ η := by
      apply one_div_four_mul_le_of_sample hmR hδ hη
      simpa [sampleCountForDelta, mul_assoc, mul_comm, mul_left_comm] using hlarge
    have heq : (1 / (4 * (m : ℝ))) / δ ^ 2 = 1 / (4 * (m : ℝ) * δ ^ 2) := by
      field_simp
    linarith [hdiv, harith, heq]
  exact hcheb.trans (ENNReal.ofReal_le_ofReal hbound)

/-! ## §5 The claim statement -/

/-- **c001 (Algorithm 2, Estimating Fit Quality) — Eq. (14), arXiv:1204.5242v2 p.4.**

The Algorithm-2 cost `log(N)·s³κ⁴/(εδ²)` decomposes as the inversion cost `(16)` times the
`1/δ²` sampling factor, is monotone in `N, s, κ` and non-increasing in `ε, δ`; the fit error
is `‖ |y⟩ − |ψ⟩ ‖² = 2 − 2Re⟨y,ψ⟩`; the swap-test outcome-1 probability is `(1−|⟨y,ψ⟩|²)/2`
in `[0,1/2]`; and Chebyshev's inequality turns `m ≥ 1/(4δ²η)` samples into a `δ`-accurate
mean estimate with failure probability at most `η`.

*Proved:* all of the above.
*Not modelled here:* the sparse-oracle program that prepares `I(F)A⁻¹I(F†)|y⟩` and the
swap-test circuit itself (residuals of the `SparseHHL` block). -/
theorem claim_c001 :
    (∀ (N s κ : ℕ) (ε δ : ℝ),
        fitQualityCost N s κ ε δ
          = (Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 4 / ε) * (1 / δ ^ 2)) ∧
      (∀ (N N' s s' κ κ' : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
        N ≤ N' → s ≤ s' → κ ≤ κ' →
          fitQualityCost N s κ ε δ ≤ fitQualityCost N' s' κ' ε δ) ∧
      (∀ (N s κ : ℕ) (ε ε' δ : ℝ), 0 < ε → 0 < δ → ε ≤ ε' →
        fitQualityCost N s κ ε' δ ≤ fitQualityCost N s κ ε δ) ∧
      (∀ (N s κ : ℕ) (ε δ δ' : ℝ), 0 < ε → 0 < δ → δ ≤ δ' →
        fitQualityCost N s κ ε δ' ≤ fitQualityCost N s κ ε δ) ∧
      (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (y ψ : E), ‖y‖ = 1 → ‖ψ‖ = 1 → ‖y - ψ‖ ^ 2 = 2 - 2 * RCLike.re (inner ℂ y ψ)) ∧
      (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (y ψ : E), ‖y‖ = 1 → ‖ψ‖ = 1 →
          swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) = (1 - ‖inner ℂ y ψ‖ ^ 2) / 2 ∧
            0 ≤ swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) ∧
            swapTestOneProbability (‖inner ℂ y ψ‖ ^ 2) ≤ 1 / 2) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ), MemLp X 2 μ → ∀ (m : ℕ), 0 < m →
          variance X μ ≤ 1 / (4 * (m : ℝ)) →
          ∀ {δ η : ℝ}, 0 < δ → 0 < η → sampleCountForDelta δ η ≤ (m : ℝ) →
            μ {ω | δ ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal η) := by
  refine ⟨fitQualityCost_eq_inversion_mul_inv_delta_sq,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N N' s s' κ κ' ε δ hε hδ hN hs hκ
    exact fitQualityCost_mono N N' s s' κ κ' ε δ hε hδ hN hs hκ
  · intro N s κ ε ε' δ hε hδ hle
    exact fitQualityCost_anti_mono_eps N s κ ε ε' δ hε hδ hle
  · intro N s κ ε δ δ' hε hδ hle
    exact fitQualityCost_anti_mono_delta N s κ ε δ δ' hε hδ hle
  · intro E _ _ y ψ hy hψ
    exact fitError_eq_norm_sub_sq y ψ hy hψ
  · intro E _ _ y ψ hy hψ
    exact swapTest_probability_unit y ψ hy hψ
  · intro Ω _ μ _ X hX m hm hvar δ η hδ hη hlarge
    exact chebyshev_sample_mean_bound μ X hX m hm hvar hδ hη hlarge

end Qatlib.Papers.QDataFit12.SparseHHL.SourceClaims
