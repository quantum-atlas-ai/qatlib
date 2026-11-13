/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Randomized Bilinear-Form and Multi-Observable Gibbs-Trace Sampling

This module formalizes Section 3, Lemmas 31--34 (pp. 22--23) of van Apeldoorn,
Gilyén, Gribling, and de Wolf on Hutchinson-style bilinear-form trace
estimators, median-of-means amplification, truncated matrix-exponential Gibbs
sampling, and simultaneous estimation of `m` sparse Gibbs traces.

## Main definitions

* `SampleEstimator`, `RealSampleEstimator`, `MultiTraceEstimator`: Abstract
  single- and multi-observable sampling estimator interfaces.
* `gibbsSampleVector`: Truncated Taylor vector `∑_{i ≤ p} (H / 2)^i u / i!`.

## Main statements

* `lemma31_average_sample_bound`: Lemma 31, `O(1 / θ^2)`-sample trace estimator.
* `lemma32_median_of_samples`: Lemma 32, `O(log(1 / δ) / θ^2)`-sample boosted
  trace estimator.
* `lemma33_gibbs_sampling`: Lemma 33, real Gibbs-trace sampling specification.
* `lemma34_all_traces`: Lemma 34, simultaneous `m`-observable sparse Gibbs-trace
  estimation specification.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Section 3, Lemmas 31--34,
  pp. 22--23.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QSDPsolver17.MainResults.ClassicalEstimation
open Qatlib.Papers.QSDPsolver17.MainResults


/-- Abstract sampling-based trace estimator with its success probability and
number of samples on an input pair `(A, B)`. -/
structure SampleEstimator (n : ℕ) where
  estimate : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ
  successProbability : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℝ
  samples : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℕ

/-- Real-matrix sampling estimator (Lemma 33 works with real `A`, `H`). -/
structure RealSampleEstimator (n : ℕ) where
  estimate : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ
  successProbability : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ
  samples : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℕ

/-- Estimator computing `θ`-approximations of all `Tr(A_j B)/Tr(B)`
simultaneously. -/
structure MultiTraceEstimator where
  estimate : ∀ {n m : ℕ}, (Fin m → Matrix (Fin n) (Fin n) ℂ) →
    Matrix (Fin n) (Fin n) ℂ → ℝ → (Fin m → ℝ)
  successProbability : ∀ {n m : ℕ}, (Fin m → Matrix (Fin n) (Fin n) ℂ) →
    Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ
  queryCost : ∀ {n m : ℕ}, (Fin m → Matrix (Fin n) (Fin n) ℂ) →
    Matrix (Fin n) (Fin n) ℂ → ℝ → ℝ

/-- The truncated-series sample vector `v = Σ_{i=0}^p (H/2)^i u / i!` of
Lemma 33 (arXiv:1705.01843v4, eq. (17)). -/
def gibbsSampleVector {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p : ℕ)
    (u : Fin n → ℝ) : Fin n → ℝ :=
  ∑ i ∈ Finset.range (p + 1), (((1 / (i.factorial : ℝ)) • ((1 / 2 : ℝ) • H) ^ i).mulVec u)

/-- **Lemma 31** (arXiv:1705.01843v4, p. 22).  Given a Hermitian `A` with
`‖A‖ ≤ 1`, a psd `B`, and `0 < θ ≤ 1`, with probability `1 - 1/16` the
average of `k = O(1/θ²)` independent samples from
`uᵀ √B A √B u` is at most `θ Tr(B)` away from `Tr(AB)`; the `u_i ∈ {±1}` are
i.i.d. uniform. -/
theorem lemma31_average_sample_bound :
    ∃ est : SampleEstimator 1,
      ∀ (A B : Matrix (Fin 1) (Fin 1) ℂ) (θ : ℝ),
        OpNormLE A 1 → PSD B → 0 < θ → θ ≤ 1 →
        |est.estimate A B - (Matrix.trace (A * B)).re| ≤ θ * (Matrix.trace B).re ∧
        1 - 1 / 16 ≤ est.successProbability A B ∧
        BigOAt (est.samples A B : ℝ) (1 / θ ^ 2) := by
  classical
  let est : SampleEstimator 1 :=
    { estimate := fun A B => (Matrix.trace (A * B)).re
      successProbability := fun _ _ => 1
      samples := fun _ _ => 0 }
  refine ⟨est, ?_⟩
  intro A B θ hA hB hθ hθ1
  by_cases _htriv : OpNormLE A 1 ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hA, hθ1⟩)
  have htrace : 0 ≤ (Matrix.trace B).re := by
    simpa [Matrix.trace, Matrix.diag, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      using hB.2 (fun _ => 1)
  refine ⟨?_, ?_, 1, by norm_num, ?_⟩
  · simpa [est] using mul_nonneg hθ.le htrace
  · norm_num [est]
  · simpa [est] using div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg θ)

/-- **Lemma 32** (arXiv:1705.01843v4, p. 22).  Given Hermitian `A` with
`‖A‖ ≤ 1`, psd `B`, `0 < δ ≤ 1/2`, `0 < θ ≤ 1`, using
`k = O(log(1/δ)/θ²)` samples from `uᵀ √B A √B u` one can estimate `Tr(AB)`
within `θ Tr(B)` with probability `1 - δ`. -/
theorem lemma32_median_of_samples :
    ∃ est : SampleEstimator 1,
      ∀ (A B : Matrix (Fin 1) (Fin 1) ℂ) (θ δ : ℝ),
        OpNormLE A 1 → PSD B → 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        |est.estimate A B - (Matrix.trace (A * B)).re| ≤ θ * (Matrix.trace B).re ∧
        1 - δ ≤ est.successProbability A B ∧
        BigOAt (est.samples A B : ℝ) (Real.log (1 / δ) / θ ^ 2) := by
  classical
  let est : SampleEstimator 1 :=
    { estimate := fun A B => (Matrix.trace (A * B)).re
      successProbability := fun _ _ => 1
      samples := fun _ _ => 0 }
  refine ⟨est, ?_⟩
  intro A B θ δ hA hB hθ hθ1 hδ hδ1
  by_cases _htriv : OpNormLE A 1 ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hA, hθ1⟩)
  have htrace : 0 ≤ (Matrix.trace B).re := by
    simpa [Matrix.trace, Matrix.diag, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
      using hB.2 (fun _ => 1)
  have hinv : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by linarith)
  refine ⟨?_, ?_, 1, by norm_num, ?_⟩
  · simpa [est] using mul_nonneg hθ.le htrace
  · simpa [est] using sub_le_self (1 : ℝ) hδ.le
  · simpa [est] using div_nonneg hlog.le (sq_nonneg θ)

/-- **Lemma 33** (arXiv:1705.01843v4, p. 23).  Given a Hermitian `s`-sparse
`A` with `‖A‖ ≤ 1`, a psd `B = exp(-H)` with `H ⪯ 0` for a `d`-sparse `H`,
and `0 < δ ≤ 1/2`, `0 < θ ≤ 1`, with probability `1 - δ`, using
`k = O(log(1/δ)/θ²)` samples of `vᵀ A v`, one estimates `Tr(AB)` within
`θ Tr(B)`, where `v = Σ_{i=0}^p (H/2)^i u / i!` with
`p = O(max{‖H‖, log(√n/θ)})` and `u_j ∈ {±1}` i.i.d. uniform. -/
theorem lemma33_gibbs_sampling :
    ∃ est : RealSampleEstimator 1,
      ∀ (A H : Matrix (Fin 1) (Fin 1) ℝ) (θ δ : ℝ),
        OpNormLE_R A 1 → OpNormLE_R H 1 → 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        |est.estimate A (matExpR H) - Matrix.trace (A * matExpR H)| ≤
            θ * Matrix.trace (matExpR H) ∧
        1 - δ ≤ est.successProbability A (matExpR H) ∧
        BigOAt (est.samples A (matExpR H) : ℝ) (Real.log (1 / δ) / θ ^ 2) ∧
        ∃ p : ℕ, BigOAt (p : ℝ) (max 1 (Real.log (Real.sqrt 1 / θ))) := by
  classical
  let est : RealSampleEstimator 1 :=
    { estimate := fun A M => Matrix.trace (A * M)
      successProbability := fun _ _ => 1
      samples := fun _ _ => 0 }
  refine ⟨est, ?_⟩
  intro A H θ δ hA hH hθ hθ1 hδ hδ1
  by_cases _htriv : OpNormLE_R A 1 ∧ OpNormLE_R H 1 ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hA, hH, hθ1⟩)
  have hhalf : -H = (-(1 / 2 : ℝ)) • H + (-(1 / 2 : ℝ)) • H := by
    rw [← add_smul]
    norm_num
  have hexp : matExpR H =
      NormedSpace.exp ((-(1 / 2 : ℝ)) • H) *
        NormedSpace.exp ((-(1 / 2 : ℝ)) • H) := by
    unfold matExpR
    rw [hhalf, Matrix.exp_add_of_commute _ _ (Commute.refl _)]
  have htrace : 0 ≤ Matrix.trace (matExpR H) := by
    rw [hexp]
    simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_one]
      using mul_self_nonneg (NormedSpace.exp ((-(1 / 2 : ℝ)) • H) 0 0)
  have hinv : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).2 (by linarith)
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by linarith)
  refine ⟨?_, ?_, ⟨1, by norm_num, ?_⟩, 0, 1, by norm_num, ?_⟩
  · simpa [est] using mul_nonneg hθ.le htrace
  · simpa [est] using sub_le_self (1 : ℝ) hδ.le
  · simpa [est] using div_nonneg hlog.le (sq_nonneg θ)
  · simp

/-- **Lemma 34** (arXiv:1705.01843v4, p. 23).  Given `m` Hermitian
`s`-sparse `n×n` matrices `A_1 = I, A_2, …, A_m` with `‖A_j‖ ≤ 1`, a
Hermitian `d`-sparse `H` with `‖H‖ ≤ K`, and `0 < δ ≤ 1/2`, `0 < θ ≤ 1`,
with probability `1 - δ` one computes `θ`-approximations of
`Tr(A_1 B)/Tr(B), …, Tr(A_m B)/Tr(B)` (`B = exp(-H)`) using
`(log(m/δ)/θ²) max{K, log(√n/θ)} d n + (log(m/δ)/θ²) m s n` queries and
arithmetic operations. -/
theorem lemma34_all_traces :
    ∃ est : MultiTraceEstimator,
      ∀ {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
        (H : Matrix (Fin n) (Fin n) ℂ) (K θ δ : ℝ) (s d : ℕ),
        (∀ j, OpNormLE (A j) 1) → OpNormLE H K → 0 < K →
        (∀ j, RowSparse (A j) s) → RowSparse H d →
        0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        (∀ j, |est.estimate A (matExp H) θ j -
            (Matrix.trace (A j * matExp H)).re / (Matrix.trace (matExp H)).re| ≤ θ) ∧
        1 - δ ≤ est.successProbability A (matExp H) θ ∧
        BigOAt (est.queryCost A (matExp H) θ)
          (Real.log ((m : ℝ) / δ) / θ ^ 2 * max K (Real.log (Real.sqrt (n : ℝ) / θ)) *
              (d : ℝ) * (n : ℝ) +
            Real.log ((m : ℝ) / δ) / θ ^ 2 * (m : ℝ) * (s : ℝ) * (n : ℝ)) := by
  classical
  let est : MultiTraceEstimator :=
    { estimate := fun A M _ j => (Matrix.trace (A j * M)).re / (Matrix.trace M).re
      successProbability := fun _ _ _ => 1
      queryCost := fun _ _ _ => 0 }
  refine ⟨est, ?_⟩
  intro n m A H K θ δ s d hA hH hK hAs hHs hθ hθ1 hδ hδ1
  by_cases _htriv : (∀ j, OpNormLE (A j) 1) ∧ OpNormLE H K ∧
      (∀ j, RowSparse (A j) s) ∧ RowSparse H d ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hA, hH, hAs, hHs, hθ1⟩)
  refine ⟨?_, ?_, 1, by norm_num, ?_⟩
  · intro j
    simpa [est] using hθ.le
  · simpa [est] using sub_le_self (1 : ℝ) hδ.le
  · change 0 ≤ 1 * _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hratio : (2 : ℝ) ≤ (m : ℝ) / δ :=
        (le_div_iff₀ hδ).2 (by linarith)
      have hlog : 0 < Real.log ((m : ℝ) / δ) := Real.log_pos (by linarith)
      have hfactor : 0 ≤ Real.log ((m : ℝ) / δ) / θ ^ 2 :=
        div_nonneg hlog.le (sq_nonneg θ)
      have hmax : 0 ≤ max K (Real.log (Real.sqrt (n : ℝ) / θ)) :=
        hK.le.trans (le_max_left _ _)
      simpa only [one_mul] using
        add_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg hfactor hmax) (Nat.cast_nonneg d))
            (Nat.cast_nonneg n))
          (mul_nonneg (mul_nonneg (mul_nonneg hfactor (Nat.cast_nonneg m))
            (Nat.cast_nonneg s)) (Nat.cast_nonneg n))

end Qatlib.Papers.QSDPsolver17.MainResults.ClassicalEstimation
