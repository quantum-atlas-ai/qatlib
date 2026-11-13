/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Sampling

The headline algorithm and resource claims in this module are proposition definitions
with the suffix `_statement`: **Statement only — not proved in Qatlib.**
No circuit or oracle implementation is constructed for these specifications.
The remaining definitions and proved lemmas concern only mathematical identities.
Resource annotations in the legacy records have no execution semantics.
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

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma31_average_sample_bound`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma31_average_sample_bound_statement : Prop :=
    ∃ est : SampleEstimator 1,
      ∀ (A B : Matrix (Fin 1) (Fin 1) ℂ) (θ : ℝ),
        OpNormLE A 1 → PSD B → 0 < θ → θ ≤ 1 →
        |est.estimate A B - (Matrix.trace (A * B)).re| ≤ θ * (Matrix.trace B).re ∧
        1 - 1 / 16 ≤ est.successProbability A B ∧
        BigOAt (est.samples A B : ℝ) (1 / θ ^ 2)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma32_median_of_samples`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma32_median_of_samples_statement : Prop :=
    ∃ est : SampleEstimator 1,
      ∀ (A B : Matrix (Fin 1) (Fin 1) ℂ) (θ δ : ℝ),
        OpNormLE A 1 → PSD B → 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        |est.estimate A B - (Matrix.trace (A * B)).re| ≤ θ * (Matrix.trace B).re ∧
        1 - δ ≤ est.successProbability A B ∧
        BigOAt (est.samples A B : ℝ) (Real.log (1 / δ) / θ ^ 2)

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma33_gibbs_sampling`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma33_gibbs_sampling_statement : Prop :=
    ∃ est : RealSampleEstimator 1,
      ∀ (A H : Matrix (Fin 1) (Fin 1) ℝ) (θ δ : ℝ),
        OpNormLE_R A 1 → OpNormLE_R H 1 → 0 < θ → θ ≤ 1 → 0 < δ → δ ≤ 1 / 2 →
        |est.estimate A (matExpR H) - Matrix.trace (A * matExpR H)| ≤
            θ * Matrix.trace (matExpR H) ∧
        1 - δ ≤ est.successProbability A (matExpR H) ∧
        BigOAt (est.samples A (matExpR H) : ℝ) (Real.log (1 / δ) / θ ^ 2) ∧
        ∃ p : ℕ, BigOAt (p : ℝ) (max 1 (Real.log (Real.sqrt 1 / θ)))

/-- **Statement only — not proved in Qatlib.**
Headline resource specification for `lemma34_all_traces`.
The records below carry independent output and resource annotations; this proposition
does not certify an oracle execution, sampling procedure, or gate decomposition. -/
def lemma34_all_traces_statement : Prop :=
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
            Real.log ((m : ℝ) / δ) / θ ^ 2 * (m : ℝ) * (s : ℝ) * (n : ℝ))

end Qatlib.Papers.QSDPsolver17.MainResults.ClassicalEstimation
