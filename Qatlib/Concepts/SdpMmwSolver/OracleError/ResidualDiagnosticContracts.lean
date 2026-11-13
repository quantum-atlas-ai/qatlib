/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpResidualMacros

/-!
# Diagnostic contracts for SDP oracle errors

This module records proposed concentration, sampling, rescaling, and Gibbs perturbation
contracts as propositions. `SdpStep2SampledOracleContract` and
`SdpSparsificationGibbsErrorContract` expose the hypotheses whose sufficiency is examined by
separate counterexamples; defining these propositions does not establish them.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `SdpSparsificationGibbsErrorContract`: The proposed statement that per-round payoff errors at
  most 1/(4T) imply Gibbs trace distance at most an arbitrary positive ε before round T.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.OracleError

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The proposed finite matrix concentration statement bounding the fraction of samples with
large averaged operator norm from Hermitian boundedness and coordinatewise zero sums. -/
def SdpMatrixHoeffdingContract : Prop :=
  ∀ (d k R : ℕ) (Z : Fin R → Fin k → Operator d) (bound δ : ℝ),
    0 < d → 0 < k → 0 < R → 0 < bound → 0 < δ →
    (∀ s i, (Z s i).IsHermitian) →
    (∀ s i, ‖Z s i‖ ≤ bound) →
    (∀ i, (∑ s, Z s i) = 0) →
    sdpEventProbability (fun s : Fin R =>
      δ ≤ ‖(k : ℝ)⁻¹ • (∑ i, Z s i)‖) ≤
      (d : ℝ) * Real.exp ((-(k : ℝ)) * δ ^ 2 / (8 * bound ^ 2))

/-- An alias for the proposed matrix concentration proposition `SdpMatrixHoeffdingContract`. -/
def SdpMatrixHoeffding : Prop := SdpMatrixHoeffdingContract

/-- The proposed implication from empirical acceptance inequalities to true weighted width and
separation bounds, without additional sample approximation hypotheses. -/
def SdpStep2SampledOracleContract : Prop :=
  ∀ (D m M : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (α R κ ν η : ℝ) (t N : ℕ) (q : Fin m → ℝ)
    (idx : Fin M → Fin m),
    0 < D → 0 < M → 0 < N → 0 < α → 1 ≤ α → 0 < R → 0 < κ → 0 < ν → 0 < η →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∀ i, 0 ≤ q i) → (∑ i, q i) = 1 →
    (∀ i, 0 ≤ y t i) →
    (∀ i, y t i = κ * (N : ℝ) * q i) →
    (∑ j : Fin M,
        (Matrix.trace (A (idx j) *
          mmwState D (sdpDualPayoff D m A Cv α y) η t)).re) / (M : ℝ) ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re /
        (κ * (N : ℝ)) - (κ + ν) →
    (∑ j : Fin M, b (idx j)) / (M : ℝ) ≤
      α / (κ * (N : ℝ)) + R * (κ + ν) →
    (∑ i, b i * y t i) ≤ sdpSampledWidthBudget α R κ ν ∧
    (∑ i, y t i *
        (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re) ≥
      (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t)).re -
        sdpSampledSeparationSlack α κ ν

/-- An alias for the proposed sampled-oracle proposition `SdpStep2SampledOracleContract`. -/
def SdpStep2SampledOracle : Prop := SdpStep2SampledOracleContract

/-- The proposed statement that a zero response at a round forces every nonnegative vector
meeting the trace threshold to have cost at least α(1 − 3Rε). -/
def SdpStep2NoOutputSeparatorContract : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (α R ε η : ℝ) (t₀ : ℕ),
    0 < D → 0 < α → 1 ≤ α → 0 < R → 0 < ε → 0 < η →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∀ i, y t₀ i = 0) →
    (∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
      ((∑ i, z i *
          (Matrix.trace (A i * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re) ≥
        (Matrix.trace (Cv * mmwState D (sdpDualPayoff D m A Cv α y) η t₀)).re -
          3 * α * ε) →
      α * (1 - 3 * R * ε) ≤ ∑ i, z i * b i)

/-- An alias for the proposed no-output separator proposition
`SdpStep2NoOutputSeparatorContract`. -/
def SdpStep2NoOutputSeparator : Prop := SdpStep2NoOutputSeparatorContract

/-- The proposed statement that per-round payoff errors at most 1/(4T) imply Gibbs trace
distance at most an arbitrary positive ε before round T. -/
def SdpSparsificationGibbsErrorContract : Prop :=
  ∀ (D m Q T : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (α ε η : ℝ)
    (idx : ℕ → Fin Q → Fin m),
    0 < D → 0 < Q → 0 < T → 0 < α → 1 ≤ α → 0 < ε → 0 < η →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α)) →
    (∀ t, ‖sdpSparsifiedPayoff D m Q A Cv α (idx t) -
        sdpDualPayoff D m A Cv α y t‖ ≤ 1 / (4 * (T : ℝ))) →
    (∀ t < T, Matrix.traceNorm
      (mmwState D (fun s => sdpDualPayoff D m A Cv α y s) η t -
        mmwState D (fun s => sdpSparsifiedPayoff D m Q A Cv α (idx s)) η t) ≤
        ε)

/-- An alias for the proposed Gibbs approximation proposition
`SdpSparsificationGibbsErrorContract`. -/
def SdpSparsificationGibbsError : Prop := SdpSparsificationGibbsErrorContract

/-- The numerical proposition asserting existence of positive real copy and measurement budgets
satisfying the displayed logarithmic upper bounds. -/
def SdpExpectationEstimationContract : Prop :=
  ∀ (n m s : ℕ) (ε h p_e : ℝ),
    0 < n → 0 < m → 0 < s → 0 < ε → 0 < h → 0 < p_e → p_e < 1 →
    (∃ copies meas : ℝ,
      0 < copies ∧ 0 < meas ∧
      copies ≤ 8 * Real.log (1 / p_e) / ε ^ 2 ∧
      meas ≤ 8 * (s : ℝ) / ε ^ 2 *
        (Real.log (4 * (n : ℝ) * (s : ℝ) / (p_e * ε))) ^ 4) ∧
    (∃ copiesO oracle : ℝ,
      0 < copiesO ∧ 0 < oracle ∧
      copiesO ≤ 8 * Real.log ((m : ℝ) / p_e) / h ^ 2 ∧
      oracle ≤ 8 * (s : ℝ) / h ^ 2 *
        (Real.log (4 * (n : ℝ) * (m : ℝ) * (s : ℝ) / (p_e * h))) ^ 4)

/-- An alias for the numerical budget proposition `SdpExpectationEstimationContract`. -/
def SdpExpectationEstimation : Prop := SdpExpectationEstimationContract

/-- The original proposed payoff-range and certificate-cost statement using the sampled width
budget with both tolerances equal to ε. -/
def SdpWidthSlackPayoffRangeOriginalContract : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ),
    0 < D → 0 < α → 2 ≤ α → 0 < R → 0 < δ → 0 < ε →
    2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) → A j₀ = 1 → b j₀ = R →
    (∀ t, (∀ i, 0 ≤ y t i) ∧
      (∑ i, b i * y t i ≤ sdpSampledWidthBudget α R ε ε)) →
    (∀ s, (sdpDualPayoff D m A Cv α y s).IsHermitian ∧
      (0 : Operator D) ≤ sdpDualPayoff D m A Cv α y s ∧
      sdpDualPayoff D m A Cv α y s ≤ 1) ∧
    (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ ε) i * b i ≤
      (1 + δ) * α)

/-- The original proposed lifting and objective-rescaling statement using normalized tolerance
δ/α and the multiplicative conclusion (1 + δ)α. -/
def SdpAlphaRescaleLemma2OriginalContract : Prop :=
  ∀ (n m : ℕ) (b : Fin m → ℝ) (R r α δ : ℝ),
    0 < n → 0 < m → 0 < R → 0 < r → 0 < α → 0 < δ →
    (∀ i, 1 ≤ b i) → α ≤ R → r * α ≤ R →
    (∃ liftedB : Fin (m + 1) → ℝ,
      (∀ i, 1 ≤ liftedB i) ∧
      liftedB (Fin.last m) = R + 1 ∧
      (∀ i : Fin m, liftedB i.castSucc = b i)) ∧
    (∀ bsol : Fin m → ℝ,
      (∀ i, 0 ≤ bsol i) →
      (∑ i, bsol i * (b i / α)) ≤ 1 + δ / α →
      (∑ i, bsol i * b i) ≤ (1 + δ) * α)

end Qatlib.Concepts.SdpMmwSolver.OracleError
