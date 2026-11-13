/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpRunDecisionContractQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Source Algorithm 3 — input/output contract (Brandão–Svore 2016)

Fixed source: arXiv:1609.05537v5, printed Algorithm 3 (page 7), with the
normalized exact-arithmetic output conventions of Eqs. (55)–(58) and the
printed failing-round alternative (p. 18).

**Input.** Oracles for `{A_1,…,A_m, C}` with `‖A_i‖, ‖C‖ ≤ 1`, and
`{b_1,…,b_m}` with `b_i ≥ 1`; parameters `R, α, δ, ξ > 0` (the extra
`A_{j₀} = I`, `b_{j₀} = R` normalization is the source's `A_1 = I, b_1 = R`
constraint).

**Output.** Either the label `Larger` (sound oracle failure at some round
`t₀ < T`), certifying that the optimal objective value is at least `(1−δ)α` by
a primal feasible witness `X ⪰ 0` (source Eq. (75)–(79)); or, after all
`T = sdpDualCertRounds D R δ η` rounds, the scale `L = ‖ȳ‖₁` and a sample from
`p = ȳ/‖ȳ‖₁`, where `ȳ = (δα/2R)e₁ + (1/T)∑_t y⁽ᵗ⁾` (Eq. (55)) is nonnegative,
`(1+δ)α`-optimal (Eq. (63)) and dual feasible (Eq. (64)–(71)).

Both branches follow from the normalized exact-arithmetic contract
`SdpRunDecisionContract`; this file exposes each branch in paper notation.
The underlying theorem is
`Qatlib.Concepts.SdpMmwSolver.SdpContract.sdpRunDecisionContract`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.SdpContract
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- **Source Algorithm 3, input record (printed p. 7).**

The oracle matrices `A : Fin m → Operator D` and `C`, the cost coefficients
`b`, and the parameters `R, α, δ, ξ` with the source's normalization and
bounds `‖A_i‖, ‖C‖ ≤ 1`, `b_i ≥ 1`, `R, α, δ, ξ > 0`. -/
structure Algorithm3Input (D m : ℕ) where
  /-- Constraint oracle matrices. -/
  A : Fin m → Operator D
  /-- Cost oracle matrix. -/
  C : Operator D
  /-- Cost coefficients. -/
  b : Fin m → ℝ
  /-- Size parameter. -/
  R : ℝ
  /-- Width / optimal-value parameter. -/
  α : ℝ
  /-- Relative accuracy. -/
  δ : ℝ
  /-- Polylog exponent. -/
  ξ : ℝ
  hermA : ∀ i, (A i).IsHermitian
  normA : ∀ i, ‖A i‖ ≤ 1
  hermC : C.IsHermitian
  normC : ‖C‖ ≤ 1
  bge : ∀ i, 1 ≤ b i
  posR : 0 < R
  posα : 0 < α
  posδ : 0 < δ
  posξ : 0 < ξ

/-- **Source Algorithm 3 — `Larger` branch (printed pp. 7, 18, Eqs. (75)–(79)).**

If the macro run stops at a sound oracle failure `t₀ < T`, it outputs the label
`Larger`, and there is a primal feasible witness `X ⪰ 0` with `tr(A_i X) ≤ b_i`,
`tr X ≤ R`, and objective `tr(CX) ≥ (1−δ)α`, i.e. the optimal objective value is
larger than `(1−δ)α`.

Underlying contract:
`Qatlib.Concepts.SdpMmwSolver.SdpContract.sdpRunDecisionContract`. -/
theorem algorithm3_largerBranch (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η : ℝ)
    (hD : 0 < D) (hα : 0 < α) (hα1 : 1 ≤ α) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hη : 0 < η) (hηε : η + ε ≤ δ / (8 * R)) (hε2 : ε ≤ δ / (16 * R))
    (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) (hC : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1)
    (hb : ∀ i, 1 ≤ b i) (hj₀ : A j₀ = 1) (hbj₀ : b j₀ = R)
    (hFail : ∃ t₀ : ℕ, t₀ < sdpDualCertRounds D R δ η ∧
      (∀ t ∈ Finset.range t₀, SdpRoundOracleContract D m A Cv b α ε η y t) ∧
      SdpRoundOracleFailure D m A Cv b α R ε η y t₀) :
    ∃ X : Operator D, X.PosSemidef ∧
      (∀ i, (Matrix.trace (A i * X)).re ≤ b i) ∧
      (Matrix.trace X).re ≤ R ∧
      (1 - δ) * α ≤ (Matrix.trace (Cv * X)).re :=
  (sdpRunDecisionContract D m A Cv b y j₀ α R δ ε η hD hα hα1 hR hδ hδ1 hε hη
    hηε hε2 hA hC hb hj₀ hbj₀).1 hFail

/-- **Source Algorithm 3 — completed-run branch (printed pp. 7, 16, Eqs. (55)–(71)).**

If every one of the `T = sdpDualCertRounds D R δ η` rounds satisfies the
per-round oracle contract `SdpRoundOracleContract`, the run completes and
outputs the scale `L = ‖ȳ‖₁ > 0` and the distribution `p = ȳ/‖ȳ‖₁` with
`ȳ = sdpDualCertificate …`, a probability distribution decomposing
`ȳ = L • p`; `ȳ` is `(1+δ)α`-optimal (`∑ ȳ_i b_i ≤ (1+δ)α`), dual feasible
(`∑ ȳ_i A_i − C ⪰ 0`), and by weak duality bounds every primal feasible
value by `(1+δ)α`.

Underlying contract:
`Qatlib.Concepts.SdpMmwSolver.SdpContract.sdpRunDecisionContract`. -/
theorem algorithm3_completionBranch (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε η : ℝ)
    (hD : 0 < D) (hα : 0 < α) (hα1 : 1 ≤ α) (hR : 0 < R) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) (hη : 0 < η) (hηε : η + ε ≤ δ / (8 * R)) (hε2 : ε ≤ δ / (16 * R))
    (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) (hC : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1)
    (hb : ∀ i, 1 ≤ b i) (hj₀ : A j₀ = 1) (hbj₀ : b j₀ = R)
    (hRound : ∀ t : ℕ, SdpRoundOracleContract D m A Cv b α ε η y t) :
    0 < sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) ∧
      (∀ i, 0 ≤ sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
      (∑ i, sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) = 1 ∧
      (∀ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i =
        sdpDualSampleScale m δ α R j₀ y (sdpDualCertRounds D R δ η) *
          sdpDualSampleDist m δ α R j₀ y (sdpDualCertRounds D R δ η) i) ∧
      (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i * b i ≤
        (1 + δ) * α) ∧
      ((∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ η) i • A i) -
          Cv).PosSemidef ∧
      (∀ X : Operator D, X.PosSemidef →
        (∀ i, (Matrix.trace (A i * X)).re ≤ b i) →
        (Matrix.trace (Cv * X)).re ≤ (1 + δ) * α) :=
  (sdpRunDecisionContract D m A Cv b y j₀ α R δ ε η hD hα hα1 hR hδ hδ1 hε hη
    hηε hε2 hA hC hb hj₀ hbj₀).2 hRound

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
