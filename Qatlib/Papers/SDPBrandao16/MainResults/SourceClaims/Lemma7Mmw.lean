/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.MmwCore.SdpLemma7SourceCoefficientsQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 7 — Matrix Multiplicative Weights (Brandão–Svore 2016)

Fixed source: arXiv:1609.05537v5, printed Lemma 7 / Eq. (21), page 11
(citing Arora–Kale, Theorem 10 of [9]).

For PSD contractions `M^(t)` (`0 ≤ M^(t) ≤ I`), `0 < ε < 1/2`, and the
learning rate `ε' = −ln(1−ε)`, define `W^(t) = exp(−ε' ∑_{τ<t} M^(τ))` and
`ρ^(t) = W^(t)/tr(W^(t))`.  Then

`∑_t tr(M^(t) ρ^(t)) ≤ (1+ε) λ_min(∑_t M^(t)) + ln(n)/ε`.

The established `sdpLemma7SourceCoefficients` already proves this exact statement
with the actual Gibbs history (`mmwState`) and the minimum eigenvalue; this
file restates it in paper notation and reuses that theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Concepts.SdpMmwSolver.MmwCore
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder BigOperators

/-- **Source Lemma 7 (Eq. (21), printed p. 11).**

Let `M : ℕ → Operator D` be a finite history of PSD contractions
(`M t` is PSD and `M t ≤ 1` for every `t < T`), let `0 < ε < 1/2`, and let
`ε' = −ln(1 − ε)`.  Writing `W^(t) = exp(−ε' ∑_{τ<t} M τ)` and
`ρ^(t) = W^(t) / tr(W^(t))` (the `mmwState D M ε' t` definition), and
`λ_min = ` the smallest eigenvalue of `∑_{t<T} M t`, one has

`∑_{t<T} tr(M^(t) ρ^(t)) ≤ (1 + ε) λ_min + ln D / ε`.

The dimension `D` plays the role of the source's `n`.

The theorem used here is:
`Qatlib.Concepts.SdpMmwSolver.MmwCore.sdpLemma7SourceCoefficients`
(coverage `equivalent`, `MmwCore/SdpLemma7SourceCoefficientsQuan`). -/
theorem lemma7_matrixMultiplicativeWeights (D T : ℕ) (M : ℕ → Operator D) (eps : ℝ)
    (hD : 0 < D) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (hM : ∀ s ∈ Finset.range T, (M s).PosSemidef ∧ M s ≤ 1) :
    let hS : (∑ t ∈ Finset.range T, M t).IsHermitian :=
      isSelfAdjoint_sum _ (fun t ht => (hM t ht).1.isHermitian)
    ∃ i : Fin D,
      (∀ j, hS.eigenvalues i ≤ hS.eigenvalues j) ∧
      (∑ t ∈ Finset.range T,
          (Matrix.trace (M t * mmwState D M (-Real.log (1 - eps)) t)).re) ≤
        (1 + eps) * hS.eigenvalues i + Real.log D / eps :=
  sdpLemma7SourceCoefficients D T M eps hD heps heps2 hM

end Qatlib.Papers.SDPBrandao16.MainResults.SourceClaims
