/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpResidualMacros
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.SdpContract

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

def SdpWidthSlackPayoffRangeContract : Prop :=
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ),
    0 < D → 0 < α → 2 ≤ α → 0 < R → 0 < δ → 0 < ε →
    2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) → A j₀ = 1 → b j₀ = R →
    (∀ t, (∀ i, 0 ≤ y t i) ∧
      (∑ i, b i * y t i ≤ α * (1 + 2 * R * ε))) →
    (∀ s, (sdpDualPayoff D m A Cv α y s).IsHermitian ∧
      (0 : Operator D) ≤ sdpDualPayoff D m A Cv α y s ∧
      sdpDualPayoff D m A Cv α y s ≤ 1) ∧
    (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ ε) i * b i ≤
      (1 + δ) * α)

def SdpConvexCombinationSamplingContract : Prop :=
  ∀ (m T : ℕ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ : ℝ),
    0 < T → 0 < α → 0 < R → 0 < δ →
    (∀ t i, 0 ≤ y t i) →
    (∀ t, 0 < ∑ i, y t i) →
    let bar := sdpDualCertificate m δ α R j₀ y T
    let scale := sdpDualSampleScale m δ α R j₀ y T
    0 < scale ∧
    (∀ i, 0 ≤ sdpDualSampleDist m δ α R j₀ y T i) ∧
    (∑ i, sdpDualSampleDist m δ α R j₀ y T i) = 1 ∧
    (∃ w : Fin (T + 1) → ℝ,
      (∀ u, 0 ≤ w u) ∧ (∑ u, w u) = 1 ∧
      w 0 = (δ * α / (2 * R)) / scale ∧
      (∀ t : Fin T, w t.succ = (∑ i, y t i) / (T : ℝ) / scale) ∧
      ∀ i, bar i = scale * sdpDualSampleDist m δ α R j₀ y T i)

def SdpLemma7SourceCoefficientsContract : Prop :=
  ∀ (D T : ℕ) (M : ℕ → Operator D) (eps : ℝ),
    0 < D → 0 < eps → eps < 1 / 2 →
    ∀ hM : ∀ s ∈ Finset.range T, (M s).PosSemidef ∧ M s ≤ 1,
    let hS : (∑ t ∈ Finset.range T, M t).IsHermitian :=
      isSelfAdjoint_sum _ (fun t ht => (hM t ht).1.isHermitian)
    ∃ i : Fin D,
      (∀ j, hS.eigenvalues i ≤ hS.eigenvalues j) ∧
      (∑ t ∈ Finset.range T,
          (Matrix.trace (M t * mmwState D M (-Real.log (1 - eps)) t)).re) ≤
        (1 + eps) * hS.eigenvalues i + Real.log D / eps

def SdpAlphaRescaleLemma2Contract : Prop :=
  ∀ (n m : ℕ) (b : Fin m → ℝ) (R r α δ : ℝ),
    0 < n → 0 < m → 0 < R → 0 < r → 0 < α → 0 < δ →
    (∀ i, 1 ≤ b i) → α ≤ R → r * α ≤ R →
    (∃ liftedB : Fin (m + 1) → ℝ,
      (∀ i, 1 ≤ liftedB i) ∧
      liftedB (Fin.last m) = R + 1 ∧
      (∀ i : Fin m, liftedB i.castSucc = b i)) ∧
    (∀ bsol : Fin m → ℝ,
      (∀ i, 0 ≤ bsol i) →
      (∑ i, bsol i * (b i / α)) ≤ 1 + δ →
      (∑ i, bsol i * b i) ≤ (1 + δ) * α)

end Qatlib.Concepts.SdpMmwSolver.SdpContract
