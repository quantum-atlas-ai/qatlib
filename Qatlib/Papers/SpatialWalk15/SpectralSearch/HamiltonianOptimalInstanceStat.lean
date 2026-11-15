/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat

@[expose] public section
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat
open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false

namespace Qatlib.Papers.SpatialWalk15.SpectralSearch

open Qatlib
open scoped Classical BigOperators ComplexConjugate

def SpatialSearchHamiltonianOptimalInstance : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ],
  ∀ (V : Matrix κ κ ℂ) (lam : κ → ℝ) (σ : κ) (c : ℝ) (ι : κ),
  V ∈ Matrix.unitaryGroup κ ℂ →
  lam σ = 1 →
  (∀ i, i ≠ σ → |lam i| ≤ c) →
  0 ≤ c → c < 1 →
  4 ≤ Fintype.card κ →
  (Real.sqrt (Fintype.card κ))⁻¹ ≤ ‖Inner (Ket ι) (fun j => V j σ)‖ →
  ‖Inner (Ket ι) (fun j => V j σ)‖ ≤ searchOverlapBound c →
  ∃ r : ℝ, -c / (1 + c) ≤ r ∧ r ≤ c / (1 - c) ∧
    ∃ t : ℝ, 0 ≤ t ∧
      t ≤ 4 * Real.sqrt (Fintype.card κ) / Real.sqrt (spectralGapParam c) ∧
      MeasureProb ((HamiltonianEvolution
        (-(Matrix.of (fun i j => Ket ι i * (starRingEnd ℂ) (Ket ι j) : Matrix κ κ ℂ))
          - (1 + r) • (V * Matrix.diagonal (fun i => (lam i : ℂ))
              * V.conjTranspose)) t).mulVec (fun j => V j σ)) {ι}
        ≥ spectralGapParam c / 8

end Qatlib.Papers.SpatialWalk15.SpectralSearch
