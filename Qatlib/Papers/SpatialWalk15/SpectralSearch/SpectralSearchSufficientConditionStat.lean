/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false

namespace Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat

open Qatlib
open scoped Classical BigOperators ComplexConjugate

noncomputable def spectralGapParam (c : ℝ) : ℝ := (1 - c) / (1 + c)

noncomputable def searchOverlapBound (c : ℝ) : ℝ :=
    min ((spectralGapParam c) ^ (3 / 2 : ℝ) / 8) (1 / 2)

def SpectralSearchSufficientCondition : Prop :=
  ∀ {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ],
  ∀ (V : Matrix κ κ ℂ) (lam : κ → ℝ) (σ : κ) (c : ℝ) (w : QState κ),
  V ∈ Matrix.unitaryGroup κ ℂ →
  lam σ = 1 →
  (∀ i, i ≠ σ → |lam i| ≤ c) →
  0 ≤ c → c < 1 →
  Normalized w →
  0 < ‖Inner w (fun j => V j σ)‖ →
  ‖Inner w (fun j => V j σ)‖ ≤ searchOverlapBound c →
  ∃ r : ℝ, -c / (1 + c) ≤ r ∧ r ≤ c / (1 - c) ∧
    ∃ t : ℝ,
      |t| ≤ 4 / (‖Inner w (fun j => V j σ)‖ * Real.sqrt (spectralGapParam c)) ∧
      ‖Inner w ((HamiltonianEvolution
        ((1 + r) • (V * Matrix.diagonal (fun i => (lam i : ℂ)) * V.conjTranspose)
          - r • (1 : Matrix κ κ ℂ)
          + Matrix.of (fun i j => w i * (starRingEnd ℂ) (w j) : Matrix κ κ ℂ)) t).mulVec
        (fun j => V j σ))‖ ^ 2 ≥ spectralGapParam c / 8

end Qatlib.Papers.SpatialWalk15.SpectralSearch.SpectralSearchSufficientConditionStat
