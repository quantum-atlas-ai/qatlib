/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpLargerTriggerRunStat
import Qatlib.Concepts.SdpMmwSolver.BranchProofs.SdpLargerBranchPrimalWitnessQuan

/-!
# Primal witnesses from a failed oracle round

`sdpLargerTriggerRun` applies the larger-branch witness theorem to the Gibbs state at a failed
oracle round. The payoff history is Hermitian, so this iterate is a density operator and the
failure condition supplies the required separation inequality.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpLargerTriggerRun`: A failed oracle round along the specified Hermitian Gibbs history
  yields a positive semidefinite primal feasible operator of trace at most R and objective at
  least (1 − δ)α. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.BranchProofs
open Matrix
open scoped Classical BigOperators

/-- A failed oracle round along the specified Hermitian Gibbs history yields a positive
semidefinite primal feasible operator of trace at most R and objective at least (1 − δ)α.
See [BrandaoSvore2017]. -/
theorem sdpLargerTriggerRun : SdpLargerTriggerRun := by
  intro D m A Cv b y j₀ α R δ ε η t₀ hD hα hR hδ hδ1 hε hεcap hA hCv hb hA0 hb0 _hprior hfail
  have hhistory (s : ℕ) : (sdpDualPayoff D m A Cv α y s).IsHermitian := by
    have hsum : (∑ i, y s i • A i).IsHermitian :=
      isSelfAdjoint_sum _ fun i _ => (hA i).smul (by simp [IsSelfAdjoint])
    have hI : (1 : Operator D).IsHermitian := Matrix.isHermitian_one
    exact ((hsum.sub hCv).add (hI.smul (by simp [IsSelfAdjoint]))).smul (by simp [IsSelfAdjoint])
  have hdensity :=
      (matrix_mw_actual_gibbs_iterates_density D (sdpDualPayoff D m A Cv α y) η t₀ hD hhistory).2
  exact sdpLargerBranchPrimalWitness D m A Cv b
    (mmwState D (sdpDualPayoff D m A Cv α y) η t₀) j₀ α R δ ε
    hα hR hδ hδ1 hε hεcap hb hA0 hb0 hdensity hfail

end Qatlib.Concepts.SdpMmwSolver.BranchProofs
