/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.QuantumGibbs
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs

/-!
# Finite-bit Metropolis kernel and ledger

This module defines the finite-bit acceptance rule and its induced finite-state Metropolis
evolution in the setting of [TemmeEtAl2011]. The dyadic rule rounds the acceptance mass down to
a multiple of `2 ^ (-k)`, and rejected off-diagonal proposals contribute to the diagonal holding
mass.

It also supplies a natural-number resource ledger whose entries are instantiated by the
accompanying bounds module.

## Main statements

* `fairBitAccept`, `fairBitGrid`, and `fairBitBranchMass` define the dyadic acceptance rule,
  grid spacing, and two coin branches.
* `fairBitKernel`, `fairBitStep`, and `fairBitEvolve` define the kernel and its iterations.
* `GibbsRunLedger` records measurement, gate, bit, and peak-space counts.

## References

* [Temme et al., 2011][TemmeEtAl2011], *Quantum Metropolis Sampling*, Eqs. (2)-(3) and Section
  3.2.
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing
namespace StageBGIBBSMETROPOLIS

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder

/-- The dyadic acceptance mass obtained by taking the natural floor of `2 ^ k * f` and dividing
by `2 ^ k`. -/
noncomputable def fairBitAccept (k : ℕ) (f : ℝ) : ℝ :=
  Qatlib.Concepts.RiskEstimation.PopulationGap.fairBitAcceptMass k f

/-- The positive dyadic grid spacing `1 / 2 ^ k` for a coin using `k` bits. -/
noncomputable def fairBitGrid (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

/-- The accepting branch mass `fairBitAccept k f` for `true` and its complement for `false`. -/
noncomputable def fairBitBranchMass (k : ℕ) (f : ℝ) (b : Bool) : ℝ :=
  if b then fairBitAccept k f else 1 - fairBitAccept k f

/-- The uniform-proposal Metropolis kernel with finite-bit thermal acceptance on off-diagonal
transitions. Its diagonal entry is one minus the total off-diagonal transition mass. -/
noncomputable def fairBitKernel {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) :
    Fin D → Fin D → ℝ :=
  fun i j =>
    if i = j then 1 - ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
      fairBitAccept k (Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance E β i j') / (D : ℝ)
    else fairBitAccept k (Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance E β i j) / (D : ℝ)

/-- The forward action of the finite-bit Metropolis kernel on a real vector, summing incoming
mass from every source state. -/
noncomputable def fairBitStep {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (p : Fin D → ℝ) : Fin D → ℝ :=
  fun j => ∑ i, p i * fairBitKernel E β k i j

/-- The iteration of the finite-bit Metropolis update, with zero steps returning the input
vector and each successor applying one additional step. -/
noncomputable def fairBitEvolve {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) :
    ℕ → (Fin D → ℝ) → (Fin D → ℝ)
  | 0, p => p
  | n + 1, p => fairBitEvolve E β k n (fairBitStep E β k p)

/-- A natural-number ledger recording energy measurements, controlled powers, inverse-QFT gates,
proposal gates, coin bits, and peak quantum and classical space for a run. -/
structure GibbsRunLedger where

  energyMeasurements : ℕ

  controlledPowers : ℕ

  inverseQftGates : ℕ

  proposalGates : ℕ

  coinBits : ℕ

  quantumPeak : ℕ

  classicalPeak : ℕ

end StageBGIBBSMETROPOLIS
end Qatlib.Papers.QMetropolis11.GibbsMixing
