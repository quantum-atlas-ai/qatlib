/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Qatlib.Concepts.RiskEstimation.PopulationGap.GibbsMetropolisDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.QuantumGibbs
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.RiskEstimation.PopulationGap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing
namespace StageBGIBBSMETROPOLIS

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder

noncomputable def fairBitAccept (k : ℕ) (f : ℝ) : ℝ :=
  Qatlib.Concepts.RiskEstimation.PopulationGap.fairBitAcceptMass k f

noncomputable def fairBitGrid (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

noncomputable def fairBitBranchMass (k : ℕ) (f : ℝ) (b : Bool) : ℝ :=
  if b then fairBitAccept k f else 1 - fairBitAccept k f

noncomputable def fairBitKernel {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) :
    Fin D → Fin D → ℝ :=
  fun i j =>
    if i = j then 1 - ∑ j' ∈ (Finset.univ : Finset (Fin D)).erase i,
      fairBitAccept k (Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance E β i j') / (D : ℝ)
    else fairBitAccept k (Qatlib.Concepts.GibbsMetropolis.RationalBath.thermalAcceptance E β i j) / (D : ℝ)

noncomputable def fairBitStep {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ)
    (p : Fin D → ℝ) : Fin D → ℝ :=
  fun j => ∑ i, p i * fairBitKernel E β k i j

noncomputable def fairBitEvolve {D : ℕ} (E : Fin D → ℝ) (β : ℝ) (k : ℕ) :
    ℕ → (Fin D → ℝ) → (Fin D → ℝ)
  | 0, p => p
  | n + 1, p => fairBitEvolve E β k n (fairBitStep E β k p)

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
