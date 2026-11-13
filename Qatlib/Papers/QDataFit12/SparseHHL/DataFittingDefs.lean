/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitSourceContinuation
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedQuan

/-!
# Cost expressions for sparse quantum data fitting

This module defines resource expressions for concise tomography, sparse fitting, phase recovery,
selection, and repeated preparation of fresh copies. `fitHeadlineCost`,
`simulationHeadlineCost`, and `readoutHeadlineCost` record the explicit dimension, sparsity,
condition, and accuracy dependence used by subsequent inequalities. The mathematical context is
[WiebeBraunLloyd2012].

## Main statements

* `fitHeadlineCost`: The fitting cost expression `log (N+1) * s³κ⁶/ε`.
* `readoutHeadlineCost`: The readout cost expression `log (N+1) * s³ * (κ⁴/(εδ²) + M'²κ⁶/ε³)`.

## References

* [Wiebe et al., 2012][WiebeBraunLloyd2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL

/-- The real tomography-settings expression `M * log (M+1)²`. -/
noncomputable def conciseTomographySettings (M : ℕ) : ℝ :=
  (M : ℝ) * Real.log (M + 1) ^ 2

/-- The tomography-settings expression multiplied by the repetition factor `f`. -/
noncomputable def conciseTomographyTotal (M f : ℕ) : ℝ :=
  conciseTomographySettings M * (f : ℝ)

/-- The natural-number sparse-fitting factor `s³κ⁶`. -/
def sparseFitHeadline (s κ : ℕ) : ℕ := s ^ 3 * κ ^ 6

/-- The phase-recovery bit count `bits + 1`. -/
def phaseRecoveryBitCount (bits : ℕ) : ℕ := bits + 1

/-- The phase-recovery gate count `bits`. -/
def phaseRecoveryGateCount (bits : ℕ) : ℕ := bits

/-- The expected fresh-copy count for `k` successes at probability `p`, multiplied by per-copy
cost `c`. -/
noncomputable def freshCopyTotalCost (k : ℕ) (p c : ℝ) : ℝ :=
  expectedFreshCopies k p * c

/-- The concise-selection sample count equal to the selected support size `M'`. -/
def conciseSelectionSamples (M' : ℕ) : ℕ := M'

/-- The fitting cost expression `log (N+1) * s³κ⁶/ε`. -/
noncomputable def fitHeadlineCost (N s κ : ℕ) (ε : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6 / ε

/-- The simulation cost expression `log (N+1) * sκ⁶/ε²`. -/
noncomputable def simulationHeadlineCost (N s κ : ℕ) (ε : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6 / ε ^ 2

/-- The readout cost expression `log (N+1) * s³ * (κ⁴/(εδ²) + M'²κ⁶/ε³)`. -/
noncomputable def readoutHeadlineCost (N s κ M' : ℕ) (ε δ : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 *
    ((κ : ℝ) ^ 4 / (ε * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3)

/-- The product of the data-fitting query ledger and the sparse-fitting factor `s³κ⁶`. -/
def sparseFitQueryCost (M r k s κ : ℕ) : ℕ :=
  dataFitQueryLedger M r k * sparseFitHeadline s κ

/-- The expected fresh-copy count multiplied by the sum of cost components `g`, `b`, and `c`. -/
noncomputable def freshCopyTotalCostFull (k : ℕ) (p g b c : ℝ) : ℝ :=
  expectedFreshCopies k p * (g + b + c)

end Qatlib.Papers.QDataFit12.SparseHHL
