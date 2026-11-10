/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitSourceContinuation
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualParameterRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDataFit12.SparseHHL

noncomputable def conciseTomographySettings (M : ℕ) : ℝ :=
  (M : ℝ) * Real.log (M + 1) ^ 2

noncomputable def conciseTomographyTotal (M f : ℕ) : ℝ :=
  conciseTomographySettings M * (f : ℝ)

def sparseFitHeadline (s κ : ℕ) : ℕ := s ^ 3 * κ ^ 6

def phaseRecoveryBitCount (bits : ℕ) : ℕ := bits + 1

def phaseRecoveryGateCount (bits : ℕ) : ℕ := bits

noncomputable def freshCopyTotalCost (k : ℕ) (p c : ℝ) : ℝ :=
  expectedFreshCopies k p * c

def conciseSelectionSamples (M' : ℕ) : ℕ := M'

noncomputable def fitHeadlineCost (N s κ : ℕ) (ε : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 * (κ : ℝ) ^ 6 / ε

noncomputable def simulationHeadlineCost (N s κ : ℕ) (ε : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) * (κ : ℝ) ^ 6 / ε ^ 2

noncomputable def readoutHeadlineCost (N s κ M' : ℕ) (ε δ : ℝ) : ℝ :=
  Real.log (N + 1) * (s : ℝ) ^ 3 *
    ((κ : ℝ) ^ 4 / (ε * δ ^ 2) + (M' : ℝ) ^ 2 * (κ : ℝ) ^ 6 / ε ^ 3)

def sparseFitQueryCost (M r k s κ : ℕ) : ℕ :=
  dataFitQueryLedger M r k * sparseFitHeadline s κ

noncomputable def freshCopyTotalCostFull (k : ℕ) (p g b c : ℝ) : ℝ :=
  expectedFreshCopies k p * (g + b + c)

end Qatlib.Papers.QDataFit12.SparseHHL
