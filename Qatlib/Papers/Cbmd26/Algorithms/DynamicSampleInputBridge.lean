/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicFreshRegisterBridge
import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDParameters

/-!
# Normalized dynamic samples from an original encoding

The identity `sampleAncillaFrame_eq` relates the padded sample frame to the standard encoding
fiber. An exact original encoding of `L + iH` bounds `H + sL`, and
`dynamic_padded_sample_encoding` supplies its normalized projected unitary encoding on the
dynamic sample registers. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `original_first_order_norm_bound`: bounds the first-order Hermitian sample.
* `dynamic_padded_sample_encoding`: gives its normalized projected unitary encoding.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator
variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]
local instance cbmdDynamicSampleInputBridgeInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))

/-- Reindexing the doubly false-tagged original ancilla frame gives the encoding fiber at
`(false, false, a₀)`. -/
theorem sampleAncillaFrame_eq (a₀ : Anc) :
    reindexFrame (sampleAncillaEquiv Anc I)
      (tagFrame false (tagFrame false (tagFrame a₀ (1 : Matrix I I ℂ)))) =
    encodingFiber ((false,false,a₀) : DynamicSampleAnc Anc) := by
  ext ⟨⟨p,c,a⟩,i⟩ j
  by_cases hp : p = false <;> by_cases hc : c = false <;>
    by_cases ha : a = a₀ <;> by_cases hi : i = j <;>
    simp [reindexFrame, sampleAncillaEquiv, tagFrame, encodingFiber_apply, Matrix.one_apply, hp,
        hc, ha, hi]

/-- An exact block encoding of `L + iH` with Hermitian components bounds `‖H + sL‖` by `α * sqrt
(1 + s²)`. -/
theorem original_first_order_norm_bound
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix (Anc × I) (Anc × I) ℂ) (a₀ : Anc) (α s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0) :
    ‖H + (s : ℂ) • L‖ ≤ α * Real.sqrt (1 + s^2) := by
  have he := original_oracle_first_order_blockEncoding L H hL hH U
    (tagFrame a₀ (1 : Matrix I I ℂ)) α 0 s henc
  simp only [zero_mul] at he
  exact exact_blockEncoding_norm_bound _ _ _ _ he

/-- An exact original encoding and the sample normalization bound give a projected unitary
encoding of `(H + sL) / Λ` on the clean dynamic sample ancilla fiber. -/
theorem dynamic_padded_sample_encoding
    (L H : Matrix I I ℂ) (hL : L.IsHermitian) (hH : H.IsHermitian)
    (U : Matrix (Anc × I) (Anc × I) ℂ) (a₀ : Anc) (α Λ s : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0)
    (hbound : α * Real.sqrt (1 + s^2) ≤ Λ) :
    ProjectedUnitaryEncoding ((Λ : ℂ)⁻¹ • (H + (s : ℂ) • L))
      ((paddedFirstOrderInputUnitary U α Λ s).submatrix
        (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I))
      (encodingFiber ((false,false,a₀) : DynamicSampleAnc Anc))
      (encodingFiber ((false,false,a₀) : DynamicSampleAnc Anc)) := by
  have he := commonNormalization_blockEncoding _ _ _ _ Λ _
    (original_oracle_first_order_blockEncoding L H hL hH U
      (tagFrame a₀ (1 : Matrix I I ℂ)) α 0 s henc) hbound
  have hr := reindexWorkspace_blockEncoding (sampleAncillaEquiv Anc I) _ _ _ _ _ he
  rw [sampleAncillaFrame_eq] at hr
  simp only [zero_mul] at hr
  have hn := exact_blockEncoding_normalized hr
  have hs : (Λ⁻¹ : ℝ) • (H + (s : ℂ) • L) = (Λ : ℂ)⁻¹ • (H + (s : ℂ) • L) := by
    ext i j
    simp [Complex.real_smul, mul_add]
  rw [hs] at hn
  exact hn

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
