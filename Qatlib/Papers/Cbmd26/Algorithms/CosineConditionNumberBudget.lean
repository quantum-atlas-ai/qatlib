/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.CosineOutputQueryBudget
import Qatlib.Papers.Cbmd26.Algorithms.SeparateOracleBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

section Spectrum
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

def matrixLeastEigenvalueIndex : Fin (Fintype.card I) :=
  ⟨Fintype.card I - 1, Nat.sub_lt Fintype.card_pos (by norm_num)⟩

def matrixLeastEigenvalue {A : Matrix I I ℂ} (hA : A.IsHermitian) : ℝ :=
  orderedHermitianValues hA (matrixLeastEigenvalueIndex (I := I))

theorem matrixLeastEigenvalue_is_min {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (∃ i, orderedHermitianValues hA i = matrixLeastEigenvalue hA) ∧
      ∀ i, matrixLeastEigenvalue hA ≤ orderedHermitianValues hA i := by
  refine ⟨⟨matrixLeastEigenvalueIndex, rfl⟩, ?_⟩
  intro i
  apply hA.eigenvalues₀_antitone
  change i.val ≤ Fintype.card I - 1
  have := i.isLt
  omega

theorem matrixLeastEigenvalue_lower {A : Matrix I I ℂ} (hA : A.IsHermitian)
    {μ : ℝ} (hlower : (A - μ • (1 : Matrix I I ℂ)).PosSemidef) :
    μ ≤ matrixLeastEigenvalue hA :=
  orderedHermitianValues_lower_of_posSemidef A hA μ hlower _

theorem matrixLeastEigenvalue_le_norm {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    matrixLeastEigenvalue hA ≤ ‖A‖ := by
  let i := matrixLeastEigenvalueIndex (I := I)
  have hb := Matrix.l2_opNorm_mulVec A (orderedHermitianBasis hA i)
  change ‖A.toEuclideanLin (orderedHermitianBasis hA i)‖ ≤ _ at hb
  rw [orderedHermitianBasis_action, norm_smul, (orderedHermitianBasis hA).norm_eq_one,
    mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb

def matrixTrueConditionMax {L H : Matrix I I ℂ}
    (hL : L.IsHermitian) (hH : H.IsHermitian) : ℝ :=
  max (‖L‖ / matrixLeastEigenvalue hL) (‖H‖ / matrixLeastEigenvalue hH)

theorem matrixTrueConditionMax_ge_one {L H : Matrix I I ℂ}
    (hL : L.IsHermitian) (hH : H.IsHermitian) {μ : ℝ} (hμ : 0 < μ)
    (hLlow : (L - μ • (1 : Matrix I I ℂ)).PosSemidef) :
    1 ≤ matrixTrueConditionMax hL hH := by
  have hp := hμ.trans_le (matrixLeastEigenvalue_lower hL hLlow)
  exact ((one_le_div hp).mpr (matrixLeastEigenvalue_le_norm hL)).trans (le_max_left _ _)

end Spectrum

theorem estimated_condition_max_le_true {βL βH μL μH ellL ellH c : ℝ}
    (hβL : 0 ≤ βL) (hβH : 0 ≤ βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hL : μL ≤ ellL) (hH : μH ≤ ellH) (hLc : ellL ≤ c * μL) (hHc : ellH ≤ c * μH)
    (hc : 1 ≤ c) :
    max (βL / ellL) (βH / ellH) ≤ max (βL / μL) (βH / μH) ∧
      max (βL / μL) (βH / μH) ≤ c * max (βL / ellL) (βH / ellH) := by
  have hc0 : 0 ≤ c := by linarith
  have hellL := hμL.trans_le hL
  have hellH := hμH.trans_le hH
  constructor
  · exact max_le_max (div_le_div_of_nonneg_left hβL hμL hL)
      (div_le_div_of_nonneg_left hβH hμH hH)
  · have hiL : 1 / μL ≤ c / ellL := (div_le_div_iff₀ hμL hellL).mpr (by simpa using! hLc)
    have hiH : 1 / μH ≤ c / ellH := (div_le_div_iff₀ hμH hellH).mpr (by simpa using! hHc)
    have hl : βL / μL ≤ c * (βL / ellL) := by
      convert! mul_le_mul_of_nonneg_left hiL hβL using 1 <;> ring
    have hh : βH / μH ≤ c * (βH / ellH) := by
      convert! mul_le_mul_of_nonneg_left hiH hβH using 1 <;> ring
    exact max_le (hl.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0))
      (hh.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0))

theorem matrix_condition_estimate {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {L H : Matrix I I ℂ} (hL : L.IsHermitian) (hH : H.IsHermitian)
    {μL μH c : ℝ} (hμL : 0 < μL) (hμH : 0 < μH)
    (hLlow : (L - μL • (1 : Matrix I I ℂ)).PosSemidef)
    (hHlow : (H - μH • (1 : Matrix I I ℂ)).PosSemidef)
    (hLc : matrixLeastEigenvalue hL ≤ c * μL)
    (hHc : matrixLeastEigenvalue hH ≤ c * μH) (hc : 1 ≤ c) :
    matrixTrueConditionMax hL hH ≤ max (‖L‖ / μL) (‖H‖ / μH) ∧
      max (‖L‖ / μL) (‖H‖ / μH) ≤ c * matrixTrueConditionMax hL hH :=
  estimated_condition_max_le_true (norm_nonneg _) (norm_nonneg _) hμL hμH
    (matrixLeastEigenvalue_lower hL hLlow) (matrixLeastEigenvalue_lower hH hHlow) hLc hHc hc

theorem condition_affine_factor_le {κ : ℝ} (hκ : 1 ≤ κ) :
    5 + 2048 * κ ≤ 2053 * κ := by linarith

theorem cosineDisplayedDegreeBound_condition_compare
    {L H γ τ ε η κestimated κtrue c : ℝ}
    (_hL : 0 ≤ L) (_hH : 0 ≤ H) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hη : 0 < η) (hc : 1 ≤ c) (hκ : κestimated ≤ c * κtrue) :
    cosineDisplayedDegreeBound L H γ τ ε η κestimated ≤
      c * cosineDisplayedDegreeBound L H γ τ ε η κtrue := by
  have hlog : 0 ≤ Real.log (2 + γ * τ^2) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hR : 0 ≤ cosineRelativeEnvelope γ τ η := by unfold cosineRelativeEnvelope; positivity
  have hlog' : 0 ≤ Real.log
      (2 + 1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2) / ε) := by
    apply Real.log_nonneg
    have : 0 ≤ 1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2) / ε := by positivity
    linarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 ≤ (τ * Real.sqrt (2 * cosineSelectedBmax L H γ τ ε η) +
      Real.log (2 + 1024 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2) / ε)) /
      Real.log 2 + 1 := by positivity
  have hf : 5 + 2048 * κestimated ≤ c * (5 + 2048 * κtrue) := by nlinarith
  unfold cosineDisplayedDegreeBound
  convert! mul_le_mul_of_nonneg_left hf hb using 1
  ring

theorem cosineDisplayedSourceBound_condition_compare
    {L H γ τ ε η κestimated κtrue c : ℝ}
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hη : 0 < η) (hc : 1 ≤ c) (hκ : κestimated ≤ c * κtrue) :
    (112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2)) *
      (8 * cosineDisplayedDegreeBound L H γ τ ε η κestimated + 2) ≤
      c * ((112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2)) *
        (8 * cosineDisplayedDegreeBound L H γ τ ε η κtrue + 2)) := by
  have hd := cosineDisplayedDegreeBound_condition_compare hL hH hγ hτ hε hη hc hκ
  have hq : 8 * cosineDisplayedDegreeBound L H γ τ ε η κestimated + 2 ≤
      c * (8 * cosineDisplayedDegreeBound L H γ τ ε η κtrue + 2) := by nlinarith
  have hlog : 0 ≤ Real.log (2 + γ * τ^2) := Real.log_nonneg (by nlinarith [sq_nonneg τ])
  have hR : 0 ≤ cosineRelativeEnvelope γ τ η := by unfold cosineRelativeEnvelope; positivity
  have hb := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ 112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ^2) by positivity)
  convert! hb using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
