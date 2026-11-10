/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximateQSVTBridge
import Qatlib.Foundations.CbmdAnalysis.Core.WaveBesselODE
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem scalar_power_term_spectral (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (c b : ℂ) (n : ℕ) :
    c • (b • A) ^ n = spectralDiagonal (orderedHermitianBasis hA)
      (fun i => c * (b * (orderedHermitianValues hA i : ℂ)) ^ n) := by
  have h := aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A _
    (orderedHermitianBasis_action hA) (C c * (C b * X) ^ n)
  simpa only [map_mul, map_pow, aeval_C, aeval_X, eval_mul, eval_pow, eval_C,
    eval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using h

theorem hermitian_scalar_series (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (c : ℕ → ℂ) (b : ℂ)
    (hc : ∀ i, Summable (fun n => c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n)) :
    hermitianFunction A hA (fun x => ∑' n : ℕ, c n * (b * (x : ℂ)) ^ n) =
      ∑' n : ℕ, c n • (b • A) ^ n := by
  let L : (Fin (Fintype.card I) → ℂ) →ₗ[ℂ] Matrix I I ℂ :=
    { toFun := spectralDiagonal (orderedHermitianBasis hA)
      map_add' := fun f g => by
        simp only [spectralDiagonal]
        have hd : Matrix.diagonal (f + g) = Matrix.diagonal f + Matrix.diagonal g := by
          exact (Matrix.diagonal_add f g).symm
        rw [hd, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c f => by simp [spectralDiagonal, Matrix.diagonal_smul,
        Matrix.mul_smul, Matrix.smul_mul] }
  have hs : Summable (fun n : ℕ => fun i : Fin (Fintype.card I) =>
      c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n) := Pi.summable.mpr hc
  have h := L.toContinuousLinearMap.map_tsum hs
  change spectralDiagonal (orderedHermitianBasis hA) (∑' n : ℕ, fun i =>
      c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n) = _ at h
  have hfun : (∑' n : ℕ, fun i : Fin (Fintype.card I) =>
      c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n) =
      fun i => ∑' n : ℕ, c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n := by
    funext i
    exact Pi.tsum_apply hs
  rw [hfun] at h
  change hermitianFunction A hA (fun x => ∑' n : ℕ, c n * (b * (x : ℂ)) ^ n) =
    ∑' n : ℕ, spectralDiagonal (orderedHermitianBasis hA)
      (fun i => c n * (b * (orderedHermitianValues hA i : ℂ)) ^ n) at h
  rw [h]
  apply tsum_congr
  intro n
  exact (scalar_power_term_spectral I A hA (c n) b n).symm

theorem wave_hermitian_function_eq_series (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (b t : ℂ) :
    hermitianFunction A hA (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator (b * (x : ℂ)) t) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator (b • A) t := by
  have h := hermitian_scalar_series I A hA
    (fun n => ((2 * n).factorial : ℂ)⁻¹) (-(t ^ 2) * b) (fun i => by
      simpa only [smul_eq_mul, mul_assoc] using
        _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_series_summable (b * (orderedHermitianValues hA i : ℂ)) t)
  simpa only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator, smul_eq_mul,
      smul_smul, mul_assoc] using h

theorem bessel_hermitian_function_eq_series (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (b t : ℂ) :
    hermitianFunction A hA (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator (b * (x : ℂ)) t) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator (b • A) t := by
  have h := hermitian_scalar_series I A hA
    (fun n => ((n.factorial : ℂ)⁻¹) ^ 2) ((-(t ^ 2) / 4) * b) (fun i => by
      simpa only [smul_eq_mul, mul_assoc] using
        _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.bessel_series_summable (b * (orderedHermitianValues hA i : ℂ)) t)
  simpa only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator, smul_eq_mul,
      smul_smul, mul_assoc] using h

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
