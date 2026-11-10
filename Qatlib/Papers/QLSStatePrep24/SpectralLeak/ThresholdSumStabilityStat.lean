/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.BandModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def Clause32ThresholdSumStability : Prop :=
  (∀ (I : Type) [Fintype I] (m l : ℕ) (γ : I → ℂ) (ζ : ℕ → I → ℂ), l ≤ m →
    let p := (normVec (weightedBandState m γ ζ))^2
    (l=0 → thresholdSum m l γ ζ=0) ∧
    (0 < l → p*(9 : ℝ)^l ≤ thresholdSum m l γ ζ ∧
      thresholdSum m l γ ζ ≤ (5/4)*p*(9 : ℝ)^l)) ∧
  ∀ (H : Type) [Fintype H] (l : ℕ) (εbm : ℝ)
    (ψ φ : Fin l → QState H), 0 ≤ εbm →
    (∀ j, normVec (ψ j) ≤ 1 ∧ normVec (φ j) ≤ 1 ∧ normVec (ψ j-φ j) ≤ 2*εbm) →
    |(∑ j : Fin l, (normVec (ψ j))^2*(9 : ℝ)^(j.val+1))-
      (∑ j : Fin l, (normVec (φ j))^2*(9 : ℝ)^(j.val+1))| ≤ (9/8)*4*εbm*(9 : ℝ)^l

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
