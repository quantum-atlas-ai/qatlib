/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def Clause7TightDirichletBounds : Prop :=
  (∀ (ρ : ℕ) (θ : ℝ), 3 ≤ ρ → 0 ≤ θ → ρ*θ ≤ Real.pi/2 →
    let D := if θ=0 then 1 else Real.sin (ρ*θ)/(ρ*Real.sin θ)
    1-(ρ : ℝ)^2*(Real.sin θ)^2/6 ≤ D ∧
    D ≤ 1-((4*Real.pi-8)/Real.pi^3)*(ρ : ℝ)^2*(Real.sin θ)^2) ∧
  (∀ c : ℝ, c < 1/6 → ∃ (ρ : ℕ) (θ : ℝ), 3 ≤ ρ ∧ 0 < θ ∧ ρ*θ ≤ Real.pi/2 ∧
    Real.sin (ρ*θ)/(ρ*Real.sin θ) < 1-c*(ρ : ℝ)^2*(Real.sin θ)^2) ∧
  (∀ c : ℝ, (4*Real.pi-8)/Real.pi^3 < c →
    ∃ (ρ : ℕ) (θ : ℝ), 3 ≤ ρ ∧ 0 < θ ∧ ρ*θ ≤ Real.pi/2 ∧
      1-c*(ρ : ℝ)^2*(Real.sin θ)^2 < Real.sin (ρ*θ)/(ρ*Real.sin θ)) ∧
  ∀ a : ℝ, 0 ≤ a → a ≤ 1 → gainLoss 3 a=1-(4/3)*a^2

end Qatlib.Concepts.QlsReadoutSpec.Amplification
