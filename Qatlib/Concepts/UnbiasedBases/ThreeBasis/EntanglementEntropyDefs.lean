/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalUnitaryDiscard
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open Qatlib
open scoped BigOperators

variable {D E : ℕ}

def reducedDensity (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.Density (Fin D) :=
  ⟨PartialTrace (outerProduct ψ),
    isDensityOperator_partialTrace (outerProduct_density hψ).1 (outerProduct_density hψ).2⟩

def entropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy (reducedDensity ψ hψ)

@[simp] theorem reducedDensity_val (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (reducedDensity ψ hψ).val = PartialTrace (outerProduct ψ) := rfl

theorem reduced_state (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (reducedDensity ψ hψ) =
      (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceRight := by
  apply MState.ext_m
  simp only [Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m, reducedDensity_val,
    ← Qatlib.Foundations.PureStateMath.BornBridge.partialTrace_mState, Qatlib.Foundations.PureStateMath.BornBridge.pure_normalizedStateEquivKet_m]
  rfl

theorem entropy_eq_partial (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    entropy ψ hψ =
      Sᵥₙ (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceRight := by
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [reduced_state]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
