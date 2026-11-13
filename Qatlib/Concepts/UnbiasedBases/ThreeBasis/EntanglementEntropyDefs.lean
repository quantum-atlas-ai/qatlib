/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.EntanglementDefs
import Qatlib.Concepts.QuantumEntropy.EntropyCalculus
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalUnitaryDiscard

/-!
# Reduced Density and Entanglement Entropy

This module defines the entanglement entropy of a normalized bipartite pure state as the von
Neumann entropy of its left reduced density matrix, using natural logarithms
[NielsenChuang2010]. The definition `reducedDensity` packages the partial trace of `outerProduct
ψ` as a density operator, and `entropy` applies the density-operator entropy to that marginal.

The bridge lemmas `reduced_state` and `entropy_eq_partial` identify these definitions with the
mixed-state representation obtained from the corresponding normalized ket. Thus the matrix
partial trace and mixed-state partial trace describe the same left subsystem.

## Main statements

- `reducedDensity` constructs the left density operator of a normalized bipartite state.
- `reducedDensity_val` exposes its underlying matrix as `PartialTrace (outerProduct ψ)`.
- `reduced_state` identifies the density with the pure mixed state's right partial trace.
- `entropy_eq_partial` identifies `entropy` with the von Neumann entropy of that marginal.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010] Michael A. Nielsen and Isaac L. Chuang, Quantum
  Computation and Quantum Information.
-/

set_option backward.isDefEq.respectTransparency false
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

/-- The density `reducedDensity ψ hψ` is the left reduced density operator of a normalized
bipartite pure state, formed by tracing its outer product over the right subsystem. -/
def reducedDensity (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.Density (Fin D) :=
  ⟨PartialTrace (outerProduct ψ),
    isDensityOperator_partialTrace (outerProduct_density hψ).1 (outerProduct_density hψ).2⟩

/-- The quantity `entropy ψ hψ` is the entanglement entropy of a normalized bipartite pure
state, defined as the von Neumann entropy of `reducedDensity ψ hψ` with natural logarithms. -/
def entropy (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) : ℝ :=
  Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy (reducedDensity ψ hψ)

/-- The matrix underlying `reducedDensity ψ hψ` is exactly `PartialTrace (outerProduct ψ)`. -/
@[simp] theorem reducedDensity_val (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    (reducedDensity ψ hψ).val = PartialTrace (outerProduct ψ) := rfl

/-- The mixed state associated to `reducedDensity ψ hψ` equals the right partial trace of the
pure mixed state associated to the normalized ket ψ. -/
theorem reduced_state (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state (reducedDensity ψ hψ) =
      (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceRight := by
  apply MState.ext_m
  simp only [Qatlib.Concepts.QuantumEntropy.EntropyCalculus.state_m, reducedDensity_val,
    ← Qatlib.Foundations.PureStateMath.BornBridge.partialTrace_mState, Qatlib.Foundations.PureStateMath.BornBridge.pure_normalizedStateEquivKet_m]
  rfl

/-- The entanglement entropy `entropy ψ hψ` is the von Neumann entropy of the right partial
trace of the pure mixed state associated to ψ. -/
theorem entropy_eq_partial (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    entropy ψ hψ =
      Sᵥₙ (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet _ ⟨ψ, hψ⟩)).traceRight := by
  unfold entropy Qatlib.Concepts.QuantumEntropy.EntropyCalculus.entropy
  rw [reduced_state]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis
