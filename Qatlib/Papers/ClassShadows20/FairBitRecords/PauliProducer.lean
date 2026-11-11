/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality

/-!
# ClassShadows20 · FairBitRecords · finite Pauli producer

This file records the finite tensor-Pauli producer used by the random-Pauli
shadow construction.  The producer is the actual Pauli-orbit POVM from the
shadow model: its effects have the exact trace `d⁻¹`, and its quadratic
measurement score agrees with the quadratic score of the input state.

The result is an exact finite measurement identity.  It does not model a
finite-gate implementation, fair-bit sampling, confidence amplification, or
the paper's global sample-complexity and SDP conclusions.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ClassShadows20.FairBitRecords

open Qatlib.Concepts.ShadowModels.ProductPOVM
open Qatlib.Foundations.FiniteStats.BornEstimator

open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Concepts.PauliClifford.PauliAlgebra

variable {V : Type*} [Fintype V]

/-- The finite tensor-Pauli producer has a normalized effect of trace `d⁻¹`
for every Pauli word, and its weighted quadratic measurement score is exactly
the corresponding quadratic score of the input state.  This is the exact
finite producer identity used by the random-Pauli shadow construction. -/
theorem source_pauli_measurement_producer
    (n : ℕ) (words : V → PauliWord n) (weights : V → ℝ)
    (ρ : MState (Reg n)) :
    (∀ q : PauliWord n,
      ((pauliOrbitPOVM n ρ).mats q).trace = (qubitDimension n)⁻¹) ∧
      measurementScore (fun i => pauliObservable n (words i)) weights
          (pauliOrbitPOVM n ρ) =
        quadraticScore (fun i => pauliObservable n (words i)) weights ρ := by
  refine ⟨?_, ?_⟩
  · intro q
    exact pauliOrbit_trace n ρ q
  · exact pauliOrbit_measurementScore n words weights ρ

end Qatlib.Papers.ClassShadows20.FairBitRecords
