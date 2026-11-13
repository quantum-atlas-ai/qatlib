/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairDefs

/-!
# Specification of Haar pair circuit semantics

`HaarPairWordSemantics` states the validity, query and gate counts, state formula, and
normalization of the prepared Haar-pair circuit. It connects the circuit encoding to the
amplified Haar-transform construction of [Cornwell2014].

## Main statements

* `HaarPairWordSemantics`: The Haar-pair circuit contract giving j data queries, one input
  query, j+2 fixed gates, validity, normalization, and the phase-queried Grover-state output
  formula.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SearchStopping.KnownCount

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- The Haar-pair circuit contract giving j data queries, one input query, j+2 fixed gates,
validity, normalization, and the phase-queried Grover-state output formula. -/
def HaarPairWordSemantics : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool), T' ∈ Matrix.unitaryGroup (I × Bool) ℂ →
    T' *ᵥ Ket seed = Uniform (I × Bool) → ∀ (j : ℕ),
    PreparedCircuitValid (aqHaarPairWord T' seed j) ∧
    preparedDataQueries (aqHaarPairWord T' seed j) = j ∧
    preparedInputQueries (aqHaarPairWord T' seed j) = 1 ∧
    preparedFixedGates (aqHaarPairWord T' seed j) = j + 2 ∧
    ∀ (E : Finset I) (S : I × Bool → Bool),
      aqHaarPairOutput T' seed j E S =
        (TensorGate (1 : Matrix I I ℂ) Hadamard) *ᵥ
          (PhaseOracle S *ᵥ GroverState (aqHaarPairMarked E) j) ∧
      Normalized (aqHaarPairOutput T' seed j E S)

end Qatlib.Concepts.AmpTransform.HaarPairTest
