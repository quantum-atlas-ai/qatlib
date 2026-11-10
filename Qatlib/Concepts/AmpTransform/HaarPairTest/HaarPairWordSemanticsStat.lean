/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairDefs
set_option warningAsError false

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
