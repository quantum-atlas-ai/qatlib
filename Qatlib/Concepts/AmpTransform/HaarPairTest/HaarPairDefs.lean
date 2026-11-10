/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalTigh
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedQueryCircuit
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.GateCore

set_option autoImplicit false
namespace Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.SearchStopping.GateCore Matrix
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
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

def aqHaarPairMarked (E : Finset I) : Finset (I × Bool) :=
  Finset.univ.filter fun z => z.1 ∈ E

noncomputable def aqHaarPreparedOfStep : Step (I × Bool) → PreparedStep (I × Bool)
  | .gate U => .gate U
  | .query => .dataForward

noncomputable def aqHaarPairWord (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool) (j : ℕ) : List (PreparedStep (I × Bool)) :=
  [.gate (TensorGate (1 : Matrix I I ℂ) Hadamard), .prepareForward] ++
    ((SourceGateCircuit T' (Ket seed) j).reverse.map aqHaarPreparedOfStep) ++
    [.gate T']

noncomputable def aqHaarPairOutput (T' : Matrix (I × Bool) (I × Bool) ℂ)
    (seed : I × Bool) (j : ℕ) (E : Finset I) (S : I × Bool → Bool) : QState (I × Bool) :=
  evaluatePrepared (PhaseOracle (fun z => decide (z.1 ∈ E))) (PhaseOracle S)
    (aqHaarPairWord T' seed j) *ᵥ Ket seed

end Qatlib.Concepts.AmpTransform.HaarPairTest
