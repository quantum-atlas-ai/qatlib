/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairDefs
set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
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

def HaarLocalDecision : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ (T' : Matrix (I × Bool) (I × Bool) ℂ) (seed : I × Bool),
    T' ∈ Matrix.unitaryGroup (I × Bool) ℂ → T' *ᵥ Ket seed = Uniform (I × Bool) →
    ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi / 2 →
    (Real.sin θ)^2 = (M : ℝ) / (Fintype.card I : ℝ) →
    let k := Nat.floor (Real.pi / (4 * θ))
    PreparedCircuitValid (aqHaarPairWord T' seed k) ∧
    preparedDataQueries (aqHaarPairWord T' seed k) = k ∧
    preparedInputQueries (aqHaarPairWord T' seed k) = 1 ∧
    preparedFixedGates (aqHaarPairWord T' seed k) = k + 2 ∧
    ∀ (E : Finset I), E.card = M → ∀ (S : I × Bool → Bool) (b : Bool),
    (∀ i ∈ E, (S (i, false) != S (i, true)) = b) →
    MeasureProb (aqHaarPairOutput T' seed k E S)
      (Finset.univ.filter fun z => z.1 ∈ E ∧ z.2 = b) = (Real.sin (((2*k+1 : ℕ) : ℝ)*θ))^2 ∧
    1 - (M : ℝ) / (Fintype.card I : ℝ) ≤
      MeasureProb (aqHaarPairOutput T' seed k E S) (Finset.univ.filter fun z => z.2 = b) ∧
    (3 * M ≤ Fintype.card I → (2/3 : ℝ) ≤
      MeasureProb (aqHaarPairOutput T' seed k E S) (Finset.univ.filter fun z => z.2 = b))

end Qatlib.Concepts.AmpTransform.HaarPairTest
