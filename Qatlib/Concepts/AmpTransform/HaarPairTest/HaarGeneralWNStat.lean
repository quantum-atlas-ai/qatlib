/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarPairDefs
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Specification of general Haar pair readout

This module defines dyadic preparation, its seed, and an optional orientation readout that
returns no result when M = 0. `HaarGeneralWN` states preparation, circuit counts, success
bounds, and invariance under orientation-preserving unitary tails in the amplified Haar setting
of [Cornwell2014].

## Main statements

* `haarDyadicPreparation`: The tensor product of the (n−1)-qubit Hadamard transform and a
  one-qubit Hadamard, acting on the pair-index and orientation registers.
* `haarSourceReadout`: The Boolean orientation as an optional result, returning `none` when M =
  0.
* `HaarGeneralWN`: The general dyadic Haar-pair contract: uniform preparation, exact circuit
  counts, amplified orientation probabilities, the empty-set readout, and invariance under
  Boolean-sector unitary transformations.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
set_option autoImplicit false
open Qatlib.Concepts.SearchStopping.KnownCount Qatlib.Concepts.PhaseGeometry.Phase Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.HaarPairTest

/-- The tensor product of the (n−1)-qubit Hadamard transform and a one-qubit Hadamard, acting on
the pair-index and orientation registers. -/
noncomputable def haarDyadicPreparation (n : ℕ) :
    Matrix (Reg (n-1) × Bool) (Reg (n-1) × Bool) ℂ :=
  TensorGate (HadamardN (n-1)) Hadamard

/-- The all-zero pair-register seed `(ZeroStr (n-1), false)`. -/
def haarDyadicSeed (n : ℕ) : Reg (n-1) × Bool := (ZeroStr (n-1), false)

/-- The Boolean orientation as an optional result, returning `none` when M = 0. -/
def haarSourceReadout {I : Type} (M : ℕ) (z : I × Bool) : Option Bool :=
  if M = 0 then none else some z.2

/-- The general dyadic Haar-pair contract: uniform preparation, exact circuit counts, amplified
orientation probabilities, the empty-set readout, and invariance under Boolean-sector
unitary transformations. -/
def HaarGeneralWN : Prop :=
  (∀ n : ℕ, 0 < n →
    let I := Reg (n-1)
    let T' := haarDyadicPreparation n
    let seed := haarDyadicSeed n
    T' ∈ Matrix.unitaryGroup (I × Bool) ℂ ∧ T' *ᵥ Ket seed = Uniform (I × Bool) ∧
    ∀ (M : ℕ) (θ : ℝ), 0 < θ → θ ≤ Real.pi/2 →
      (Real.sin θ)^2 = (M : ℝ)/(Fintype.card I : ℝ) →
    let k := Nat.floor (Real.pi/(4*θ))
    PreparedCircuitValid (aqHaarPairWord T' seed k) ∧
    preparedDataQueries (aqHaarPairWord T' seed k) = k ∧
    preparedInputQueries (aqHaarPairWord T' seed k) = 1 ∧
    preparedFixedGates (aqHaarPairWord T' seed k) = k+2 ∧
    ∀ E : Finset I, E.card = M → ∀ (S : I × Bool → Bool) (b : Bool),
    (∀ i ∈ E, (S (i,false) != S (i,true)) = b) →
    MeasureProb (aqHaarPairOutput T' seed k E S)
      (Finset.univ.filter (fun z => z.1 ∈ E ∧ z.2 = b)) =
      (Real.sin (((2*k+1 : ℕ) : ℝ)*θ))^2 ∧
    1-(M : ℝ)/(Fintype.card I : ℝ) ≤
      MeasureProb (aqHaarPairOutput T' seed k E S) (Finset.univ.filter (fun z => z.2 = b)) ∧
    (3*M ≤ Fintype.card I → (2/3 : ℝ) ≤
      MeasureProb (aqHaarPairOutput T' seed k E S) (Finset.univ.filter (fun z => z.2 = b)))) ∧
  (∀ n : ℕ, 0 < n → ∀ S : Reg (n-1) × Bool → Bool,
    let T' := haarDyadicPreparation n
    let seed := haarDyadicSeed n
    PreparedCircuitValid (aqHaarPairWord T' seed 0) ∧
    preparedDataQueries (aqHaarPairWord T' seed 0) = 0 ∧
    preparedInputQueries (aqHaarPairWord T' seed 0) = 1 ∧
    preparedFixedGates (aqHaarPairWord T' seed 0) = 2 ∧
    MeasureProb (aqHaarPairOutput T' seed 0 ∅ S)
      (Finset.univ.filter (fun z => haarSourceReadout 0 z = none)) = 1) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
    (U : Bool → Matrix I I ℂ), (∀ b, U b ∈ Matrix.unitaryGroup I ℂ) →
    ∀ (ψ : QState (I × Bool)) (b : Bool),
    let W : Matrix (I × Bool) (I × Bool) ℂ := fun i j =>
      if i.2 = j.2 then U i.2 i.1 j.1 else 0
    MeasureProb (W *ᵥ ψ) (Finset.univ.filter (fun z => z.2 = b)) =
      MeasureProb ψ (Finset.univ.filter (fun z => z.2 = b)))

end Qatlib.Concepts.AmpTransform.HaarPairTest
