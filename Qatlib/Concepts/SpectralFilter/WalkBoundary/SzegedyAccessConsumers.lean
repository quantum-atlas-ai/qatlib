/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess

/-!
# Counted Szegedy access and a periodic endpoint

This module transfers a discriminant rotation-plane statement to a counted Szegedy circuit and
constructs explicit preparation access for the deterministic two-state flip chain. The example
specializes the quantized-walk framework of [Szegedy2004].

`periodicFlipPreparation` prepares the row-isometry columns, and the associated Szegedy walk and
counted implementation evaluate to the identity. The syntactic word still has four queries and
four gates.

## Main statements

* `counted_szegedy_existing_plane_consumer`: the counted walk action on a discriminant rotation
  plane.
* `counted_szegedy_periodic_endpoint_actual_consumer`: preparation and identity-walk properties
  of the periodic example.
* `counted_szegedy_periodic_endpoint_costs`: exact costs of its counted word.

## References

* [Szegedy, 2004][Szegedy2004]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.SpectralFilter.WalkBoundary

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open scoped Classical BigOperators

/-- A normalized real discriminant eigenvector with eigenvalue `cos θ` and nonzero `sin θ` gives
orthonormal states on which the counted walk sends the first state to the rotation
combination with angle `2*θ`. -/
theorem counted_szegedy_existing_plane_consumer {I : Type*} [Fintype I] [DecidableEq I] :
    ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ) (v : I → ℝ) (θ : ℝ),
    IsTransitionMatrix P → U ∈ Matrix.unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i) →
    (∑ i, (v i)^2)=1 → Real.sin θ≠0 → SzegedyDiscriminant P *ᵥ v = Real.cos θ • v →
    ∃ w₀ w₁ : QState (I × I), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁=0 ∧
      evaluate U (countedSzegedyWord j) *ᵥ w₀ =
        ((Real.cos (2*θ):ℂ) • w₀ + (Real.sin (2*θ):ℂ) • w₁) := by
  intro P j U v θ hP hU hprep hv hs hvD
  rw [counted_szegedy_actual_walk_semantics P j U hP hU hprep]
  obtain ⟨w₀, w₁, hn₀, hn₁, horth, hrot, -⟩ := szegedy_spectral_map P hP v hv θ hs hvD
  exact ⟨w₀, w₁, hn₀, hn₁, horth, hrot⟩

/-- The deterministic transition matrix that flips a Boolean state at every step. -/
def periodicFlipTransition : Bool → Bool → ℝ :=
  fun a b => if b = !a then 1 else 0

/-- The pair permutation sending `(a,b)` to `(a,b xor not a)`. -/
def periodicFlipPerm : Bool × Bool → Bool × Bool :=
  fun p => (p.1, p.2 ^^ (!p.1))

/-- The pair permutation `periodicFlipPerm` is an involution. -/
theorem periodicFlipPerm_invol : Function.Involutive periodicFlipPerm := by
  intro p
  obtain ⟨a, b⟩ := p
  fin_cases a <;> fin_cases b <;> simp [periodicFlipPerm]

/-- The permutation matrix implementing `periodicFlipPerm`. -/
noncomputable def periodicFlipPreparation : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  permMatrix periodicFlipPerm

/-- The periodic flip preparation matrix is unitary. -/
theorem periodicFlipPreparation_unitary :
    periodicFlipPreparation ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  permMatrix_unitary periodicFlipPerm_invol

/-- The periodic flip preparation sends each basis ket to the ket of its permuted index. -/
theorem periodicFlipPreparation_mulVec_ket (q : Bool × Bool) :
    periodicFlipPreparation *ᵥ Ket q = Ket (periodicFlipPerm q) :=
  applyGate_permMatrix_ket periodicFlipPerm_invol q

/-- The periodic flip preparation equals its conjugate transpose. -/
theorem periodicFlipPreparation_conjTranspose :
    periodicFlipPreparationᴴ = periodicFlipPreparation :=
  permMatrix_conjTranspose periodicFlipPerm_invol

/-- The deterministic Boolean flip matrix is a transition matrix. -/
theorem periodicFlipTransition_isTransition : IsTransitionMatrix periodicFlipTransition := by
  refine ⟨fun x y => by by_cases h : y = !x <;> simp [periodicFlipTransition, h], fun x => ?_⟩
  fin_cases x <;> simp [periodicFlipTransition]

/-- The Szegedy isometry of the flip chain sends `Ket i` to `Ket (i, not i)`. -/
theorem szegedyIsometry_periodicFlip_col (i : Bool) :
    SzegedyIsometry periodicFlipTransition *ᵥ Ket i = Ket (i, !i) := by
  funext p
  obtain ⟨a, b⟩ := p
  rw [mulVec_ket_column]
  simp only [SzegedyIsometry, Matrix.of_apply]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [periodicFlipTransition, Real.sqrt_one, Real.sqrt_zero, Ket]

/-- With the second register initialized to false, the periodic flip preparation produces each
column of the Szegedy isometry. -/
theorem periodicFlipPreparation_prepares :
    ∀ i : Bool, periodicFlipPreparation *ᵥ TensorState (Ket i) (Ket false)
      = SzegedyIsometry periodicFlipTransition *ᵥ Ket i := by
  intro i
  rw [tensorState_ket_ket, periodicFlipPreparation_mulVec_ket,
    szegedyIsometry_periodicFlip_col]
  fin_cases i <;> rfl

/-- The adjoint Szegedy isometry sends the supported flip-pair ket back to its input ket. -/
theorem szegedyIsometry_periodicFlip_conjTranspose_col (i : Bool) :
    (SzegedyIsometry periodicFlipTransition)ᴴ *ᵥ Ket (i, !i) = Ket i := by
  funext k
  rw [conjTranspose_mulVec_ket_apply]
  simp only [SzegedyIsometry, Matrix.of_apply]
  fin_cases i <;> fin_cases k <;>
    simp [periodicFlipTransition, Real.sqrt_one, Ket]

/-- The adjoint Szegedy isometry annihilates each equal-pair basis ket. -/
theorem szegedyIsometry_periodicFlip_conjTranspose_anti (i : Bool) :
    (SzegedyIsometry periodicFlipTransition)ᴴ *ᵥ Ket (i, i) = 0 := by
  funext k
  rw [conjTranspose_mulVec_ket_apply]
  simp only [SzegedyIsometry, Matrix.of_apply]
  fin_cases i <;> fin_cases k <;>
    simp [periodicFlipTransition, Real.sqrt_zero]

/-- The Szegedy reflection fixes each supported flip-pair basis ket. -/
theorem szegedyReflection_periodicFlip_fix (i : Bool) :
    SzegedyReflection periodicFlipTransition *ᵥ Ket (i, !i) = Ket (i, !i) := by
  refine applyGate_reflectionAbout_of_fixed ?_
  show (SzegedyIsometry periodicFlipTransition
      * (SzegedyIsometry periodicFlipTransition)ᴴ) *ᵥ Ket (i, !i) = _
  rw [← Matrix.mulVec_mulVec, szegedyIsometry_periodicFlip_conjTranspose_col,
    szegedyIsometry_periodicFlip_col]

/-- The Szegedy reflection negates each equal-pair basis ket. -/
theorem szegedyReflection_periodicFlip_neg (i : Bool) :
    SzegedyReflection periodicFlipTransition *ᵥ Ket (i, i) = -(Ket (i, i)) := by
  refine applyGate_reflectionAbout_of_zero ?_
  show (SzegedyIsometry periodicFlipTransition
      * (SzegedyIsometry periodicFlipTransition)ᴴ) *ᵥ Ket (i, i) = _
  rw [← Matrix.mulVec_mulVec, szegedyIsometry_periodicFlip_conjTranspose_anti,
    Matrix.mulVec_zero]

/-- Collect the transition and preparation properties of the periodic flip example, prove that
its walk and counted implementation equal the identity, and show that the adjoint row
isometry annihilates `Ket (false,false)`. -/
theorem counted_szegedy_periodic_endpoint_actual_consumer :
    (∀ a b : Bool, periodicFlipTransition a b = if b = !a then 1 else 0) ∧
    periodicFlipPreparation ∈ Matrix.unitaryGroup (Bool × Bool) ℂ ∧
    (∀ i, periodicFlipPreparation *ᵥ TensorState (Ket i) (Ket false)
      = SzegedyIsometry periodicFlipTransition *ᵥ Ket i) ∧
    SzegedyWalk periodicFlipTransition = 1 ∧
    evaluate periodicFlipPreparation (countedSzegedyWord false) = 1 ∧
    (SzegedyIsometry periodicFlipTransition)ᴴ *ᵥ Ket (false, false) = 0 := by
  have hwalk : SzegedyWalk periodicFlipTransition = 1 := by
    refine matrix_eq_of_forall_mulVec_ket fun q => ?_
    obtain ⟨i, b⟩ := q
    have rfix : ∀ k : Bool, SzegedyReflection periodicFlipTransition *ᵥ Ket (k, !k)
        = Ket (k, !k) := szegedyReflection_periodicFlip_fix
    have rneg : ∀ k : Bool, SzegedyReflection periodicFlipTransition *ᵥ Ket (k, k)
        = -(Ket (k, k)) := szegedyReflection_periodicFlip_neg
    have sw : ∀ p : Bool × Bool, SwapGate *ᵥ Ket p = Ket (Prod.swap p) :=
      applyGate_permMatrix_ket Prod.swap_swap
    have c00 : SwapGate *ᵥ Ket (false, false) = Ket (false, false) := sw _
    have c01 : SwapGate *ᵥ Ket (false, true) = Ket (true, false) := sw _
    have c10 : SwapGate *ᵥ Ket (true, false) = Ket (false, true) := sw _
    have c11 : SwapGate *ᵥ Ket (true, true) = Ket (true, true) := sw _
    have f01 : SzegedyReflection periodicFlipTransition *ᵥ Ket (false, true)
        = Ket (false, true) := rfix false
    have f10 : SzegedyReflection periodicFlipTransition *ᵥ Ket (true, false)
        = Ket (true, false) := rfix true
    have n00 : SzegedyReflection periodicFlipTransition *ᵥ Ket (false, false)
        = -(Ket (false, false)) := rneg false
    have n11 : SzegedyReflection periodicFlipTransition *ᵥ Ket (true, true)
        = -(Ket (true, true)) := rneg true
    simp only [SzegedyWalk, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    fin_cases i <;> fin_cases b <;> first
    | rw [n00, Matrix.mulVec_neg, c00, Matrix.mulVec_neg, n00, neg_neg, c00]
    | rw [f01, c01, f10, c10]
    | rw [f10, c10, f01, c01]
    | rw [n11, Matrix.mulVec_neg, c11, Matrix.mulVec_neg, n11, neg_neg, c11]
  refine ⟨fun a b => rfl, periodicFlipPreparation_unitary,
    periodicFlipPreparation_prepares, hwalk, ?_, ?_⟩
  · rw [counted_szegedy_actual_walk_semantics periodicFlipTransition false
      periodicFlipPreparation periodicFlipTransition_isTransition
      periodicFlipPreparation_unitary periodicFlipPreparation_prepares, hwalk]
  · funext k
    rw [conjTranspose_mulVec_ket_apply]
    simp only [SzegedyIsometry, Matrix.of_apply]
    fin_cases k <;>
      simp [periodicFlipTransition, Real.sqrt_zero]

/-- The periodic flip counted word evaluates to the identity while retaining four queries and
four gates. -/
theorem counted_szegedy_periodic_endpoint_costs :
    evaluate periodicFlipPreparation (countedSzegedyWord false) = 1 ∧
    adjointQueryCount (countedSzegedyWord false) = 4 ∧
    adjointGateCount (countedSzegedyWord false) = 4 :=
  ⟨counted_szegedy_periodic_endpoint_actual_consumer.2.2.2.2.1,
    (counted_szegedy_actual_word_and_counts false).2.1,
    (counted_szegedy_actual_word_and_counts false).2.2⟩

end Qatlib.Concepts.SpectralFilter.WalkBoundary
