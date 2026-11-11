/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowTomog26.PovmMinimax.ActualLemma2
import Qatlib.Concepts.ShadowModels.ProductPOVM.ProductOptimum

/-!
# Product-effect POVMs and the block state optimum

This module specializes the Lemma 2 optimization in [XuEtAl2026] to a fixed partition of qubits.
`PhysicalProductPOVM` requires each effect to be a nonnegative multiple of a partition product
state, and `productMeasurementValue` takes the supremum over such Pauli-word-indexed POVMs.

The normalized-effect characterization reduces this optimization to `actualMeasurementValue` on
`partitionStates`. A maximizing product state exists, and its Pauli-orbit POVM dominates every
product-effect POVM with any specified finite outcome type.

## Main statements

* `physical_admissible_iff` and `productMeasurement_eq_actual` identify the two measurement
  formulations.
* `source_lemma2_product_value` and `source_lemma2_product_delta` identify measurement and
  product-state values.
* `source_lemma2_product_attained` constructs an optimizing product state and its orbit POVM.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ShadowTomog26.PovmMinimax
open scoped Classical BigOperators
open Qatlib.Concepts.ShadowModels.ProductPOVM
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.PureStateMath
variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] {N : ℕ} (sizes : J → ℕ)

/-- The supremum of the weighted Pauli measurement score over Pauli-word-indexed POVMs whose
effects are nonnegative multiples of product states across the specified qubit partition. -/
def productMeasurementValue (sites : Fin N ≃ Σ j,Fin (sizes j)) (words : V → PauliWord N) (w : V → ℝ) : ℝ :=
  sSup (Set.range (fun P : {P : POVM (PauliWord N) (Reg N) // PhysicalProductPOVM sizes sites P} =>
    measurementScore (fun i => pauliObservable N (words i)) w P.val))

/-- A Pauli-word-indexed POVM has product effects across the partition exactly when every
nonzero normalized effect belongs to `partitionStates sizes sites`. -/
theorem physical_admissible_iff (sites : Fin N ≃ Σ j,Fin (sizes j)) (P : POVM (PauliWord N) (Reg N)) :
    PhysicalProductPOVM sizes sites P ↔ Admissible N (partitionStates sizes sites) P :=
  ⟨fun h s hn => physical_product_normalized sizes sites P h s hn,
    fun h => normalized_product_physical sizes sites P h⟩

/-- The product-effect measurement supremum equals `actualMeasurementValue` for the set of
partition product states. -/
theorem productMeasurement_eq_actual (sites : Fin N ≃ Σ j,Fin (sizes j))
    (words : V → PauliWord N) (w : V → ℝ) :
    productMeasurementValue sizes sites words w=actualMeasurementValue N words w (partitionStates sizes sites) := by
  unfold productMeasurementValue actualMeasurementValue
  congr 1
  ext r
  constructor
  · rintro ⟨P,rfl⟩
    exact ⟨⟨P.val,(physical_admissible_iff sizes sites P.val).mp P.property⟩,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨⟨P.val,(physical_admissible_iff sizes sites P.val).mpr P.property⟩,rfl⟩

/-- For nonnegative weights, the product-effect measurement supremum equals the supremum of
weighted squared Pauli expectations over states that are products across the specified
partition [XuEtAl2026]. -/
theorem source_lemma2_product_value (sites : Fin N ≃ Σ j,Fin (sizes j))
    (words : V → PauliWord N) (w : V → ℝ) (hw : ∀ i,0 ≤ w i) :
    productMeasurementValue sizes sites words w=
      stateScoreValue (fun i => pauliObservable N (words i)) w (partitionStates sizes sites) := by
  rw [productMeasurement_eq_actual]
  exact actual_measurement_state_value N words w hw (partitionStates sizes sites)
    (partitionStates_nonempty sizes sites) (partitionStates_pauli_closed sizes sites)

/-- The simplex infimum of product-effect measurement values equals the simplex infimum of the
corresponding partition product-state values [XuEtAl2026]. -/
theorem source_lemma2_product_delta (sites : Fin N ≃ Σ j,Fin (sizes j)) (words : V → PauliWord N) :
    sInf ((fun w => productMeasurementValue sizes sites words w) '' stdSimplex ℝ V)=
      sInf ((fun w => stateScoreValue (fun i => pauliObservable N (words i)) w (partitionStates sizes sites)) '' stdSimplex ℝ V) := by
  congr 1
  ext r
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,(source_lemma2_product_value sizes sites words w hw.1).symm⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,source_lemma2_product_value sizes sites words w hw.1⟩

/-- For nonnegative weights, some partition product state maximizes the weighted squared Pauli
expectations, and its Pauli-orbit POVM has product effects. That orbit POVM has score at
least that of every product-effect POVM with the specified arbitrary finite outcome type
[XuEtAl2026]. -/
theorem source_lemma2_product_attained {Ω : Type*} [Fintype Ω]
    (sites : Fin N ≃ Σ j,Fin (sizes j)) (words : V → PauliWord N) (w : V → ℝ) (hw : ∀ i,0 ≤ w i) :
    ∃ ρ : ∀ j,MState (Reg (sizes j)),
      (∀ σ : ∀ j,MState (Reg (sizes j)),
        quadraticScore (fun i => pauliObservable N (words i)) w (partitionState sizes sites σ) ≤
          quadraticScore (fun i => pauliObservable N (words i)) w (partitionState sizes sites ρ)) ∧
      PhysicalProductPOVM sizes sites (pauliOrbitPOVM N (partitionState sizes sites ρ)) ∧
      ∀ P : POVM Ω (Reg N),PhysicalProductPOVM sizes sites P →
        measurementScore (fun i => pauliObservable N (words i)) w P ≤
          measurementScore (fun i => pauliObservable N (words i)) w (pauliOrbitPOVM N (partitionState sizes sites ρ)) := by
  obtain ⟨ρ,hρ⟩ := product_score_attained sizes sites (fun i => pauliObservable N (words i)) w
  have hvalue : stateScoreValue (fun i => pauliObservable N (words i)) w (partitionStates sizes sites)=
      quadraticScore (fun i => pauliObservable N (words i)) w (partitionState sizes sites ρ) := by
    apply le_antisymm
    · apply csSup_le
        (show (quadraticScore (fun i => pauliObservable N (words i)) w '' partitionStates sizes sites).Nonempty from
          ⟨_,partitionState sizes sites ρ,⟨ρ,rfl⟩,rfl⟩)
      rintro _ ⟨σ,⟨σj,rfl⟩,rfl⟩
      exact hρ σj
    · exact stateScore_le_value _ _ hw _ _ ⟨ρ,rfl⟩
  refine ⟨ρ,hρ,pauliOrbit_physical_product sizes sites ρ,?_⟩
  intro P hP
  rw [pauliOrbit_measurementScore]
  rw [← hvalue]
  exact measurementScore_le_stateValue _ _ hw _ P (physical_product_normalized sizes sites P hP)

end Qatlib.Papers.ShadowTomog26.PovmMinimax
