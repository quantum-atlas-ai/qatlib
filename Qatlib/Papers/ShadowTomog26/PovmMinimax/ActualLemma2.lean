/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PauliScoreEquality
import Mathlib.Analysis.Convex.StdSimplex
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
variable {V : Type*} [Fintype V]

def Admissible (n : ℕ) (K : Set (MState (Reg n))) (P : POVM (PauliWord n) (Reg n)) : Prop :=
  ∀ q (hne : P.mats q≠0),normalizedEffect (P.mats q) (P.nonneg q) hne∈K

def actualMeasurementValue (n : ℕ) (words : V → PauliWord n) (w : V → ℝ) (K : Set (MState (Reg n))) : ℝ :=
  sSup (Set.range (fun P : {P : POVM (PauliWord n) (Reg n) // Admissible n K P} =>
    measurementScore (fun i => pauliObservable n (words i)) w P.val))

theorem orbit_normalized_state (n : ℕ) (ρ : MState (Reg n)) (q : PauliWord n)
    (hne : (pauliOrbitPOVM n ρ).mats q≠0) :
    normalizedEffect ((pauliOrbitPOVM n ρ).mats q) ((pauliOrbitPOVM n ρ).nonneg q) hne=
      pauliConjugateState n q ρ := by
  apply MState.ext_m
  have hm : (normalizedEffect ((pauliOrbitPOVM n ρ).mats q) ((pauliOrbitPOVM n ρ).nonneg q) hne).M=
      (pauliConjugateState n q ρ).M := by
    change (((pauliOrbitPOVM n ρ).mats q).trace)⁻¹ • (pauliOrbitPOVM n ρ).mats q=_
    rw [pauliOrbit_trace]
    change ((qubitDimension n)⁻¹)⁻¹ • ((qubitDimension n)⁻¹ • (pauliConjugateState n q ρ).M)=_
    rw [inv_inv,smul_smul,mul_inv_cancel₀ (qubitDimension_pos n).ne',one_smul]
  exact congrArg HermitianMat.mat hm

theorem orbit_admissible (n : ℕ) (K : Set (MState (Reg n)))
    (hK : ∀ q ρ,ρ∈K → pauliConjugateState n q ρ∈K) (ρ : MState (Reg n)) (hρ : ρ∈K) :
    Admissible n K (pauliOrbitPOVM n ρ) := by
  intro q hne
  rw [orbit_normalized_state]
  exact hK q ρ hρ

theorem actual_measurement_state_value (n : ℕ) (words : V → PauliWord n) (w : V → ℝ)
    (hw : ∀ i,0 ≤ w i) (K : Set (MState (Reg n))) (hKne : K.Nonempty)
    (hK : ∀ q ρ,ρ∈K → pauliConjugateState n q ρ∈K) :
    actualMeasurementValue n words w K=stateScoreValue (fun i => pauliObservable n (words i)) w K := by
  obtain ⟨ρ0,hρ0⟩ := hKne
  letI : Nonempty {P : POVM (PauliWord n) (Reg n) // Admissible n K P} :=
    ⟨⟨pauliOrbitPOVM n ρ0,orbit_admissible n K hK ρ0 hρ0⟩⟩
  have hb : BddAbove (Set.range (fun P : {P : POVM (PauliWord n) (Reg n) // Admissible n K P} =>
      measurementScore (fun i => pauliObservable n (words i)) w P.val)) := by
    refine ⟨stateScoreValue (fun i => pauliObservable n (words i)) w K,?_⟩
    rintro _ ⟨P,rfl⟩
    exact measurementScore_le_stateValue _ _ hw K P.val P.property
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨P,rfl⟩
    exact measurementScore_le_stateValue _ _ hw K P.val P.property
  · apply csSup_le (show (quadraticScore (fun i => pauliObservable n (words i)) w '' K).Nonempty from ⟨_,ρ0,hρ0,rfl⟩)
    rintro _ ⟨ρ,hρ,rfl⟩
    have h := le_csSup hb (Set.mem_range_self
      (⟨pauliOrbitPOVM n ρ,orbit_admissible n K hK ρ hρ⟩ : {P : POVM (PauliWord n) (Reg n) // Admissible n K P}))
    change measurementScore (fun i => pauliObservable n (words i)) w (pauliOrbitPOVM n ρ) ≤ _ at h
    rw [pauliOrbit_measurementScore] at h
    exact h

theorem actual_global_measurement_state_value (n : ℕ) (words : V → PauliWord n) (w : V → ℝ)
    (hw : ∀ i,0 ≤ w i) :
    actualMeasurementValue n words w Set.univ=stateScoreValue (fun i => pauliObservable n (words i)) w Set.univ :=
  actual_measurement_state_value n words w hw Set.univ ⟨MState.uniform,Set.mem_univ _⟩
    (fun _ _ _ => Set.mem_univ _)

theorem actual_lemma2_delta (n : ℕ) (words : V → PauliWord n)
    (K : Set (MState (Reg n))) (hKne : K.Nonempty)
    (hK : ∀ q ρ,ρ∈K → pauliConjugateState n q ρ∈K) :
    sInf ((fun w => actualMeasurementValue n words w K) '' stdSimplex ℝ V)=
      sInf ((fun w => stateScoreValue (fun i => pauliObservable n (words i)) w K) '' stdSimplex ℝ V) := by
  congr 1
  ext t
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,(actual_measurement_state_value n words w hw.1 K hKne hK).symm⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w,hw,actual_measurement_state_value n words w hw.1 K hKne hK⟩

end Qatlib.Papers.ShadowTomog26.PovmMinimax
