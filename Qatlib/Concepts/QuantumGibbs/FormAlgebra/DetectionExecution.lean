/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess

/-!
# Marked-event execution after row preparation

This module combines ideal row-state preparation with a marked phase reflection and computes the
resulting marked mass. It also bounds the marked-coordinate error of computed preparation and
packages legality and resource facts in `GeneralSourceDetectionAccount`, providing setup and
checking ingredients for the walk-search framework of [MagniezNayakRolandSantha2011].

## Main statements

* `generalDetectionExecution_exact`: The marked output mass is the marked transition-row mass.
* `generalDetectionExecution_amplitude_error`: An error bound for computed marked amplitudes.
* `clause5_complete`: The combined setup and marked-check account.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace DetectionExecution

open Matrix
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- The diagonal phase reflection negating the marked set is unitary. -/
theorem generalMarkedReflection_unitary {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    generalMarkedReflection S ∈ Matrix.unitaryGroup V ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simp only [Matrix.star_apply, generalMarkedReflection, Matrix.diagonal_apply,
        if_pos rfl]
      by_cases hx : x ∈ S <;> simp [hx]
    · intro k _ hk
      simp [Matrix.star_apply, generalMarkedReflection, Matrix.diagonal_apply, Ne.symm hk]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkx : k = x
    · subst hkx
      simp [Matrix.star_apply, generalMarkedReflection, Matrix.diagonal_apply, hxy,
        Ne.symm hxy]
    · simp [Matrix.star_apply, generalMarkedReflection, Matrix.diagonal_apply, hkx,
      Ne.symm hkx]

/-- The singleton marked-reflection word is a well-formed adjoint circuit. -/
theorem generalCheckWord_wellFormed {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    WellFormedAdjointCircuit (generalCheckWord S) := by
  intro W hW
  simp only [generalCheckWord, List.mem_singleton] at hW
  have hW' : W = generalMarkedReflection S := AdjointStep.gate.inj hW
  rw [hW']
  exact generalMarkedReflection_unitary S

/-- The marked-check word uses no oracle queries and exactly one fixed gate. -/
theorem generalCheckWord_costs {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    adjointQueryCount (generalCheckWord S) = 0 ∧ adjointGateCount (generalCheckWord S) = 1 := by
  simp [generalCheckWord, adjointQueryCount, adjointGateCount]

/-- Evaluating the marked-check word with identity oracle gives the marked reflection. -/
theorem generalCheckWord_evaluate {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) :
    evaluate 1 (generalCheckWord S) = generalMarkedReflection S := by
  simp [generalCheckWord, evaluate, instructionMatrix]

/-- The marked reflection multiplies a state coordinate by negative one on the marked set and by
one elsewhere. -/
theorem generalMarkedReflection_mulVec {V : Type} [Fintype V] [DecidableEq V] (S : Finset V)
    (ψ : QState V) (u : V) :
    (generalMarkedReflection S *ᵥ ψ) u
      = (if u ∈ S then (-1 : ℂ) else 1) * ψ u := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single u]
  · simp [generalMarkedReflection, Matrix.diagonal_apply]
  · intro k _ hk
    simp [generalMarkedReflection, Matrix.diagonal_apply, Ne.symm hk]
  · simp

/-- Applying the marked reflection preserves marked measurement mass. -/
theorem generalMarkedMass_check {V : Type} [Fintype V] [DecidableEq V] (S : Finset V)
    (ψ : QState V) :
    generalMarkedMass S (generalMarkedReflection S *ᵥ ψ) = generalMarkedMass S ψ := by
  unfold generalMarkedMass
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hx : u ∈ S
  · simp [generalMarkedReflection_mulVec, hx]
  · simp [generalMarkedReflection_mulVec, hx]

/-- The marked mass of a kernel row state is the sum of its transition weights over marked
vertices. -/
theorem generalMarkedMass_rowState {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) :
    generalMarkedMass S (generalRowState K p) = ∑ u ∈ S, (K.weight p u : ℝ) := by
  unfold generalMarkedMass
  apply Finset.sum_congr rfl
  intro u hu
  have h : 0 ≤ (K.weight p u : ℚ) := K.nonnegative p u
  have h' : 0 ≤ ((K.weight p u : ℚ) : ℝ) := by exact_mod_cast h
  have h'' : 0 ≤ Real.sqrt ((K.weight p u : ℚ) : ℝ) := Real.sqrt_nonneg _
  simp only [generalRowState, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h'']
  exact Real.sq_sqrt h'

/-- The state obtained by ideal row preparation from `Ket p`, followed by the marked-check word. -/
noncomputable def generalDetectionExecution {V : ℕ} (K : GeneralKernel V)
    (p : GeneralVertex V) (S : Finset (GeneralVertex V)) :
    QState (GeneralVertex V) :=
  evaluate 1 (generalCheckWord S) *ᵥ (evaluate 1 (generalIdealSetupWord K p) *ᵥ Ket p)

/-- The marked mass after ideal row preparation and checking equals the kernel row's total
marked transition weight. -/
theorem generalDetectionExecution_exact {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) :
    generalMarkedMass S (generalDetectionExecution K p S) = ∑ u ∈ S, (K.weight p u : ℝ) := by
  unfold generalDetectionExecution
  have hc : evaluate 1 (generalCheckWord S) = generalMarkedReflection S :=
    generalCheckWord_evaluate S
  rw [hc]
  rw [generalMarkedMass_check]
  rw [generalIdealSetupWord_exact]
  exact generalMarkedMass_rowState K p S

/-- The sum of squared computed-versus-ideal amplitude errors over marked vertices is at most
`(32 * V / 2^k)^2`. -/
theorem generalDetectionExecution_amplitude_error {V : ℕ} (K : GeneralKernel V)
    (p : GeneralVertex V) (S : Finset (GeneralVertex V)) (k : ℕ) :
    (∑ u ∈ S, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
        - (generalRowState K p) u)‖ ^ 2)
      ≤ (32 * (V : ℝ) / 2 ^ k) ^ 2 := by
  have herr : ‖toEuclidean_fromVec
      (((evaluate 1 (generalSetupWord K p k)
          - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
        *ᵥ Ket p))‖
        ≤ 32 * (V : ℝ) / 2 ^ k := generalSetupWord_state_error K p k
  have hB : (relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)) *ᵥ Ket p)
      = generalRowState K p := by
    rw [relabelGate_mulVec_apply, relabelState_pivotRelabel_symm_ket]
    obtain ⟨hu, huMass, hket⟩ := rational_weight_ideal_preparation_exact V
      (rowWeight K p) (rowWeight_nonneg K p) (by
        rw [rowWeight_mass_one]
        exact_mod_cast (by norm_num : (0 : ℝ) < 1))
    rw [huMass]
    exact (generalRowState_eq_relabel K p).symm
  have hid : (((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p)
      - (generalRowState K p)) : QState (GeneralVertex V))
      = (((evaluate 1 (generalSetupWord K p k)
          - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
        *ᵥ Ket p) : QState (GeneralVertex V)) := by
    rw [Matrix.sub_mulVec, hB]
  have hsq : (∑ u, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
      - (generalRowState K p) u)‖ ^ 2)
      = ‖toEuclidean_fromVec
          (((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p)
            - (generalRowState K p)) : QState (GeneralVertex V))‖ ^ 2 :=
    (norm_toEuclidean_fromVec_sq _).symm
  rw [hid] at hsq
  have hsq' : (∑ u, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
      - (generalRowState K p) u)‖ ^ 2)
      ≤ (32 * (V : ℝ) / 2 ^ k) ^ 2 := by
    rw [hsq]
    calc
      ‖toEuclidean_fromVec
          (((evaluate 1 (generalSetupWord K p k)
              - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
            *ᵥ Ket p))‖ ^ 2
          = ‖toEuclidean_fromVec
              (((evaluate 1 (generalSetupWord K p k)
                  - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
                *ᵥ Ket p))‖
              * ‖toEuclidean_fromVec
                  (((evaluate 1 (generalSetupWord K p k)
                      - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
                    *ᵥ Ket p))‖ := by exact sq _
      _ ≤ (32 * (V : ℝ) / 2 ^ k) * ‖toEuclidean_fromVec
              (((evaluate 1 (generalSetupWord K p k)
                  - relabelGate (pivotRelabel p) (idealWeightPrepare (rowWeight K p)))
                *ᵥ Ket p))‖ :=
        mul_le_mul_of_nonneg_right herr (norm_nonneg _)
      _ ≤ (32 * (V : ℝ) / 2 ^ k) * (32 * (V : ℝ) / 2 ^ k) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ = (32 * (V : ℝ) / 2 ^ k) ^ 2 := by ring
  calc
    (∑ u ∈ S, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
        - (generalRowState K p) u)‖ ^ 2)
        ≤ ∑ u, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
            - (generalRowState K p) u)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun u _ _ => sq_nonneg _)
    _ ≤ (32 * (V : ℝ) / 2 ^ k) ^ 2 := hsq'

/-- The list of further source-detection components to be supplied beyond the setup, check, and
amplitude guarantees in this module. -/
def generalSourceDetectionResidual : List String :=
  [ "the graph-local update word and the Szegedy walk dynamics on the general graph are not built here",
    "the intertwining with the double-frame source oracle of szegedyTheorem4WalkOracle is not built here",
    "the realised reachable-spectrum statement is not built here",
    "the uniform unknown-marked-mass tolerant schedule is not built here",
    "the finite-gate and bit-time ledgers of the source-detection execution are not built here" ]

/-- A proposition packaging check legality and costs, computed setup legality, the ideal marked
output law, and the computed marked-amplitude error bound. -/
structure GeneralSourceDetectionAccount (V : ℕ) (K : GeneralKernel V)
    (p : GeneralVertex V) (S : Finset (GeneralVertex V)) (k : ℕ) : Prop where

  checkLegal : WellFormedAdjointCircuit (generalCheckWord S)

  checkCosts : adjointQueryCount (generalCheckWord S) = 0 ∧
    adjointGateCount (generalCheckWord S) = 1

  setupLegal : WellFormedAdjointCircuit (generalSetupWord K p k)

  outputLaw : generalMarkedMass S (generalDetectionExecution K p S)
      = ∑ u ∈ S, (K.weight p u : ℝ)

  amplitudeError :
    (∑ u ∈ S, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
        - (generalRowState K p) u)‖ ^ 2)
      ≤ (32 * (V : ℝ) / 2 ^ k) ^ 2

/-- The constructed setup and check satisfy every field of `GeneralSourceDetectionAccount`. -/
theorem clause5_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    GeneralSourceDetectionAccount V K p S k := by
  exact ⟨generalCheckWord_wellFormed S, generalCheckWord_costs S,
    generalSetupWord_wellFormed K p k, generalDetectionExecution_exact K p S,
    generalDetectionExecution_amplitude_error K p S k⟩

/-- Ideal detection has marked mass equal to the kernel row's marked weight, and the marked
reflection preserves the row state's marked mass. -/
theorem clause6_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    generalMarkedMass S (generalDetectionExecution K p S)
        = ∑ u ∈ S, (K.weight p u : ℝ) ∧
      generalMarkedMass S (generalMarkedReflection S
        *ᵥ (generalRowState K p)) = generalMarkedMass S (generalRowState K p) := by
  exact ⟨generalDetectionExecution_exact K p S, generalMarkedMass_check S _⟩

/-- Ideal detection is exactly the marked reflection applied to the row state, and computed
setup has the displayed squared marked-amplitude error bound. -/
theorem clause7_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    generalDetectionExecution K p S
        = generalMarkedReflection S *ᵥ (generalRowState K p) ∧
      (∑ u ∈ S, ‖((evaluate 1 (generalSetupWord K p k) *ᵥ Ket p) u
          - (generalRowState K p) u)‖ ^ 2)
        ≤ (32 * (V : ℝ) / 2 ^ k) ^ 2 := by
  refine ⟨?_, generalDetectionExecution_amplitude_error K p S k⟩
  unfold generalDetectionExecution
  rw [generalCheckWord_evaluate]
  rw [generalIdealSetupWord_exact]

end DetectionExecution
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
