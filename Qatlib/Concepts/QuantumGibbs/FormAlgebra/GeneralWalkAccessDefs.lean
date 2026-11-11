/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Rational kernels and row-setup definitions

This module defines finite rational transition kernels on a vertex type with a distinguished
element. It relabels a chosen pivot to that element and defines ideal and computed words for
preparing the square-root transition row, a standard ingredient of the walk construction in
[Szegedy2004].

## Main statements

* `GeneralKernel`: Nonnegative rational row weights summing to one.
* `generalRowState_eq_relabel`: The row state as a relabelled rational-weight target.
* `generalSetupWord`: The computed pivot-relabelled row-preparation word.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace GeneralWalkAccessDefs

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators
set_option autoImplicit false

/-- The finite vertex type `Option (Fin V)`, with distinguished vertex `none`. -/
abbrev GeneralVertex (V : ℕ) := Option (Fin V)

/-- A rational transition kernel on `GeneralVertex V` with nonnegative weights and each row
summing to one. -/
structure GeneralKernel (V : ℕ) where

  weight : GeneralVertex V → GeneralVertex V → ℚ

  nonnegative : ∀ v u, 0 ≤ weight v u

  rowSum : ∀ v, ∑ u, weight v u = 1

/-- The vertex equivalence exchanging `none` with the pivot `p`. -/
def pivotRelabel {V : ℕ} (p : GeneralVertex V) : GeneralVertex V ≃ GeneralVertex V :=
  Equiv.swap none p

/-- The pivot relabeling sends `none` to `p`. -/
@[simp] theorem pivotRelabel_none {V : ℕ} (p : GeneralVertex V) :
    pivotRelabel p none = p := Equiv.swap_apply_left none p

/-- The pivot relabeling sends `p` to `none`. -/
@[simp] theorem pivotRelabel_p {V : ℕ} (p : GeneralVertex V) :
    pivotRelabel p p = none := Equiv.swap_apply_right none p

/-- The inverse pivot relabeling exchanges `none` and `p` and fixes every other vertex. -/
theorem pivotRelabel_symm_apply {V : ℕ} (p u : GeneralVertex V) :
    (pivotRelabel p).symm u = if u = none then p else if u = p then none else u := rfl

/-- The row of `K` at `p`, with its column indices relabelled by `pivotRelabel p`. -/
def rowWeight {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    GeneralVertex V → ℚ :=
  fun a => K.weight p (pivotRelabel p a)

/-- The relabelled row weight at `none` is the kernel's diagonal weight at `p`. -/
@[simp] theorem rowWeight_none {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    rowWeight K p none = K.weight p p := by
  simp [rowWeight]

/-- Every relabelled row weight of a general kernel is nonnegative. -/
theorem rowWeight_nonneg {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    ∀ a, 0 ≤ rowWeight K p a := by
  intro a
  exact K.nonnegative p (pivotRelabel p a)

/-- The rational mass of the relabelled row equals the sum of the original row's weights. -/
theorem rowWeight_mass {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    rationalWeightMass (rowWeight K p) = ∑ u, K.weight p u := by
  unfold rationalWeightMass rowWeight
  have h : (∑ a, K.weight p (pivotRelabel p a)) = ∑ u, K.weight p u :=
    Equiv.sum_comp (pivotRelabel p) (K.weight p)
  rw [h]

/-- The relabelled row has rational mass one. -/
theorem rowWeight_mass_one {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    rationalWeightMass (rowWeight K p) = 1 := by
  rw [rowWeight_mass]
  exact K.rowSum p

/-- Relabel the matrix of a fixed-gate instruction while retaining forward and backward query
instructions. -/
noncomputable def relabelAdjointStep {I J : Type} (e : I ≃ J) :
    AdjointStep I → AdjointStep J
  | .gate V => .gate (relabelGate e V)
  | .forward => .forward
  | .backward => .backward

/-- Relabeling a fixed-gate instruction gives the fixed gate with relabelled matrix. -/
@[simp] theorem relabelAdjointStep_gate {I J : Type} (e : I ≃ J) (V : Matrix I I ℂ) :
    relabelAdjointStep e (.gate V) = .gate (relabelGate e V) := rfl

/-- Matrix application commutes with simultaneous relabeling of the matrix and state. -/
theorem relabelGate_mulVec {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) (ψ : QState I) :
    (relabelGate e M) *ᵥ (relabelState e ψ) = relabelState e (M *ᵥ ψ) := by
  classical
  ext u
  have hL : ((relabelGate e M) *ᵥ (relabelState e ψ)) u
      = ∑ v, M (e.symm u) (e.symm v) * ψ (e.symm v) := by
    simp only [Matrix.mulVec, dotProduct]
    simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, relabelState_apply]
  have hR : relabelState e (M *ᵥ ψ) u = ∑ w, M (e.symm u) w * ψ w := by
    simp only [relabelState_apply, Matrix.mulVec, dotProduct]
  rw [hL, hR]
  exact Equiv.sum_comp e.symm (fun w => M (e.symm u) w * ψ w)

/-- Evaluation of a relabelled fixed-gate list equals relabeling its evaluated matrix. -/
theorem evaluate_relabel_gate_list {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (gs : List (Matrix I I ℂ)) :
    evaluate (1 : Matrix J J ℂ)
        ((gs.map (fun V => AdjointStep.gate V)).map (relabelAdjointStep e))
      = relabelGate e (evaluate (1 : Matrix I I ℂ) (gs.map (fun V => AdjointStep.gate V))) := by
  induction gs with
  | nil =>
    simp only [List.map_nil, evaluate]
    rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one e]
  | cons V gs ih =>
    simp only [List.map_cons, relabelAdjointStep_gate, evaluate, instructionMatrix]
    rw [Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul e]
    rw [ih]

/-- A relabelled matrix acts by inverse relabeling the input state, applying the original
matrix, and relabeling the result. -/
theorem relabelGate_mulVec_apply {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) (ψ : QState J) :
    (relabelGate e M) *ᵥ ψ = relabelState e (M *ᵥ (relabelState e.symm ψ)) := by
  have h := relabelGate_mulVec e M (relabelState e.symm ψ)
  have hround : relabelState e (relabelState e.symm ψ) = ψ := by
    funext j
    simp [relabelState, Function.comp_apply]
  rw [hround] at h
  exact h

/-- The inverse relabeling of a vertex different from `none` is different from the pivot. -/
theorem pivotRelabel_symm_ne_pivot {V : ℕ} (p u : GeneralVertex V) (hu : u ≠ none) :
    (pivotRelabel p).symm u ≠ p := by
  by_cases hup : u = p
  · have hp : p ≠ none := by
      intro hpc
      exact hu (hpc ▸ hup)
    rw [hup]
    have h1 : (pivotRelabel p).symm p = none := by
      simp [pivotRelabel_symm_apply, hp]
    rw [h1]
    exact Ne.symm hp
  · have h1 : (pivotRelabel p).symm u = u := by
      simp [pivotRelabel_symm_apply, hu, hup]
    rw [h1]
    exact hup

/-- Relabeling the pivot basis state by `pivotRelabel p` gives the distinguished basis state. -/
theorem relabelState_pivotRelabel_ket {V : ℕ} (p : GeneralVertex V) :
    relabelState (pivotRelabel p) (Qatlib.Foundations.PureStateMath.Ket p) = Qatlib.Foundations.PureStateMath.Ket none := by
  classical
  ext u
  rw [relabelState_apply]
  by_cases hu : u = none
  · rw [hu]
    have h1 : (pivotRelabel p).symm none = p := by
      simp [pivotRelabel_symm_apply]
    rw [h1]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · by_cases hup : u = p
    · have hp : p ≠ none := by
        intro hpc
        exact hu (hpc ▸ hup)
      rw [hup]
      have h1 : (pivotRelabel p).symm p = none := by
        simp [pivotRelabel_symm_apply, hp]
      rw [h1]
      simp [Qatlib.Foundations.PureStateMath.Ket, hp, Ne.symm hp]
    · have h1 : (pivotRelabel p).symm u = u := by
        simp [pivotRelabel_symm_apply, hu, hup]
      rw [h1]
      simp [Qatlib.Foundations.PureStateMath.Ket, hu, hup]

/-- Relabeling the pivot basis state by the inverse pivot equivalence gives the distinguished
basis state. -/
theorem relabelState_pivotRelabel_symm_ket {V : ℕ} (p : GeneralVertex V) :
    relabelState (pivotRelabel p).symm (Qatlib.Foundations.PureStateMath.Ket p) = Qatlib.Foundations.PureStateMath.Ket none := by
  classical
  ext u
  rw [relabelState_apply]
  simp only [Equiv.symm_symm]
  by_cases hu : u = none
  · rw [hu]
    have h1 : (pivotRelabel p) none = p := pivotRelabel_none p
    rw [h1]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · by_cases hup : u = p
    · have hp : p ≠ none := by
        intro hpc
        exact hu (hpc ▸ hup)
      rw [hup]
      have h1 : (pivotRelabel p) p = none := pivotRelabel_p p
      rw [h1]
      simp [Qatlib.Foundations.PureStateMath.Ket, hp, Ne.symm hp]
    · have h1 : (pivotRelabel p) u = u := by
        simp [pivotRelabel, Equiv.swap_apply_def, hu, hup]
      rw [h1]
      simp [Qatlib.Foundations.PureStateMath.Ket, hu, hup]

/-- The state whose amplitude at `u` is the nonnegative square root of the transition weight
`K.weight p u`. -/
noncomputable def generalRowState {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    QState (GeneralVertex V) :=
  fun u => Real.sqrt ((K.weight p u : ℚ) : ℝ)

/-- The row-state amplitude at `u` equals the square root of the corresponding real-coerced
rational weight. -/
theorem generalRowState_apply {V : ℕ} (K : GeneralKernel V) (p u : GeneralVertex V) :
    generalRowState K p u = Real.sqrt ((K.weight p u : ℚ) : ℝ) := rfl

/-- The row state is the pivot relabeling of the rational weight target for the relabelled row. -/
theorem generalRowState_eq_relabel {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    generalRowState K p = relabelState (pivotRelabel p) (rationalWeightTarget (rowWeight K p)) := by
  classical
  ext u
  rw [relabelState_apply, rationalWeightTarget]
  have hw : rowWeight K p ((pivotRelabel p).symm u) = K.weight p u := by
    simp only [rowWeight]
    exact congrArg (K.weight p) (Equiv.symm_apply_apply (pivotRelabel p) u)
  have hm : rationalWeightMass (rowWeight K p) = 1 := rowWeight_mass_one K p
  rw [hw, hm]
  simp only [generalRowState, div_one]

/-- The computed rational-weight preparation word with each instruction relabelled from the
distinguished vertex to the pivot. -/
noncomputable def generalSetupWord {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (k : ℕ) : List (AdjointStep (GeneralVertex V)) :=
  (rationalWeightWord (rowWeight K p) k).map (relabelAdjointStep (pivotRelabel p))

/-- The ideal weight preparation word with each instruction relabelled by the pivot equivalence. -/
noncomputable def generalIdealSetupWord {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V) :
    List (AdjointStep (GeneralVertex V)) :=
  (idealWeightWord (rowWeight K p)).map (relabelAdjointStep (pivotRelabel p))

end GeneralWalkAccessDefs
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
