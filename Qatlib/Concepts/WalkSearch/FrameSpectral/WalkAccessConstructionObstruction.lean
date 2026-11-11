/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkAccessConstructionDefs

/-!
# Constant row restrictions on anchored access

This module proves a necessary restriction on anchored row preserving access: all square-root
transition rows must coincide. With the transition matrix hypothesis,
`anchoredRowPreserving_constantRows` converts this into equality of the transition rows
themselves. These results concern the quantum walk framework of [Szegedy2004].

## Main statements

* `anchoredRowPreserving_constantSqrtProfile`: A common square-root row profile forced by
  anchored access.
* `anchoredRowPreserving_constantRows`: A common transition row profile.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open scoped Classical BigOperators

universe u v

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.WalkSearch.CountedWalk

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

/-- If row preserving access maps each anchored basis input to its Szegedy row state, then the
square-root transition profile is independent of the row index. -/
theorem anchoredRowPreserving_constantSqrtProfile {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ)
    (hanchor : ∀ i : I, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i)
    (hU : RowPreservingAccess U) :
    ∃ π : I → ℝ, ∀ i y, Real.sqrt (P i y) = π y := by
  obtain ⟨V, W, hVf, hWb, hVW⟩ := hU
  have hcol : ∀ (i y : I), V y j = (Real.sqrt (P i y) : ℂ) := by
    intro i y
    have hanc := congrFun (hanchor i) (i, y)
    have hrow :=
        hVf (TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j)) i y
    rw [hrow] at hanc
    have hdelta : (fun e ↦ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) (i, e)) = Qatlib.Foundations.PureStateMath.Ket j := by
      funext e
      by_cases h : e = j
      · subst h
        simp [tensorState_apply, Qatlib.Foundations.PureStateMath.Ket]
      · simp [tensorState_apply, Qatlib.Foundations.PureStateMath.Ket, h]
    rw [hdelta, mulVec_ket_column] at hanc
    rw [mulVec_ket_column] at hanc
    have hsz : SzegedyIsometry P (i, y) i = (Real.sqrt (P i y) : ℂ) := by
      simp [SzegedyIsometry, Matrix.of_apply]
    rw [hsz] at hanc
    exact hanc
  have hsame : ∀ (i i' y : I), Real.sqrt (P i y) = Real.sqrt (P i' y) := by
    intro i i' y
    have h1 := hcol i y
    have h2 := hcol i' y
    have h3 : (Real.sqrt (P i y) : ℂ) = (Real.sqrt (P i' y) : ℂ) := by
      rw [← h1, ← h2]
    exact Complex.ofReal_inj.mp h3
  by_cases hne : Nonempty I
  · obtain ⟨i₀⟩ := hne
    refine ⟨fun y => Real.sqrt (P i₀ y), ?_⟩
    intro i y
    exact hsame i i₀ y
  · refine ⟨fun _ => (0 : ℝ), ?_⟩
    intro i y
    exact (not_nonempty_iff.mp hne).elim i

/-- For a transition matrix, anchored row preserving access forces all transition rows to be
equal. -/
theorem anchoredRowPreserving_constantRows {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ)
    (hanchor : ∀ i : I, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i)
    (hU : RowPreservingAccess U) (hP : IsTransitionMatrix P) :
    ∃ π : I → ℝ, ∀ i y, P i y = π y := by
  obtain ⟨σ, hσ⟩ := anchoredRowPreserving_constantSqrtProfile P j U hanchor hU
  by_cases hne : Nonempty I
  · obtain ⟨i₀⟩ := hne
    refine ⟨fun y => P i₀ y, ?_⟩
    intro i y
    calc P i y = (Real.sqrt (P i y)) ^ 2 := (Real.sq_sqrt (hP.1 i y)).symm
      _ = (Real.sqrt (P i₀ y)) ^ 2 := by rw [hσ i y, hσ i₀ y]
      _ = P i₀ y := Real.sq_sqrt (hP.1 i₀ y)
  · refine ⟨fun _ => (0 : ℝ), ?_⟩
    intro i y
    exact (not_nonempty_iff.mp hne).elim i
end Qatlib.Concepts.WalkSearch.FrameSpectral
