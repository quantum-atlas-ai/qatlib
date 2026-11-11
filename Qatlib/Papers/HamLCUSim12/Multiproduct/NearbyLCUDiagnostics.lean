/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUContracts
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity

/-!
# Diagnostics of the legacy nearby-unitary circuit

This module proves that the legacy `lcuLevelGate` preserves the ancilla mask and hence has zero
failure output from the designated input fiber. It also proves that the legacy circuit vanishes
at κ = 0, yielding `not_lemma2Fiber` and `not_lemma2CircuitUnitary` as counterexamples to its
proposed specifications. See [ChildsWiebe2012] for the multiproduct and linear-combination
simulation framework.

## Main statements

* `lemma2FailureProb_zero`: The legacy two-unitary LCU failure probability is identically zero.
* `not_lemma2Fiber`: Refutes the legacy `Lemma2Fiber` specification using the zero circuit at κ
  = 0.
* `not_lemma2CircuitUnitary`: Refutes the legacy `Lemma2CircuitUnitary` specification using the
  zero circuit at κ = 0 on a one-dimensional system.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Matrix

/-- The product of two matrices that vanish between different first-coordinate fibers also
vanishes between different first-coordinate fibers. -/
private theorem mask_mul {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (U V : Matrix (K × I) (K × I) ℂ)
    (hU : ∀ p q, p.1 ≠ q.1 → U p q = 0)
    (hV : ∀ p q, p.1 ≠ q.1 → V p q = 0) :
    ∀ p q, p.1 ≠ q.1 → (U * V) p q = 0 := by
  intro p q hpq
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro r _hr
  by_cases hpr : p.1 = r.1
  · have hrq : r.1 ≠ q.1 := by rw [← hpr]; exact hpq
    rw [hV r q hrq, mul_zero]
  · rw [hU p r hpr, zero_mul]

/-- The legacy `lcuLevelGate` has zero matrix entries between distinct ancilla masks for
arbitrary rotation and controlled-input matrices. -/
theorem lcuLevelGate_preserves_mask {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (i : Fin k) (V : Matrix (Fin 2) (Fin 2) ℂ)
    (Cx Cy : Matrix ((Fin k → Bool) × I) ((Fin k → Bool) × I) ℂ) :
    ∀ p q, p.1 ≠ q.1 → lcuLevelGate k i V Cx Cy p q = 0 := by
  unfold lcuLevelGate
  apply mask_mul
  · intro p q hpq
    simp [rotGate, hpq]
  · apply mask_mul
    · intro p q hpq
      simp [ctrlGate, hpq]
    · intro p q hpq
      simp [rotGate, hpq]

/-- A matrix preserving the first-coordinate fibers sends a state supported on fiber z to zero
on any different fiber z'. -/
theorem maskPreserving_output_zero {K I : Type} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (U : Matrix (K × I) (K × I) ℂ)
    (hU : ∀ p q, p.1 ≠ q.1 → U p q = 0) (z z' : K) (hz : z' ≠ z)
    (ψ : QState I) (x : I) :
    (U *ᵥ TensorState (Ket z) ψ) (z', x) = 0 := by
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro q _hq
  by_cases hq : q.1 = z
  · have hne : z' ≠ q.1 := by rw [hq]; exact hz
    rw [hU (z', x) q hne, zero_mul]
  · simp [TensorState, Ket, hq]

/-- The legacy two-unitary LCU output has zero amplitude on the true ancilla fiber for every
choice of κ, inputs, and state. -/
theorem lemma2Output_failure_zero {I : Type} [Fintype I] [DecidableEq I]
    (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) (x : I) :
    lemma2Output κ Ua Ub ψ (fun _ => true, x) = 0 := by
  apply maskPreserving_output_zero _
    (lcuLevelGate_preserves_mask 1 0 (vKappa κ) (liftSys 1 Ua) (liftSys 1 Ub))
  intro he
  have hh := congrFun he 0
  simp at hh

/-- The legacy two-unitary LCU failure probability is identically zero. -/
theorem lemma2FailureProb_zero {I : Type} [Fintype I] [DecidableEq I]
    (κ : ℝ) (Ua Ub : Matrix I I ℂ) (ψ : QState I) :
    lemma2FailureProb κ Ua Ub ψ = 0 := by
  unfold lemma2FailureProb MeasureProb
  apply Finset.sum_eq_zero
  intro p hp
  have hmask : p.1 = (fun _ => true : Fin 1 → Bool) := by
    simpa [lemma2FailSet] using (Finset.mem_product.mp hp).1
  rcases p with ⟨z, x⟩
  dsimp only at hmask
  subst z
  simp [BornProb, lemma2Output_failure_zero]

/-- Establishes the legacy nearby-unitary failure-bound proposition using the identically zero
failure probability. -/
theorem lemma2NearbyFailure : Lemma2NearbyFailure := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb Δ _hΔ _hbound ψ _hψ
  rw [lemma2FailureProb_zero]
  positivity

/-- Establishes the legacy uniform failure-bound proposition using the identically zero failure
probability. -/
theorem lemma2NearbyFailureCrude : Lemma2NearbyFailureCrude := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb ψ _hψ
  rw [lemma2FailureProb_zero]
  positivity

/-- Every diagonal entry of `vKappa 0` is zero. -/
private theorem vKappa_zero_diagonal (i : Fin 2) : vKappa 0 i i = 0 := by
  fin_cases i <;> norm_num [vKappa]

/-- The legacy rotation gate constructed from `vKappa 0` is the zero matrix. -/
theorem rotGate_kappa_zero {I : Type} [Fintype I] [DecidableEq I]
    (k : ℕ) (i : Fin k) : rotGate (I := I) k i (vKappa 0) = 0 := by
  ext p q
  by_cases hpq : p.1 = q.1
  · simp only [rotGate, Matrix.of_apply, hpq, ↓reduceIte]
    simpa using vKappa_zero_diagonal (if q.1 i then 1 else 0)
  · simp [rotGate, hpq]

/-- At κ = 0, the legacy two-unitary LCU circuit is the zero matrix for arbitrary input
matrices. -/
theorem lemma2Circuit_kappa_zero {I : Type} [Fintype I] [DecidableEq I]
    (Ua Ub : Matrix I I ℂ) : lemma2Circuit 0 Ua Ub = 0 := by
  simp [lemma2Circuit, lcuLevelGate, rotGate_kappa_zero]

/-- Refutes the legacy `Lemma2Fiber` specification using the zero circuit at κ = 0. -/
theorem not_lemma2Fiber : ¬ Lemma2Fiber := by
  intro h
  have he := (h Unit 0 (by norm_num) 1 1 (by simp) (by simp) (fun _ => 1)).1 ()
  norm_num [lemma2Output, lemma2Circuit_kappa_zero, ApplyGate] at he

/-- Refutes the legacy `Lemma2CircuitUnitary` specification using the zero circuit at κ = 0 on a
one-dimensional system. -/
theorem not_lemma2CircuitUnitary : ¬ Lemma2CircuitUnitary := by
  intro h
  have he := h Unit 0 (by norm_num) 1 1 (by simp) (by simp)
  rw [lemma2Circuit_kappa_zero] at he
  have heq := Matrix.mem_unitaryGroup_iff.mp he
  have hentry := congrFun (congrFun heq ((fun _ => false), ())) ((fun _ => false), ())
  simp at hentry

end Qatlib.Papers.HamLCUSim12.Multiproduct
