/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GramRealization.ChannelHelpers
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit

/-!
# Controlled permutation collision readout

This module constructs controlled permutation selectors and shows that output marginals depend
only on the collision relation among the selected seed images. The word `queryWord` implements
the readout with one selector query and one gate, connecting Gram-matrix readout to oracle
discrimination settings such as [MeyerPommersheim2009].

## Main statements

* `selector_unitary`: The controlled permutation selector is unitary.

* `output_marginal_eq`: Controlled permutation families with the same collision relation on
  their seeds give identical control-register marginals for the same input amplitudes and final
  matrix.

* `queryWord_counts`: The controlled readout word contains exactly one query and one gate.

* `queryWord_correct`: Evaluating the controlled readout query word on a seeded tensor state
  yields the defined controlled readout output.

## References

* [Meyer and Pommersheim, 2009][MeyerPommersheim2009]

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout
open scoped BigOperators
variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- The controlled permutation matrix that applies `σ i` to the second register when the first
register is `i`. -/
noncomputable def selector (σ : I → Equiv.Perm J) : Matrix (I × J) (I × J) ℂ :=
  Qatlib.Concepts.BlockEncoding.LinearCombination.Select (fun i => Qatlib.Foundations.PureStateMath.permMatrix (σ i))

/-- The controlled permutation selector is unitary. -/
theorem selector_unitary (σ : I → Equiv.Perm J) :
    Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector σ ∈ Matrix.unitaryGroup (I × J) ℂ :=
  Qatlib.Concepts.BlockEncoding.LinearCombination.select_unitary _ (fun i => Qatlib.Concepts.HspRecovery.RecordExtract.permMatrix_unitary_of_injective (σ i).injective)

/-- Applying the selector to `a` tensored with a basis seed produces the tagged family `a i •
Ket (σ i seed)`. -/
theorem prepared (σ : I → Equiv.Perm J) (a : Qatlib.Foundations.PureStateMath.QState I) (seed : J) :
    Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector σ) (Qatlib.Foundations.PureStateMath.TensorState a (Qatlib.Foundations.PureStateMath.Ket seed)) =
      Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState (fun i => a i • Qatlib.Foundations.PureStateMath.Ket (σ i seed)) := by
  funext p
  simp [Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector, Qatlib.Concepts.BlockEncoding.LinearCombination.Select, Qatlib.Foundations.PureStateMath.ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.TensorState,
    Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.taggedState, Fintype.sum_prod_type, Qatlib.Foundations.PureStateMath.permMatrix, Qatlib.Foundations.PureStateMath.Ket,
    Matrix.of_apply, mul_ite, ite_mul]

/-- The inner product of two weighted basis states is the conjugate coefficient product times
the indicator that their basis labels coincide. -/
private theorem inner_weighted_ket (a b : ℂ) (j k : J) :
    Qatlib.Foundations.PureStateMath.Inner (a • Qatlib.Foundations.PureStateMath.Ket j) (b • Qatlib.Foundations.PureStateMath.Ket k) = star a * b * (if j = k then 1 else 0) := by
  by_cases h : j = k
  · subst k
    simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
        Qatlib.Foundations.PureStateMath.Ket, mul_ite, Pi.smul_apply, smul_eq_mul]
  · simp [Qatlib.Foundations.PureStateMath.Inner, dotProduct,
      Qatlib.Foundations.PureStateMath.Ket, mul_ite, Pi.smul_apply, smul_eq_mul, h, Ne.symm h]

/-- The state obtained by applying the controlled permutation selector to a seeded tensor state
and then applying `U` on the control register. -/
noncomputable def output (U : Matrix I I ℂ) (σ : I → Equiv.Perm J)
    (a : Qatlib.Foundations.PureStateMath.QState I) (seed : J) : Qatlib.Foundations.PureStateMath.QState (I × J) :=
  Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ))
    (Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector σ) (Qatlib.Foundations.PureStateMath.TensorState a (Qatlib.Foundations.PureStateMath.Ket seed)))

/-- Controlled permutation families with the same collision relation on their seeds give
identical control-register marginals for the same input amplitudes and final matrix. -/
theorem output_marginal_eq (U : Matrix I I ℂ)
    (σ : I → Equiv.Perm J) (τ : I → Equiv.Perm K)
    (a : Qatlib.Foundations.PureStateMath.QState I) (j₀ : J) (k₀ : K)
    (hcollision : ∀ i j, σ i j₀ = σ j j₀ ↔ τ i k₀ = τ j k₀) (x : I) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output U σ a j₀) (Finset.univ.filter (fun p : I × J => p.1 = x)) =
      Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output U τ a k₀) (Finset.univ.filter (fun p : I × K => p.1 = x)) := by
  simp only [Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output,
      Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.prepared]
  apply Qatlib.Concepts.GramQueryCore.GramRealization.GramMarginalReadout.marginal_eq_of_gram
  intro i j
  rw [inner_weighted_ket, inner_weighted_ket]
  simp only [hcollision i j]

/-- A normalized input state remains normalized after the controlled selector and a unitary
matrix on the control register. -/
theorem output_normalized (U : Matrix I I ℂ) (σ : I → Equiv.Perm J)
    (a : Qatlib.Foundations.PureStateMath.QState I) (seed : J) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ha : Qatlib.Foundations.PureStateMath.Normalized a) : Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output U σ a seed) :=
  Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Foundations.PureStateMath.tensorGate_unitary hU (Submonoid.one_mem _))
    (Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector_unitary σ) (Qatlib.Foundations.PureStateMath.normalized_tensorState ha (Qatlib.Foundations.PureStateMath.normalized_ket seed)))

/-- The query word combining one forward selector query with the gate `U` tensored with the
identity. -/
noncomputable def queryWord (U : Matrix I I ℂ) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (I × J)) :=
  [.gate (Qatlib.Foundations.PureStateMath.TensorGate U (1 : Matrix J J ℂ)), .forward]

omit [Fintype I] [DecidableEq I] [Fintype J] in

/-- The controlled readout word contains exactly one query and one gate. -/
theorem queryWord_counts (U : Matrix I I ℂ) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.queryWord (J := J) U) = 1 ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.queryWord (J := J) U) = 1 := by
  constructor <;> rfl

/-- Evaluating the controlled readout query word on a seeded tensor state yields the defined
controlled readout output. -/
theorem queryWord_correct (U : Matrix I I ℂ) (σ : I → Equiv.Perm J)
    (a : Qatlib.Foundations.PureStateMath.QState I) (seed : J) :
    Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.selector σ) (Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.queryWord U))
      (Qatlib.Foundations.PureStateMath.TensorState a (Qatlib.Foundations.PureStateMath.Ket seed)) = Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output U σ a seed := by
  simp [Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.queryWord, Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate, Qatlib.Concepts.CoherentSim.CoherentOAA.instructionMatrix,
    Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout.output, Qatlib.Foundations.PureStateMath.ApplyGate, Matrix.mulVec_mulVec]

end Qatlib.Concepts.GramQueryCore.GramRealization.ControlledCollisionReadout
