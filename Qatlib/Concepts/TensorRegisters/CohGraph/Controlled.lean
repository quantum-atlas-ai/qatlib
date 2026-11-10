/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.CohGraph.GraphState

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.CohGraph

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

def controlledPermutation (p : I → Equiv.Perm O) : Equiv.Perm (I × O) where
  toFun q := (q.1,p q.1 q.2)
  invFun q := (q.1,(p q.1).symm q.2)
  left_inv := by rintro ⟨i,o⟩; simp
  right_inv := by rintro ⟨i,o⟩; simp

noncomputable def controlledUnitary (p : I → Equiv.Perm O) :
    EuclideanSpace ℂ (I × O) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × O) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (controlledPermutation p)

theorem controlledUnitary_graph (p : I → Equiv.Perm O) (f : I → O) :
    controlledUnitary p (graphState f) = graphState (fun i => p i (f i)) := by
  unfold graphState
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact EuclideanSpace.piLpCongrLeft_single (controlledPermutation p) _ _

end Qatlib.Concepts.TensorRegisters.CohGraph
