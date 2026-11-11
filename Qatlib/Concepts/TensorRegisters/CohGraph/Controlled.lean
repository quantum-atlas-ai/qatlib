/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.CohGraph.GraphState

/-!
# Controlled permutations of coherent graph states

The permutation `controlledPermutation` applies a control-dependent permutation to the output
register. Its lift `controlledUnitary` is a complex linear isometry equivalence and maps a
coherent graph state to the graph of the transformed function. For background, see
[NielsenChuang2010].

## Main statements

* `controlledUnitary_graph`: controlled permutation action on coherent graph states.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.CohGraph

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- The permutation `(i, o) ↦ (i, p i o)`, preserving the control register. -/
def controlledPermutation (p : I → Equiv.Perm O) : Equiv.Perm (I × O) where
  toFun q := (q.1,p q.1 q.2)
  invFun q := (q.1,(p q.1).symm q.2)
  left_inv := by rintro ⟨i,o⟩; simp
  right_inv := by rintro ⟨i,o⟩; simp

/-- The complex linear isometry equivalence induced by `controlledPermutation` on the joint
register. -/
noncomputable def controlledUnitary (p : I → Equiv.Perm O) :
    EuclideanSpace ℂ (I × O) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × O) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (controlledPermutation p)

/-- Applying the controlled permutation to `graphState f` produces the graph state of `fun i =>
p i (f i)`. -/
theorem controlledUnitary_graph (p : I → Equiv.Perm O) (f : I → O) :
    controlledUnitary p (graphState f) = graphState (fun i => p i (f i)) := by
  unfold graphState
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact EuclideanSpace.piLpCongrLeft_single (controlledPermutation p) _ _

end Qatlib.Concepts.TensorRegisters.CohGraph
