module

public import Qatlib.Papers.CommuteTest05.RelationAdv.Lemma18State

@[expose] public section

/-!
# Concrete Euclidean consumer for the CommuteTest05 Lemma 18 bridge

The finite relation has one pair, both input classes are nonempty, and both real-valued complex
states are normalized with a nonzero amplitude in the flipped coordinate. Thus the consumer
exercises a genuine two-dimensional Euclidean instance rather than an empty or degenerate one.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.CommuteTest05Lemma18State

open Qatlib.Papers.CommuteTest05.RelationAdv

private def u : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(3 / 5 : ℂ), 4 / 5]

private def v : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(3 / 5 : ℂ), -(4 / 5 : ℂ)]

private theorem u_norm : ‖u‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [u, Fin.sum_univ_two]
  norm_num

private theorem v_norm : ‖v‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [v, Fin.sum_univ_two]
  norm_num

private def stateLeft : Bool → EuclideanSpace ℂ (Fin 2) := fun _ => u

private def stateRight : Bool → EuclideanSpace ℂ (Fin 2) := fun _ => v

private def relation : Finset (Bool × Bool) := {(false, true)}

private theorem relation_nonempty : relation.Nonempty := by
  refine ⟨(false, true), ?_⟩
  simp [relation]

/-- The consumer invokes the top-level Euclidean theorem on a nonempty relation with positive
minimum-degree parameters and nonzero flipped-coordinate amplitudes. -/
example :
    |adversaryOverlapAfterFlip relation (fun _ => 0) stateLeft stateRight -
      adversaryOverlap relation stateLeft stateRight| ≤ (2 : ℝ) := by
  have h := lemma18_state_increment_bound (m := 1) (m' := 1) relation relation_nonempty
    (fun _ => 0) stateLeft stateRight (by norm_num) (by norm_num)
    (fun x => Bool.rec u_norm u_norm x) (fun y => Bool.rec v_norm v_norm y)
    (by simp [relation, stateLeft, u]; norm_num)
    (by simp [relation, stateRight, v]; norm_num)
  have hcard : relation.card = 1 := by decide
  rw [hcard] at h
  norm_num at h
  exact h

/-- Both flipped-coordinate amplitudes are nonzero, excluding the vacuous zero-amplitude branch. -/
example : ‖u 0‖ = 3 / 5 ∧ ‖v 0‖ = 3 / 5 := by
  constructor
  · simp [u]
  · simp [v]

end QatlibTests.CommuteTest05Lemma18State
