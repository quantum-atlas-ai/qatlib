/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BKFermion17.QubitAlgebra.Words

@[expose] public section

/-!
# General qubit edge algebra

This module lifts the word-level endpoint analysis of
`Qatlib.Papers.BKFermion17.QubitAlgebra.Words` to the literal Pauli matrices of an indexed
simple graph. The edge operators use the increasing orientation, for which the sign in
[SetiaWhitfield2018], Eq. (25) is positive. The vertex and edge operators are involutions
and vertex operators commute with each other. Distinct edge operators anticommute at a shared
endpoint and commute for disjoint edges. A vertex operator anticommutes with an incident edge
operator and commutes with a non-incident edge operator.

The statements are uniform in the mode and edge counts and use the actual matrix products on the
`2 ^ E`-dimensional edge register.

## Main statements

* `vertexOperator_sq`, `edgeOperator_sq`: the generators are involutions.
* `vertexOperator_commute`: arbitrary vertex operators commute.
* `edgeOperator_anticommute_of_share`: sharing one endpoint gives an anticommutator.
* `edgeOperator_commute_of_noCoincidence`: disjoint endpoints commute.
* `vertexOperator_anticommute_of_incident`: a vertex anticommutes with its incident edges.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.BKFermion17.QubitAlgebra

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.GraphWords

variable {M E : ℕ}

/-- The Pauli matrix of the all-identity word is the identity matrix. -/
theorem pauliWordOp_identityWord (n : ℕ) :
    pauliWordOp n (fun _ => Pauli1.I) = 1 := by
  rw [pauliWordOp_eq]
  have h : (fun _ : Fin n => P1 Pauli1.I) = fun _ => (1 : Matrix Bool Bool ℂ) :=
    funext fun _ => P1_one
  rw [h, productMatrix_one]

/-- Every Pauli word matrix squares to the identity matrix. -/
theorem pauliWordOp_mul_self (n : ℕ) (w : PauliWord n) :
    pauliWordOp n w * pauliWordOp n w = 1 := by
  rw [pauliWordOp_mul]
  have hphase : (∑ i, pauliMulPhase (w i) (w i)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    exact pauliMulPhase_self (w i)
  have hword : (fun i => pauliMul1 (w i) (w i)) = fun _ => Pauli1.I := by
    funext i
    exact pauliMul1_self (w i)
  rw [hphase, hword, pauliWordOp_identityWord]
  simp

/-- A vanishing symplectic pairing makes two Pauli word matrices commute. -/
theorem pauliWordOp_commute_of_form_zero {n : ℕ} (w v : PauliWord n)
    (h : symplecticForm (symplecticX w, symplecticZ w)
      (symplecticX v, symplecticZ v) = 0) :
    pauliWordOp n w * pauliWordOp n v = pauliWordOp n v * pauliWordOp n w := by
  rw [pauliWordOp_symplectic, h]
  simp

/-- A unit symplectic pairing makes two Pauli word matrices anticommute. -/
theorem pauliWordOp_anticommute_of_form_one {n : ℕ} (w v : PauliWord n)
    (h : symplecticForm (symplecticX w, symplecticZ w)
      (symplecticX v, symplecticZ v) = 1) :
    pauliWordOp n w * pauliWordOp n v = -(pauliWordOp n v * pauliWordOp n w) := by
  rw [pauliWordOp_symplectic, h]
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

/-- Every graph vertex operator is an involution. -/
theorem vertexOperator_sq (G : IndexedGraph M E) (v : Fin M) :
    vertexOperator G v * vertexOperator G v = 1 := by
  unfold vertexOperator
  exact pauliWordOp_mul_self E (vertexWord G v)

/-- Every graph edge operator is an involution. -/
theorem edgeOperator_sq (G : IndexedGraph M E) (e : Fin E) :
    edgeOperator G e * edgeOperator G e = 1 := by
  unfold edgeOperator
  exact pauliWordOp_mul_self E (edgeWord G e)

/-- Arbitrary graph vertex operators commute. -/
theorem vertexOperator_commute (G : IndexedGraph M E) (v w : Fin M) :
    vertexOperator G v * vertexOperator G w = vertexOperator G w * vertexOperator G v := by
  unfold vertexOperator
  exact pauliWordOp_commute_of_form_zero _ _ (symplecticForm_vertex_vertex_eq G v w)

/-- Graph edge operators whose edges share one endpoint anticommute. -/
theorem edgeOperator_anticommute_of_share (G : IndexedGraph M E) (e f : Fin E)
    (h : ShareOneEndpoint G e f) :
    edgeOperator G e * edgeOperator G f = -(edgeOperator G f * edgeOperator G e) := by
  unfold edgeOperator
  exact pauliWordOp_anticommute_of_form_one _ _
    (by
      rw [symplecticForm_edge_edge_eq]
      exact edgeWord_z_sum_eq_one_of_share G e f h)

/-- Graph edge operators with no common endpoint commute. -/
theorem edgeOperator_commute_of_noCoincidence (G : IndexedGraph M E) (e f : Fin E)
    (h : NoEndpointCoincidence G e f) :
    edgeOperator G e * edgeOperator G f = edgeOperator G f * edgeOperator G e := by
  unfold edgeOperator
  exact pauliWordOp_commute_of_form_zero _ _
    (by
      rw [symplecticForm_edge_edge_eq]
      exact edgeWord_z_sum_eq_zero_of_none G e f h)

/-- A graph vertex operator anticommutes with the operator of an incident edge. -/
theorem vertexOperator_anticommute_of_incident (G : IndexedGraph M E) (v : Fin M)
    (e : Fin E) (h : incident G v e) :
    vertexOperator G v * edgeOperator G e = -(edgeOperator G e * vertexOperator G v) := by
  unfold vertexOperator edgeOperator
  exact pauliWordOp_anticommute_of_form_one _ _
    (by
      rw [symplecticForm_vertex_edge_eq]
      simp [h])

/-- A graph vertex operator commutes with the operator of a non-incident edge. -/
theorem vertexOperator_commute_of_not_incident (G : IndexedGraph M E) (v : Fin M)
    (e : Fin E) (h : ¬ incident G v e) :
    vertexOperator G v * edgeOperator G e = edgeOperator G e * vertexOperator G v := by
  unfold vertexOperator edgeOperator
  exact pauliWordOp_commute_of_form_zero _ _
    (by
      rw [symplecticForm_vertex_edge_eq]
      simp [h])

end Qatlib.Papers.BKFermion17.QubitAlgebra
