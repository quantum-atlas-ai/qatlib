module

public import Qatlib.Papers.BKFermion17.QubitAlgebra.Relations

@[expose] public section

/-!
# Consumer regression for the general BKSF qubit edge algebra

This ordinary-module consumer specializes the general graph edge algebra to two concrete
non-degenerate graphs: the three-vertex triangle with three edges, and the four-vertex graph
with the two disjoint edges `(0, 1)` and `(2, 3)`. It exercises the general anticommutation,
commutation, involution, and incidence statements on actual `8`- and `4`-dimensional edge
registers, and records a nonzero matrix entry to witness that the edge generator is not the
identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace QatlibTests.BKFermion17QubitAlgebraRegression

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.GraphWords
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Papers.BKFermion17.QubitAlgebra

/-- The three-vertex triangle graph with edges `(0, 1)`, `(1, 2)`, and `(0, 2)`. -/
def triangleGraph : IndexedGraph 3 3 where
  left := ![0, 1, 0]
  right := ![1, 2, 2]
  ordered := by decide
  simple := by decide

/-- The four-vertex graph with the two disjoint edges `(0, 1)` and `(2, 3)`. -/
def disjointEdgeGraph : IndexedGraph 4 2 where
  left := ![0, 2]
  right := ![1, 3]
  ordered := by decide
  simple := by decide

/-- Adjacent triangle edges anticommute as matrix products on the eight-dimensional edge
register. -/
theorem triangle_edge_anticommute :
    edgeOperator triangleGraph 0 * edgeOperator triangleGraph 1 =
      -(edgeOperator triangleGraph 1 * edgeOperator triangleGraph 0) :=
  edgeOperator_anticommute_of_share triangleGraph 0 1 (by decide)

/-- The triangle vertex generators commute. -/
theorem triangle_vertex_commute :
    vertexOperator triangleGraph 0 * vertexOperator triangleGraph 1 =
      vertexOperator triangleGraph 1 * vertexOperator triangleGraph 0 :=
  vertexOperator_commute triangleGraph 0 1

/-- A triangle vertex generator anticommutes with its incident edge generator. -/
theorem triangle_vertex_edge_anticommute :
    vertexOperator triangleGraph 0 * edgeOperator triangleGraph 0 =
      -(edgeOperator triangleGraph 0 * vertexOperator triangleGraph 0) :=
  vertexOperator_anticommute_of_incident triangleGraph 0 0 (by decide)

/-- The triangle edge generator is an involution. -/
theorem triangle_edge_sq :
    edgeOperator triangleGraph 0 * edgeOperator triangleGraph 0 = 1 :=
  edgeOperator_sq triangleGraph 0

/-- The disjoint edge generators commute. -/
theorem disjoint_edge_commute :
    edgeOperator disjointEdgeGraph 0 * edgeOperator disjointEdgeGraph 1 =
      edgeOperator disjointEdgeGraph 1 * edgeOperator disjointEdgeGraph 0 :=
  edgeOperator_commute_of_noCoincidence disjointEdgeGraph 0 1 (by decide)

/-- A triangle vertex generator commutes with the opposite edge generator. -/
theorem triangle_vertex_edge_commute :
    vertexOperator triangleGraph 0 * edgeOperator triangleGraph 1 =
      edgeOperator triangleGraph 1 * vertexOperator triangleGraph 0 :=
  vertexOperator_commute_of_not_incident triangleGraph 0 1 (by decide)

/-- The general classification puts the adjacent triangle pair in the shared-endpoint case. -/
theorem triangle_classification :
    ShareOneEndpoint triangleGraph 0 1 ∨ NoEndpointCoincidence triangleGraph 0 1 :=
  shareOneEndpoint_or_noCoincidence triangleGraph (by decide)

/-- The word-level symplectic pairing of the adjacent triangle edges evaluates to one. -/
theorem triangle_edge_form_eq_one :
    symplecticForm
        (symplecticX (edgeWord triangleGraph 0), symplecticZ (edgeWord triangleGraph 0))
        (symplecticX (edgeWord triangleGraph 1), symplecticZ (edgeWord triangleGraph 1)) = 1 := by
  rw [symplecticForm_edge_edge_eq]
  decide

/-- A concrete off-diagonal matrix entry of the first triangle edge generator is one, so the
generator is not the identity matrix and the algebra statements are non-vacuous. -/
theorem triangle_edge_operator_offdiag :
    edgeOperator triangleGraph 0 (fun _ => false) (fun i => i = 0) = 1 := by
  unfold edgeOperator pauliWordOp
  rw [Fin.prod_univ_three]
  simp [edgeWord, triangleGraph, before, incident, otherEndpoint, pauli1Matrix,
    boolEquivFin2, pauliX, Matrix.one_apply]

end QatlibTests.BKFermion17QubitAlgebraRegression
