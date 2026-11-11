/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright: paper-layer formalization for SparseCIMat13.
Source: B. Toloui and P. J. Love, "Quantum Algorithms for Quantum Chemistry based on the
sparsity of the CI-matrix", arXiv:1312.2579 (2013), Section III D p.7 and Appendix A
(Eqs. (A1)-(A54)), Main Theorem of Appendix A.5, pdf p.15-18.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Edge-label collision theorem for the CI graph (arXiv:1312.2579, App. A.5)

The graph of the CI matrix has one node per configuration `orb(x)` (a `ne`-element subset
of `Fin no`), ordered by the binary index of Eq. (13).  Two nodes are connected when the
configurations differ by one or two orbitals (Slater rules, Eqs. (5)-(8)).  Section III D
(p.7) separates the two excitation classes before assigning labels: single-excitation
edges and double-excitation edges are coloured in disjoint label ranges.  Accordingly,
for an edge `{x,y}`, `x < y`, the label pair of Appendix A is computed inside the class of
that edge:

  `e_{x→y} = #{y' | index y' ≤ index y, y' differs from x by k orbitals}`,
  `e_{y→x} = #{x' | index x' ≤ index x, x' differs from y by k orbitals}`,

where `k = 1` for a single-excitation edge and `k = 2` for a double-excitation edge.
This is the semantics used by the closed forms (A12)-(A17) and by the case analysis
(A24)-(A54), which only count same-class neighbours.

The Main Theorem of Appendix A.5 states that for `x < y < z` with `x ~ y` and `y ~ z`
in the same excitation class, the two adjacent edges cannot have identical label pairs.
Consequently the standard `(i,j)` colouring needs no third label for CI graphs (claim
c002 of the paper); for a general graph a third label is necessary, as the concrete
5-vertex path counterexample below shows.

## Formalization status

The two same-class Main Theorem statements are recorded below as faithful `Prop`-valued
definitions.  Their proofs are the remaining gap of this paper.  A proof requires
re-deriving the edge-label closed forms, because the printed Appendix A formulas are not
correct as extracted: the single-excitation out-label (A12) is missing the term counting
occupied orbitals strictly between the removed and added orbital, and the pair-excitation
formulas (A16)-(A17) do not reproduce the neighbour counts (checked exhaustively for small
orbital numbers).  The corrected single-excitation formulas, which were verified
exhaustively for `no ≤ 8`, are

  `e_{x→y} = R1(x,u) + E_u(x)·L_u(x) + ne − L_d(x) − H_u(x)`,
  `e_{y→x} = R1(x,u) + 1 + d − L_d(x)`,

with `d` the removed orbital, `u > d` the added orbital, `L_t(x) = #{i ∈ x | i < t}`,
`E_t(x) = t − L_t(x)`, `H_t(x) = #{i ∈ x | i > t}` and
`R1(x,u) = ∑_{i ∈ x, i > u} (i − L_i(x))`.  The corrected pair-excitation counts follow
from the residual-maximum decomposition of `index (x−A+B) ≤ index y`, and the three
inclusion cases of (A24)-(A54) reduce to the comparison of `u' = u(y,z)` with
`u = u(x,y)`: the case `u' < u` gives `e_{z→y} > e_{y→x}`, the case `u' > u` gives
either `e_{y→z} > e_{x→y}` (when `y` has an occupied orbital in `(u,u')`) or the same
conclusion with the corrected `R1` comparison.  Mechanizing these counts and comparisons
is the documented next step.
-/

namespace Qatlib.Papers.SparseCIMat13.MainResults.Coloring

open Finset

/-- Paper Eq. (13): the binary index of a configuration,
`x = ∑_{χ ∈ orb(x)} 2^(χ-1)`.  With `Fin no` numbered from `0`, the exponent is
`i.val`. -/
def ciIndex {no : ℕ} (x : Finset (Fin no)) : ℕ :=
  ∑ i ∈ x, 2 ^ (i : ℕ)

/-- Single-orbital Slater excitation: the two configurations differ in exactly one
occupied orbital (nonzero CI-matrix entry of single-excitation type). -/
def ciSingleAdjacent {no : ℕ} (x y : Finset (Fin no)) : Prop :=
  (x \ y).card = 1 ∧ (y \ x).card = 1

/-- Two-orbital Slater excitation: the two configurations differ in exactly two
occupied orbitals (nonzero CI-matrix entry of pair-excitation type). -/
def ciDoubleAdjacent {no : ℕ} (x y : Finset (Fin no)) : Prop :=
  (x \ y).card = 2 ∧ (y \ x).card = 2

/-- Slater-rule adjacency of two configurations: they differ in exactly one or exactly two
orbitals (nonzero CI-matrix entry, Eqs. (5)-(8)). -/
def ciAdjacent {no : ℕ} (x y : Finset (Fin no)) : Prop :=
  ciSingleAdjacent x y ∨ ciDoubleAdjacent x y

/-- Single-excitation adjacency is decidable for finite configurations. -/
instance {no : ℕ} (x y : Finset (Fin no)) : Decidable (ciSingleAdjacent x y) := by
  unfold ciSingleAdjacent
  infer_instance

/-- Double-excitation adjacency is decidable for finite configurations. -/
instance {no : ℕ} (x y : Finset (Fin no)) : Decidable (ciDoubleAdjacent x y) := by
  unfold ciDoubleAdjacent
  infer_instance

/-- Configuration-interaction adjacency is decidable. -/
instance {no : ℕ} (x y : Finset (Fin no)) : Decidable (ciAdjacent x y) := by
  unfold ciAdjacent
  infer_instance

/-- Adjacency is symmetric (the CI matrix is Hermitian). -/
theorem ciAdjacent_symm {no : ℕ} {x y : Finset (Fin no)} (h : ciAdjacent x y) :
    ciAdjacent y x := by
  rcases h with h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩

/-- Appendix A, Eq. (A1)/(A2): for an ordered pair `x < y`, the number of nodes `y' ≤ y`
to which `x` is connected.  This is the first component `e_{x→y}` of the edge label pair,
after restricting the adjacency relation to the excitation class of the edge. -/
def graphEdgeOut {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidableRel adj] (ord : α → ℕ) (x y : α) : ℕ :=
  (Finset.univ.filter (fun y' => ord y' ≤ ord y ∧ adj x y')).card

/-- Appendix A, Eq. (A1): for an ordered pair `x < y`, the number of nodes `x' ≤ x` to
which `y` is connected.  This is the second component `e_{y→x}` of the edge label pair,
after restricting the adjacency relation to the excitation class of the edge. -/
def graphEdgeIn {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) [DecidableRel adj] (ord : α → ℕ) (x y : α) : ℕ :=
  (Finset.univ.filter (fun x' => ord x' ≤ ord x ∧ adj x' y)).card

/-- Single-excitation outgoing label `e_{x→y}`: neighbours of `x` of single-excitation
type with binary index at most that of `y`. -/
def singleEdgeOut {no : ℕ} (x y : Finset (Fin no)) : ℕ :=
  graphEdgeOut ciSingleAdjacent ciIndex x y

/-- Single-excitation incoming label `e_{y→x}`: neighbours of `y` of single-excitation
type with binary index at most that of `x`. -/
def singleEdgeIn {no : ℕ} (x y : Finset (Fin no)) : ℕ :=
  graphEdgeIn ciSingleAdjacent ciIndex x y

/-- Pair-excitation outgoing label `e_{x→y}`: neighbours of `x` of pair-excitation type
with binary index at most that of `y`. -/
def doubleEdgeOut {no : ℕ} (x y : Finset (Fin no)) : ℕ :=
  graphEdgeOut ciDoubleAdjacent ciIndex x y

/-- Pair-excitation incoming label `e_{y→x}`: neighbours of `y` of pair-excitation type
with binary index at most that of `x`. -/
def doubleEdgeIn {no : ℕ} (x y : Finset (Fin no)) : ℕ :=
  graphEdgeIn ciDoubleAdjacent ciIndex x y

/-- Appendix A.5, Main Theorem for single-excitation edges (faithful statement
contract): for any trio of states `x < y < z` whose graph nodes are connected by
single-orbital excitations, the two adjacent single-excitation edges do not carry the
same label pair `(e_{x→y}, e_{y→x}) = (e_{y→z}, e_{z→y})`.  This is the statement whose
proof is the remaining gap; the printed Appendix A formulas need the erratum recorded in
the module docstring before the case analysis (A24)-(A37) can be mechanized. -/
def ci_single_edgeLabel_no_collision : Prop :=
  ∀ (no ne : ℕ) (x y z : Finset (Fin no)),
    x.card = ne → y.card = ne → z.card = ne →
    ciIndex x < ciIndex y → ciIndex y < ciIndex z →
    ciSingleAdjacent x y → ciSingleAdjacent y z →
    ¬ (singleEdgeOut x y = singleEdgeOut y z ∧
       singleEdgeIn x y = singleEdgeIn y z)

/-- Appendix A.5, Main Theorem for pair-excitation edges (faithful statement contract):
for any trio of states `x < y < z` whose graph nodes are connected by two-orbital
excitations, the two adjacent pair-excitation edges do not carry the same label pair.
The pair-excitation counting formulas (A16)-(A17) require the correction described in
the module docstring before the case analysis (A38)-(A54) can be mechanized. -/
def ci_double_edgeLabel_no_collision : Prop :=
  ∀ (no ne : ℕ) (x y z : Finset (Fin no)),
    x.card = ne → y.card = ne → z.card = ne →
    ciIndex x < ciIndex y → ciIndex y < ciIndex z →
    ciDoubleAdjacent x y → ciDoubleAdjacent y z →
    ¬ (doubleEdgeOut x y = doubleEdgeOut y z ∧
       doubleEdgeIn x y = doubleEdgeIn y z)

/-- Claim c002 (paper Section III D, p.7), main direction: for CI graphs the standard
`(i,j)` colouring needs no third label.  Since Section III D separates the two excitation
classes before labelling, it suffices that neither class has a collision on adjacent
edges; mixed-class adjacent edges are distinguished by the disjoint colour ranges.
This is the `Prop`-valued contract combining the two same-class Main Theorems. -/
def ci_third_color_label_not_needed : Prop :=
  ci_single_edgeLabel_no_collision ∧ ci_double_edgeLabel_no_collision

/-! ## General graphs do need a third colour label (claim c002, second half) -/

/-- The path graph on 5 vertices `0 - 1 - 2 - 3 - 4`, used to show that for a general
Hamiltonian the pair `(i,j)` can collide on adjacent edges (Section III D, p.7). -/
def pathAdj (a b : Fin 5) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

/-- Adjacency in the finite path is decidable. -/
instance : DecidableRel pathAdj := fun a b => by
  unfold pathAdj
  infer_instance

/-- On the 5-vertex path, the label pairs of the adjacent edges `(1,2)` and `(2,3)`
(both equal to `(2,1)`) coincide, so a third colour label is necessary in general.
Proved by evaluation of the definitions. -/
theorem pathAdj_collision :
    graphEdgeOut pathAdj (fun i : Fin 5 => i.val) ⟨1, by omega⟩ ⟨2, by omega⟩ =
      graphEdgeOut pathAdj (fun i : Fin 5 => i.val) ⟨2, by omega⟩ ⟨3, by omega⟩ ∧
    graphEdgeIn pathAdj (fun i : Fin 5 => i.val) ⟨1, by omega⟩ ⟨2, by omega⟩ =
      graphEdgeIn pathAdj (fun i : Fin 5 => i.val) ⟨2, by omega⟩ ⟨3, by omega⟩ := by
  decide

/-- Claim c002, negative direction: on a general graph (here the 5-vertex path) adjacent
edges can carry equal label pairs, so the third colour label `v` is genuinely needed when
the CI/Slater structure is absent.  Witness: nodes `1 < 2 < 3`. -/
theorem general_graph_needs_third_color_label :
    ∃ (ord : Fin 5 → ℕ) (x y z : Fin 5), ord x < ord y ∧ ord y < ord z ∧
      pathAdj x y ∧ pathAdj y z ∧
      graphEdgeOut pathAdj ord x y = graphEdgeOut pathAdj ord y z ∧
      graphEdgeIn pathAdj ord x y = graphEdgeIn pathAdj ord y z :=
  ⟨fun i => i.val, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
    by decide, by decide, by decide, by decide,
    pathAdj_collision.1, pathAdj_collision.2⟩

end Qatlib.Papers.SparseCIMat13.MainResults.Coloring
