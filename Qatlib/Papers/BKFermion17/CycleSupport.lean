/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.Relations

/-!
# Cycle support and the hydrogen loop

This module enumerates even-degree edge subsets of the four-vertex hydrogen graph. It shows that
the full edge set is its unique nonempty cycle subset and relates its ordered edge list to the
Pauli loop product. Products of operators fixing a state also fix that state. See
[SetiaWhitfield2018].

## Main statements

* `h2_unique_loop`: the only nonempty even-degree subset is the full edge set.
* `h2Loop_eq_loopProduct`: the loop is the ordered product of its edge generators.
* `stabilizer_compose`: fixed states are preserved by operator products.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BKFermion17.CycleSupport

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Papers.BKFermion17.H2Edge
open Qatlib.Papers.BKFermion17.H2Edge

/-- If both `P` and `Q` fix `ψ`, then their matrix product fixes `ψ`. -/
theorem stabilizer_compose {n : ℕ} (P Q : Matrix (Reg n) (Reg n) ℂ) (ψ : Reg n → ℂ)
    (hP : P.mulVec ψ = ψ) (hQ : Q.mulVec ψ = ψ) : (P * Q).mulVec ψ = ψ := by
  rw [← Matrix.mulVec_mulVec, hQ, hP]

/-- The product of two loop matrices fixing `ψ` also fixes `ψ`. -/
theorem loop_composition_stabilizes {n : ℕ} (C₁ C₂ : Matrix (Reg n) (Reg n) ℂ)
    (ψ : Reg n → ℂ) (h₁ : C₁.mulVec ψ = ψ) (h₂ : C₂.mulVec ψ = ψ) :
    (C₁ * C₂).mulVec ψ = ψ :=
  stabilizer_compose C₁ C₂ ψ h₁ h₂

/-- The finite edge set used for the four-vertex hydrogen example. -/
def h2EdgeSet : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (1, 2), (2, 3), (0, 3)}

/-- The parity of the number of edges in `S` incident to vertex `v`. -/
def degreeParity (S : Finset (Fin 4 × Fin 4)) (v : Fin 4) : ℕ :=
  (S.filter (fun e => e.1 = v ∨ e.2 = v)).card % 2

/-- The set `S` is contained in `h2EdgeSet` and has even degree at every vertex. -/
def IsCycleSet (S : Finset (Fin 4 × Fin 4)) : Prop :=
  S ⊆ h2EdgeSet ∧ ∀ v : Fin 4, degreeParity S v = 0

/-- The hydrogen graph has four edges. -/
theorem h2EdgeSet_card : h2EdgeSet.card = 4 := by
  decide

/-- The hydrogen graph has four vertices. -/
theorem h2_vertex_count : Fintype.card (Fin 4) = 4 :=
  Fintype.card_fin 4

/-- The edge count minus the vertex count plus one equals one for the hydrogen graph. -/
theorem h2_independent_loop_count :
    (h2EdgeSet.card : ℤ) - (Fintype.card (Fin 4) : ℤ) + 1 = 1 := by
  rw [h2EdgeSet_card, h2_vertex_count]
  norm_num

/-- The even-degree subsets of the hydrogen edge set are exactly the empty set and the full edge
set. -/
theorem h2_cycles_filter :
    h2EdgeSet.powerset.filter (fun S => ∀ v : Fin 4, degreeParity S v = 0) = {∅, h2EdgeSet} := by
  decide

/-- Every even-degree subset of the hydrogen edge set is either empty or the full edge set. See
[Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem h2_cycle_space (S : Finset (Fin 4 × Fin 4)) (hS : S ∈ h2EdgeSet.powerset)
    (h : ∀ v : Fin 4, degreeParity S v = 0) : S = ∅ ∨ S = h2EdgeSet := by
  have hmem : S ∈ h2EdgeSet.powerset.filter (fun S => ∀ v : Fin 4, degreeParity S v = 0) :=
    Finset.mem_filter.mpr ⟨hS, h⟩
  rw [h2_cycles_filter] at hmem
  simpa using hmem

/-- There is exactly one nonempty even-degree subset of the hydrogen edge set. -/
theorem h2_nonempty_cycles_card :
    (h2EdgeSet.powerset.filter
        (fun S => (∀ v : Fin 4, degreeParity S v = 0) ∧ S ≠ ∅)).card = 1 := by
  decide

/-- The set of nonempty even-degree subsets of the hydrogen edge set is the singleton containing
the full edge set. -/
theorem h2_unique_loop :
    (h2EdgeSet.powerset.filter
        (fun S => (∀ v : Fin 4, degreeParity S v = 0) ∧ S ≠ ∅)) = {h2EdgeSet} := by
  decide

/-- The ordered list of directed edges traversing the hydrogen loop. -/
def h2LoopEdges : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 2), (2, 3), (3, 0)]

/-- The ordered Pauli product of the hydrogen edge generators along a list of directed edges. -/
def loopProduct : List (Fin 4 × Fin 4) → PauliElem 4
  | [] => 1
  | e :: es => PauliElem.mul (h2A e.1 e.2) (loopProduct es)

/-- The hydrogen loop equals the ordered product along `h2LoopEdges`. -/
theorem h2Loop_eq_loopProduct : h2Loop = loopProduct h2LoopEdges := by
  decide

/-- Forgetting edge orientation, the loop edge list has the same support as `h2EdgeSet`. -/
theorem h2LoopEdges_support :
    h2LoopEdges.toFinset.image (fun e => (min e.1 e.2, max e.1 e.2)) =
      h2EdgeSet.image (fun e => (min e.1 e.2, max e.1 e.2)) := by
  decide

end Qatlib.Papers.BKFermion17.CycleSupport
