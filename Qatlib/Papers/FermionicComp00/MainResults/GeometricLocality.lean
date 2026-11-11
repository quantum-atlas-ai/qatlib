/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Graph locality and encoded gate representations

`sourceGraph` describes a symmetric loop-free finite edge set, with incident-edge counts and
their maximum. The module also defines a small matrix gate family, its gate-counted circuits,
and the intertwining predicate `Represents` for an encoding matrix.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `sourceDegree_le_maxDegree`: bounds each incident-edge count.
* `sourceSymplecticCircuit`: records circuits and their gate counts.
* `Represents`: compatibility of operators with an encoding.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.GeometricLocality

/-- A finite graph specified by ordered edges, closed under reversal and containing no loops. -/
structure sourceGraph (m : ℕ) where
  edges : Finset (Fin m × Fin m)
  symm : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  noLoop : ∀ e ∈ edges, e.1 ≠ e.2

/-- The number of ordered edges incident to `v` in the symmetric edge set. -/
def sourceDegree {m : ℕ} (G : sourceGraph m) (v : Fin m) : ℕ :=
  (G.edges.filter (fun e => e.1 = v ∨ e.2 = v)).card

/-- The maximum of the incident ordered-edge counts over all vertices, with value zero for an
empty vertex set. -/
def sourceMaxDegree {m : ℕ} (G : sourceGraph m) : ℕ :=
  Finset.univ.sup (sourceDegree G)

/-- Every vertex incident-edge count is bounded by the maximum count. -/
theorem sourceDegree_le_maxDegree {m : ℕ} (G : sourceGraph m) (_hm : 0 < m) (v : Fin m) :
    sourceDegree G v ≤ sourceMaxDegree G := by
  unfold sourceMaxDegree
  exact Finset.le_sup (Finset.mem_univ v)

/-- The one-qubit Hadamard matrix in the computational basis. -/
def sourceH : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.of fun y x =>
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (-1 : ℂ) ^ (if x 0 ∧ y 0 then 1 else 0)

/-- The two-qubit controlled bit-flip matrix with the first bit as control. -/
def sourceLambdaX : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.of fun y x => if y 0 = x 0 ∧ y 1 = (x 1 ^^ x 0) then 1 else 0

/-- The diagonal two-qubit gate multiplying the doubly occupied basis state by `Complex.I`. -/
def sourceLambdaI : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.diagonal (fun x => if x 0 ∧ x 1 then Complex.I else 1)

/-- The arity-indexed family consisting of `sourceH` at arity one and `sourceLambdaX`,
`sourceLambdaI` at arity two. -/
def sourceSymplecticGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceH}
  | 2 => {sourceLambdaX, sourceLambdaI}
  | _ => ∅

/-- The Hadamard matrix belongs to the one-qubit source gate family. -/
theorem sourceH_mem : sourceH ∈ sourceSymplecticGates 1 := by
  simp [sourceSymplecticGates]

/-- The controlled bit-flip matrix belongs to the two-qubit source gate family. -/
theorem sourceLambdaX_mem : sourceLambdaX ∈ sourceSymplecticGates 2 := by
  simp [sourceSymplecticGates]

/-- The controlled imaginary-phase matrix belongs to the two-qubit source gate family. -/
theorem sourceLambdaI_mem : sourceLambdaI ∈ sourceSymplecticGates 2 := by
  simp [sourceSymplecticGates]

/-- The matrix obtained by applying `G` at the selected positions and requiring all other
register bits to remain unchanged. -/
def applyAt {m p : ℕ} (pos : Fin p → Fin m) (G : Matrix (Reg p) (Reg p) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x => G (fun t => y (pos t)) (fun t => x (pos t)) *
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ∉ Finset.univ.image pos)),
      (if y s = x s then (1 : ℂ) else 0)

/-- The gate-counted closure of the identity under left multiplication by injectively placed
source gates. -/
inductive sourceSymplecticCircuit (u : ℕ) : Matrix (Reg u) (Reg u) ℂ → ℕ → Prop
  | one : sourceSymplecticCircuit u 1 0
  | gate {p : ℕ} {G : Matrix (Reg p) (Reg p) ℂ} (hG : G ∈ sourceSymplecticGates p)
      (pos : Fin p → Fin u) (hpos : Function.Injective pos)
      {V : Matrix (Reg u) (Reg u) ℂ} {g : ℕ} (hV : sourceSymplecticCircuit u V g) :
      sourceSymplecticCircuit u (applyAt pos G * V) (g + 1)

/-- The matrix sending each computational basis vector indexed by `x` to the basis vector
indexed by `J x`. -/
def encodingMatrix {m q : ℕ} (J : Reg m → Reg q) : Matrix (Reg q) (Reg m) ℂ :=
  Matrix.of fun y x => if y = J x then 1 else 0

/-- The intertwining relation expressing that the encoded operator acts compatibly with the
original operator through `encodingMatrix J`. -/
def Represents {m q : ℕ} (J : Reg m → Reg q) (U : Matrix (Reg m) (Reg m) ℂ)
    (V : Matrix (Reg q) (Reg q) ℂ) : Prop :=
  V * encodingMatrix J = encodingMatrix J * U

end Qatlib.Papers.FermionicComp00.MainResults.GeometricLocality
