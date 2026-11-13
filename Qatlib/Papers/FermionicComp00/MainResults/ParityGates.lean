/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Parity-preserving source gates

The module defines a one-mode phase, a controlled sign, and the two-mode matrix `sourceHTilde`,
whose nonzero entries preserve bit parity. These matrices form `sourceParityGates`;
`GateProduct` records products of gates placed at injectively selected register positions.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `sourceParityGates`: the arity-indexed source gate family.
* `sourceLambdaZ_mem`: the controlled sign belongs to that family.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical Matrix.Norms.L2Operator

namespace Qatlib.Papers.FermionicComp00.MainResults.ParityGates

/-- The complex phase `exp (i * π / 4)`. -/
def sourcePhase : ℂ := Complex.exp (Complex.I * (Real.pi / 4 : ℂ))

/-- The diagonal one-mode gate applying `sourcePhase` to the occupied basis state. -/
def sourceLambdaPhase : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.diagonal (fun x => if x 0 then sourcePhase else 1)

/-- The diagonal two-mode gate applying a minus sign exactly to the doubly occupied basis state. -/
def sourceLambdaZ : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.diagonal (fun x => if x 0 ∧ x 1 then (-1 : ℂ) else 1)

/-- The two-mode matrix with Hadamard amplitudes in the second bit and a first-bit constraint
that preserves total bit parity. -/
def sourceHTilde : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.of fun y x =>
    if y 0 = (x 0 ^^ x 1 ^^ y 1) then
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (-1 : ℂ) ^ (if x 1 ∧ y 1 then 1 else 0)
    else 0

/-- The arity-indexed family containing `sourceLambdaPhase` at arity one and `sourceLambdaZ`,
`sourceHTilde` at arity two. -/
def sourceParityGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceLambdaPhase}
  | 2 => {sourceLambdaZ, sourceHTilde}
  | _ => ∅

/-- The controlled-sign matrix belongs to the two-mode parity gate family. -/
theorem sourceLambdaZ_mem : sourceLambdaZ ∈ sourceParityGates 2 := by
  simp [sourceParityGates]

/-- The matrix obtained by applying `G` at the selected positions and requiring all other
register bits to remain unchanged. -/
def applyAt {m p : ℕ} (pos : Fin p → Fin m) (G : Matrix (Reg p) (Reg p) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x => G (fun t => y (pos t)) (fun t => x (pos t)) *
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ∉ Finset.univ.image pos)),
      (if y s = x s then (1 : ℂ) else 0)

/-- Matrices generated from the identity by left multiplication with gates placed at injectively
selected register positions. -/
inductive GateProduct {m : ℕ} (gates : (p : ℕ) → Set (Matrix (Reg p) (Reg p) ℂ)) :
    Matrix (Reg m) (Reg m) ℂ → Prop
  | one : GateProduct gates 1
  | apply {p : ℕ} {G : Matrix (Reg p) (Reg p) ℂ} (hG : G ∈ gates p)
      (pos : Fin p → Fin m) (hpos : Function.Injective pos)
      {V : Matrix (Reg m) (Reg m) ℂ} (hV : GateProduct gates V) :
      GateProduct gates (applyAt pos G * V)

end Qatlib.Papers.FermionicComp00.MainResults.ParityGates
