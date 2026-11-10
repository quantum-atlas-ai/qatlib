/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical Matrix.Norms.L2Operator

namespace Qatlib.Papers.FermionicComp00.MainResults.ParityGates

def sourcePhase : ℂ := Complex.exp (Complex.I * (Real.pi / 4 : ℂ))

def sourceLambdaPhase : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.diagonal (fun x => if x 0 then sourcePhase else 1)

def sourceLambdaZ : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.diagonal (fun x => if x 0 ∧ x 1 then (-1 : ℂ) else 1)

def sourceHTilde : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.of fun y x =>
    if y 0 = (x 0 ^^ x 1 ^^ y 1) then
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (-1 : ℂ) ^ (if x 1 ∧ y 1 then 1 else 0)
    else 0

def sourceParityGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceLambdaPhase}
  | 2 => {sourceLambdaZ, sourceHTilde}
  | _ => ∅

theorem sourceLambdaZ_mem : sourceLambdaZ ∈ sourceParityGates 2 := by
  simp [sourceParityGates]

def applyAt {m p : ℕ} (pos : Fin p → Fin m) (G : Matrix (Reg p) (Reg p) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x => G (fun t => y (pos t)) (fun t => x (pos t)) *
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ∉ Finset.univ.image pos)),
      (if y s = x s then (1 : ℂ) else 0)

inductive GateProduct {m : ℕ} (gates : (p : ℕ) → Set (Matrix (Reg p) (Reg p) ℂ)) :
    Matrix (Reg m) (Reg m) ℂ → Prop
  | one : GateProduct gates 1
  | apply {p : ℕ} {G : Matrix (Reg p) (Reg p) ℂ} (hG : G ∈ gates p)
      (pos : Fin p → Fin m) (hpos : Function.Injective pos)
      {V : Matrix (Reg m) (Reg m) ℂ} (hV : GateProduct gates V) :
      GateProduct gates (applyAt pos G * V)

end Qatlib.Papers.FermionicComp00.MainResults.ParityGates
