/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.GeometricLocality

structure sourceGraph (m : ℕ) where
  edges : Finset (Fin m × Fin m)
  symm : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  noLoop : ∀ e ∈ edges, e.1 ≠ e.2

def sourceDegree {m : ℕ} (G : sourceGraph m) (v : Fin m) : ℕ :=
  (G.edges.filter (fun e => e.1 = v ∨ e.2 = v)).card

def sourceMaxDegree {m : ℕ} (G : sourceGraph m) : ℕ :=
  Finset.univ.sup (sourceDegree G)

theorem sourceDegree_le_maxDegree {m : ℕ} (G : sourceGraph m) (_hm : 0 < m) (v : Fin m) :
    sourceDegree G v ≤ sourceMaxDegree G := by
  unfold sourceMaxDegree
  exact Finset.le_sup (Finset.mem_univ v)

def sourceH : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.of fun y x =>
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (-1 : ℂ) ^ (if x 0 ∧ y 0 then 1 else 0)

def sourceLambdaX : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.of fun y x => if y 0 = x 0 ∧ y 1 = (x 1 ^^ x 0) then 1 else 0

def sourceLambdaI : Matrix (Reg 2) (Reg 2) ℂ :=
  Matrix.diagonal (fun x => if x 0 ∧ x 1 then Complex.I else 1)

def sourceSymplecticGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceH}
  | 2 => {sourceLambdaX, sourceLambdaI}
  | _ => ∅

theorem sourceH_mem : sourceH ∈ sourceSymplecticGates 1 := by
  simp [sourceSymplecticGates]

theorem sourceLambdaX_mem : sourceLambdaX ∈ sourceSymplecticGates 2 := by
  simp [sourceSymplecticGates]

theorem sourceLambdaI_mem : sourceLambdaI ∈ sourceSymplecticGates 2 := by
  simp [sourceSymplecticGates]

def applyAt {m p : ℕ} (pos : Fin p → Fin m) (G : Matrix (Reg p) (Reg p) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x => G (fun t => y (pos t)) (fun t => x (pos t)) *
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ∉ Finset.univ.image pos)),
      (if y s = x s then (1 : ℂ) else 0)

inductive sourceSymplecticCircuit (u : ℕ) : Matrix (Reg u) (Reg u) ℂ → ℕ → Prop
  | one : sourceSymplecticCircuit u 1 0
  | gate {p : ℕ} {G : Matrix (Reg p) (Reg p) ℂ} (hG : G ∈ sourceSymplecticGates p)
      (pos : Fin p → Fin u) (hpos : Function.Injective pos)
      {V : Matrix (Reg u) (Reg u) ℂ} {g : ℕ} (hV : sourceSymplecticCircuit u V g) :
      sourceSymplecticCircuit u (applyAt pos G * V) (g + 1)

def encodingMatrix {m q : ℕ} (J : Reg m → Reg q) : Matrix (Reg q) (Reg m) ℂ :=
  Matrix.of fun y x => if y = J x then 1 else 0

def Represents {m q : ℕ} (J : Reg m → Reg q) (U : Matrix (Reg m) (Reg m) ℂ)
    (V : Matrix (Reg q) (Reg q) ℂ) : Prop :=
  V * encodingMatrix J = encodingMatrix J * U

end Qatlib.Papers.FermionicComp00.MainResults.GeometricLocality
