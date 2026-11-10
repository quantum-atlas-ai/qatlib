/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped Classical Matrix.Norms.L2Operator

namespace Qatlib.Papers.FermionicComp00.MainResults.FermionicGates

def sourceLfmPhase : Matrix (Reg 1) (Reg 1) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • numberOp (0 : Fin 1))

def sourceLfmHop : Matrix (Reg 2) (Reg 2) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    (creation (0 : Fin 2) * annihilation (1 : Fin 2) +
      creation (1 : Fin 2) * annihilation (0 : Fin 2)))

def sourceLfmPair : Matrix (Reg 2) (Reg 2) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    (annihilation (1 : Fin 2) * annihilation (0 : Fin 2) +
      creation (0 : Fin 2) * creation (1 : Fin 2)))

def sourceLfmDensity : Matrix (Reg 2) (Reg 2) ℂ :=
  NormedSpace.exp (((Real.pi : ℂ) * Complex.I) •
    (numberOp (0 : Fin 2) * numberOp (1 : Fin 2)))

def sourceFermionGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceLfmPhase}
  | 2 => {sourceLfmHop, sourceLfmPair, sourceLfmDensity}
  | _ => ∅

theorem sourceLfmPhase_mem : sourceLfmPhase ∈ sourceFermionGates 1 := by
  simp [sourceFermionGates]

theorem sourceLfmHop_mem : sourceLfmHop ∈ sourceFermionGates 2 := by
  simp [sourceFermionGates]

theorem sourceLfmPair_mem : sourceLfmPair ∈ sourceFermionGates 2 := by
  simp [sourceFermionGates]

theorem sourceLfmDensity_mem : sourceLfmDensity ∈ sourceFermionGates 2 := by
  simp [sourceFermionGates]

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

end Qatlib.Papers.FermionicComp00.MainResults.FermionicGates
