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

namespace Qatlib.Papers.FermionicComp00.MainResults.MajoranaGates

def sourceMajorana {m : ℕ} (j : Fin (2 * m)) : Matrix (Reg m) (Reg m) ℂ :=
  if j.val % 2 = 0 then
    creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ +
      annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩
  else
    (-Complex.I) •
      (annihilation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩ -
        creation ⟨j.val / 2, Nat.div_lt_of_lt_mul j.isLt⟩)

def sourceMajoranaPairGate : Matrix (Reg 1) (Reg 1) ℂ :=
  NormedSpace.exp ((Real.pi / 8 : ℝ) •
    (sourceMajorana (m := 1) (0 : Fin 2) * sourceMajorana (m := 1) (1 : Fin 2)))

def sourceMajoranaFourGate : Matrix (Reg 2) (Reg 2) ℂ :=
  NormedSpace.exp ((((Real.pi / 4 : ℝ) : ℂ) * Complex.I) •
    (sourceMajorana (m := 2) (0 : Fin 4) * sourceMajorana (m := 2) (1 : Fin 4) *
      sourceMajorana (m := 2) (2 : Fin 4) * sourceMajorana (m := 2) (3 : Fin 4)))

def sourceMajoranaGates (p : ℕ) : Set (Matrix (Reg p) (Reg p) ℂ) :=
  match p with
  | 1 => {sourceMajoranaPairGate}
  | 2 => {sourceMajoranaFourGate}
  | _ => ∅

theorem sourceMajoranaPairGate_mem : sourceMajoranaPairGate ∈ sourceMajoranaGates 1 := by
  simp [sourceMajoranaGates]

theorem sourceMajoranaFourGate_mem : sourceMajoranaFourGate ∈ sourceMajoranaGates 2 := by
  simp [sourceMajoranaGates]

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

end Qatlib.Papers.FermionicComp00.MainResults.MajoranaGates
