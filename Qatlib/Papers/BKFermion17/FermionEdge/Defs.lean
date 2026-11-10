/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BKFermion17.FermionEdge
open Matrix
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
open Qatlib.Foundations.PureStateMath

def paperCeven {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  majoranaEven i

def paperCodd {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  -majoranaOdd i

def edgeB {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Complex.I • (majoranaEven i * majoranaOdd i)

def edgeA {n : ℕ} (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  (-Complex.I) • (majoranaEven i * majoranaEven j)

@[simp] theorem paperCodd_eq {n : ℕ} (i : Fin n) :
    paperCodd i = -majoranaOdd i := rfl

theorem edgeB_eq {n : ℕ} (i : Fin n) :
    edgeB i = Complex.I • (majoranaEven i * majoranaOdd i) := rfl

theorem edgeA_eq {n : ℕ} (i j : Fin n) :
    edgeA i j = (-Complex.I) • (majoranaEven i * majoranaEven j) := rfl

theorem edgeA_antisym {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeA j i = -edgeA i j := by
  unfold edgeA
  have h : majoranaEven j * majoranaEven i = -(majoranaEven i * majoranaEven j) :=
    eq_neg_of_add_eq_zero_left (majoranaEven_anticommute n j i (Ne.symm hij))
  rw [h, smul_neg]

end Qatlib.Papers.BKFermion17.FermionEdge
