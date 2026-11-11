/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Fermionic edge-generator definitions

This module fixes the Majorana sign convention used in the paper and defines the fermionic
generators `edgeA` and `edgeB`. It relates them to the library Majorana operators and proves
reversal of the oriented edge generator changes its sign for distinct endpoints. See
[SetiaWhitfield2018].

## Main statements

* `paperCodd_eq`: relates the paper and library odd-Majorana conventions.
* `edgeB_eq`: expresses the vertex generator as a Majorana product.
* `edgeA_antisym`: reversing an edge negates its generator.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BKFermion17.FermionEdge
open Matrix
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Fermion
open Qatlib.Foundations.PureStateMath

/-- The paper’s even Majorana operator at mode `i`. -/
def paperCeven {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  majoranaEven i

/-- The paper’s odd Majorana operator at mode `i`, using its sign convention. -/
def paperCodd {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  -majoranaOdd i

/-- The vertex generator defined as `-Complex.I` times the paper’s even-odd Majorana product. -/
def edgeB {n : ℕ} (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Complex.I • (majoranaEven i * majoranaOdd i)

/-- The oriented edge generator defined as `-Complex.I` times the product of the paper’s even
Majorana operators at `i` and `j`. -/
def edgeA {n : ℕ} (i j : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  (-Complex.I) • (majoranaEven i * majoranaEven j)

/-- The paper’s odd Majorana operator is the negative of the library’s `majoranaOdd`. -/
@[simp] theorem paperCodd_eq {n : ℕ} (i : Fin n) :
    paperCodd i = -majoranaOdd i := rfl

/-- The vertex generator equals `Complex.I` times the library even-odd Majorana product. -/
theorem edgeB_eq {n : ℕ} (i : Fin n) :
    edgeB i = Complex.I • (majoranaEven i * majoranaOdd i) := rfl

/-- The oriented edge generator equals `-Complex.I` times the library even-even Majorana
product. -/
theorem edgeA_eq {n : ℕ} (i j : Fin n) :
    edgeA i j = (-Complex.I) • (majoranaEven i * majoranaEven j) := rfl

/-- Reversing an edge with distinct endpoints negates its fermionic generator. -/
theorem edgeA_antisym {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    edgeA j i = -edgeA i j := by
  unfold edgeA
  have h : majoranaEven j * majoranaEven i = -(majoranaEven i * majoranaEven j) :=
    eq_neg_of_add_eq_zero_left (majoranaEven_anticommute n j i (Ne.symm hij))
  rw [h, smul_neg]

end Qatlib.Papers.BKFermion17.FermionEdge
