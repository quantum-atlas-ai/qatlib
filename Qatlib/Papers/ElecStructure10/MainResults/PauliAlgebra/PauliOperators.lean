/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

set_option backward.isDefEq.respectTransparency false

/-!
# ElecStructure10.MainResults.PauliAlgebra — per-site Pauli operators on `Reg n`

Source: Whitfield, Biamonte, Aspuru-Guzik, *Simulation of Electronic Structure
Hamiltonians Using Quantum Computers*, fixed arXiv:1001.3855v3 (PDF fetched from
`assets/1001.3855.pdf`), Section 3.1 (Eqs. (5a)/(5b), around p. 6) and Table A2.

This file fixes the paper's Pauli vocabulary on the computational register
`Reg n = Fin n → Bool` of the frozen fermion package
`QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision`.  The paper's `σ^x, σ^y, σ^z`
(single-qubit Pauli matrices with eigenvalues `±1`) act as a tensor product with
the identity on the remaining qubits; we spell out those *per-site* operators
entry-wise so that the Jordan–Wigner decompositions of Eqs. (17) and (21) become
plain matrix identities on `Matrix (Reg n) (Reg n) ℂ`.

* `zOp i` — `σ^z` on site `i`, identity elsewhere (diagonal);
* `xOp i` — `σ^x` on site `i`, identity elsewhere (bit-flip permutation);
* `yOp i` — `σ^y` on site `i`, identity elsewhere (bit-flip with phase);
* `zString is` — product of `zOp i` over `i ∈ is` (Jordan–Wigner `Z`-string).

All of these are the paper's own tensor-product operators, not weakened
surrogates: `xOp i`, `yOp i`, `zOp i` are pointwise the `2 × 2` Pauli matrices
from Eq. (5a)/(5b) placed at coordinate `i`, i.e. `PauliX_i ⊗ 1`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open scoped BigOperators

namespace Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra

variable {n : ℕ}

/-- `σ^z` on site `i` and identity elsewhere.  Diagonal with entry `+1` when bit
`i` is `0` and `−1` when bit `i` is `1` (paper Section 3.1: eigenvectors of
`σ^z` are `|0⟩,|1⟩` with eigenvalues `+1,-1`). -/
noncomputable def zOp (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x : Reg n => if x i then (-1 : ℂ) else 1)

/-- `σ^x` on site `i` and identity elsewhere: flips bit `i`, entry `1`. -/
noncomputable def xOp (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x => if y = Function.update x i (!x i) then 1 else 0

/-- `σ^y` on site `i` and identity elsewhere: flips bit `i` with the Pauli phase
`|0⟩ ↦ i|1⟩`, `|1⟩ ↦ −i|0⟩` (paper's `σ^y = [[0,−i],[i,0]]`). -/
noncomputable def yOp (i : Fin n) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun y x =>
    if y = Function.update x i (!x i) then (if x i then -(Complex.I) else Complex.I) else 0

/-- Jordan–Wigner `Z`-string over a finite index set: the diagonal operator
whose `x`-entry is `∏_{i∈is} (if x_i then −1 else 1)`.  The paper writes this
as `⊗_{k} σ_k^z`; this is the same operator because the `zOp i` pairwise commute
(they are diagonal).  Defined with a scalar product so no commutativity of the
matrix ring is needed. -/
noncomputable def zString (is : Finset (Fin n)) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun x : Reg n => ∏ i ∈ is, (if x i then (-1 : ℂ) else 1))

/-- Entry formula for the `Z`-string of paper Table A2 (`⊗_k σ_k^z`): the only
non-zero entries are diagonal, with value `∏_{i∈is} (if x_i then −1 else 1)`. -/
@[simp] theorem zString_apply (is : Finset (Fin n)) (y x : Reg n) :
    zString is y x = if y = x then (∏ i ∈ is, (if x i then (-1 : ℂ) else 1)) else 0 := by
  rw [zString, Matrix.diagonal_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h, if_neg h]

/-- Entry formula for `σ^z` of paper Section 3.1 (eigenvalues `+1, −1` for bits
`0, 1`): diagonal, `+1` when bit `i` of `x` is `0` and `−1` when it is `1`. -/
@[simp] theorem zOp_apply (i : Fin n) (y x : Reg n) :
    zOp i y x = if y = x then (if x i then (-1 : ℂ) else 1) else 0 := by
  rw [zOp, Matrix.diagonal_apply]
  by_cases h : y = x
  · subst h; simp
  · rw [if_neg h, if_neg h]

/-- Entry formula for `σ^x` (paper Section 3.1, `σ^x = [[0,1],[1,0]]` acting on
site `i`): the only non-zero entries are the bit-flip permutation ones, with
value `1`. -/
@[simp] theorem xOp_apply (i : Fin n) (y x : Reg n) :
    xOp i y x = if y = Function.update x i (!x i) then 1 else 0 := rfl

/-- Entry formula for `σ^y` (paper Section 3.1, `σ^y = [[0,−i],[i,0]]` acting on
site `i`): the bit-flip permutation entries carry the phase `i` on `|0⟩` and
`−i` on `|1⟩`. -/
@[simp] theorem yOp_apply (i : Fin n) (y x : Reg n) :
    yOp i y x =
      if y = Function.update x i (!x i) then (if x i then -(Complex.I) else Complex.I) else 0 :=
  rfl

/-- `zOp i` is a diagonal matrix: it is zero off the diagonal. -/
theorem zOp_apply_of_ne {i : Fin n} {y x : Reg n} (h : y ≠ x) : zOp i y x = 0 := by
  rw [zOp_apply, if_neg h]

/-- `zString` over the empty set is the identity: the paper omits `σ^z` factors
when `p+1 > q−1` (adjacent orbitals). -/
@[simp] theorem zString_empty : zString (n := n) (∅ : Finset (Fin n)) = 1 := by
  rw [zString]
  simp [Matrix.diagonal_one]

/-- The `Z`-string of a fresh site composes with the remaining `Z`-string. -/
theorem zString_insert {is : Finset (Fin n)} {i : Fin n} (h : i ∉ is) :
    zString (insert i is) = zOp i * zString is := by
  rw [zString, zString, zOp, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [Finset.prod_insert h]

end Qatlib.Papers.ElecStructure10.MainResults.PauliAlgebra
