/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic

/-!
# Jordan--Wigner locality of the discretised Gross--Neveu Hamiltonian (source Appendix A)

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Appendix A, Eqs. (A1)--(A11).

Appendix A defines the Jordan--Wigner map of Eqs. (A3)--(A8) and then observes that "the long
tails of `Z` tensor products cancel out and we are left with local Hamiltonian terms", giving
the explicitly mapped terms of Eqs. (A9)--(A11). The mechanism is purely algebraic and is
what this module formalises:

* the single-register Pauli matrices and jump operators satisfy `Z² = 1`, `{a⁺, a⁻} = 1` and
  `(a⁺)² = (a⁻)² = 0` (Eqs. (A1)--(A2) on one register);
* `Z a^{±} = -a^{±} Z`, the anticommutation that turns the `Z` string into the fermionic
  minus sign;
* if a prefix operator squares to the identity — as every `Z` string does, since each factor
  does — then it drops out of a Jordan--Wigner product; this is Eq. (A9)'s statement that the
  string covering sites `1 .. η-1` cancels because the creation and annihilation operators at
  neighbouring sites carry the *same* string there.

The key structural lemma `jw_prefix_cancels` is parametric in the prefix index set `π`, so it
covers strings of arbitrary length: whatever the lattice position `η`, the resulting term has
the identity on the whole prefix and only local registers `A⁻ · Z⁺`, `A⁺` survive. This is
the precise sense in which the mapped terms are local. `touchedRegisters` records the
position-independent register count `2N + 1` of Eq. (A9).

Boundary: this module does not build the full `2N`-register lattice Hilbert space, the
Fourier/Bogoliubov diagonalisation, or the specific coupling constants of Eqs. (A9)--(A11);
it proves the algebraic locality mechanism those equations rest on. The `h.c.` adjoints and
the `i`/`m₀`/`g₀`/`r` prefactors are absorbed into the generic local blocks `A⁻`, `Z⁺`, `A⁺`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Kronecker

namespace Qatlib.Papers.FermionQFT17.PrepContracts.JWLocality

/-- The Pauli `Z` matrix on one two-level register. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The Pauli `X` matrix on one two-level register. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The raising operator `a⁺ = [[0,0],[1,0]]` of Appendix A. -/
def aPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 1, 0]

/-- The lowering operator `a⁻ = [[0,1],[0,0]]` of Appendix A. -/
def aMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- `Z² = 1`: each `Z` factor of a parity string is an involution, which is why the string
squares to the identity. -/
theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- `X² = 1`, the companion involution used when a hopping block is combined with its
adjoint. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Z` string anticommutes with the raising operator: `Z a⁺ = -a⁺ Z`. This is the
algebraic source of the fermionic minus sign in the Jordan--Wigner map. -/
theorem pauliZ_aPlus_anticomm : pauliZ * aPlus = -(aPlus * pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, aPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Z` string anticommutes with the lowering operator: `Z a⁻ = -a⁻ Z`. -/
theorem pauliZ_aMinus_anticomm : pauliZ * aMinus = -(aMinus * pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, aMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Eq. (A1) on one register: the canonical anticommutation relation `{a⁺, a⁻} = 1`. -/
theorem car_anticomm : aPlus * aMinus + aMinus * aPlus = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aPlus, aMinus]

/-- Eq. (A2) on one register: `(a⁻)² = 0`. -/
theorem aMinus_sq : aMinus * aMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aMinus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Eq. (A2) on one register: `(a⁺)² = 0`. -/
theorem aPlus_sq : aPlus * aPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- A parity block spanning two registers is still an involution: `(Z ⊗ Z)² = 1`. -/
theorem blockZ_sq : (pauliZ ⊗ₖ pauliZ) * (pauliZ ⊗ₖ pauliZ) = 1 := by
  rw [← mul_kronecker_mul, pauliZ_sq, one_kronecker_one]

/-- Local rewriting of a tensor product with a negated left factor, used to move the
fermionic minus sign out of the Kronecker product. -/
theorem neg_kronecker_local {l m n p : Type*} (A : Matrix l m ℂ) (B : Matrix n p ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j
  simp [Matrix.neg_apply, neg_mul]

/-- Appendix A, "the long tails of `Z` tensor products cancel out": if the prefix operator
`Sp` squares to the identity, then it disappears from the Jordan--Wigner product, leaving the
identity on the whole prefix and only the local blocks `A⁻ · Z⁺` and `A⁺`. This is Eq. (A9)
with the string over sites `1 .. η-1` cancelled; `π` is the prefix register set, so the
statement holds for strings of arbitrary length. -/
theorem jw_prefix_cancels {π : Type*} [Fintype π] [DecidableEq π]
    (Sp : Matrix π π ℂ) (hSp : Sp * Sp = 1)
    (Aminus Zplus Aplus : Matrix (Fin 2) (Fin 2) ℂ) :
    ((Sp ⊗ₖ Aminus) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * ((Sp ⊗ₖ Zplus) ⊗ₖ Aplus) =
      (1 ⊗ₖ (Aminus * Zplus)) ⊗ₖ Aplus := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, hSp, one_mul]

/-- The Jordan--Wigner `Z` string produces the fermionic anticommutation between two
distinct registers: with the second register carrying the parity `Z`, the two operators
anticommute. This is the property that makes the map of Eqs. (A3)--(A8) a representation of
the CAR algebra of Eqs. (A1)--(A2). -/
theorem jw_fermion_anticommute :
    (aMinus ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (pauliZ ⊗ₖ aMinus) =
      -((pauliZ ⊗ₖ aMinus) * (aMinus ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul]
  have h : aMinus * pauliZ = -(pauliZ * aMinus) := by
    rw [pauliZ_aMinus_anticomm, neg_neg]
  rw [h, neg_kronecker_local]

/-- Eq. (A9): the number of site registers touched by a mapped hopping term for `N` fermion
species is `2N + 1` — the two `a^{±}` registers plus the `2N - 1` intervening `Z` registers. -/
def touchedRegisters (N : ℕ) : ℕ :=
  2 * N + 1

/-- The register count of Eq. (A9) does not depend on the lattice position, and grows by two
for each additional fermion species. -/
theorem touchedRegisters_succ (N : ℕ) : touchedRegisters (N + 1) = touchedRegisters N + 2 := by
  unfold touchedRegisters
  ring

end Qatlib.Papers.FermionQFT17.PrepContracts.JWLocality
