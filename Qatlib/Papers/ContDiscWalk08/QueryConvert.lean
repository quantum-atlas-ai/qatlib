/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs

/-!
# Bit-query Hamiltonians

The definitions `flipBit`, `oracleFlip`, and `oracleHamiltonian` realize a Boolean oracle as an
involutive permutation matrix. The module verifies its action on basis states, Hermiticity,
unitarity, and inner-product preservation, supplying the oracle representation used in
[Childs2010].

## Main statements

* `oracleHamiltonian_mulVec_ket`: the oracle flips the target bit according to the input.
* `oracleHamiltonian_isHermitian` and `oracleHamiltonian_unitary`: matrix properties of the
  oracle.

## References

* [Childs, 2010][Childs2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.QueryConvert

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Defines the Boolean exclusive-or operation on the control bit `c` and target bit `b`. -/
def flipBit (c b : Bool) : Bool := c != b

/-- Applying the bit flip with the same control twice returns the original bit. -/
theorem flipBit_involutive (c : Bool) : Function.Involutive (flipBit c) := by
  intro b
  cases c <;> cases b <;> rfl

/-- Defines the oracle permutation that preserves the index and flips its target bit according
to `x`. -/
def oracleFlip (x : I → Bool) (p : I × Bool) : I × Bool :=
  (p.1, flipBit (x p.1) p.2)

/-- The oracle permutation is involutive. -/
theorem oracleFlip_involutive (x : I → Bool) : Function.Involutive (oracleFlip x) := by
  intro p
  obtain ⟨i, b⟩ := p
  show (i, flipBit (x i) (flipBit (x i) b)) = (i, b)
  rw [flipBit_involutive]

/-- Defines the bit-query Hamiltonian as the permutation matrix of `oracleFlip x`. -/
def oracleHamiltonian (x : I → Bool) : Matrix (I × Bool) (I × Bool) ℂ :=
  permMatrix (oracleFlip x)

/-- The oracle Hamiltonian has entry one exactly when its row index is the oracle image of its
column index, and zero otherwise. -/
theorem oracleHamiltonian_apply (x : I → Bool) (p q : I × Bool) :
    oracleHamiltonian x p q = if p = oracleFlip x q then 1 else 0 := rfl

/-- The oracle Hamiltonian maps the basis state `(i, b)` to `(i, flipBit (x i) b)`. This
realizes the bit-query action in [Childs2010]. -/
theorem oracleHamiltonian_mulVec_ket (x : I → Bool) (i : I) (b : Bool) :
    oracleHamiltonian x *ᵥ Ket (i, b) = Ket (i, flipBit (x i) b) := by
  have h := applyGate_permMatrix_ket (oracleFlip_involutive x) (i, b)
  simpa using! h

/-- The action of the oracle Hamiltonian on a state is precomposition with the involutive oracle
permutation. -/
theorem oracleHamiltonian_mulVec (x : I → Bool) (ψ : QState (I × Bool)) :
    oracleHamiltonian x *ᵥ ψ = fun p => ψ (oracleFlip x p) := by
  funext p
  exact applyGate_permMatrix (oracleFlip_involutive x) ψ p

/-- The bit-query Hamiltonian is Hermitian, as required by the oracle model in [Childs2010]. -/
theorem oracleHamiltonian_isHermitian (x : I → Bool) :
    (oracleHamiltonian x).IsHermitian :=
  permMatrix_conjTranspose (oracleFlip_involutive x)

/-- The oracle Hamiltonian squares to the identity. -/
theorem oracleHamiltonian_mul_self (x : I → Bool) :
    oracleHamiltonian x * oracleHamiltonian x = 1 :=
  permMatrix_mul_self (oracleFlip_involutive x)

/-- The oracle Hamiltonian is unitary. -/
theorem oracleHamiltonian_unitary (x : I → Bool) :
    oracleHamiltonian x ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (oracleFlip_involutive x)

/-- The oracle Hamiltonian preserves the inner product of any two states. -/
theorem inner_oracleHamiltonian (x : I → Bool) (ψ φ : QState (I × Bool)) :
    Inner (oracleHamiltonian x *ᵥ ψ) (oracleHamiltonian x *ᵥ φ) = Inner ψ φ :=
  inner_applyGate (oracleHamiltonian_unitary x) ψ φ

/-- The matrix entry from `(i, b)` to its bit-flipped oracle image equals one. -/
theorem oracleHamiltonian_edge (x : I → Bool) (i : I) (b : Bool) :
    oracleHamiltonian x (i, flipBit (x i) b) (i, b) = 1 := by
  rw [oracleHamiltonian_apply]
  have h : (i, flipBit (x i) b) = oracleFlip x (i, b) := rfl
  rw [h, if_pos rfl]

end Qatlib.Papers.ContDiscWalk08.QueryConvert
