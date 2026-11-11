/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Data.Nat.Bitwise

/-!
# Qubit operators for the pairing Hamiltonian

Computational-basis bit operations define the Pauli matrices and pair interactions on `Fin (2 ^
N)`. Hermiticity of the free, interaction, and full pairing Hamiltonians gives the concrete
operator model underlying [WuByrdLidar2002], with register cardinality and qubit-count
identities.

## Main statements

* `pairingHp_isHermitian`: the full pairing Hamiltonian is Hermitian.
* `qubit_count`: the register dimension corresponds to `N` qubits.

## References

* [Wu et al., 2002][WuByrdLidar2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PairingModel01.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath (Operator)

/-- The Boolean value of bit `m` in the computational-basis label `x`. -/
def bitOf (N : ℕ) (m : Fin N) (x : Fin (2 ^ N)) : Bool := x.val.testBit (m : ℕ)

/-- The computational-basis label obtained by toggling bit `m` using bitwise exclusive-or. -/
def flipFun (N : ℕ) (m : Fin N) (x : Fin (2 ^ N)) : Fin (2 ^ N) :=
  ⟨x.val ^^^ 2 ^ (m : ℕ),
    Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) m.isLt)⟩

/-- Toggling a fixed bit is an involution. -/
theorem flipFun_involutive (N : ℕ) (m : Fin N) : Function.Involutive (flipFun N m) := by
  intro x
  apply Fin.ext
  simp [flipFun]

/-- Bit flips at any two positions commute. -/
theorem flipFun_comm (N : ℕ) (m l : Fin N) :
    Function.Commute (flipFun N m) (flipFun N l) := by
  intro x
  apply Fin.ext
  simp only [flipFun, Fin.val_mk]
  rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (2 ^ (m : ℕ)) (2 ^ (l : ℕ))]

/-- The composition of two bit flips is an involution. -/
theorem flipFun_comp_involutive (N : ℕ) (m l : Fin N) :
    Function.Involutive (flipFun N m ∘ flipFun N l) := by
  intro x
  simp only [Function.comp_apply]
  rw [flipFun_comm N m l x, flipFun_involutive N l, flipFun_involutive N m]

/-- Toggling bit `m` negates its Boolean value. -/
theorem bitOf_flipFun_self (N : ℕ) (m : Fin N) (x : Fin (2 ^ N)) :
    bitOf N m (flipFun N m x) = !(bitOf N m x) := by
  simp [bitOf, flipFun, Nat.testBit_xor]

/-- Toggling a bit at a position different from `m` leaves bit `m` unchanged. -/
theorem bitOf_flipFun_of_ne (N : ℕ) {m l : Fin N} (h : m ≠ l) (x : Fin (2 ^ N)) :
    bitOf N m (flipFun N l x) = bitOf N m x := by
  have h' : (l : ℕ) ≠ (m : ℕ) := fun e => h (Fin.ext e.symm)
  simp [bitOf, flipFun, Nat.testBit_xor, Nat.testBit_two_pow_of_ne h']

/-- For distinct positions, flipping both bits preserves whether their Boolean values agree. -/
theorem bitOf_agree_flip (N : ℕ) {m l : Fin N} (h : m ≠ l) (x : Fin (2 ^ N)) :
    (bitOf N m (flipFun N m (flipFun N l x)) = bitOf N l (flipFun N m (flipFun N l x))) ↔
      (bitOf N m x = bitOf N l x) := by
  have h1 : bitOf N m (flipFun N m (flipFun N l x)) = !(bitOf N m (flipFun N l x)) :=
    bitOf_flipFun_self N m (flipFun N l x)
  have h2 : bitOf N m (flipFun N l x) = bitOf N m x := bitOf_flipFun_of_ne N h x
  have h3 : bitOf N l (flipFun N m (flipFun N l x)) = !(bitOf N l x) := by
    rw [bitOf_flipFun_of_ne N (Ne.symm h) (flipFun N l x), bitOf_flipFun_self]
  rw [h1, h2, h3]
  cases bitOf N m x <;> cases bitOf N l x <;> simp

/-- The diagonal Pauli Z operator at site `m`, with eigenvalue negative one on labels whose
`m`th bit is true. -/
noncomputable def sigmaZ (N : ℕ) (m : Fin N) : Operator (2 ^ N) :=
  Matrix.diagonal (fun x => if bitOf N m x then (-1 : ℂ) else 1)

/-- The site Pauli Z operator is Hermitian. -/
theorem sigmaZ_isHermitian (N : ℕ) (m : Fin N) : (sigmaZ N m).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  rw [sigmaZ, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    split_ifs <;> simp
  · simp [h, Ne.symm h]

/-- The Pauli X operator at site `m`, represented by the permutation matrix of the corresponding
bit flip. -/
noncomputable def sigmaX (N : ℕ) (m : Fin N) : Operator (2 ^ N) :=
  Qatlib.Foundations.PureStateMath.permMatrix (flipFun N m)

/-- The site Pauli X operator is Hermitian. -/
theorem sigmaX_isHermitian (N : ℕ) (m : Fin N) : (sigmaX N m).IsHermitian :=
  Qatlib.Foundations.PureStateMath.permMatrix_conjTranspose
    (flipFun_involutive N m)

/-- The product of the matrices associated with `σ` and `τ` is the matrix associated with `σ ∘
τ`. -/
theorem permMatrix_mul_perm (N : ℕ) (σ τ : Fin (2 ^ N) → Fin (2 ^ N)) :
    Qatlib.Foundations.PureStateMath.permMatrix σ *
        Qatlib.Foundations.PureStateMath.permMatrix τ =
      Qatlib.Foundations.PureStateMath.permMatrix (σ ∘ τ) := by
  ext i j
  simp only [Qatlib.Foundations.PureStateMath.permMatrix, Matrix.mul_apply,
    Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ (τ j)) h

/-- The product of two site Pauli X operators is the permutation matrix of the composed bit
flips. -/
theorem sigmaX_mul_sigmaX (N : ℕ) (m l : Fin N) :
    sigmaX N m * sigmaX N l =
      Qatlib.Foundations.PureStateMath.permMatrix
        (flipFun N m ∘ flipFun N l) := by
  unfold sigmaX
  exact permMatrix_mul_perm N (flipFun N m) (flipFun N l)

/-- The product of any two site Pauli X operators is Hermitian. -/
theorem sigmaX_mul_sigmaX_isHermitian (N : ℕ) (m l : Fin N) :
    (sigmaX N m * sigmaX N l).IsHermitian := by
  rw [sigmaX_mul_sigmaX]
  exact Qatlib.Foundations.PureStateMath.permMatrix_conjTranspose
    (flipFun_comp_involutive N m l)

/-- The diagonal phase operator with entry `−i` when bit `m` is true and `i` otherwise. -/
noncomputable def phaseDiag (N : ℕ) (m : Fin N) : Operator (2 ^ N) :=
  Matrix.diagonal (fun x => if bitOf N m x then (-Complex.I) else Complex.I)

/-- The site Pauli Y operator defined as `sigmaX N m * phaseDiag N m`. -/
noncomputable def sigmaY (N : ℕ) (m : Fin N) : Operator (2 ^ N) :=
  sigmaX N m * phaseDiag N m

/-- A site's diagonal phase operator commutes with the Pauli X operator at a distinct site. -/
theorem phaseDiag_comm_sigmaX (N : ℕ) {m l : Fin N} (h : m ≠ l) :
    phaseDiag N m * sigmaX N l = sigmaX N l * phaseDiag N m := by
  ext i j
  simp only [phaseDiag, sigmaX, Qatlib.Foundations.PureStateMath.permMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  by_cases hij : i = flipFun N l j
  · simp [hij, bitOf_flipFun_of_ne N h j]
  · simp [hij]

/-- The diagonal operator with value negative one when bits `m` and `l` agree and positive one
otherwise. -/
noncomputable def sigmaZPair (N : ℕ) (m l : Fin N) : Operator (2 ^ N) :=
  Matrix.diagonal (fun x => if bitOf N m x = bitOf N l x then (-1 : ℂ) else 1)

/-- The product of two site phase operators equals `sigmaZPair`. -/
theorem phaseDiag_mul_phaseDiag (N : ℕ) (m l : Fin N) :
    phaseDiag N m * phaseDiag N l = sigmaZPair N m l := by
  rw [phaseDiag, phaseDiag, sigmaZPair, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases ha : bitOf N m x <;> by_cases hb : bitOf N l x <;>
    simp [ha, hb, Complex.I_mul_I]

/-- The diagonal pair operator `sigmaZPair` is Hermitian. -/
theorem sigmaZPair_isHermitian (N : ℕ) (m l : Fin N) : (sigmaZPair N m l).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  rw [sigmaZPair, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h
    split_ifs <;> simp
  · simp [h, Ne.symm h]

/-- For distinct sites, the product of their Pauli X operators commutes with `sigmaZPair`. -/
theorem sigmaZPair_comm_sigmaXPair (N : ℕ) {m l : Fin N} (h : m ≠ l) :
    Commute (sigmaX N m * sigmaX N l) (sigmaZPair N m l) := by
  rw [sigmaX_mul_sigmaX]
  ext i j
  simp only [sigmaZPair, Qatlib.Foundations.PureStateMath.permMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Function.comp_apply]
  by_cases hij : i = flipFun N m (flipFun N l j)
  · by_cases hb : (bitOf N m j = bitOf N l j) <;>
      simp [hij, hb, bitOf_agree_flip N h j]
  · simp [hij]

/-- For distinct sites, the product of their Pauli Y operators equals the product of their Pauli
X operators followed by `sigmaZPair`. -/
theorem sigmaY_mul_sigmaY (N : ℕ) {m l : Fin N} (h : m ≠ l) :
    sigmaY N m * sigmaY N l = (sigmaX N m * sigmaX N l) * sigmaZPair N m l := by
  calc sigmaY N m * sigmaY N l
      = sigmaX N m * (phaseDiag N m * (sigmaX N l * phaseDiag N l)) := by
          unfold sigmaY; rw [mul_assoc]
    _ = sigmaX N m * ((phaseDiag N m * sigmaX N l) * phaseDiag N l) := by rw [mul_assoc]
    _ = sigmaX N m * ((sigmaX N l * phaseDiag N m) * phaseDiag N l) := by
          rw [phaseDiag_comm_sigmaX N h]
    _ = sigmaX N m * (sigmaX N l * (phaseDiag N m * phaseDiag N l)) := by rw [mul_assoc]
    _ = sigmaX N m * (sigmaX N l * sigmaZPair N m l) := by rw [phaseDiag_mul_phaseDiag]
    _ = (sigmaX N m * sigmaX N l) * sigmaZPair N m l := by rw [mul_assoc]

/-- The product of the Pauli Y operators at distinct sites is Hermitian. -/
theorem sigmaY_mul_sigmaY_isHermitian (N : ℕ) {m l : Fin N} (h : m ≠ l) :
    (sigmaY N m * sigmaY N l).IsHermitian := by
  rw [sigmaY_mul_sigmaY N h]
  exact ((sigmaX_mul_sigmaX_isHermitian N m l).commute_iff
    (sigmaZPair_isHermitian N m l)).mp (sigmaZPair_comm_sigmaXPair N h)

/-- The pairing interaction term `sigmaX N m * sigmaX N l + sigmaY N m * sigmaY N l`. -/
noncomputable def pairTerm (N : ℕ) (m l : Fin N) : Operator (2 ^ N) :=
  sigmaX N m * sigmaX N l + sigmaY N m * sigmaY N l

/-- The pairing interaction term is Hermitian for distinct sites. -/
theorem pairTerm_isHermitian (N : ℕ) {m l : Fin N} (h : m ≠ l) :
    (pairTerm N m l).IsHermitian :=
  (sigmaX_mul_sigmaX_isHermitian N m l).add (sigmaY_mul_sigmaY_isHermitian N h)

/-- The free pairing Hamiltonian, summing `ε m / 2` times the Pauli Z operator at each site. -/
noncomputable def pairingH0 (N : ℕ) (ε : Fin N → ℝ) : Operator (2 ^ N) :=
  ∑ m : Fin N, ((ε m / 2 : ℝ) : ℂ) • sigmaZ N m

/-- The free pairing Hamiltonian is Hermitian. -/
theorem pairingH0_isHermitian (N : ℕ) (ε : Fin N → ℝ) : (pairingH0 N ε).IsHermitian := by
  show (pairingH0 N ε)ᴴ = pairingH0 N ε
  unfold pairingH0
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.conjTranspose_smul, (sigmaZ_isHermitian N m)]
  congr 1
  simp

/-- The interaction Hamiltonian, summing `V m l / 2` times `pairTerm N m l` over pairs with `m <
l`. -/
noncomputable def pairingHI (N : ℕ) (V : Fin N → Fin N → ℝ) : Operator (2 ^ N) :=
  ∑ m : Fin N, ∑ l : Fin N,
    if m < l then ((V m l / 2 : ℝ) : ℂ) • pairTerm N m l else 0

/-- The pairing interaction Hamiltonian is Hermitian. -/
theorem pairingHI_isHermitian (N : ℕ) (V : Fin N → Fin N → ℝ) :
    (pairingHI N V).IsHermitian := by
  show (pairingHI N V)ᴴ = pairingHI N V
  unfold pairingHI
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases hml : m < l
  · rw [if_pos hml, Matrix.conjTranspose_smul, (pairTerm_isHermitian N (ne_of_lt hml))]
    congr 1
    simp
  · rw [if_neg hml]
    simp

/-- The full pairing Hamiltonian, equal to the sum of `pairingH0` and `pairingHI`. -/
noncomputable def pairingHp (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) : Operator (2 ^ N) :=
  pairingH0 N ε + pairingHI N V

/-- The full pairing Hamiltonian is Hermitian. -/
theorem pairingHp_isHermitian (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) :
    (pairingHp N ε V).IsHermitian :=
  (pairingH0_isHermitian N ε).add (pairingHI_isHermitian N V)

/-- The computational-basis register has cardinality `2 ^ N`. -/
theorem register_dimension (N : ℕ) : Fintype.card (Fin (2 ^ N)) = 2 ^ N :=
  Fintype.card_fin _

/-- The base-two natural logarithm of the computational-basis register cardinality is `N`. -/
theorem qubit_count (N : ℕ) :
    Nat.log 2 (Fintype.card (Fin (2 ^ N))) = N := by
  rw [register_dimension]
  exact Nat.log_pow (by norm_num) N

end Qatlib.Papers.PairingModel01.MainResults
