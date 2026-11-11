/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch25.MainResults.CyclicTrace
import Qatlib.Papers.OrderedSearch25.MainResults.SourceProp22BlockDiagonal
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiSectorHelpers

/-!
# Proposition 23: swapping the diagonal blocks of the block-form solution

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Section 3.4,
Proposition 23, Equations (119)–(126).

Given the block-form matrix `M̃ = [[U, V], [V, U]]` of Proposition 22, the paper
considers the matrix `M̌ = [[V, U], [U, V]]` obtained by exchanging the two
diagonal blocks (equivalently, swapping the two half-blocks of every column),
and shows that the averaged matrices
`M := (M̃ + (-1)^t M̌)/2` again satisfy the SDP of Proposition 21.

This module formalises the *trace* part of that argument, which is the part
that interacts with the cyclic trace `Tr_j` of `CyclicTrace.lean`:

* `cycTrace_submatrix_right` — `Tr_j(A ∘ (id × T^a)) = Tr_{j+a}(A)`;
* `cycTrace_submatrix_half` — `Tr_j(M̌) = Tr_{j-n}(M)`, Equation (120);
* `bssE0_colShift` and `cycTrace_hadamard_half` — the phase sign flip
  `E_0 ⊙ M̌ = -((E_0 ⊙ M) ∘ (id × T^n))`, whence
  `Tr_j(E_0 ⊙ M̌) = -Tr_{j-n}(E_0 ⊙ M)`, the identity used in Equation (123);
* `hasBlockForm_swap` — the swapped matrix is again of block form, with the
  roles of `U` and `V` exchanged.

The positive-semidefiniteness half of Proposition 23 (Equation (121), the
Hadamard congruence producing `U ± V ⪰ 0`, and the Kronecker-product form of
`M^(t)`) is not formalised here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open scoped BigOperators ComplexOrder
open Matrix

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

variable {N : ℕ} [NeZero N]

/-- Negating a matrix negates all cyclic traces. -/
theorem cycTrace_neg (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    cycTrace (-A) j = -cycTrace A j := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum]
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib]

/-- Equality of `Fin` indices gives equality of cyclic traces. -/
theorem cycTrace_congr (A : Matrix (Fin N) (Fin N) ℂ) {i j : Fin N}
    (h : (i : ℕ) = (j : ℕ)) : cycTrace A i = cycTrace A j := by
  congr 1
  exact Fin.ext h

/-- Powers of the translation add: `T^(l+m) = T^l ∘ T^m`. -/
theorem cycShiftPow_add (l m : ℕ) :
    cycShiftPow N (l + m) = cycShiftPow N l * cycShiftPow N m := by
  simp [cycShiftPow, pow_add]

/-- The translation has order `N`: `T^N = 1`. -/
theorem cycShiftPow_self : cycShiftPow N N = 1 := by
  ext i
  rw [cycShiftPow_val, Equiv.Perm.one_apply, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- `T^l` depends only on `l` modulo `N`. -/
theorem cycShiftPow_mod (l : ℕ) : cycShiftPow N (l % N) = cycShiftPow N l := by
  have hN : ((finShiftEquiv N) ^ N : Equiv.Perm (Fin N)) = 1 := by
    simpa only [cycShiftPow] using cycShiftPow_self (N := N)
  simp only [cycShiftPow]
  conv_rhs => rw [← Nat.div_add_mod l N]
  rw [pow_add, pow_mul, hN, one_pow, one_mul]

/-- Swapping the two blocks of every column: `A ↦ A ∘ (id × T^n)` on `Fin (2n)`. -/
noncomputable def shiftHalf (n : ℕ) [NeZero n] : Equiv.Perm (Fin (2 * n)) :=
  haveI : NeZero (2 * n) := ⟨by have h : 0 < n := NeZero.pos n; omega⟩
  (finShiftEquiv (2 * n)) ^ n

/-- The half turn sends the first half to the second half. -/
theorem shiftHalf_first (n : ℕ) [NeZero n] (i : Fin n) :
    shiftHalf n (halfL n i) = halfR n i := by
  haveI : NeZero (2 * n) := ⟨by have h : 0 < n := NeZero.pos n; omega⟩
  have h := ti_shift_half_first n i
  simpa only [shiftHalf, cycShiftPow, halfL, halfR] using h

/-- The half turn sends the second half to the first half. -/
theorem shiftHalf_second (n : ℕ) [NeZero n] (i : Fin n) :
    shiftHalf n (halfR n i) = halfL n i := by
  haveI : NeZero (2 * n) := ⟨by have h : 0 < n := NeZero.pos n; omega⟩
  have h := ti_shift_half_second n i
  simpa only [shiftHalf, cycShiftPow, halfL, halfR] using h

/-- The index `n` as an element of `Fin (2n)`: the half turn `T^n`. -/
def halfIdx (n : ℕ) [NeZero n] : Fin (2 * n) := ⟨n, by have h := NeZero.pos n; omega⟩

/-- Column shift: `Tr_j(A ∘ (id × T^a)) = Tr_{j+a}(A)`. -/
theorem cycTrace_submatrix_right (A : Matrix (Fin N) (Fin N) ℂ) (a j : Fin N) :
    cycTrace (A.submatrix id (cycShiftPow N a.val)) j
      = cycTrace A ((cycShiftPow N a.val) j) := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum]
  simp only [Matrix.submatrix_apply, id_eq]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [← Equiv.Perm.mul_apply, ← cycShiftPow_add]
  congr 1
  rw [cycShiftPow_apply_comm (i := a) (a := j), cycShiftPow_val, cycShiftPow_mod,
    Nat.add_comm]

/-- **Equation (120)**: `Tr_j(M̌) = Tr_{j-n}(M)`, where `M̌` swaps the two
diagonal blocks of the block-form matrix `M`. -/
theorem cycTrace_submatrix_half (n : ℕ) [NeZero n]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (j : Fin (2 * n)) :
    cycTrace (A.submatrix id (shiftHalf n)) j
      = cycTrace A (shiftResidue (2 * n) (halfIdx n) j) := by
  haveI : NeZero (2 * n) := ⟨by have h : 0 < n := NeZero.pos n; omega⟩
  have hhalf : shiftHalf n = cycShiftPow (2 * n) n := rfl
  rw [hhalf]
  have h := cycTrace_submatrix_right (N := 2 * n) A (halfIdx n) j
  change cycTrace (A.submatrix id (cycShiftPow (2 * n) (halfIdx n).val)) j
      = cycTrace A (shiftResidue (2 * n) (halfIdx n) j)
  rw [h]
  apply cycTrace_congr
  rw [cycShiftPow_val]
  simp only [shiftResidue, Fin.val_mk, halfIdx]
  congr 1
  omega

/-- The phase matrix `E_0` is symmetric. -/
theorem bssE0_comm (n : ℕ) (a b : Fin (2 * n)) : bssE0 n a b = bssE0 n b a := by
  simp only [bssE0, Matrix.of_apply]
  by_cases h : ((a : ℕ) < n) = ((b : ℕ) < n)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Swapping the column by a half turn flips the phase sign:
`E_0[a, T^n b] = -E_0[a, b]`. -/
theorem bssE0_colShift (n : ℕ) [NeZero n] (a b : Fin (2 * n)) :
    bssE0 n a (shiftHalf n b) = - bssE0 n a b := by
  haveI : NeZero (2 * n) := ⟨by have h : 0 < n := NeZero.pos n; omega⟩
  have hhalf : shiftHalf n = cycShiftPow (2 * n) n := rfl
  rw [hhalf, bssE0_comm n a, bssE0_comm n a,
    bssE0_rowShift n b a]

/-- `E_0 ⊙ M̌ = -((E_0 ⊙ M) ∘ (id × T^n))`: swapping the columns of `M`
multiplies its phase-masked entries by `-1`. -/
theorem bssE0_hadamard_half (n : ℕ) [NeZero n]
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    Matrix.hadamard (bssE0 n) (M.submatrix id (shiftHalf n))
      = -((Matrix.hadamard (bssE0 n) M).submatrix id (shiftHalf n)) := by
  ext a b
  simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, id_eq, Matrix.neg_apply]
  rw [bssE0_colShift]
  ring

/-- **Equation (123)**: `Tr_j(E_0 ⊙ M̌) = -Tr_{j-n}(E_0 ⊙ M)`. -/
theorem cycTrace_hadamard_half (n : ℕ) [NeZero n]
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (j : Fin (2 * n)) :
    cycTrace (Matrix.hadamard (bssE0 n) (M.submatrix id (shiftHalf n))) j
      = - cycTrace (Matrix.hadamard (bssE0 n) M) (shiftResidue (2 * n) (halfIdx n) j) := by
  rw [bssE0_hadamard_half, cycTrace_neg, cycTrace_submatrix_half]

/-- Exchanging the diagonal blocks preserves the block form, with the roles of
`U` and `V` exchanged (Equation (120)). -/
theorem hasBlockForm_swap (n : ℕ) [NeZero n]
    (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) (U V : Matrix (Fin n) (Fin n) ℂ)
    (h : HasBlockForm n M U V) :
    HasBlockForm n (M.submatrix id (shiftHalf n)) V U := by
  intro i j
  obtain ⟨h00, h01, h10, h11⟩ := h i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.submatrix_apply, id_eq]
    rw [shiftHalf_first n, h01]
  · simp only [Matrix.submatrix_apply, id_eq]
    rw [shiftHalf_second n, h00]
  · simp only [Matrix.submatrix_apply, id_eq]
    rw [shiftHalf_first n, h11]
  · simp only [Matrix.submatrix_apply, id_eq]
    rw [shiftHalf_second n, h10]

end Qatlib.Papers.OrderedSearch25.MainResults
