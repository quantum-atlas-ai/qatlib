/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch25.MainResults.SourceLemma29Initial
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdp
import Mathlib.LinearAlgebra.Matrix.Hadamard

/-!
# The cyclic trace `Tr_j` on `2n × 2n` matrices

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Section 3.4,
Equation (1) and the proof of Proposition 21.

The paper works with the *cyclic* generalized trace of a `2n × 2n` matrix,
`Tr_j(M) := tr_j(M) + tr_{j-2n}(M)` for `0 ≤ j < 2n`, i.e. the sum of the
entries of `M` on the `j`-th cyclic superdiagonal. This module provides that
functional (`cycTrace`) on a general `N × N` index set, together with the
structural facts used in Proposition 21:

* `cycTrace_eq_sum` — `Tr_j A` is the sum of `A p (T^j p)` along the cyclic
  diagonal, where `T = finShiftEquiv N` is the translation of Equation (4).
* `sum_transport_eq_toeplitz` — the sum of all cyclic translates
  `∑_i T^{-i} A T^i` is the Toeplitz matrix whose `j`-th diagonal is `Tr_j A`
  (Equations (99)–(100)); this is the averaging identity at the heart of
  Proposition 21.
* `cycTrace_submatrix_left` — shifting the *row* index by `T^a` shifts the
  cyclic-trace index by `-a`; this is the `Tr_j(M̌) = Tr_{j-n}(M)` step of
  Proposition 23.
* `cycTrace_submatrix_conj` — shifting both indices leaves `Tr_j` unchanged,
  the invariance behind Equation (117) of Proposition 22.

Everything is a finite sum identity on `Fin N`; no analysis is involved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open scoped BigOperators ComplexOrder
open Matrix

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

variable {N : ℕ} [NeZero N]

/-- The cyclic generalized trace `Tr_j` of arXiv:2503.21090v2 Equation (1)
specialized to a `2n × 2n` matrix: `tr_j(A) + tr_{j-N}(A)`, the sum over the
whole residue class `j mod N` of the generalized diagonals. -/
def cycTrace (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : ℂ :=
  genTrace A (j : ℤ) + genTrace A ((j : ℤ) - (N : ℤ))

/-- `Tr_j A` is the sum of `A` along the cyclic diagonal `p ↦ T^j p`, with
`T = finShiftEquiv N` the translation of Equation (4). This is the frozen
cyclic-diagonal bridge specialized to the index `j`. -/
theorem cycTrace_eq_sum (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    cycTrace A j = ∑ p : Fin N, A p (cycShiftPow N j.val p) := by
  have h := genTrace_cyclic_bridge A j.val j.isLt
  simpa [cycTrace] using h

/-- The cyclic trace is additive. -/
theorem cycTrace_add (A B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    cycTrace (A + B) j = cycTrace A j + cycTrace B j := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum, cycTrace_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp [Matrix.add_apply]

/-- The cyclic trace is `ℂ`-homogeneous. -/
theorem cycTrace_smul (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    cycTrace (c • A) j = c * cycTrace A j := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp [Matrix.smul_apply, smul_eq_mul]

/-- The cyclic trace of the zero matrix vanishes. -/
theorem cycTrace_zero (j : Fin N) : cycTrace (0 : Matrix (Fin N) (Fin N) ℂ) j = 0 := by
  rw [cycTrace_eq_sum]
  simp

/-- A modular arithmetic identity: adding `x + z` and `y + N - z` modulo `N`
agrees with adding `x + y`. -/
theorem nat_add_sub_key (x y z : ℕ) (hz : z ≤ N) :
    ((x + z) % N + (y + N - z) % N) % N = (x + y) % N := by
  rw [← Nat.add_mod]
  have h : (x + z) + (y + N - z) = (x + y) + N := by omega
  rw [h, Nat.add_mod_right]

/-- A modular arithmetic identity: a summand already below `N` may be added
outside the modulus. -/
theorem nat_mod_add_lt {y : ℕ} (hy : y < N) (x : ℕ) : (x % N + y) % N = (x + y) % N := by
  nth_rewrite 2 [Nat.add_mod]
  rw [Nat.mod_eq_of_lt hy]

/-- A modular arithmetic identity: a summand may be reduced modulo `N` before
adding. -/
theorem nat_add_mod_right (x y : ℕ) : (x + y % N) % N = (x + y) % N := by
  rw [Nat.add_mod x (y % N), Nat.mod_mod, Nat.add_mod x y]

/-- The residue of `b - a` in `Fin N`, written so that it never leaves `ℕ`. -/
def shiftResidue (N : ℕ) [NeZero N] (a b : Fin N) : Fin N :=
  ⟨((b : ℕ) + N - (a : ℕ)) % N, Nat.mod_lt _ (NeZero.pos N)⟩

/-- `T^{-a} T^b = T^{b-a}` at the level of indices. -/
theorem shiftResidue_spec (a b i : Fin N) :
    (cycShiftPow N (shiftResidue N a b).val) ((cycShiftPow N i.val) a)
      = (cycShiftPow N i.val) b := by
  apply Fin.ext
  rw [cycShiftPow_val, cycShiftPow_val, cycShiftPow_val]
  simp only [shiftResidue, Fin.val_mk]
  rw [← Nat.add_mod]
  have h : ((a : ℕ) + i.val) + ((b : ℕ) + N - (a : ℕ)) = (b : ℕ) + i.val + N := by omega
  rw [h, Nat.add_mod_right]

/-- `T^{j} T^{a} = T^{j-a} T^{a}` at the level of indices. -/
theorem shiftResidue_apply_left (a j p : Fin N) :
    (cycShiftPow N (shiftResidue N a j).val) ((cycShiftPow N a.val) p)
      = (cycShiftPow N j.val) p := by
  apply Fin.ext
  rw [cycShiftPow_val, cycShiftPow_val, cycShiftPow_val]
  simp only [shiftResidue, Fin.val_mk]
  exact nat_add_sub_key p.val j.val a.val (Nat.le_of_lt a.isLt)

/-- Two translations of the same index commute. -/
theorem shiftResidue_commute (a j p : Fin N) :
    (cycShiftPow N a.val) ((cycShiftPow N j.val) p)
      = (cycShiftPow N j.val) ((cycShiftPow N a.val) p) := by
  apply Fin.ext
  rw [cycShiftPow_val, cycShiftPow_val, cycShiftPow_val, cycShiftPow_val]
  rw [nat_mod_add_lt a.isLt ((p : ℕ) + j.val),
    nat_mod_add_lt j.isLt ((p : ℕ) + a.val)]
  congr 1
  omega

/-- The Toeplitz matrix `toep(Tr_0 A, …, Tr_{N-1} A)` of Equations (99)–(100):
the `(a,b)` entry is the cyclic trace at the residue `b - a`. -/
def toeplitzOf (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => cycTrace A (shiftResidue N a b)

/-- The cyclic translation `T^i` acts on `a` by adding `i` modulo `N`. -/
theorem cycShiftPow_apply_comm (i a : Fin N) :
    (cycShiftPow N i.val) a = (cycShiftPow N a.val) i := by
  apply Fin.ext
  rw [cycShiftPow_val, cycShiftPow_val, Nat.add_comm]

/-- The bijection `i ↦ T^i a` of `Fin N`. -/
theorem cycShiftPow_apply_bijective (a : Fin N) :
    Function.Bijective (fun i : Fin N => (cycShiftPow N i.val) a) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    rw [cycShiftPow_val, cycShiftPow_val] at hv
    have hm : ((a : ℕ) + i.val) ≡ ((a : ℕ) + j.val) [MOD N] := hv
    have hm' : i.val ≡ j.val [MOD N] := Nat.ModEq.add_left_cancel' _ hm
    exact Nat.ModEq.eq_of_lt_of_lt hm' i.isLt j.isLt
  · intro p
    refine ⟨⟨((p : ℕ) + N - (a : ℕ)) % N, Nat.mod_lt _ (NeZero.pos N)⟩, ?_⟩
    apply Fin.ext
    rw [cycShiftPow_val]
    rw [nat_add_mod_right]
    have h2 : (a : ℕ) + ((p : ℕ) + N - (a : ℕ)) = (p : ℕ) + N := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]

/-- **Equations (99)–(100)**: the sum of all cyclic translates of `A` is the
Toeplitz matrix whose `j`-th diagonal is the cyclic trace `Tr_j A`. Applied to
`A = M_0^(t)` this is Equation (99); applied to `A = E_0 ⊙ M_0^(t)` it is
Equation (100). -/
theorem sum_transport_eq_toeplitz (A : Matrix (Fin N) (Fin N) ℂ) :
    (∑ i : Fin N, A.submatrix (cycShiftPow N i.val) (cycShiftPow N i.val))
      = toeplitzOf A := by
  ext a b
  rw [Matrix.sum_apply, toeplitzOf, Matrix.of_apply, cycTrace_eq_sum]
  simp only [Matrix.submatrix_apply]
  rw [Fintype.sum_bijective (fun i : Fin N => (cycShiftPow N i.val) a)
    (cycShiftPow_apply_bijective a)
    (fun i => A ((cycShiftPow N i.val) a) ((cycShiftPow N i.val) b))
    (fun p => A p ((cycShiftPow N (shiftResidue N a b).val) p))
    (fun i => by
      show A ((cycShiftPow N i.val) a) ((cycShiftPow N i.val) b)
          = A ((cycShiftPow N i.val) a)
              ((cycShiftPow N (shiftResidue N a b).val) ((cycShiftPow N i.val) a))
      rw [shiftResidue_spec])]

/-- The `(0, j)` entry of the Toeplitz matrix is the cyclic trace at `j`, so
equality of Toeplitz matrices reads off all cyclic traces. -/
theorem toeplitzOf_apply_zero (A : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    toeplitzOf A 0 j = cycTrace A j := by
  rw [toeplitzOf, Matrix.of_apply]
  have h : shiftResidue N 0 j = j := by
    apply Fin.ext
    simp [shiftResidue, Nat.mod_eq_of_lt j.isLt]
  rw [h]

/-- If two Toeplitz matrices agree then the underlying cyclic traces agree at
every index; this is how the paper reads Equations (103)–(104) off (99)–(100). -/
theorem cycTrace_eq_of_toeplitzOf_eq {A B : Matrix (Fin N) (Fin N) ℂ}
    (h : toeplitzOf A = toeplitzOf B) (j : Fin N) : cycTrace A j = cycTrace B j := by
  have := congrFun (congrFun h 0) j
  simpa [toeplitzOf_apply_zero] using this

/-- Row shift: `Tr_j(A ∘ (T^a × id)) = Tr_{j-a}(A)`. This is the
`Tr_j(M̌) = Tr_{j-n}(M)` step of Proposition 23 (Equation (120)). -/
theorem cycTrace_submatrix_left (A : Matrix (Fin N) (Fin N) ℂ) (a j : Fin N) :
    cycTrace (A.submatrix (cycShiftPow N a.val) id) j = cycTrace A (shiftResidue N a j) := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum]
  simp only [Matrix.submatrix_apply, id_eq]
  rw [Fintype.sum_bijective (fun p : Fin N => (cycShiftPow N a.val) p)
    (cycShiftPow N a.val).bijective
    (fun p => A ((cycShiftPow N a.val) p) ((cycShiftPow N j.val) p))
    (fun q => A q ((cycShiftPow N (shiftResidue N a j).val) q))
    (fun p => by
      show A ((cycShiftPow N a.val) p) ((cycShiftPow N j.val) p)
          = A ((cycShiftPow N a.val) p)
              ((cycShiftPow N (shiftResidue N a j).val) ((cycShiftPow N a.val) p))
      rw [shiftResidue_apply_left])]

/-- Simultaneous shift: `Tr_j(A ∘ (T^a × T^a)) = Tr_j(A)`. Translations
permute each residue class, so the cyclic trace is invariant; this is the
invariance behind Equation (117) of Proposition 22. -/
theorem cycTrace_submatrix_conj (A : Matrix (Fin N) (Fin N) ℂ) (a j : Fin N) :
    cycTrace (A.submatrix (cycShiftPow N a.val) (cycShiftPow N a.val)) j = cycTrace A j := by
  rw [cycTrace_eq_sum, cycTrace_eq_sum]
  simp only [Matrix.submatrix_apply]
  rw [Fintype.sum_bijective (fun p : Fin N => (cycShiftPow N a.val) p)
    (cycShiftPow N a.val).bijective
    (fun p => A ((cycShiftPow N a.val) p) ((cycShiftPow N a.val) ((cycShiftPow N j.val) p)))
    (fun q => A q ((cycShiftPow N j.val) q))
    (fun p => by
      show A ((cycShiftPow N a.val) p) ((cycShiftPow N a.val) ((cycShiftPow N j.val) p))
          = A ((cycShiftPow N a.val) p) ((cycShiftPow N j.val) ((cycShiftPow N a.val) p))
      rw [shiftResidue_commute])]

/-- The phase matrix `E_0 = [[J_n, -J_n], [-J_n, J_n]]` of Equation (90):
entry `+1` on pairs lying in the same half of `Fin (2n)` and `-1` otherwise. -/
def bssE0 (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  Matrix.of fun a b => if ((a : ℕ) < n) = ((b : ℕ) < n) then 1 else -1

/-- Adding `n` modulo `2n` flips which half of `Fin (2n)` an index lies in. -/
theorem half_shift_lt (n : ℕ) [NeZero n] (a : Fin (2 * n)) :
    (((cycShiftPow (2 * n) n) a : ℕ) < n) = ¬ ((a : ℕ) < n) := by
  have hv := cycShiftPow_val (2 * n) n a
  rw [hv]
  have h2n : 0 < 2 * n := NeZero.pos (2 * n)
  rcases Nat.lt_or_ge (a : ℕ) n with ha | ha
  · have hlt : ((a : ℕ) + n) % (2 * n) = (a : ℕ) + n := by
      rw [Nat.mod_eq_of_lt]; omega
    rw [hlt]
    simp [ha, not_lt.mpr (by omega : n ≤ (a : ℕ) + n)]
  · have hge : ((a : ℕ) + n) % (2 * n) = (a : ℕ) + n - 2 * n := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      rw [Nat.mod_eq_of_lt]; omega
    rw [hge]
    simp [ha, (by omega : (a : ℕ) + n - 2 * n < n)]

/-- The phase matrix entry is the product of the two half-signs of its indices. -/
theorem bssE0_eq_prod (n : ℕ) (a b : Fin (2 * n)) :
    bssE0 n a b = (if ((a : ℕ) < n) then (1 : ℂ) else -1) *
      (if ((b : ℕ) < n) then (1 : ℂ) else -1) := by
  simp only [bssE0, Matrix.of_apply]
  by_cases ha : ((a : ℕ) < n) <;> by_cases hb : ((b : ℕ) < n) <;> simp [ha, hb]

/-- Shifting a row index by `n` flips the half-sign. -/
theorem if_half_shift (n : ℕ) [NeZero n] (a : Fin (2 * n)) :
    (if (((cycShiftPow (2 * n) n) a : ℕ) < n) then (1 : ℂ) else -1)
      = -(if ((a : ℕ) < n) then (1 : ℂ) else -1) := by
  have h := half_shift_lt n a
  by_cases ha : ((a : ℕ) < n)
  · have h2 : ¬ (((cycShiftPow (2 * n) n) a : ℕ) < n) := by rw [h]; simp [ha]
    simp [ha, h2]
  · have h2 : (((cycShiftPow (2 * n) n) a : ℕ) < n) := by rw [h]; simp [ha]
    simp [ha, h2]

/-- **Equation (90)** as a sign flip: the phase matrix at the row-shifted index
is the negative of `E_0`. This is the `E_0 ⊙ M̌ = -(E_0 ⊙ M)` relation used in
Equation (123) of Proposition 23. -/
theorem bssE0_rowShift (n : ℕ) [NeZero n] (a b : Fin (2 * n)) :
    bssE0 n ((cycShiftPow (2 * n) n) a) b = - bssE0 n a b := by
  rw [bssE0_eq_prod, bssE0_eq_prod, if_half_shift]
  ring

end Qatlib.Papers.OrderedSearch25.MainResults
