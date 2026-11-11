/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma S1: the cyclic-shift twirl identity

Fixed arXiv:2607.29382v2, Lemma S1, page S4 (Eqs. (S1)–(S2)).

For an orthonormal basis `{|j⟩}` of a `K`-dimensional space, the cyclic shift
`S = Σ_j |j ⊕ 1⟩⟨j|`, and a diagonal `A = Σ_j a_j |j⟩⟨j|`, Lemma S1 states
`Σ_{r=0}^{K−1} S^r A S^{−r} = tr(A) I`, hence
`Σ_{r=1}^{K−1} S^r A S^{−r} = tr(A) I − A`.

The paper indexes the basis by `j = 0, …, K−1` with addition mod `K`; we model it by
`ZMod n` with `n = K` (`NeZero n` encodes `K ≥ 1`, and the paper's `K` is a block
dimension, so `K ≥ 1` always).  `S^r = Σ_j |j ⊕ r⟩⟨j|` has matrix entries
`(S^r)_{ij} = [i = j + r]`, which is the definition of `cyclicShiftPow` below (this is
the transpose of Mathlib's permutation-matrix row convention, and it is the form in which
the paper's powers are used).  The twirl identity is proved entrywise: conjugating a
diagonal by `S^r` shifts the diagonal by `r`, and the shifts `r ↦ i − r` enumerate every
basis label exactly once, giving the trace.
-/

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.SpectralTwirl

set_option autoImplicit false
noncomputable section

variable {n : ℕ} [NeZero n]

attribute [local instance] Classical.propDecidable

/-- The `r`-fold cyclic shift `S^r = Σ_j |j ⊕ r⟩⟨j|` of Eq. (S1), i.e. the matrix with
entries `(S^r)_{ij} = [i = j + r]`. -/
def cyclicShiftPow (r : ZMod n) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if i = j + r then 1 else 0

/-- The cyclic shift `S = Σ_j |j ⊕ 1⟩⟨j|` of Eq. (S1). -/
def cyclicShift : Matrix (ZMod n) (ZMod n) ℂ :=
  cyclicShiftPow (1 : ZMod n)

/-- The zero-th power of the shift is the identity, `S^0 = I`. -/
theorem cyclicShiftPow_zero : cyclicShiftPow (0 : ZMod n) = 1 := by
  ext i j
  simp [cyclicShiftPow, Matrix.one_apply]

/-- Powers of the cyclic shift add: `S^r S^s = S^{r+s}` (the paper's `S^{r}` notation). -/
theorem cyclicShiftPow_mul (r s : ZMod n) :
    cyclicShiftPow r * cyclicShiftPow s = cyclicShiftPow (r + s) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (j + s)]
  · simp only [cyclicShiftPow, Matrix.of_apply]
    simp [add_assoc, add_comm, add_left_comm]
  · intro b _ hb
    simp [cyclicShiftPow, hb]
  · intro h
    simp at h

/-- `S^r` agrees with the `r`-fold matrix power of `S` (paper's notation `S^r`). -/
theorem cyclicShift_pow (r : ℕ) :
    (cyclicShift (n := n)) ^ r = cyclicShiftPow (r : ZMod n) := by
  induction r with
  | zero =>
    rw [pow_zero]
    simpa using (cyclicShiftPow_zero (n := n)).symm
  | succ k ih =>
    rw [pow_succ, ih, cyclicShift]
    rw [cyclicShiftPow_mul, Nat.cast_add, Nat.cast_one]

/-- Conjugating a diagonal matrix by `S^r` shifts the diagonal: `S^r A S^{−r}` is the
diagonal with entries `a (i − r)` (the entrywise form of `S^r A S^{−r}` in the proof of
Lemma S1). -/
theorem cyclicShiftPow_conj_diagonal (a : ZMod n → ℂ) (r : ZMod n) (i j : ZMod n) :
    (cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ) i j =
      if i = j then a (i - r) else 0 := by
  rw [Matrix.mul_apply]
  have hSD : ∀ l, (cyclicShiftPow r * diagonal a) i l =
      if i = l + r then a l else 0 := by
    intro l
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single l]
    · simp [cyclicShiftPow, Matrix.diagonal_apply]
    · intro b _ hb
      simp [Matrix.diagonal_apply, hb]
    · intro h
      simp at h
  have hconj : ∀ l j', (cyclicShiftPow (n := n) r)ᴴ l j' =
      if j' = l + r then 1 else 0 := by
    intro l j'
    rw [Matrix.conjTranspose_apply]
    simp only [cyclicShiftPow, Matrix.of_apply]
    by_cases h : j' = l + r
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl (fun l _ => by rw [hSD l, hconj l j])]
  rw [Finset.sum_eq_single (i - r)]
  · have hsub : (i - r) + r = i := sub_add_cancel i r
    rw [hsub]
    by_cases hji : j = i
    · subst hji
      simp
    · have hij : i ≠ j := fun h => hji h.symm
      simp [hji, hij]
  · intro b _ hb
    have hb' : i ≠ b + r := by
      intro h
      apply hb
      rw [eq_sub_iff_add_eq]
      exact h.symm
    simp [hb']
  · intro h
    simp at h

/-- The sum over `r` of the shifted diagonals at a fixed basis vector `i` is the total
trace: `r ↦ i − r` is a bijection of `ZMod n`. -/
theorem sum_shift_diagonal (a : ZMod n → ℂ) (i : ZMod n) :
    (∑ r : ZMod n, a (i - r)) = ∑ j : ZMod n, a j := by
  let e : ZMod n ≃ ZMod n :=
    { toFun := fun r => i - r
      invFun := fun j => i - j
      left_inv := by intro x; simp [sub_sub_self]
      right_inv := by intro x; simp [sub_sub_self] }
  have h := Equiv.sum_comp e a
  simpa [e] using h

/-- **Lemma S1, first identity** (page S4, Eq. (S2)):
`Σ_{r=0}^{K−1} S^r A S^{−r} = tr(A) I` for diagonal `A`. -/
theorem sum_cyclicShift_conj_diagonal (a : ZMod n → ℂ) :
    (∑ r : ZMod n, cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ) =
      (∑ j : ZMod n, a j) • (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun r _ => cyclicShiftPow_conj_diagonal a r i j)]
  by_cases hij : i = j
  · subst hij
    simpa using sum_shift_diagonal a i
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

/-- **Lemma S1, second identity** (page S4): subtracting the `r = 0` term,
`Σ_{r=1}^{K−1} S^r A S^{−r} = tr(A) I − A`.  Here the sum is over the nonzero shifts
`r : ZMod n`, which is exactly `r = 1, …, K−1` in the paper's indexing. -/
theorem sum_nonzero_cyclicShift_conj_diagonal (a : ZMod n → ℂ) :
    (∑ r ∈ (Finset.univ.erase 0), cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ) =
      (∑ j : ZMod n, a j) • (1 : Matrix (ZMod n) (ZMod n) ℂ) - diagonal a := by
  classical
  have hfull := sum_cyclicShift_conj_diagonal (n := n) a
  have hzero : cyclicShiftPow (0 : ZMod n) * diagonal a * (cyclicShiftPow (0 : ZMod n))ᴴ =
      diagonal a := by
    rw [cyclicShiftPow_zero]
    simp
  have hsplit : (∑ r : ZMod n,
        cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ) =
      cyclicShiftPow (0 : ZMod n) * diagonal a * (cyclicShiftPow (0 : ZMod n))ᴴ +
        ∑ r ∈ (Finset.univ.erase 0),
          cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ := by
    have h := (Finset.sum_erase_add (Finset.univ : Finset (ZMod n))
      (fun r => cyclicShiftPow r * diagonal a * (cyclicShiftPow r)ᴴ)
      (Finset.mem_univ 0)).symm
    rw [h]
    abel
  rw [hfull, hzero] at hsplit
  rw [hsplit]
  abel

end

end Qatlib.Papers.HamInversion26.SpinInversion.SpectralTwirl
