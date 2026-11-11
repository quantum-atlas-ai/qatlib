/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Qatlib.Papers.HamEvoPrec13.MainResults.SparseMatching

/-!
# Matched block Hamiltonians

Berry--Cleve--Somma, "Exponential improvement in precision for Hamiltonian-evolution
simulation", fixed arXiv:1308.5424v3, Eqs. (2)--(6) and Lemma 1.

Lemma 1 decomposes a one-sparse real Hamiltonian into equally weighted sums of commuting
self-inverse Hamiltonians. The building block of that decomposition is a matrix whose
`2 × 2` blocks, indexed by a partial matching `mate`, are either `±σₓ` (`d = 0`, `y = ±1`)
or `±1` (`d = ±1`, `y = 0`), with `1 × 1` blocks at the fixed points of the matching.

This file shows that every such matrix is a symmetric one-sparse involution, and that any
two of them commute. These are exactly the properties the paper needs: symmetry makes the
matrix a Hamiltonian, one-sparseness keeps it inside the paper's class, `U * U = 1` gives
Eq. (5) (`U` is self-inverse), and commutation lets the exponential of the sum factor
without error.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamEvoPrec13.MainResults

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coefficient data that make a matched block matrix a self-inverse Hamiltonian.

`inv` says the matching is involutive, `diag_pair` and `off_pair` say the two coefficient
families are constant on matched pairs (so both `2 × 2` blocks are symmetric), `off_fixed`
makes the off-diagonal coefficient vanish at fixed points, `orthogonal` is the `d * y = 0`
condition that makes every block either `±σₓ` or `±1`, and `unit` normalizes the nonzero
coefficient to `±1`. -/
structure MatchedUnit (mate : n → n) (d y : n → ℝ) : Prop where
  /-- The matching is an involution. -/
  inv : ∀ a, mate (mate a) = a
  /-- The diagonal coefficient is constant on matched pairs. -/
  diag_pair : ∀ a, d (mate a) = d a
  /-- The off-diagonal coefficient is constant on matched pairs. -/
  off_pair : ∀ a, y (mate a) = y a
  /-- The off-diagonal coefficient vanishes at fixed points. -/
  off_fixed : ∀ a, mate a = a → y a = 0
  /-- Every block is either diagonal or off-diagonal. -/
  orthogonal : ∀ a, d a * y a = 0
  /-- The block is a unit vector. -/
  unit : ∀ a, d a * d a + y a * y a = 1

/-- The block matrix attached to a matching `mate`, with diagonal block value `d a` and
off-diagonal block value `y a` in row `a`. This is the matrix shape used in Eqs. (2)--(4)
of the paper. -/
def matchedBlock (mate : n → n) (d y : n → ℝ) : Matrix n n ℝ :=
  fun a b => if b = a then d a else if b = mate a then y a else 0

/-- The diagonal entry of a matched block matrix is the diagonal coefficient. -/
@[simp]
theorem matchedBlock_diag (mate : n → n) (d y : n → ℝ) (a : n) :
    matchedBlock mate d y a a = d a := by
  simp [matchedBlock]

/-- At a non-fixed point the off-diagonal entry in row `a` is the off-diagonal coefficient. -/
theorem matchedBlock_off {mate : n → n} {d y : n → ℝ} {a : n} (h : mate a ≠ a) :
    matchedBlock mate d y a (mate a) = y a := by
  rw [matchedBlock]
  rw [if_neg h, if_pos rfl]

/-- By symmetry of the matching the transposed off-diagonal entry agrees with the
off-diagonal coefficient of the partner. -/
theorem matchedBlock_off' {mate : n → n} {d y : n → ℝ} (hinv : ∀ a, mate (mate a) = a)
    {a : n} (h : mate a ≠ a) : matchedBlock mate d y (mate a) a = y (mate a) := by
  rw [matchedBlock]
  rw [if_neg (Ne.symm h), if_pos (hinv a).symm]

/-- Entries of a matched block matrix outside the diagonal and the matching vanish. -/
theorem matchedBlock_other {mate : n → n} {d y : n → ℝ} {a b : n} (hb : b ≠ a)
    (hm : b ≠ mate a) : matchedBlock mate d y a b = 0 := by
  rw [matchedBlock]
  rw [if_neg hb, if_neg hm]

/-- A sum of a function supported on `{a, mate a}` with `mate a ≠ a` reduces to two terms. -/
private theorem sum_univ_eq_pair {mate : n → n} {f : n → ℝ} {a : n} (h : mate a ≠ a)
    (hz : ∀ c, c ≠ a → c ≠ mate a → f c = 0) : ∑ c, f c = f a + f (mate a) := by
  have hsub : ∑ c, f c = ∑ c ∈ ({a, mate a} : Finset n), f c := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro c _; simp
    · intro c _ hc
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      exact hz c hc.1 hc.2
  rw [hsub, show ({a, mate a} : Finset n) = insert a {mate a} from rfl]
  rw [Finset.sum_insert (by simpa [Finset.mem_singleton, eq_comm] using h),
    Finset.sum_singleton]

/-- A sum of a function supported on a fixed point reduces to one term. -/
private theorem sum_univ_eq_self {f : n → ℝ} {a : n}
    (hz : ∀ c, c ≠ a → f c = 0) : ∑ c, f c = f a := by
  refine Finset.sum_eq_single a ?_ ?_
  · intro c _ hc; exact hz c hc
  · intro hmem; exact absurd (Finset.mem_univ a) hmem

/-- A matched block matrix is symmetric, because both coefficient families are constant
on matched pairs. -/
theorem matchedBlock_isSymm {mate : n → n} {d y : n → ℝ} (h : MatchedUnit mate d y) :
    (matchedBlock mate d y).IsSymm := by
  refine Matrix.IsSymm.ext fun a b => ?_
  by_cases hba : b = a
  · subst b; rfl
  · by_cases hbm : b = mate a
    · subst b
      rw [matchedBlock_off' h.inv hba, matchedBlock_off hba, h.off_pair a]
    · rw [matchedBlock_other hba hbm, matchedBlock_other (Ne.symm hba)]
      intro ha
      exact hbm (by rw [← h.inv b, ← ha])

/-- A matched block matrix is one-sparse: in each row only the diagonal and the matched
entry can be nonzero, and `d * y = 0` excludes one of them. -/
theorem matchedBlock_isOneSparse {mate : n → n} {d y : n → ℝ} (h : MatchedUnit mate d y) :
    IsOneSparse (matchedBlock mate d y) := by
  intro a
  refine Finset.card_le_one_iff.mpr (fun {x z} hx hz => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hz
  have hx' : x = a ∨ x = mate a := by
    by_contra hc
    rw [not_or] at hc
    exact hx (matchedBlock_other hc.1 hc.2)
  have hz' : z = a ∨ z = mate a := by
    by_contra hc
    rw [not_or] at hc
    exact hz (matchedBlock_other hc.1 hc.2)
  rcases hx' with hx' | hx'
  · rcases hz' with hz' | hz'
    · rw [hx', hz']
    · rcases eq_or_ne (mate a) a with hma | hma
      · rw [hx', hz', hma]
      · exfalso
        have hda : d a ≠ 0 := fun h0 => hx (by rw [hx', matchedBlock_diag, h0])
        have hya : y a ≠ 0 := fun h0 => hz (by rw [hz', matchedBlock_off hma, h0])
        exact mul_ne_zero hda hya (h.orthogonal a)
  · rcases hz' with hz' | hz'
    · rcases eq_or_ne (mate a) a with hma | hma
      · rw [hx', hz', hma]
      · exfalso
        have hda : d a ≠ 0 := fun h0 => hz (by rw [hz', matchedBlock_diag, h0])
        have hya : y a ≠ 0 := fun h0 => hx (by rw [hx', matchedBlock_off hma, h0])
        exact mul_ne_zero hda hya (h.orthogonal a)
    · rw [hx', hz']

/-- A matched block matrix squares to the identity: each `2 × 2` block is `±σₓ` or `±1`,
and each fixed point carries a `±1` entry. This is the self-inverse property used in
Eq. (5) of the paper. -/
theorem matchedBlock_mul_self {mate : n → n} {d y : n → ℝ} (h : MatchedUnit mate d y) :
    matchedBlock mate d y * matchedBlock mate d y = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hba : b = a
  · subst b
    rw [Matrix.one_apply, if_pos rfl]
    rcases eq_or_ne (mate a) a with hma | hma
    · rw [sum_univ_eq_self (a := a)
        (f := fun c => matchedBlock mate d y a c * matchedBlock mate d y c a)
        (by intro c hc; simp [matchedBlock, hc, Ne.symm hc, hma])]
      simp only [matchedBlock_diag]
      have hunit := h.unit a
      rw [h.off_fixed a hma, mul_zero, add_zero] at hunit
      exact hunit
    · rw [sum_univ_eq_pair (a := a) hma
        (f := fun c => matchedBlock mate d y a c * matchedBlock mate d y c a)
        (by intro c hc hcm; simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm])]
      simp only [matchedBlock_diag, matchedBlock_off hma, matchedBlock_off' h.inv hma,
        h.off_pair a]
      exact h.unit a
  · rw [Matrix.one_apply, if_neg (Ne.symm hba)]
    by_cases hbm : b = mate a
    · subst b
      rw [sum_univ_eq_pair (a := a) hba
        (f := fun c => matchedBlock mate d y a c * matchedBlock mate d y c (mate a))
        (by intro c hc hcm; simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm])]
      simp only [matchedBlock_diag, matchedBlock_off hba,
        h.diag_pair a, h.orthogonal a, mul_comm (y a) (d a)]
      simp
    · rcases eq_or_ne (mate a) a with hma | hma
      · rw [sum_univ_eq_self (a := a)
          (f := fun c => matchedBlock mate d y a c * matchedBlock mate d y c b)
          (by intro c hc; simp [matchedBlock, hc, Ne.symm hc, hma])]
        simp [matchedBlock, hba, hbm, hma]
      · rw [sum_univ_eq_pair (a := a) hma
          (f := fun c => matchedBlock mate d y a c * matchedBlock mate d y c b)
          (by intro c hc hcm; simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm])]
        simp [matchedBlock, hba, hbm, hma, h.inv a]

/-- Two matched block matrices with the same matching commute: every block lies in the
two-dimensional algebra spanned by the identity and `σₓ`, which is commutative. -/
theorem matchedBlock_mul_comm {mate : n → n} {d y d' y' : n → ℝ}
    (h : MatchedUnit mate d y) (h' : MatchedUnit mate d' y') :
    Commute (matchedBlock mate d y) (matchedBlock mate d' y') := by
  rw [Commute]
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hba : b = a
  · subst b
    rcases eq_or_ne (mate a) a with hma | hma
    · rw [sum_univ_eq_self (a := a)
          (f := fun c => matchedBlock mate d y a c * matchedBlock mate d' y' c a),
        sum_univ_eq_self (a := a)
          (f := fun c => matchedBlock mate d' y' a c * matchedBlock mate d y c a)]
      · simp only [matchedBlock_diag]
        ring
      · intro c hc
        simp [matchedBlock, hc, Ne.symm hc, hma]
      · intro c hc
        simp [matchedBlock, hc, Ne.symm hc, hma]
    · rw [sum_univ_eq_pair (a := a) hma
          (f := fun c => matchedBlock mate d y a c * matchedBlock mate d' y' c a),
        sum_univ_eq_pair (a := a) hma
          (f := fun c => matchedBlock mate d' y' a c * matchedBlock mate d y c a)]
      · simp only [matchedBlock_diag, matchedBlock_off hma, matchedBlock_off' h.inv hma,
          matchedBlock_off' h'.inv hma, h'.off_pair a, h.off_pair a]
        ring
      · intro c hc hcm
        simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]
      · intro c hc hcm
        simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]
  · by_cases hbm : b = mate a
    · subst b
      rw [sum_univ_eq_pair (a := a) hba
            (f := fun c => matchedBlock mate d y a c * matchedBlock mate d' y' c (mate a)),
          sum_univ_eq_pair (a := a) hba
            (f := fun c => matchedBlock mate d' y' a c * matchedBlock mate d y c (mate a))]
      · simp only [matchedBlock_diag, matchedBlock_off hba, matchedBlock_off' h'.inv hba,
          matchedBlock_off' h.inv hba, h'.diag_pair a, h.diag_pair a]
        ring
      · intro c hc hcm
        simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]
      · intro c hc hcm
        simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]
    · rcases eq_or_ne (mate a) a with hma | hma
      · rw [sum_univ_eq_self (a := a)
            (f := fun c => matchedBlock mate d y a c * matchedBlock mate d' y' c b),
          sum_univ_eq_self (a := a)
            (f := fun c => matchedBlock mate d' y' a c * matchedBlock mate d y c b)]
        · simp [matchedBlock, hba, hbm, hma]
        · intro c hc
          simp [matchedBlock, hc, Ne.symm hc, hma]
        · intro c hc
          simp [matchedBlock, hc, Ne.symm hc, hma]
      · rw [sum_univ_eq_pair (a := a) hma
            (f := fun c => matchedBlock mate d y a c * matchedBlock mate d' y' c b),
          sum_univ_eq_pair (a := a) hma
            (f := fun c => matchedBlock mate d' y' a c * matchedBlock mate d y c b)]
        · simp [matchedBlock, hba, hbm, hma, h.inv a]
        · intro c hc hcm
          simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]
        · intro c hc hcm
          simp [matchedBlock, hc, Ne.symm hc, hcm, Ne.symm hcm]

end Qatlib.Papers.HamEvoPrec13.MainResults
