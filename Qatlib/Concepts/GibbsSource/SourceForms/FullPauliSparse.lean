/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliFamily

@[expose] public section


/-!
# One nonzero entry per row and column of the complete local Pauli family

This module records the actual computational-basis support of all `3n`
unscaled local Pauli proposals.  The property allows zero rows and columns;
it imposes no nonzero-amplitude or frequency-separation hypothesis.  It is
not asserted after an arbitrary energy-basis rotation.
-/

open Qatlib.Concepts.CodingDecoding.CssTesters



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix

/-- Every row and column is supported at at most one coordinate.  The chosen
coordinate is permitted to have zero amplitude. -/
def fullMatrixOneSparse {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ i, ∃ j, ∀ k, k ≠ j → A i k = 0) ∧
  (∀ j, ∃ i, ∀ k, k ≠ i → A k j = 0)

/-- Scalar multiplication does not enlarge the row or column supports. -/
theorem fullMatrixOneSparse_smul {D : ℕ} (c : ℂ) {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : fullMatrixOneSparse A) : fullMatrixOneSparse (c • A) := by
  rcases hA with ⟨hrow, hcol⟩
  constructor
  · intro i
    obtain ⟨j, hj⟩ := hrow i
    refine ⟨j, fun k hk => ?_⟩
    simp [Matrix.smul_apply, hj k hk]
  · intro j
    obtain ⟨i, hi⟩ := hcol j
    refine ⟨i, fun k hk => ?_⟩
    simp [Matrix.smul_apply, hi k hk]

/-- Products of matrices with at most one supported coordinate in every row
and column retain the same property. -/
theorem fullMatrixOneSparse_mul {D : ℕ} {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : fullMatrixOneSparse A) (hB : fullMatrixOneSparse B) :
    fullMatrixOneSparse (A * B) := by
  classical
  constructor
  · intro i
    obtain ⟨t, ht⟩ := hA.1 i
    obtain ⟨j, hj⟩ := hB.1 t
    refine ⟨j, fun k hk => ?_⟩
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s = t
    · subst s
      simp [hj k hk]
    · simp [ht s hs]
  · intro j
    obtain ⟨t, ht⟩ := hB.2 j
    obtain ⟨i, hi⟩ := hA.2 t
    refine ⟨i, fun k hk => ?_⟩
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : s = t
    · subst s
      simp [hi k hk]
    · simp [ht s hs]

/-- A bijective coordinate enumeration preserves a supplied row/column
support description, including empty index types. -/
theorem fullMatrixOneSparse_reindex_of_rows_cols {D : ℕ} {ι : Type*}
    (e : ι ≃ Fin D) (A : Matrix ι ι ℂ)
    (hrow : ∀ i, ∃ j, ∀ k, k ≠ j → A i k = 0)
    (hcol : ∀ j, ∃ i, ∀ k, k ≠ i → A k j = 0) :
    fullMatrixOneSparse (Matrix.reindex e e A) := by
  constructor
  · intro i
    obtain ⟨j, hj⟩ := hrow (e.symm i)
    refine ⟨e j, fun k hk => ?_⟩
    change A (e.symm i) (e.symm k) = 0
    apply hj
    intro h
    apply hk
    simpa only [e.apply_symm_apply] using congrArg e h
  · intro j
    obtain ⟨i, hi⟩ := hcol (e.symm j)
    refine ⟨e i, fun k hk => ?_⟩
    change A (e.symm k) (e.symm j) = 0
    apply hi
    intro h
    apply hk
    simpa only [e.apply_symm_apply] using congrArg e h

/-- The actual local bit flip has one supported entry in each row and
column under the fixed register-to-`Fin` enumeration. -/
theorem fullPauliX_oneSparse (n : ℕ) (i : Fin n) :
    fullMatrixOneSparse (fullPauliX n i) := by
  classical
  unfold fullPauliX
  rw [Matrix.coe_reindexAlgEquiv]
  apply fullMatrixOneSparse_reindex_of_rows_cols
  · intro a
    refine ⟨a - Pi.single i 1, fun b hb => ?_⟩
    have hab : a ≠ b + Pi.single i 1 := by
      intro h
      exact hb ((eq_sub_iff_add_eq).mpr h.symm)
    simp [cssPauliX, hab]
  · intro b
    refine ⟨b + Pi.single i 1, fun a ha => ?_⟩
    simp [cssPauliX, ha]

/-- The actual local phase Pauli is diagonal in the same enumeration. -/
theorem fullPauliZ_oneSparse (n : ℕ) (i : Fin n) :
    fullMatrixOneSparse (fullPauliZ n i) := by
  classical
  unfold fullPauliZ
  rw [Matrix.coe_reindexAlgEquiv]
  apply fullMatrixOneSparse_reindex_of_rows_cols
  · intro a
    refine ⟨a, fun b hb => ?_⟩
    simp [cssPauliZ, Ne.symm hb]
  · intro b
    refine ⟨b, fun a ha => ?_⟩
    simp [cssPauliZ, ha]

/-- The included `Y = i X Z` retains its original complex phase and the
same row/column support bound. -/
theorem fullPauliY_oneSparse (n : ℕ) (i : Fin n) :
    fullMatrixOneSparse (fullPauliY n i) := by
  unfold fullPauliY
  exact fullMatrixOneSparse_smul Complex.I
    (fullMatrixOneSparse_mul (fullPauliX_oneSparse n i) (fullPauliZ_oneSparse n i))

/-- All actual `3n` equal-weight, unscaled Pauli proposals are one-sparse in
the computational basis.  Arbitrary spectral rotations are not assumed to
preserve this property. -/
theorem fullPauliFamily_oneSparse (n : ℕ) (P : FullPauliLabel n) :
    fullMatrixOneSparse (fullPauliFamily n P) := by
  unfold fullPauliFamily
  split
  · exact fullPauliX_oneSparse n P.1
  · split
    · exact fullPauliY_oneSparse n P.1
    · exact fullPauliZ_oneSparse n P.1

end Qatlib.Concepts.GibbsSource.SourceForms
