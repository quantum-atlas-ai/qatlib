/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Affine transformations of Hermitian spectra

The module transports finite Hermitian diagonalizations and characteristic polynomials through
real affine transformations `a • 1 + b • A`. For nonnegative `b`, `eigenvalues₀_affine`
identifies the ordered eigenvalues, and `native_gap_affine` computes the scaling of the gap
between the two lowest entries.

These are finite spectral calculus identities in the setting of [Bhatia1997].

## Main statements

* `affine_charpoly`: factorization using the affinely transformed eigenvalues.
* `eigenvalues₀_affine`: nonnegative scaling preserves the ordering of the transformed spectrum.
* `native_gap_affine`: the lowest spectral gap is multiplied by `b`.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section
open scoped Matrix
open Matrix Unitary

namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : Matrix I I ℂ}

omit [Fintype I] in

/-- A real affine combination of the identity and a Hermitian matrix is Hermitian. -/
theorem affine_hermitian (hA : A.IsHermitian) (a b : ℝ) :
    (a • (1 : Matrix I I ℂ) + b • A).IsHermitian :=
  (Matrix.isHermitian_one.smul (k := a) (by rfl)).add (hA.smul (k := b) (by rfl))

/-- An affine transform of a Hermitian matrix is diagonalized by the original eigenvector
unitary, with eigenvalues `a + b * λ`. -/
theorem affine_diagonalization (hA : A.IsHermitian) (a b : ℝ) :
    a • (1 : Matrix I I ℂ) + b • A =
      conjStarAlgAut ℂ (Matrix I I ℂ) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => ((a + b * hA.eigenvalues i : ℝ) : ℂ))) := by
  have hd : Matrix.diagonal (fun i => ((a + b * hA.eigenvalues i : ℝ) : ℂ)) =
      (a : ℂ) • (1 : Matrix I I ℂ) +
        (b : ℂ) • Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [hd, map_add, map_smul, map_smul, map_one]
  have hs := hA.spectral_theorem
  change A = conjStarAlgAut ℂ (Matrix I I ℂ) hA.eigenvectorUnitary
    (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) at hs
  rw [← hs]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The characteristic polynomial of `a • 1 + b • A` factors into linear terms at the affine
images of the Hermitian eigenvalues. -/
theorem affine_charpoly (hA : A.IsHermitian) (a b : ℝ) :
    (a • (1 : Matrix I I ℂ) + b • A).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((a + b * hA.eigenvalues i : ℝ) : ℂ)) := by
  rw [affine_diagonalization hA a b, conjStarAlgAut_apply,
    Matrix.charpoly_mul_comm, ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

/-- The eigenvalues indexed by the original finite type and those indexed in spectral order have
the same multiset. -/
theorem eigenvalue_multiset (hA : A.IsHermitian) :
    Multiset.map hA.eigenvalues Finset.univ.val =
      Multiset.map hA.eigenvalues₀ Finset.univ.val := by
  have hr := hA.roots_charpoly_eq_eigenvalues.symm.trans hA.roots_charpoly_eq_eigenvalues₀
  apply Multiset.map_injective Complex.ofReal_injective
  simpa only [Multiset.map_map, Function.comp_def] using! hr

/-- The real parts of the characteristic roots of an affine Hermitian transform form the
multiset of affine images of the ordered eigenvalues. -/
theorem affine_real_roots (hA : A.IsHermitian) (a b : ℝ) :
    ((a • (1 : Matrix I I ℂ) + b • A).charpoly.roots.map Complex.re) =
      Multiset.map (fun i => a + b * hA.eigenvalues₀ i) Finset.univ.val := by
  have hr : (a • (1 : Matrix I I ℂ) + b • A).charpoly.roots =
      Multiset.map (fun i => ((a + b * hA.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    rw [affine_charpoly hA a b, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
  rw [hr, Multiset.map_map]
  simp only [Function.comp_def, Complex.ofReal_re]
  change Multiset.map ((fun x : ℝ => a + b * x) ∘ hA.eigenvalues) Finset.univ.val =
    Multiset.map ((fun x : ℝ => a + b * x) ∘ hA.eigenvalues₀) Finset.univ.val
  rw [← Multiset.map_map, ← Multiset.map_map, eigenvalue_multiset]

/-- For nonnegative `b`, the ordered eigenvalues of `a • 1 + b • A` are `a + b * λ` in the
original spectral order. -/
theorem eigenvalues₀_affine (hA : A.IsHermitian) (a b : ℝ) (hb : 0 ≤ b) :
    (affine_hermitian hA a b).eigenvalues₀ = fun i => a + b * hA.eigenvalues₀ i := by
  apply List.ofFn_inj.mp
  rw [← (affine_hermitian hA a b).sort_roots_charpoly_eq_eigenvalues₀]
  change (((a • (1 : Matrix I I ℂ) + b • A).charpoly.roots.map Complex.re).sort (· ≥ ·)) = _
  rw [affine_real_roots hA a b]
  simp only [Fin.univ_val_map, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  apply Antitone.sortedGE_ofFn
  intro i j hij
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hA.eigenvalues₀_antitone hij) hb)

/-- Each ordered eigenvalue of an affine Hermitian transform is the corresponding affine image
when the scale is nonnegative. -/
theorem eigenvalues₀_affine_apply (hA : A.IsHermitian) (a b : ℝ) (hb : 0 ≤ b)
    (i : Fin (Fintype.card I)) :
    (affine_hermitian hA a b).eigenvalues₀ i = a + b * hA.eigenvalues₀ i :=
  congrFun (eigenvalues₀_affine hA a b hb) i

/-- In dimension at least two, both lowest ordered eigenvalues transform by `λ ↦ a + b * λ` for
nonnegative `b`. -/
theorem native_lowest_pair_affine (hA : A.IsHermitian) (hI : 2 ≤ Fintype.card I)
    (a b : ℝ) (hb : 0 ≤ b) :
    (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩ =
        a + b * hA.eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩ ∧
      (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ =
        a + b * hA.eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ :=
  ⟨eigenvalues₀_affine_apply hA a b hb _, eigenvalues₀_affine_apply hA a b hb _⟩

/-- In dimension at least two, a real affine transform with nonnegative scale multiplies the gap
between the two lowest ordered eigenvalues by that scale. -/
theorem native_gap_affine (hA : A.IsHermitian) (hI : 2 ≤ Fintype.card I)
    (a b : ℝ) (hb : 0 ≤ b) :
    (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ -
        (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩ =
      b * (hA.eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ -
        hA.eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩) := by
  rw [eigenvalues₀_affine_apply hA a b hb, eigenvalues₀_affine_apply hA a b hb]
  ring

/-- In dimension at least two, a real affine transform with positive scale multiplies the lowest
spectral gap by that scale. -/
theorem native_gap_positive_affine (hA : A.IsHermitian) (hI : 2 ≤ Fintype.card I)
    (a b : ℝ) (hb : 0 < b) :
    (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ -
        (affine_hermitian hA a b).eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩ =
      b * (hA.eigenvalues₀ ⟨Fintype.card I - 2, by omega⟩ -
        hA.eigenvalues₀ ⟨Fintype.card I - 1, by omega⟩) :=
  native_gap_affine hA hI a b hb.le

end Qatlib.Foundations.MatrixAlgebra.RankOneSecular
