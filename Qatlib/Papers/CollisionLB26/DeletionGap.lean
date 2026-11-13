/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.PositiveGap

/-!
# Spectral separation for tuple-deletion adjacency

This module specializes tuple-deletion operators to injective tuples of finite labels for the
spectral argument in [MagniezZur2026]. It identifies the kernel at eigenvalue `-s`, constructs a
nonzero vector at that eigenvalue under the size assumptions, and bounds real eigenvalues
strictly above it.

## Main statements

* `actual_bottom_kernel`: the shifted adjacency kernel equals the deletion kernel.
* `actual_bottom_exists`: existence of an eigenvector with eigenvalue `-s`.
* `actual_positive_gram_gap` and `actual_nonbottom_eigenvalue`: lower bounds `N-2*s+2` and
  `N-3*s+2` for the respective eigenvalues.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.CollisionLB26.DeletionGap
open Qatlib.Foundations.MatrixGeometry.TupleDeletion
local instance (n : ℕ) : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a=b)

/-- The type of injective tuples of length `s` with labels in `Fin N`. -/
abbrev Vertices (s N : ℕ) := InjectiveTuple (Fin s) (Fin N)

/-- The complex tuple-deletion adjacency matrix on injective tuples from `Fin s` to `Fin N`. -/
def actualAdjacency (s N : ℕ) : Matrix (Vertices s N) (Vertices s N) ℂ := adjacency

/-- The complex linear action of `actualAdjacency` on the Euclidean space of injective tuples. -/
def actualAdjacencyAction (s N : ℕ) : EuclideanSpace ℂ (Vertices s N) →ₗ[ℂ] EuclideanSpace ℂ (Vertices s N) :=
  Matrix.toEuclideanLin (actualAdjacency s N)

/-- The kernel of the adjacency matrix shifted by `s` times the identity equals the kernel of
the tuple-deletion matrix; see [MagniezZur2026]. -/
theorem actual_bottom_kernel (s N : ℕ) :
    ((actualAdjacency s N)+(s : ℂ) • 1).mulVecLin.ker=
      (deletion (I := Fin s) (L := Fin N)).mulVecLin.ker := by
  simpa only [actualAdjacency,Fintype.card_fin] using!
      (shifted_adjacency_kernel (I := Fin s) (L := Fin N))

/-- For `s > 0` and `2*s ≤ N`, the tuple-deletion adjacency matrix possesses a nonzero
eigenvector with eigenvalue `-s`, as used in [MagniezZur2026]. -/
theorem actual_bottom_exists (s N : ℕ) (hs : 0 < s) (hN : 2*s ≤ N) :
    ∃ v : Vertices s N → ℂ,v ≠ 0 ∧ actualAdjacency s N*ᵥ v=(-(s : ℂ)) • v := by
  simpa only [Vertices,actualAdjacency,Fintype.card_fin] using!
    (exists_bottom_eigenvector (I := Fin s) (L := Fin N)
      (by simpa only [Fintype.card_fin] using! hs) (by simpa only [Fintype.card_fin] using! hN))

/-- For `s > 0` and `2*s ≤ N`, every positive real eigenvalue of the deletion Gram action with a
nonzero eigenvector is at least `N-2*s+2`. -/
theorem actual_positive_gram_gap (s N : ℕ) (hs : 0 < s) (hN : 2*s ≤ N)
    (v : EuclideanSpace ℂ (Vertices s N)) (hv : v ≠ 0) (ev : ℝ) (hev : 0 < ev)
    (he : deletionGramAction v=(ev : ℂ) • v) :
    (N : ℝ)-2*(s : ℝ)+2 ≤ ev := by
  have hsn : s ≤ N := by omega
  simpa only [Fintype.card_fin] using!
    (deletionGram_source_gap (I := Fin s) (L := Fin N) v hv
      (by simpa only [Fintype.card_fin] using! hs) (by simpa only [Fintype.card_fin] using! hsn) ev hev he)

/-- For `s > 0` and `2*s ≤ N`, a real eigenvalue of the adjacency action strictly above `-s` is
at least `N-3*s+2`, as used in [MagniezZur2026]. -/
theorem actual_nonbottom_eigenvalue (s N : ℕ) (hs : 0 < s) (hN : 2*s ≤ N)
    (v : EuclideanSpace ℂ (Vertices s N)) (hv : v ≠ 0) (α : ℝ) (hα : -(s : ℝ) < α)
    (he : actualAdjacencyAction s N v=(α : ℂ) • v) :
    (N : ℝ)-3*(s : ℝ)+2 ≤ α := by
  have hraw : adjacency (I := Fin s) (L := Fin N)*ᵥ WithLp.ofLp v=(α : ℂ) • WithLp.ofLp v := by
    exact congrArg WithLp.ofLp he
  have hg : deletionGramAction v=((α+(s : ℝ) : ℝ) : ℂ) • v := by
    change WithLp.toLp 2 (((deletion (I := Fin s) (L := Fin N))ᴴ*deletion)*ᵥ WithLp.ofLp v)=_
    rw [deletion_gram,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hraw]
    ext y
    change (α : ℂ)*v y+(Fintype.card (Fin s) : ℂ)*v y=(((α+(s : ℝ) : ℝ) : ℂ))*v y
    simp only [Fintype.card_fin,Complex.ofReal_add,Complex.ofReal_natCast]
    ring
  have hp : 0 < α+(s : ℝ) := by linarith
  have h := actual_positive_gram_gap s N hs hN v hv (α+(s : ℝ)) hp hg
  linarith
end Qatlib.Papers.CollisionLB26.DeletionGap
