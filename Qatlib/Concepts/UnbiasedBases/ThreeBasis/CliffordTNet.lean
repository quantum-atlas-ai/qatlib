/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CliffordTDensity
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite Clifford-T Nets for SU(2)

This module turns Clifford-T density into finite approximation sets using compactness. The
general lemma `IsCompact.exists_finite_net` produces a finite net with centers in a set whose
closure contains a given compact set. The matrix lemmas establish that `su2Set`, the
determinant-one two-dimensional unitaries, is closed, bounded in the L2 operator norm, and
compact.

The inclusion `su2Set_subset_closure_cliffordT` then yields `exists_finite_cliffordT_net`: for
every positive tolerance there is a finite collection of Clifford-T matrices approximating every
element of `su2Set`. This is the qualitative initial-net input used in Solovay-Kitaev
approximation [DawsonNielsen2006]; the theorem asserts existence without a cardinality or
gate-length estimate.

## Main statements

- `IsCompact.exists_finite_net` gives a finite net with centers in a prescribed dense set.
- `isCompact_su2Set` proves compactness of SU(2) in the matrix metric.
- `su2Set_subset_closure_cliffordT` records the required density inclusion.
- `exists_finite_cliffordT_net` supplies finite Clifford-T nets at every positive precision.

## References

- [Dawson and Nielsen, 2006][DawsonNielsen2006], *The Solovay-Kitaev algorithm*.
-/

open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

section

open Matrix Metric Set

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open QuantumInfo.SU2

/-- If a compact subset `K` of a metric space lies in the closure of `D`, then for every
positive `ε` there is a finite set of points in `D` whose open `ε`-balls cover `K`. -/
theorem IsCompact.exists_finite_net {X : Type*} [MetricSpace X] {K D : Set X} (hK : IsCompact K)
    (hKD : K ⊆ closure D) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, (↑F : Set X) ⊆ D ∧ ∀ x ∈ K, ∃ y ∈ F, dist x y < ε := by
  have hcover : K ⊆ ⋃ y ∈ D, ball y ε := by
    intro x hx
    obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.1 (hKD hx) ε hε
    exact mem_biUnion hyD (by rwa [mem_ball])
  obtain ⟨b, hbD, hbfin, hbcover⟩ :=
    hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro y hy
    exact hbD (hbfin.mem_toFinset.1 hy)
  · intro x hx
    obtain ⟨y, hyb, hxy⟩ := Set.mem_iUnion₂.1 (hbcover hx)
    exact ⟨y, hbfin.mem_toFinset.2 hyb, mem_ball.1 hxy⟩

/-- The set of unitary complex matrices indexed by a finite type is closed in the ambient matrix
space. -/
theorem isClosed_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] :
    IsClosed (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have hset : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))
      = (fun U : Matrix n n ℂ => U * star U) ⁻¹' {1} := by
    ext U
    simp [Matrix.mem_unitaryGroup_iff]
  rw [hset]
  exact isClosed_singleton.preimage (continuous_id.mul continuous_star)

/-- This set consists of the two-dimensional complex matrices that are unitary and have
determinant one. -/
def su2Set : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ U.det = 1}

/-- The set `su2Set` is closed, as the intersection of the unitary matrices with the
determinant-one level set. -/
theorem isClosed_su2Set : IsClosed su2Set := by
  have hset : su2Set = (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
      ∩ (fun U : Matrix (Fin 2) (Fin 2) ℂ => U.det) ⁻¹' {1} := rfl
  rw [hset]
  exact isClosed_unitaryGroup.inter (isClosed_singleton.preimage continuous_id.matrix_det)

/-- Every element of `su2Set` lies in the closed unit ball centered at the zero matrix for the
L2 operator norm. -/
theorem su2Set_subset_closedBall :
    su2Set ⊆ closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  intro U hU
  rw [mem_closedBall_zero_iff, CStarRing.norm_of_mem_unitary hU.1]

/-- The set `su2Set` is compact in the ambient matrix metric, since it is a closed subset of the
closed unit ball in a finite-dimensional space. -/
theorem isCompact_su2Set : IsCompact su2Set :=
  (isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1).of_isClosed_subset
    isClosed_su2Set su2Set_subset_closedBall

/-- Every determinant-one two-dimensional unitary matrix belongs to the topological closure of
the Clifford-T submonoid. -/
theorem su2Set_subset_closure_cliffordT :
    su2Set ⊆ closure (cliffordT : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  fun _ hU => det_one_mem_cliffordTLim hU.1 hU.2

/-- For every positive `ε`, a finite set of Clifford-T matrices approximates every matrix in
`su2Set` within distance strictly less than `ε`. This is the qualitative finite-net input
for the Solovay-Kitaev framework [DawsonNielsen2006]. -/
theorem exists_finite_cliffordT_net {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ A ∈ F, A ∈ cliffordT) ∧ ∀ U ∈ su2Set, ∃ A ∈ F, dist U A < ε := by
  obtain ⟨F, hFsub, hFnet⟩ :=
    IsCompact.exists_finite_net isCompact_su2Set su2Set_subset_closure_cliffordT hε
  exact ⟨F, fun A hA => hFsub hA, hFnet⟩

end Qatlib.Concepts.UnbiasedBases.ThreeBasis

end
