/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CliffordTDensity
import Mathlib.Analysis.CStarAlgebra.Matrix
set_option warningAsError false
open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

section

open Matrix Metric Set

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

open QuantumInfo.SU2

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

theorem isClosed_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] :
    IsClosed (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have hset : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))
      = (fun U : Matrix n n ℂ => U * star U) ⁻¹' {1} := by
    ext U
    simp [Matrix.mem_unitaryGroup_iff]
  rw [hset]
  exact isClosed_singleton.preimage (continuous_id.mul continuous_star)

def su2Set : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ U.det = 1}

theorem isClosed_su2Set : IsClosed su2Set := by
  have hset : su2Set = (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
      ∩ (fun U : Matrix (Fin 2) (Fin 2) ℂ => U.det) ⁻¹' {1} := rfl
  rw [hset]
  exact isClosed_unitaryGroup.inter (isClosed_singleton.preimage continuous_id.matrix_det)

theorem su2Set_subset_closedBall :
    su2Set ⊆ closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  intro U hU
  rw [mem_closedBall_zero_iff, CStarRing.norm_of_mem_unitary hU.1]

theorem isCompact_su2Set : IsCompact su2Set :=
  (isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1).of_isClosed_subset
    isClosed_su2Set su2Set_subset_closedBall

theorem su2Set_subset_closure_cliffordT :
    su2Set ⊆ closure (cliffordT : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  fun _ hU => det_one_mem_cliffordTLim hU.1 hU.2

theorem exists_finite_cliffordT_net {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ A ∈ F, A ∈ cliffordT) ∧ ∀ U ∈ su2Set, ∃ A ∈ F, dist U A < ε := by
  obtain ⟨F, hFsub, hFnet⟩ :=
    IsCompact.exists_finite_net isCompact_su2Set su2Set_subset_closure_cliffordT hε
  exact ⟨F, fun A hA => hFsub hA, hFnet⟩

end Qatlib.Concepts.UnbiasedBases.ThreeBasis

end
