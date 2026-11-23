module

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.SchmidtEuclidean

/-!
# Concrete consumer for the Euclidean Schmidt-rank overlap bound

The rank-one supported coefficient vector on two copies of `Fin 2` is normalized and has
left-row support `{0}`.  Both the direct Lemma-4 model bound and the uniform-constant
wrapper are exercised on this non-degenerate instance.
-/

set_option autoImplicit false

namespace QatlibTests.SpacetimeLB26SchmidtEuclideanRegression

open Qatlib.Papers.SpacetimeLB26.ScalarSupport.SchmidtEuclidean

/-- A normalized pure coefficient vector supported only in the first left-factor row. -/
def sampleSchmidtState : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun p : Fin 2 × Fin 2 =>
    if p.1 = 0 ∧ p.2 = 0 then (1 : ℂ) else 0

/-- The direct rank-one bound gives an overlap of at most one half in dimension two. -/
theorem sampleSchmidtState_overlap_le_half :
    maxEntangledOverlap 2 sampleSchmidtState ≤ 1 / 2 := by
  have hnorm : ‖sampleSchmidtState‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [sampleSchmidtState, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hsupport : ∀ p : Fin 2 × Fin 2, p.1 ∉ ({0} : Finset (Fin 2)) →
      sampleSchmidtState p = 0 := by
    intro p hp
    have h0 : p.1 ≠ 0 := fun h => hp (by simp [h])
    simp [sampleSchmidtState, h0]
  have hbound := schmidt_rank_overlap_bound (D := 2) (d := 1) (by norm_num) {0}
    (by norm_num : ({0} : Finset (Fin 2)).card = 1) sampleSchmidtState hnorm hsupport
  simpa using hbound

/-- The uniform theorem applies to the same concrete normalized state. -/
theorem sampleSchmidtState_uniform_wrapper :
    ∃ C : ℝ, 0 < C ∧
      maxEntangledOverlap 2 sampleSchmidtState ≤ C * (1 / 2) := by
  obtain ⟨C, hC, hbound⟩ := schmidt_rank_overlap_uniform_constant
  have hnorm : ‖sampleSchmidtState‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [sampleSchmidtState, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hsupport : ∀ p : Fin 2 × Fin 2, p.1 ∉ ({0} : Finset (Fin 2)) →
      sampleSchmidtState p = 0 := by
    intro p hp
    have h0 : p.1 ≠ 0 := fun h => hp (by simp [h])
    simp [sampleSchmidtState, h0]
  exact ⟨C, hC, by
    simpa using hbound 2 1 (by norm_num) {0}
      (by norm_num : ({0} : Finset (Fin 2)).card = 1) sampleSchmidtState hnorm hsupport⟩

end QatlibTests.SpacetimeLB26SchmidtEuclideanRegression
