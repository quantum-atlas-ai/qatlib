module

public import Qatlib.Papers.WalkSearch06.MainResults.UnitSingularSector
public import Qatlib.Papers.WalkSearch06.ReverseWalk.CycleDiscriminant

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.WalkSearch06.ReverseWalk.TimeReversal
open Matrix
open Qatlib.Papers.WalkSearch06.MainResults
open Qatlib.Papers.WalkSearch06.ReverseWalk.CycleDiscriminant
open scoped Matrix.Norms.L2Operator

namespace QatlibTests.WalkSearch06CycleDiscriminant

/-- The common-subspace identity action on the whole two-dimensional walk space. -/
theorem unit_sector_top_consumer :
    (∀ v ∈ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) ⊓ ⊤,
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).reflection
        ((⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).reflection v) = v) :=
  (szegedy_unit_singular_sector ⊤ ⊤).1

/-- The common-orthogonal-complement identity action on the whole two-dimensional
walk space when both subspaces are zero. -/
theorem unit_sector_orthogonal_consumer (v : EuclideanSpace ℂ (Fin 2)) :
    (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).reflection
      ((⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).reflection v) = v :=
  (szegedy_unit_singular_sector ⊥ ⊥).2 v (by simp)

/-- The discriminant of the directed three-cycle has Euclidean operator norm one. -/
theorem cycle_three_discriminant_norm :
    ‖discriminant (directedCycle 3) (directedCyclePi 3)‖ = 1 :=
  directedCycle_discriminant_norm 3 (by norm_num)

/-- A uniform constant, chosen before the dimension, bounds the Euclidean operator norm
of the discriminant of every non-degenerate directed cycle. -/
theorem cycle_uniform_consumer :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 2 ≤ n →
      ‖discriminant (directedCycle n) (directedCyclePi n)‖ ≤ C :=
  directedCycle_discriminant_norm_le_uniform

/-- The constant vector is a fixed vector of the four-cycle discriminant. -/
theorem cycle_four_eigenvector :
    discriminant (directedCycle 4) (directedCyclePi 4) *ᵥ (fun _ => (1 : ℝ)) =
      fun _ => 1 :=
  directedCycle_discriminant_mulVec_const_one 4 (by norm_num)

/-- The three-cycle walk fixes every vector under the two conditional-span reflections. -/
theorem cycle_three_reflection_consumer (v : EuclideanSpace ℂ (Fin 3 × Fin 3)) :
    (directedCycleReverseSpan 3).reflection ((directedCycleForwardSpan 3).reflection v) = v :=
  directedCycle_reflection_product_apply 3 (by norm_num) v

end QatlibTests.WalkSearch06CycleDiscriminant
